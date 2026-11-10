/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForge
public import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10Aux
import Computational.Proofs.CryptoGames.SM.Theorem8.Lemma10
import VCVio.OracleComp.EvalDist.Measure

/-!
# `DeliverForge` Lemma 10

**Checked by Lean.** Lifts Lemma 10 (hop H1 → H2) to the extended `DeliverForge` oracle
specification `specDF`: with a uniform CKA key in epoch `t_heal`, the simulation of `redCKAAuthDF`
is bounded by that of `redPRNGAuthDF` with the real root RNG.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM CryptoGames.SM.Engine CryptoGames.SM.Construction.AuthL10

namespace AuthL10DF

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ)

abbrev SMSpecDF (Γ T Sig SS RS M CCoins E : Type) :=
  unifSpec + specDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

abbrev SMCompDF (Γ T Sig SS RS M CCoins E : Type) :=
  AdversaryCompDF (PartyState Γ T Sig SS RS) M CCoins (Header T × E)

def stepCDF (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateC Γ T Sig SS RS M E I) × CKA.GameState Γ T) :=
  (simulateQ (cImpl cka Δcka mo.tH)
    ((implEDF (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esC)).run sc

def stepPDF (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateP Γ T Sig SS RS M E K) × PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDF (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

def runLDF (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) : ProbComp Bool := do
  let r ← (simulateQ (cImpl cka Δcka mo.tH)
    ((simulateQ (implEDF (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esC)).run sc
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runRDF (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implEDF (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDF_pure (mo : Mode) (b' : Bool) (esC : EStateC Γ T Sig SS RS M E I)
    (sc : CKA.GameState Γ T) :
    runLDF cka prng fs Δcka qep mo (pure b') esC sc = pure (authOut (2 + Δcka) mo.policy esC) := by
  simp [runLDF, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDF_pure (mo : Mode) (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runRDF cka prng fs Δcka qep mo (pure b') esP sp = pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runRDF, map_eq_bind_pure_comp]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
theorem runLDF_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    runLDF cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esC sc =
      stepCDF cka prng fs Δcka qep mo q esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runLDF, stepCDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runRDF_query_bind (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runRDF cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDF cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runRDF, stepPDF, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDF_coins (mo : Mode) (n : unifSpec.Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDF cka prng fs Δcka qep mo (.inl n) esC sc =
      stepC cka prng fs Δcka qep mo (.inl n) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDF_coins (mo : Mode) (n : unifSpec.Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDF cka prng fs Δcka qep mo (.inl n) esP sp =
      stepP cka prng fs Δcka qep mo (.inl n) esP sp := rfl

omit [DecidableEq I] [SampleableType KR] [SampleableType KC] [SampleableType K] in
@[simp]
theorem stepCDF_base (mo : Mode)
    (q : (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) :
    stepCDF cka prng fs Δcka qep mo (.inr (.inl q)) esC sc =
      stepC cka prng fs Δcka qep mo (.inr q) esC sc := rfl

omit [SampleableType KR] [SampleableType KC] in
@[simp]
theorem stepPDF_base (mo : Mode)
    (q : (SM.spec (PartyState Γ T Sig SS RS) M CCoins (Header T × E)).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    stepPDF cka prng fs Δcka qep mo (.inr (.inl q)) esP sp =
      stepP cka prng fs Δcka qep mo (.inr q) esP sp := rfl

theorem stepCDF_abort (mo : Mode)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esC : EStateC Γ T Sig SS RS M E I) (sc : CKA.GameState Γ T) (hab : esC.abort = true) :
    ∀ r ∈ support (stepCDF cka prng fs Δcka qep mo q esC sc), r.1.2.abort = true := by
  intro r hr
  rcases q with n | (q_base | ⟨P, c, c'⟩)
  · exact stepC_abort cka prng fs Δcka qep mo (.inl n) esC sc hab r hr
  · exact stepC_abort cka prng fs Δcka qep mo (.inr q_base) esC sc hab r hr
  · simp only [stepCDF, implEDF, QueryImpl.add_apply, deliverForgeE, StateT.run_bind,
      StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab

theorem runLDF_abort (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true) :
    𝒟[runLDF cka prng fs Δcka qep mo oa esC sc] = 𝒟[(pure false : ProbComp Bool)] := by
  induction oa using OracleComp.inductionOn generalizing esC sc with
  | pure b' =>
    rw [runLDF_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runLDF_query_bind]
    exact evalDist_bind_false_of_support _ _ fun r hr =>
      ih r.1.1 (stepCDF_abort cka prng fs Δcka qep mo q esC sc hab r hr)

theorem runLDF_abort_apply_true_le (mo : Mode) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T} (hab : esC.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runLDF cka prng fs Δcka qep mo oa esC sc] {true} ≤ rhs := by
  rw [runLDF_abort cka prng fs Δcka qep mo oa hab]
  simp

theorem step_coinsE_DF_le (mo : Mode) (n : unifSpec.Domain)
    (k : (SMSpec Γ T Sig SS RS M CCoins E).Range (.inl n) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inl n) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inl n) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_coinsE, stepP_coinsE, bind_map_left, bind_map_left]
  exact OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
    fun u _ => ih u hS

theorem step_challE_DF_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × M × M × Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inr q))))) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  rw [stepC_challE cka prng fs Δcka qep mo hauth, stepP_challE cka prng fs Δcka qep mo hauth,
    pure_bind, pure_bind]
  exact ih none hS

theorem step_corrE_DF_le (mo : Mode) (hauth : mo.auth = true) (P : Party)
    (k : Option (PartyState Γ T Sig SS RS) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inr P)) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hca : esP.g.corrAllowed P = esC.g.corrAllowed P := eraseSt_corrAllowed hS.g_eq P
  by_cases hguard : esC.g.win || !esC.g.corrAllowed P
  · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hguard
    have hC : stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc = pure ((none, esC), sc) := by
      simp [stepC, implE, corrE, hS.abort_C, hguard, StateT.run_pure]
    have hP : stepP cka prng fs Δcka qep mo (.inr (.inr P)) esP sp = pure ((none, esP), sp) := by
      simp [stepP, implE, corrE, hS.abort_P, hwin, hca, hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    have hld : mo.policy.leakDoom esP.g (esP.g.afterCorr P) =
        mo.policy.leakDoom esC.g (esC.g.afterCorr P) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_afterCorr hS.g_eq P) mo.policy
    have hcd : mo.policy.corrDoom esP.g P = mo.policy.corrDoom esC.g P :=
      eraseSt_corrDoom hS.g_eq mo.policy P
    by_cases hdoom : mo.policy.leakDoom esC.g (esC.g.afterCorr P) || mo.policy.corrDoom esC.g P
    · simp only [Bool.or_eq_true] at hdoom
      have hC : stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc =
          pure ((none, { esC with abort := true }), sc) := by
        simp [stepC, implE, corrE, abortE, hS.abort_C, hguard, hdoom, StateT.run_modify]
      rw [hC, pure_bind]
      exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hdoom
      have hkr : knownRoot mo (esC.g.epoch P) = true :=
        knownRoot_of_not_doom mo hauth esC.g P hdoom.1 hdoom.2
      have hrootP : (esP.g.st P).root = some (esC.g.st P).root := by
        rw [hS.root_P P, hkr]
        rfl
      have hP : stepP cka prng fs Δcka qep mo (.inr (.inr P)) esP sp =
          pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
            (esC.g.st P).vS (esC.g.st P).vR), { esP with g := esP.g.afterCorr P }), sp) := by
        simp [stepP, implE, corrE, hooksPRNG, hS.abort_P, hwin, hca, hguard,
          hld, hcd, hdoom.1, hdoom.2, hrootP, StateT.run_modify, hS.realParty_eq P]
      by_cases hloc : localCKA mo Δcka (esC.g.epoch P)
      · have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
          rw [hS.γ_C P, hloc]
          rfl
        have hC : stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc =
            pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
              (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
          simp [stepC, implE, corrE, hooksCKA, hS.abort_C, hguard, hdoom.1, hdoom.2,
            hγC, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih _ (hS.afterCorr P)
      · simp only [Bool.not_eq_true] at hloc
        have hγC : (esC.g.st P).γ = none := by
          rw [hS.γ_C P, hloc]
          rfl
        have hcka := (hS.cka_st P (Or.inl hloc)).1
        by_cases hcorr : sc.allowCorr mo.tH || sc.finished Δcka mo.tH P
        · simp only [Bool.or_eq_true] at hcorr
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc =
              pure ((some (realParty (esC.g.st P) (esP.g.st P).γ (esC.g.st P).root
                (esC.g.st P).vS (esC.g.st P).vR), { esC with g := esC.g.afterCorr P }), sc) := by
            simp [stepC, implE, corrE, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, hcka, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih _ (hS.afterCorr P)
        · simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hcorr
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inr P)) esC sc =
              pure ((none, { esC with abort := true }), sc) := by
            simp [stepC, implE, corrE, abortE, hooksCKA, liftC, CKA.corrQuery, cImpl,
              CKA.oracleImpl, CKA.corrImpl, hS.abort_C, hguard, hdoom.1, hdoom.2, hγC,
              hcorr, simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
              StateT.run_modify]
          rw [hC, pure_bind]
          exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _

theorem step_injectE_DF_le (mo : Mode) (hauth : mo.auth = true)
    (q : Party × (Header T × E))
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'}, Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inr q))) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr q))) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
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
    have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepC, implE, injectE, hS.abort_C, hguard, StateT.run_pure]
    have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, injectE, hS.abort_P, hwin, htrans, hsafe, hguard, StateT.run_pure]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false'] at hguard
    rcases hguard with ⟨⟨hwin0, htrans0⟩, hsafe0⟩
    by_cases hsend : P.sendsIn c.1.1 || decide (esC.g.epoch P + 1 < c.1.1)
    · simp only [Bool.or_eq_true, decide_eq_true_eq] at hsend
      have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
          pure ((some .rejected, esC), sc) := by
        simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
          hS.id_C P, hS.tcur_C P, hsend, StateT.run_pure, hesC_eq]
      have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
          pure ((some .rejected, esP), sp) := by
        simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0, hsafe0,
          hS.id_P P, hS.tcur_P P, hsend, StateT.run_pure, hesP_eq]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih (some .rejected) hS
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hsend
      rcases hsend with ⟨hsend0, hle⟩
      by_cases hnew : c.1.1 = esC.g.epoch P + 1
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
        have htriv_false :
            ∀ i', esC.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := fun i' =>
          trivial_false_of_safeInj esC.g (2 + Δcka) P i' hsafe0 hS.comp_inv
        have htrivP_false :
            ∀ i', esP.g.trivial (2 + Δcka) ⟨P.other, esC.g.epoch P + 1, i'⟩ = false := fun i' => by
          rw [eraseSt_trivial hS.g_eq]
          exact htriv_false i'
        cases hTn : c.1.2 with
        | none =>
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
              pure ((some .rejected, esC), sc) := by
            simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, StateT.run_pure, hesC_eq]
          have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0,
              hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn, StateT.run_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) hS
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
                  runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
                𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp >>= fun r =>
                  runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
            intro γC' σC' γP' σP' rs sp' hsp' hsp_eq hsC hsP
            have hS' : Sync prng Δcka mo esC sc esP sp' := by
              rw [hsp_eq]
              exact hS.set_prf sp'.prf hsp'
            rcases hfs : fs.receive rs c.1 c.2 with _ | ⟨v', i', m'⟩
            · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                  pure ((some .rejected, esP), sp') := by
                simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                  StateT.run_bind, simulateQ_bind, hsP, hfs, StateT.run_pure, simulateQ_pure,
                  hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS'
            · by_cases hqep : qep + 1 < esC.g.epoch P + 1
              · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                    pure ((some .rejected, esC), sc) := by
                  simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                    hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep,
                    StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                    pure ((some .rejected, esP), sp') := by
                  simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                    hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                    StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, StateT.run_pure,
                    simulateQ_pure, hesP_eq]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih (some .rejected) hS'
              · have htrivC := htriv_false i'
                have htrivP := htrivP_false i'
                by_cases hinj : (mo.cfg (M := M)).injectFull (esC.g.epoch P + 1)
                · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                      pure ((some .rejected,
                        { esC with g := { esC.g with win := true } }), sc) := by
                    simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                      pure ((some .rejected,
                        { esP with g := { esP.g with win := true } }), sp') := by
                    simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                      hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                      StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  rw [hsp_eq]
                  exact ih (some .rejected) (hS.set_win_prf true sp'.prf hsp')
                · simp only [Bool.not_eq_true] at hinj
                  have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                      pure ((some .rejected, esC), sc) := by
                    simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                      hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC, hfs, hqep, htrivC, hinj,
                      StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
                  have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                      pure ((some .rejected, esP), sp') := by
                    simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                      hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn,
                      StateT.run_bind, simulateQ_bind, hsP, hfs, hqep, htrivP, hinj,
                      StateT.run_pure, simulateQ_pure, hesP_eq]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) hS'
          have hcache := hS.cache_at_succ P c.1.1 hnew
          have hnone :
              (∀ Im, esC.h.cache (esC.g.epoch P + 1) ≠ some (Tn, Im)) →
              (∀ σc k, esP.h.cache (esC.g.epoch P + 1) ≠ some (Tn, σc, k)) →
              𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc >>= fun r =>
                  runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
                𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp >>= fun r =>
                  runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
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
                    simulateQ_bind, simulateQ_query, map_eq_bind_pure_comp,
                    StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_set]
              · simp only [Bool.not_eq_true] at hloc
                have hγC : (esC.g.st P).γ = none := by
                  simp [hS.γ_C P, hloc]
                have hsC_abort : ((hooksCKA cka prng fs Δcka mo).startRecv esC.g P
                    (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root Tn).run esC.h =
                    pure (none, esC.h) := by
                  rw [hsC_un]
                  simp [hauth, htStar, hγC]
                have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                    pure ((none, { esC with abort := true }), sc) := by
                  simp [stepC, implE, injectE, abortE, vRecv, hS.abort_C, hwin0, htrans0,
                    hsafe0, hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_abort,
                    StateT.run_bind, StateT.run_pure, StateT.run_modify,
                    simulateQ_pure]
                rw [hC, pure_bind]
                exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
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
              have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0', hnew, hTn, hsC_rej,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0', hnew, hTn, hsP_rej,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
          rcases hcache with ⟨hcC, hcP⟩ | ⟨Tm, Im, hcC, hcP⟩
          · rw [hnew] at hcC hcP
            exact hnone (by simp [hcC]) (by simp [hcP])
          · rw [hnew] at hcC hcP
            by_cases hTm : Tm = Tn
            · subst hTm
              let p := prng.up (esC.g.st P).root Im
              refine hafter ((esC.g.st P).γ.map fun γ => (cka.receive γ Tm).1) p.1
                (cka.receive (esP.g.st P).γ Tm).1
                (esP.g.st (Party.senderOf (esC.g.epoch P + 1))).root
                (fs.initReceiver p.2) sp (Or.inl rfl) rfl ?_ ?_
              · simp [hooksCKA, hcC, p, StateT.run_bind, StateT.run_get, StateT.run_pure]
              · simp [hooksPRNG, hcP, p, StateT.run_bind, StateT.run_get, StateT.run_pure,
                  simulateQ_pure]
            · exact hnone (by simp [hcC, hTm]) (by simp [hcP, hTm])
      · have hle_ep : c.1.1 ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
              pure ((some .rejected, esC), sc) := by
            simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
              hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_pure, hesC_eq]
          have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe, hwin0, htrans0,
              hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, StateT.run_pure,
              hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) hS
        | some v =>
          rcases hfs : fs.receive v c.1 c.2 with _ | ⟨v', i', m'⟩
          · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq]
            have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR,
                hfs, StateT.run_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          · by_cases hqep : qep + 1 < c.1.1
            · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0, hsafe0,
                  hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep, StateT.run_pure,
                  hesC_eq]
              have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans, hsafe,
                  hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR,
                  hfs, hqep, StateT.run_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
            · let pos : SM.Pos := ⟨P.other, c.1.1, i'⟩
              have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
                have hvR'_eq : Function.update (esP.g.st P).vR c.1.1 (some v') = vR' := by
                  simp [vR', hS.vR_eq P]
                have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                    pure ((some (.accepted c.1.1 i' (some m')),
                      { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }), sc) := by
                  simp [stepC, implE, injectE, vRecv, commitE, hooksCKA, hS.abort_C, hwin0,
                    htrans0, hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                    htriv, pos, vR', StateT.run_pure, StateT.run_modify]
                have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                    pure ((some (.accepted c.1.1 i' (some m')),
                      { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }), sp) := by
                  simp [stepP, implE, injectE, vRecv, commitE, hS.abort_P, hwin,
                    htrans, hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle,
                    hnew, hvRP, hvR, hfs, hqep, htriv_eq, htriv, pos, hvR'_eq,
                    StateT.run_pure, StateT.run_modify]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih _ (hS.accept_old P vR' pos hle_ep)
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (mo.cfg (M := M)).injectFull c.1.1
                · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                      pure ((some .rejected,
                        { esC with g := { esC.g with win := true } }), sc) := by
                    simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0,
                      hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                      htriv, hinj, pos, StateT.run_pure, StateT.run_modify]
                  have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                      pure ((some .rejected,
                        { esP with g := { esP.g with win := true } }), sp) := by
                    simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans,
                      hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                      hvRP, hvR, hfs, hqep, htriv_eq, htriv, hinj, pos,
                      StateT.run_pure, StateT.run_modify]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl))
                · simp only [Bool.not_eq_true] at hinj
                  have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esC sc =
                      pure ((some .rejected, esC), sc) := by
                    simp [stepC, implE, injectE, vRecv, hS.abort_C, hwin0, htrans0,
                      hsafe0, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, hqep,
                      htriv, hinj, pos, StateT.run_pure, hesC_eq]
                  have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inr (P, c)))) esP sp =
                      pure ((some .rejected, esP), sp) := by
                    simp [stepP, implE, injectE, vRecv, hS.abort_P, hwin, htrans,
                      hsafe, hwin0, htrans0, hsafe0, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew,
                      hvRP, hvR, hfs, hqep, htriv_eq, htriv, hinj, pos, StateT.run_pure, hesP_eq]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) hS

theorem step_deliverE_DF_le (mo : Mode) (hauth : mo.auth = true)
    (P : Party) (c : Header T × E)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have htrans : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have hchall : esP.g.chall = esC.g.chall := eraseSt_chall hS.g_eq
  have hcfg_win : (mo.cfg : SM.Config M).deliverWin = false := by
    simp [Mode.cfg, hauth, SM.Config.auth]
  have hesC_eq :
      ({ g := esC.g, h := esC.h, abort := false } : EStateC Γ T Sig SS RS M E I) = esC :=
    estate_mk_abort_false hS.abort_C
  have hesP_eq :
      ({ g := esP.g, h := esP.h, abort := false } : EStateP Γ T Sig SS RS M E K) = esP :=
    estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esC.g.win = true
  · have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepC, implE, deliverE, hS.abort_C, hwin0]
    have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, deliverE, hS.abort_P, hwin, hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
          pure ((none, esC), sc) := by
        simp [stepC, implE, deliverE, hS.abort_C, hwin0, hr]
      have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
          pure ((none, esP), sp) := by
        simp [stepP, implE, deliverE, hS.abort_P, hwin, hwin0, htrans, hr]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih none hS
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
      · have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
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
            pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h),
              sp) := by
          simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
            simulateQ_pure]
        cases hfs : fs.receive (fs.initReceiver p.2) c.1 c.2 with
        | none =>
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
              pure ((some .rejected, esC), sc) := by
            simp [stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
          have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
              hS.id_P P, hS.tcur_P P, hsend0', hnew, hct2, hstartP, hfs,
              StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) hS
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
            have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
                pure ((some (.accepted m i' (if esC.g.chall.contains r.pos then none else some m')),
                  { esC with g := esC.g.accept P stC_final r.pos }), sc) := by
              simp [stepC, implE, deliverE, commitE, vRecv, hS.abort_C, hwin0, hr,
                hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
                hγC, hloc_m, m, vR', γC_final, stC_final, γP', StateT.run_bind,
                StateT.run_pure, StateT.run_modify, simulateQ_pure]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C
              (fun h => by simp [m, hloc_m] at h))
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
              have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
                  pure ((some (.accepted m i'
                      (if esC.g.chall.contains r.pos then none else some m')),
                    { esC with g := esC.g.accept P stC_final r.pos }), sc') := by
                simp [stepC, implE, deliverE, commitE, liftC, CKA.receiveQuery,
                  CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, vRecv,
                  hS.abort_C, hwin0, hr, hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew,
                  hct2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m,
                  sc', CKA.GameState.afterReceive, CKA.GameState.finished, hsc_epP,
                  m, vR', γC_final, stC_final, γP',
                  simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C
                (fun h => by simp [m, hloc_m] at h))
            · have hloc_m : localCKA mo Δcka m = false := by
                simp [localCKA, htL_none, hfin]
              have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
                  pure ((some (.accepted m i'
                      (if esC.g.chall.contains r.pos then none else some m')),
                    { esC with g := esC.g.accept P stC_final r.pos }), sc') := by
                simp [stepC, implE, deliverE, commitE, liftC, CKA.receiveQuery,
                  cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv, hS.abort_C, hwin0, hr,
                  hcfg_win, hS.id_C P, hS.tcur_C P, hsend0', hnew, hct2, hstartC, hp1, p, hfs,
                  hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m, sc', m, vR', γC_final, stC_final,
                  γP', simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
              rw [hC, hP, pure_bind, pure_bind]
              refine ih _ (hS.accept_new P γP' vR' r.pos hr_ep hO_ep hS.b_C fun _ => ?_)
              simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO,
                hsc_epO, hO_ep]
      · have hle_ep : r.pos.epoch ≤ esC.g.epoch P := by omega
        have hvRP : (esP.g.st P).vR c.1.1 = (esC.g.st P).vR c.1.1 := by rw [hS.vR_eq P]
        cases hvR : (esC.g.st P).vR c.1.1 with
        | none =>
          have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
              pure ((some .rejected, esC), sc) := by
            simp [stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
              hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_pure, hesC_eq]
          have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
              pure ((some .rejected, esP), sp) := by
            simp [stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
              hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, StateT.run_pure, hesP_eq]
          rw [hC, hP, pure_bind, pure_bind]
          exact ih (some .rejected) hS
        | some v =>
          cases hfs : fs.receive v c.1 c.2 with
          | none =>
            have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepC, implE, deliverE, vRecv, hS.abort_C, hwin0, hr, hcfg_win,
                hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, StateT.run_pure, hesC_eq]
            have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepP, implE, deliverE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr, hcfg_win,
                hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                StateT.run_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let vR' := Function.update (esC.g.st P).vR c.1.1 (some v')
            have hvRP_all : (esP.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
            have hC : stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esC sc =
                pure ((some (.accepted c.1.1 i'
                  (if esC.g.chall.contains r.pos then none else some m')),
                  { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } r.pos }), sc) := by
              simp [stepC, implE, deliverE, commitE, vRecv, hS.abort_C, hwin0, hr,
                hcfg_win, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs, vR',
                StateT.run_pure, StateT.run_modify]
            have hP : stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr (P, c))))) esP sp =
                pure ((some (.accepted c.1.1 i'
                  (if esC.g.chall.contains r.pos then none else some m')),
                  { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } r.pos }), sp) := by
              simp [stepP, implE, deliverE, commitE, vRecv, hS.abort_P, hwin, hwin0, htrans, hr,
                hcfg_win, hchall, hS.id_P P, hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs,
                hvRP_all, vR', StateT.run_pure, StateT.run_modify]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih _ (hS.accept_old P vR' r.pos hle_ep)

omit [SampleableType KC] in
theorem ih_postSend_new_DF (mo : Mode)
    (P : Party) (m_msg : M) (bad : Bool)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true})
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
    𝒟[runLDF cka prng fs Δcka qep mo (k outC.1) outC.2 sc'] {true} ≤
      𝒟[runRDF cka prng fs Δcka qep mo (k outP.1) outP.2 sp'] {true} := by
  intro m p σP' resC resP outC outP
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  let fe := fs.send (fs.initSender p.2) (m, some Tm) m_msg
  have hS' := hS.record_new_epoch P bad γP' Tm Im fe.1 m_msg fe.2 sc' sp' hsend hb_sc' hb_sp'
    hcka' hprng_before hprng_after hprng_at
  dsimp only [outC, outP, resC, resP, postSendC, postSendP]
  simp only [hepP, m]
  exact ih (some ((m, some Tm), fe.2)) hS'

theorem step_transmitE_same_epoch_DF_le (mo : Mode)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = false)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>=
        fun res => runLDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>=
        fun res => runRDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  have hidxP : esP.g.idx P = esC.g.idx P := congrFun (eraseSt_idx hS.g_eq) P
  have hsend0 : P.sendsIn (esC.g.epoch P) = true := sendsIn_of_succ_false hsend
  by_cases hqep : qep < esC.g.epoch P
  · have hC : stepC cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepC, implE, transmitE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend, hqep]
    have hP : stepP cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP, hsend,
        hqep]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · have hld : mo.policy.leakDoom esP.g esP.g = mo.policy.leakDoom esC.g esC.g :=
      eraseSt_leakDoom hS.g_eq hS.g_eq mo.policy
    by_cases hdoom : mo.policy.leakDoom esC.g esC.g
    · have hC : stepC cka prng fs Δcka qep mo
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
          pure ((none, { esC with abort := true }), sc) := by
        simp [stepC, implE, transmitE, abortE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend,
          hqep, hdoom, StateT.run_modify]
      rw [hC, pure_bind]
      exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
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
        have hC : stepC cka prng fs Δcka qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
            pure ((some c, { esC with g := esC.g.record (2 + Δcka) P (esC.g.st P) rcd false }),
              sc) := by
          simp [stepC, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_C, hwin0,
            hsend, hqep, hdoom, hS.id_C P, hS.tcur_C P, hvS, c, rcd,
            StateT.run_pure, StateT.run_modify]
        have hP : stepP cka prng fs Δcka qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
            pure ((some c, { esP with g := esP.g.record (2 + Δcka) P (esP.g.st P) rcd false }),
              sp) := by
          simp [stepP, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0,
            hepP, hidxP, hld, hsend, hqep, hdoom, hS.id_P P, hS.tcur_P P, hvSP, hvS, hTcurP,
            c, rcd, StateT.run_pure, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind, ← hstC, ← hstP]
        exact ih (some c) (hS.record_same_epoch P none m_msg default hsend0)
      | some v =>
        let h : Header T := (esC.g.epoch P, (esC.g.st P).curCkaMsg)
        let fe := fs.send v h m_msg
        let c : Header T × E := (h, fe.2)
        let rcd : SM.Record M (Header T × E) := ⟨⟨P, esC.g.epoch P, esC.g.idx P + 1⟩, m_msg, c⟩
        have hC : stepC cka prng fs Δcka qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
            pure ((some c, { esC with
              g := esC.g.record (2 + Δcka) P { esC.g.st P with vS := some fe.1 } rcd false }),
              sc) := by
          simp [stepC, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_C,
            hwin0, hsend, hqep, hdoom, hS.id_C P, hS.tcur_C P, hvS, h, fe, c, rcd,
            StateT.run_pure, StateT.run_modify]
        have hP : stepP cka prng fs Δcka qep mo
            (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
            pure ((some c, { esP with
              g := esP.g.record (2 + Δcka) P { esP.g.st P with vS := some fe.1 } rcd false }),
              sp) := by
          simp [stepP, implE, transmitE, vSend, SM.GameState.epMgmt, hS.abort_P,
            hwin, hwin0, hepP, hidxP, hld, hsend, hqep, hdoom, hS.id_P P, hS.tcur_P P, hvSP,
            hvS, hTcurP, h, fe, c, rcd, StateT.run_pure, StateT.run_modify]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih (some c) (hS.record_same_epoch P (some fe.1) m_msg fe.2 hsend0)

omit [SampleableType KC] in
theorem startSendP_coins_DF_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (bad : Bool)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true})
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
    𝒟[runLDF cka prng fs Δcka qep mo (k outC.1) outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δcka P m_msg bad esP out.1
          runRDF cka prng fs Δcka qep mo (k outP.1) outP.2 out.2] {true} := by
  intro m c_cka p resC outC
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with
      hEq | hEq
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
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        pure (resP, sp) := by
      simp [startSendP_body, rootPRNG, hgt_star, hrootP0, hkr_m, c_cka, p, σP', resP,
        StateT.run_pure, StateT.run_modify, simulateQ_pure]
    rw [hP, pure_bind]
    exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg bad k hS ih c_cka.1 c_cka.2.1 c_cka.2.2
      sc' sp hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega) (fun h => by omega)
  · by_cases heq_star : m = mo.tStar
    · have hkr_m : knownRoot mo m = true := by
        simp [knownRoot, heq_star]
      have hlt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
      have hnot_lt0 :
          (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
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
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp =
          pure (resP, sp') := by
        simp [startSendP_body, rootPRNG, heq_star, hnot_tH_star,
          liftP, PRFPRNG.challPrfQuery, pImpl, PRFPRNG.oracleImpl, PRFPRNG.challPrfImpl,
          knownRoot, hcorr, hprng, hS.b_P, hσ, c_cka, p, σP', resP, sp',
          simulateQ_bind, simulateQ_query, simulateQ_pure,
          map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
      rw [hP, pure_bind]
      exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg bad k hS ih c_cka.1 c_cka.2.1
        c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega)
        (fun _ _ => ⟨hσ, hcorr, hprng⟩)
    · have hlt_star : m < mo.tStar := by omega
      have hlt0 : max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tStar := by omega
      by_cases hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = true
      · have hkr_m : knownRoot mo m = true := by
          simp [knownRoot, hlt_tH]
        have hlt_tH0 :
            (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = true := by
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
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
              esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, processCorr, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = true by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg bad k hS ih c_cka.1 c_cka.2.1
          c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ _ => ⟨rfl, rfl, hprng, hprf⟩)
          (fun _ h => by simp [m, hlt_tH] at h)
          (fun h => by omega)
      · simp only [Bool.not_eq_true] at hlt_tH
        have hkr_m : knownRoot mo m = false := by
          simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
        have hlt_tH0 :
            (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = false := by
          rw [hmax0]
          cases htL : mo.tL with
          | none => simp
          | some l =>
            simp only [htL, Option.isSome_some, Bool.true_and,
              decide_eq_false_iff_not] at hnot_tH hlt_tH ⊢
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
            ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
              esP.h)).run sp =
            pure (resP, sp') := by
          simp [startSendP_body, rootPRNG, hgt_star, heq_star,
            show (mo.tL.isSome && (m = mo.tH)) = false by simpa [m] using hnot_tH,
            show (mo.tL.isSome && (m < mo.tH)) = false by simpa [m] using hlt_tH,
            liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
            PRFPRNG.processImpl, PRFPRNG.samIfNec,
            hcorr, hprng, hprf, hσ, hkr_m, c_cka, p, σP', resP, sp',
            simulateQ_bind, simulateQ_query, simulateQ_pure,
            map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
        rw [hP, pure_bind]
        exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg bad k hS ih c_cka.1 c_cka.2.1
          c_cka.2.2 sc' sp' hsend hb_sc' hS.b_P hcka'
          (fun _ h => by simp [m, hlt_tH] at h)
          (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
          (fun h => by omega)

omit [SampleableType KC] in
theorem startSendP_chall_DF_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true})
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
          (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
            fs.initSender p.2),
            { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) })
        let outC := postSendC fs Δcka P m_msg false esC resC
        runLDF cka prng fs Δcka qep mo (k outC.1) outC.2 sc'] {true} ≤
      𝒟[(simulateQ (pImpl prng)
          ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
            esP.h)).run sp >>=
        fun out =>
          let outP := postSendP fs Δcka P m_msg false esP out.1
          runRDF cka prng fs Δcka qep mo (k outP.1) outP.2 out.2] {true} := by
  intro m c_cka
  obtain ⟨hO_ep, hmax0, hroot0⟩ := hS.ping_pong_synced P hsend
  have hroot_max : (esC.g.st (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B)))).root =
      (esC.g.st P).root := by
    rcases party_eq_or_eq_other (Party.senderOf (max (esC.g.epoch .A) (esC.g.epoch .B))) P with
      hEq | hEq
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
  have hlt_tH0 :
      (mo.tL.isSome && decide (max (esC.g.epoch .A) (esC.g.epoch .B) < mo.tH)) = true := by
    rw [hmax0]
    simp [htL_some, show esC.g.epoch P < mo.tH by omega]
  obtain ⟨hσ, hcorr, hprng, hprf⟩ := hS.prng_before_tH hlt0 hlt_tH0
  rw [hroot_max] at hσ
  by_cases heq_star : m = mo.tStar
  · have hkr_m : knownRoot mo m = true := by
      simp [knownRoot, heq_star]
    have hstar_eq_tH : mo.tStar = mo.tH := heq_star.symm.trans hm_tH
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esC.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := true, prng := true }) := by
      simp [startSendP_body, rootPRNG, heq_star, htL_some, hstar_eq_tH,
        liftP, PRFPRNG.challPrngQuery, PRFPRNG.corrQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.challPrngImpl, PRFPRNG.corrImpl, PRFPRNG.samIfNec,
        knownRoot, hprf, hS.b_P, hσ, c_cka,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg false k hS ih c_cka.1 c_cka.2.1 I₁
      sc' { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := true, prng := true }
      hsend hb_sc' hS.b_P hcka' (fun h => by omega) (fun h => by omega)
      (fun _ h => by simp [← heq_star, m, htL_some, hm_tH] at h)
  · have hlt_star : m < mo.tStar := by omega
    have hlt_tH : (mo.tL.isSome && decide (m < mo.tH)) = false := by
      simp [hm_tH]
    have hkr_m : knownRoot mo m = false := by
      simp [knownRoot, hlt_tH, show ¬ mo.tStar ≤ m by omega]
    have hP : (simulateQ (pImpl prng)
        ((startSendP_body cka prng fs mo m (esP.g.st P).γ (esP.g.st P).root coins).run
          esP.h)).run sp =
        ($ᵗ I : ProbComp I) >>= fun I₁ =>
          let p := prng.up (esC.g.st P).root I₁
          let σP' := if knownRoot mo m then some p.1 else none
          pure ((some (c_cka.1, c_cka.2.1, σP', fs.initSender p.2),
            { cache := Function.update esP.h.cache m (some (c_cka.2.1, σP', p.2)) }),
            { sp with σ := p.1, corr := false }) := by
      simp [startSendP_body, rootPRNG, hgt_star, heq_star, htL_some, ← hm_tH,
        liftP, PRFPRNG.processQuery, pImpl, PRFPRNG.oracleImpl,
        PRFPRNG.processImpl, PRFPRNG.samIfNec,
        hprng, hprf, hσ, hkr_m, c_cka,
        simulateQ_bind, simulateQ_query, simulateQ_pure,
        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify, bind_assoc]
    rw [hP, bind_assoc]
    refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
      fun I₁ _ => ?_
    rw [pure_bind]
    exact ih_postSend_new_DF cka prng fs Δcka qep mo P m_msg false k hS ih c_cka.1 c_cka.2.1 I₁
      sc' { sp with σ := (prng.up (esC.g.st P).root I₁).1, corr := false }
      hsend hb_sc' hS.b_P hcka'
      (fun _ h => by simp [m, hlt_tH] at h)
      (fun _ _ => ⟨rfl, rfl, hprng, fun _ => hprf⟩)
      (fun h => by omega)

theorem step_transmitE_new_epoch_DF_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (hwin0 : esC.g.win = false)
    (hsend : P.sendsIn (esC.g.epoch P + 1) = true)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>=
        fun res => runLDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>=
        fun res => runRDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have hepP : esP.g.epoch P = esC.g.epoch P := congrFun (eraseSt_epoch hS.g_eq) P
  by_cases hqep : qep < esC.g.epoch P + 1
  · have hqep_le : qep ≤ esC.g.epoch P := by omega
    have hC : stepC cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepC, implE, transmitE, SM.GameState.epMgmt, hS.abort_C, hwin0, hsend, hqep_le]
    have hP : stepP cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, SM.GameState.epMgmt, hS.abort_P, hwin, hwin0, hepP, hsend,
        hqep_le]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · have hld : mo.policy.leakDoom esP.g (epMgmtNew esP.g (2 + Δcka) P r.isSome) =
        mo.policy.leakDoom esC.g (epMgmtNew esC.g (2 + Δcka) P r.isSome) :=
      eraseSt_leakDoom hS.g_eq (eraseSt_epMgmtNew hS.g_eq (2 + Δcka) P r.isSome) mo.policy
    by_cases hdoom : mo.policy.leakDoom esC.g (epMgmtNew esC.g (2 + Δcka) P r.isSome)
    · have hC : stepC cka prng fs Δcka qep mo
          (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
          pure ((none, { esC with abort := true }), sc) := by
        simp [stepC, implE, transmitE, abortE,
          epMgmt_eq_epMgmtNew esC.g (2 + Δcka) qep P r.isSome hsend hqep,
          hS.abort_C, hwin0, hdoom, StateT.run_modify]
      rw [hC, pure_bind]
      exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
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
            (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
              fs.initSender p.2),
              { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
          have hC : (simulateQ (cImpl cka Δcka mo.tH)
              (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P true)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run
                esC.h)).run sc =
              pure (resC, sc) := by
            simp [hooksCKA, cacheC, hγC, hloc_m, m, c_cka, p, resC,
              StateT.run_pure, StateT.run_modify, simulateQ_pure]
          simp only [Option.isSome_some]
          rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
          simpa [m, c_cka, p, resC] using
            startSendP_coins_DF_le cka prng fs Δcka qep mo hvalid P m_msg true k hS ih coins sc
              hsend hnot_tH hS.b_C (fun h => by simp [hloc] at h)
        | none =>
          have hC : (simulateQ (cImpl cka Δcka mo.tH)
              (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run esC.h)).run sc =
              ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                let c_cka := cka.send (esP.g.st P).γ coins
                let p := prng.up (esC.g.st P).root c_cka.2.2
                pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
                  fs.initSender p.2),
                  { cache :=
                    Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }), sc) := by
            simp [hooksCKA, cacheC, hγC, hloc_m, m,
              StateT.run_bind, StateT.run_pure, StateT.run_modify,
              simulateQ_bind, simulateQ_pure, map_eq_bind_pure_comp, bind_assoc]
          simp only [Option.isSome_none]
          rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
          refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
            fun coins _ => ?_
          rw [pure_bind, pure_bind]
          exact startSendP_coins_DF_le cka prng fs Δcka qep mo hvalid P m_msg false k hS ih coins sc
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
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run
                  esC.h)).run sc =
                pure ((none, esC.h), sc) := by
              simp [hooksCKA, liftC, CKA.sendWithAdversaryCoinsQuery, cImpl, CKA.oracleImpl, CKA.sendWithAdversaryCoinsImpl,
                hγC, hcanS, hsc_epP, hbad_ok,
                simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind]
            exact runLDF_abort_apply_true_le cka prng fs Δcka qep mo (k none) rfl _
          · have hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false := by
              simp [show esC.g.epoch P + 1 ≠ mo.tH by omega]
            have hfin : ¬ (mo.tH + Δcka ≤ m) := by omega
            have hloc_m : localCKA mo Δcka m = false := by
              simp [localCKA, htL_none, hfin]
            let c_cka := cka.send (esP.g.st P).γ coins
            let p := prng.up (esC.g.st P).root c_cka.2.2
            let sc' := sc.afterSend P c_cka.1 c_cka.2.1
            let resC : Option (Option Γ × T × Sig × SS) × CKAState T I :=
              (some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
                fs.initSender p.2),
                { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) })
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P true)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root (some coins)).run
                  esC.h)).run sc =
                pure (resC, sc') := by
              simp [hooksCKA, cacheC, liftC, CKA.sendWithAdversaryCoinsQuery, cImpl, CKA.oracleImpl,
                CKA.sendWithAdversaryCoinsImpl, hγC, hcanS, hsc_epP, hsc_stP, hbad_ok, hfin, hloc_m, m, c_cka, p,
                sc', resC, simulateQ_bind, simulateQ_query, simulateQ_pure,
                map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
            simp only [Option.isSome_some]
            rw [hC, pure_bind, pure_bind, hepP, startSendP_some_eq]
            refine startSendP_coins_DF_le cka prng fs Δcka qep mo hvalid P m_msg true k hS ih
              coins sc' hsend hnot_tH hS.b_C fun _ => ?_
            simp [sc', c_cka, CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO,
              hO_ep]
        | none =>
          by_cases heq_tH : esC.g.epoch P + 1 = mo.tH
          · have htH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = true := by
              simp [htL_some, heq_tH]
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run
                  esC.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins => ($ᵗ I : ProbComp I) >>= fun I₁ =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esC.g.st P).root I₁
                  pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
                    fs.initSender p.2),
                    { cache := Function.update esC.h.cache m (some (c_cka.2.1, I₁)) }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              by_cases hΔ : Δcka = 0
              · simp [hooksCKA, cacheC, liftC, CKA.challQuery, CKA.corrQuery, cImpl,
                  CKA.oracleImpl, CKA.challImpl, CKA.corrImpl, CKA.GameState.afterSend,
                  CKA.GameState.finished, localCKA, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP,
                  hS.b_C, hΔ, m, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  bind_assoc]
              · simp [hooksCKA, cacheC, liftC, CKA.challQuery, cImpl, CKA.oracleImpl,
                  CKA.challImpl, localCKA, htL_none, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hS.b_C,
                  hΔ, m, simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [bind_assoc]
            have hstep := startSendP_chall_DF_le cka prng fs Δcka qep mo hvalid P m_msg k hS ih
              coins (sc.afterSend P (cka.send (esP.g.st P).γ coins).1
                (cka.send (esP.g.st P).γ coins).2.1)
              hsend htH hS.b_C (fun _ => by
                simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep])
            simpa [pure_bind] using hstep
          · have hnot_tH : (mo.tL.isSome && decide (esC.g.epoch P + 1 = mo.tH)) = false := by
              simp [heq_tH]
            have hC : (simulateQ (cImpl cka Δcka mo.tH)
                (((hooksCKA cka prng fs Δcka mo).startSend (epMgmtNew esC.g (2 + Δcka) P false)
                  P (esC.g.epoch P + 1) (esC.g.st P).γ (esC.g.st P).root none).run
                  esC.h)).run sc =
                ($ᵗ CCoins : ProbComp CCoins) >>= fun coins =>
                  let c_cka := cka.send (esP.g.st P).γ coins
                  let p := prng.up (esC.g.st P).root c_cka.2.2
                  pure ((some (if localCKA mo Δcka m then some c_cka.1 else none, c_cka.2.1, p.1,
                    fs.initSender p.2),
                    { cache := Function.update esC.h.cache m (some (c_cka.2.1, c_cka.2.2)) }),
                    sc.afterSend P c_cka.1 c_cka.2.1) := by
              by_cases hfin : mo.tH + Δcka ≤ m
              · have hloc_m : localCKA mo Δcka m = true := by simp [localCKA, hfin]
                simp [hooksCKA, cacheC, liftC, CKA.sendQuery, CKA.corrQuery, cImpl, CKA.oracleImpl,
                  CKA.sendImpl, CKA.corrImpl, CKA.GameState.afterSend, CKA.GameState.finished,
                  hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                  simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  bind_assoc]
              · have hloc_m : localCKA mo Δcka m = false := by simp [localCKA, htL_none, hfin]
                simp [hooksCKA, cacheC, liftC, CKA.sendQuery, cImpl, CKA.oracleImpl,
                  CKA.sendImpl, hγC, heq_tH, hcanS, hsc_epP, hsc_stP, hfin, hloc_m, m,
                  simulateQ_bind, simulateQ_query, simulateQ_pure,
                  map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                  bind_assoc]
            simp only [Option.isSome_none]
            rw [hC, hepP, startSendP_none_eq, bind_assoc, bind_assoc]
            refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _
              (MeasurableSet.singleton true) fun coins _ => ?_
            rw [pure_bind, pure_bind]
            refine startSendP_coins_DF_le cka prng fs Δcka qep mo hvalid P m_msg false k hS ih coins
              (sc.afterSend P (cka.send (esP.g.st P).γ coins).1 (cka.send (esP.g.st P).γ coins).2.1)
              hsend hnot_tH hS.b_C fun _ => ?_
            simp [CKA.GameState.afterSend, Party.other_ne, hsc_epP, hsc_stO, hsc_epO, hO_ep]

theorem step_transmitE_DF_le (mo : Mode)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party) (m_msg : M) (r : Option CCoins)
    (k : Option (Header T × E) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepC cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc >>=
        fun res => runLDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} ≤
      𝒟[stepP cka prng fs Δcka qep mo (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp >>=
        fun res => runRDF cka prng fs Δcka qep mo (k res.1.1) res.1.2 res.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  by_cases hwin0 : esC.g.win = true
  · have hC : stepC cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepC, implE, transmitE, hS.abort_C, hwin0]
    have hP : stepP cka prng fs Δcka qep mo
        (.inr (.inl (.inl (.inl (.inl (P, m_msg, r)))))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepP, implE, transmitE, hS.abort_P, hwin, hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true] at hwin0
    by_cases hsend : P.sendsIn (esC.g.epoch P + 1) = true
    · exact step_transmitE_new_epoch_DF_le cka prng fs Δcka qep mo hvalid P m_msg r k hS hwin0
        hsend ih
    · simp only [Bool.not_eq_true] at hsend
      exact step_transmitE_same_epoch_DF_le cka prng fs Δcka qep mo P m_msg r k hS hwin0 hsend ih

theorem step_deliverForgeE_DF_le (mo : Mode) (_hauth : mo.auth = true)
    (P : Party) (c c' : Header T × E)
    (k : Option (SM.RecvResult M) → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp)
    (ih : ∀ u {esC' sc' esP' sp'},
      Sync prng Δcka mo esC' sc' esP' sp' →
      𝒟[runLDF cka prng fs Δcka qep mo (k u) esC' sc'] {true} ≤
        𝒟[runRDF cka prng fs Δcka qep mo (k u) esP' sp'] {true}) :
    𝒟[stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc >>= fun r =>
        runLDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} ≤
      𝒟[stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp >>= fun r =>
        runRDF cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2] {true} := by
  have hwin : esP.g.win = esC.g.win := eraseSt_win hS.g_eq
  have htrans_c : esP.g.inTransit P.other c = esC.g.inTransit P.other c :=
    eraseSt_inTransit hS.g_eq P.other c
  have htrans_c' : esP.g.inTransit P.other c' = esC.g.inTransit P.other c' :=
    eraseSt_inTransit hS.g_eq P.other c'
  have hcomp : esP.g.comp = esC.g.comp := eraseSt_comp hS.g_eq
  have hesC_eq :
      ({ g := esC.g, h := esC.h, abort := false } : EStateC Γ T Sig SS RS M E I) = esC :=
    estate_mk_abort_false hS.abort_C
  have hesP_eq :
      ({ g := esP.g, h := esP.h, abort := false } : EStateP Γ T Sig SS RS M E K) = esP :=
    estate_mk_abort_false hS.abort_P
  by_cases hwin0 : esC.g.win = true
  · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
        pure ((none, esC), sc) := by
      simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0]
    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
        pure ((none, esP), sp) := by
      simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0]
    rw [hC, hP, pure_bind, pure_bind]
    exact ih none hS
  · simp only [Bool.not_eq_true] at hwin0
    cases hr : esC.g.inTransit P.other c with
    | none =>
      have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
          pure ((none, esC), sc) := by
        simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0, hr]
      have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
          pure ((none, esP), sp) := by
        simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0, htrans_c, hr]
      rw [hC, hP, pure_bind, pure_bind]
      exact ih none hS
    | some r =>
      by_cases hguard :
          ((esC.g.inTransit P.other c').isSome || esC.g.comp.contains r.pos || c.1 != c'.1) = true
      · simp only [Bool.or_eq_true, List.contains_iff_mem, bne_iff_ne] at hguard
        have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
            pure ((none, esC), sc) := by
          simp [stepCDF, implEDF, deliverForgeE, hS.abort_C, hwin0, hr, hguard, StateT.run_pure]
        have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
            pure ((none, esP), sp) := by
          simp [stepPDF, implEDF, deliverForgeE, hS.abort_P, hwin, hwin0, htrans_c, hr,
            htrans_c', hcomp, hguard, StateT.run_pure]
        rw [hC, hP, pure_bind, pure_bind]
        exact ih none hS
      · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
        rcases hguard with ⟨⟨htrans0, hcomp0⟩, hhdr⟩
        have hcomp0' : r.pos ∉ esC.g.comp := by simpa using hcomp0
        have hhdr' : c'.1 = c.1 := hhdr.symm
        obtain ⟨hmem, hsender, hct⟩ := inTransit_some_props hr
        obtain ⟨ht1, hsend_other, hle_other, _⟩ := hS.trans_inv r hmem
        rw [hct] at ht1
        rw [hsender] at hsend_other hle_other
        have hsend0 : P.sendsIn c'.1.1 = false := by
          rw [hhdr', ht1]
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
        have hle : ¬ (esC.g.epoch P + 1 < c'.1.1) := by rw [hhdr', ht1]; omega
        by_cases hnew : c'.1.1 = esC.g.epoch P + 1
        ·
          have hnew_c : c.1.1 = esC.g.epoch P + 1 := by rw [hhdr, hnew]
          have hsend0' : P.sendsIn (esC.g.epoch P + 1) = false := hnew ▸ hsend0
          obtain ⟨hr_ep, hP_eq_R, hO_eq_S, hO_ep, hmax_eq, Tm, Im, hct2, hcC, hST, hSroot,
            hcP, hlast⟩ := hS.deliver_new_info hr hnew_c
          have hc'2 : c'.1.2 = some Tm := by rw [hhdr', hct2]
          let p := prng.up (esC.g.st P).root Im
          have hp1 : (prng.up (esC.g.st P).root Im).1 = (esC.g.st P.other).root := hSroot.symm
          let γP' := (cka.receive (esP.g.st P).γ Tm).1
          have hstartC := fun ctx γv =>
            hooksCKA_startRecv_honest cka prng fs Δcka mo ctx P (esC.g.epoch P + 1) γv
              (esC.g.st P).root Tm Im esC.h hcC
          have hstartP : (simulateQ (pImpl prng)
              (((hooksPRNG cka prng fs mo).startRecv esP.g P (esC.g.epoch P + 1)
                (esP.g.st P).γ (esP.g.st P).root Tm).run esP.h)).run sp =
              pure ((some (some (γP', (esP.g.st P.other).root, fs.initReceiver p.2)), esP.h),
                sp) := by
            simp [hooksPRNG, hcP, p, γP', StateT.run_bind, StateT.run_get, StateT.run_pure,
              simulateQ_pure]
          cases hfs : fs.receive (fs.initReceiver p.2) c'.1 c'.2 with
          | none =>
            have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                hp1, p, hfs, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                hesC_eq]
            have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0',
                hnew, hc'2, hstartP, hfs, StateT.run_bind, StateT.run_pure, simulateQ_bind,
                simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          | some vim =>
            rcases vim with ⟨v', i', m'⟩
            let m := esC.g.epoch P + 1
            have hne_ep : (m != r.pos.epoch) = false := by
              simp [m, hr_ep]
            by_cases hqep : qep + 1 < m
            · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                  hp1, p, hfs, m, hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                  htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                  hsend0', hnew, hc'2, hstartP, hfs, m, hqep, StateT.run_bind, StateT.run_pure,
                  simulateQ_bind, simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
            · let pos : SM.Pos := ⟨P.other, m, i'⟩
              have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                eraseSt_trivial hS.g_eq (2 + Δcka) pos
              by_cases htriv : esC.g.trivial (2 + Δcka) pos
              · let vR' := Function.update (Function.update (esC.g.st P).vR m
                  (some (fs.initReceiver p.2))) m (some v')
                let γC_final := if localCKA mo Δcka m then some γP' else none
                let stC_final : VP (Option Γ) T Sig SS RS :=
                  { esC.g.st P with
                    tcur := m, γ := γC_final, root := (esC.g.st P.other).root, vR := vR' }
                let stP_final : VP Γ T (Option Sig) SS RS :=
                  { esP.g.st P with
                    tcur := m, γ := γP', root := (esP.g.st P.other).root, vR := vR' }
                have hvRP : (esP.g.st P).vR = (esC.g.st P).vR := hS.vR_eq P
                have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                    pure ((some (.accepted m i' (some m')),
                      { esP with g := esP.g.accept P stP_final pos }), sp) := by
                  simp [stepPDF, implEDF, deliverForgeE, commitE, vRecv, hS.abort_P, hwin, hwin0,
                    htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                    hS.tcur_P P, hsend0', hnew, hc'2, hvRP, hstartP, hfs, m, hqep, hr_ep, pos,
                    htriv_eq, htriv, vR', stP_final, γP', StateT.run_bind, StateT.run_pure,
                    StateT.run_modify, simulateQ_bind, simulateQ_pure]
                by_cases hloc : localCKA mo Δcka (esC.g.epoch P) = true
                · have hloc_m : localCKA mo Δcka m = true := by
                    simp only [localCKA, Bool.or_eq_true, decide_eq_true_eq] at hloc ⊢
                    rcases hloc with h1 | h2
                    · exact Or.inl h1
                    · exact Or.inr (by omega)
                  have hγC : (esC.g.st P).γ = some (esP.g.st P).γ := by
                    rw [hS.γ_C P, hloc]; rfl
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some (.accepted m i' (some m')),
                        { esC with g := esC.g.accept P stC_final pos }), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, commitE, vRecv, hS.abort_C, hwin0, hr,
                      htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2,
                      hstartC, hp1, p, hfs, hγC, hloc_m, m, hqep, hr_ep, pos, htriv, vR',
                      γC_final, stC_final, γP', StateT.run_bind, StateT.run_pure,
                      StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
                    (fun h => by simp [m, hloc_m] at h))
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
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some (.accepted m i' (some m')),
                          { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [stepCDF, implEDF, deliverForgeE, commitE, liftC, CKA.receiveQuery,
                        CKA.corrQuery, cImpl, CKA.oracleImpl, CKA.receiveImpl, CKA.corrImpl, vRecv,
                        hS.abort_C, hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P,
                        hS.tcur_C P, hsend0', hnew, hc'2, hstartC, hp1, p, hfs, hγC, hcanR,
                        hlast_eq, hsc_stP, hfin, hloc_m, sc', CKA.GameState.afterReceive,
                        CKA.GameState.finished, hsc_epP, m, hqep, hr_ep, pos, htriv, vR',
                        γC_final, stC_final, γP', simulateQ_bind, simulateQ_query,
                        simulateQ_pure, map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C
                      (fun h => by simp [m, hloc_m] at h))
                  · have hloc_m : localCKA mo Δcka m = false := by
                      simp [localCKA, htL_none, hfin]
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some (.accepted m i' (some m')),
                          { esC with g := esC.g.accept P stC_final pos }), sc') := by
                      simp [stepCDF, implEDF, deliverForgeE, commitE, liftC, CKA.receiveQuery,
                        cImpl, CKA.oracleImpl, CKA.receiveImpl, vRecv, hS.abort_C, hwin0, hr,
                        htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew,
                        hc'2, hstartC, hp1, p, hfs, hγC, hcanR, hlast_eq, hsc_stP, hfin, hloc_m,
                        sc', m, hqep, hr_ep, pos, htriv, vR', γC_final, stC_final, γP',
                        simulateQ_bind, simulateQ_query, simulateQ_pure,
                        map_eq_bind_pure_comp, StateT.run_bind, StateT.run_pure, StateT.run_modify]
                    rw [hC, hP, pure_bind, pure_bind]
                    refine ih _ (hS.accept_new P γP' vR' pos rfl hO_ep hS.b_C fun _ => ?_)
                    simp [sc', CKA.GameState.afterReceive, Party.other_ne, hsc_epP, hsc_stO,
                      hsc_epO, hO_ep]
              · simp only [Bool.not_eq_true] at htriv
                by_cases hinj : (mo.cfg (M := M)).injectFull m
                · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some .rejected,
                        { esC with g := { esC.g with win := true } }), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                      hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                      hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some .rejected,
                        { esP with g := { esP.g with win := true } }), sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                      hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                      hsend0', hnew, hc'2, hstartP, hfs, m, hqep, hr_ep, pos, htriv_eq,
                      htriv, hinj, StateT.run_bind, StateT.run_pure, StateT.run_modify,
                      simulateQ_bind, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl))
                · simp only [Bool.not_eq_true] at hinj
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some .rejected, esC), sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                      hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0', hnew, hc'2, hstartC,
                      hp1, p, hfs, m, hqep, hr_ep, pos, htriv, hinj, StateT.run_bind,
                      StateT.run_pure, simulateQ_pure, hesC_eq]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some .rejected, esP), sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                      hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                      hsend0', hnew, hc'2, hstartP, hfs, m, hqep, hr_ep, pos, htriv_eq,
                      htriv, hinj, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
                      hesP_eq]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih (some .rejected) hS
        ·
          have hle_ep : c'.1.1 ≤ esC.g.epoch P := by omega
          have hvRP : (esP.g.st P).vR c'.1.1 = (esC.g.st P).vR c'.1.1 := by rw [hS.vR_eq P]
          cases hvR : (esC.g.st P).vR c'.1.1 with
          | none =>
            have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                pure ((some .rejected, esC), sc) := by
              simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, StateT.run_bind,
                StateT.run_pure, simulateQ_pure, hesC_eq]
            have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                pure ((some .rejected, esP), sp) := by
              simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c, hr,
                htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P, hsend0,
                hle, hnew, hvRP, hvR, StateT.run_bind, StateT.run_pure, simulateQ_pure, hesP_eq]
            rw [hC, hP, pure_bind, pure_bind]
            exact ih (some .rejected) hS
          | some v =>
            cases hfs : fs.receive v c'.1 c'.2 with
            | none =>
              have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                  pure ((some .rejected, esC), sc) := by
                simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                  hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                  StateT.run_bind, StateT.run_pure, simulateQ_pure, hesC_eq]
              have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                  pure ((some .rejected, esP), sp) := by
                simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                  hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                  hsend0, hle, hnew, hvRP, hvR, hfs, StateT.run_bind, StateT.run_pure,
                  simulateQ_pure, hesP_eq]
              rw [hC, hP, pure_bind, pure_bind]
              exact ih (some .rejected) hS
            | some vim =>
              rcases vim with ⟨v', i', m'⟩
              have heq_ep : r.pos.epoch = c'.1.1 := by rw [hhdr', ht1]
              have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [heq_ep]
              by_cases hqep : qep + 1 < c'.1.1
              · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                    pure ((some .rejected, esC), sc) := by
                  simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                    hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                    hqep, StateT.run_bind, StateT.run_pure, simulateQ_pure,
                    hesC_eq]
                have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                    pure ((some .rejected, esP), sp) := by
                  simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0, htrans_c,
                    hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P, hS.tcur_P P,
                    hsend0, hle, hnew, hvRP, hvR, hfs, hqep, StateT.run_bind, StateT.run_pure,
                    simulateQ_pure, hesP_eq]
                rw [hC, hP, pure_bind, pure_bind]
                exact ih (some .rejected) hS
              · let pos : SM.Pos := ⟨P.other, c'.1.1, i'⟩
                have htriv_eq : esP.g.trivial (2 + Δcka) pos = esC.g.trivial (2 + Δcka) pos :=
                  eraseSt_trivial hS.g_eq (2 + Δcka) pos
                by_cases htriv : esC.g.trivial (2 + Δcka) pos
                · let vR' := Function.update (esC.g.st P).vR c'.1.1 (some v')
                  have hvR'_eq : Function.update (esP.g.st P).vR c'.1.1 (some v') = vR' := by
                    simp [vR', hS.vR_eq P]
                  have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esC with g := esC.g.accept P { esC.g.st P with vR := vR' } pos }),
                        sc) := by
                    simp [stepCDF, implEDF, deliverForgeE, vRecv, commitE, hooksCKA, hS.abort_C,
                      hwin0, hr, htrans0, hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0,
                      hle, hnew, hvR, hfs, hqep, heq_ep, htriv, pos, vR', StateT.run_bind,
                      StateT.run_pure, StateT.run_modify, simulateQ_pure]
                  have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                      pure ((some (.accepted c'.1.1 i' (some m')),
                        { esP with g := esP.g.accept P { esP.g.st P with vR := vR' } pos }),
                        sp) := by
                    simp [stepPDF, implEDF, deliverForgeE, vRecv, commitE, hS.abort_P, hwin, hwin0,
                      htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                      hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                      htriv, pos, hvR'_eq, StateT.run_bind, StateT.run_pure,
                      StateT.run_modify, simulateQ_pure]
                  rw [hC, hP, pure_bind, pure_bind]
                  exact ih _ (hS.accept_old P vR' pos hle_ep)
                · simp only [Bool.not_eq_true] at htriv
                  by_cases hinj : (mo.cfg (M := M)).injectFull c'.1.1
                  · have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some .rejected, { esC with g := { esC.g with win := true } }),
                          sc) := by
                      simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                        hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                        hqep, heq_ep, htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify, simulateQ_pure]
                    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, { esP with g := { esP.g with win := true } }),
                          sp) := by
                      simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0,
                        htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                        hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        StateT.run_modify, simulateQ_pure]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) (hS.set_win_prf true sp.prf (Or.inl rfl))
                  · simp only [Bool.not_eq_true] at hinj
                    have hC : stepCDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esC sc =
                        pure ((some .rejected, esC), sc) := by
                      simp [stepCDF, implEDF, deliverForgeE, vRecv, hS.abort_C, hwin0, hr, htrans0,
                        hcomp0', hhdr, hS.id_C P, hS.tcur_C P, hsend0, hle, hnew, hvR, hfs,
                        hqep, heq_ep, htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        simulateQ_pure, hesC_eq]
                    have hP : stepPDF cka prng fs Δcka qep mo (.inr (.inr (P, c, c'))) esP sp =
                        pure ((some .rejected, esP), sp) := by
                      simp [stepPDF, implEDF, deliverForgeE, vRecv, hS.abort_P, hwin, hwin0,
                        htrans_c, hr, htrans_c', htrans0, hcomp, hcomp0', hhdr, hS.id_P P,
                        hS.tcur_P P, hsend0, hle, hnew, hvRP, hvR, hfs, hqep, heq_ep, htriv_eq,
                        htriv, hinj, pos, StateT.run_bind, StateT.run_pure,
                        simulateQ_pure, hesP_eq]
                    rw [hC, hP, pure_bind, pure_bind]
                    exact ih (some .rejected) hS

theorem runLDF_le_runRDF (mo : Mode) (hauth : mo.auth = true)
    (hvalid : SM.lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esC : EStateC Γ T Sig SS RS M E I} {sc : CKA.GameState Γ T}
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    (hS : Sync prng Δcka mo esC sc esP sp) :
    𝒟[runLDF cka prng fs Δcka qep mo oa esC sc] {true} ≤
      𝒟[runRDF cka prng fs Δcka qep mo oa esP sp] {true} := by
  induction oa using OracleComp.inductionOn generalizing esC sc esP sp with
  | pure b' =>
    rw [runLDF_pure, runRDF_pure, hS.authOut_eq]
  | query_bind q k ih =>
    rw [runLDF_query_bind, runRDF_query_bind]
    rcases q with n | (((((⟨P, m_msg, r⟩ | q_ch) | ⟨P, c⟩) | q_inj) | P) | ⟨P, c, c'⟩)
    · exact step_coinsE_DF_le cka prng fs Δcka qep mo n k hS @ih
    · exact step_transmitE_DF_le cka prng fs Δcka qep mo hvalid P m_msg r k hS @ih
    · exact step_challE_DF_le cka prng fs Δcka qep mo hauth q_ch k hS @ih
    · exact step_deliverE_DF_le cka prng fs Δcka qep mo hauth P c k hS @ih
    · exact step_injectE_DF_le cka prng fs Δcka qep mo hauth q_inj k hS @ih
    · exact step_corrE_DF_le cka prng fs Δcka qep mo hauth P k hS @ih
    · exact step_deliverForgeE_DF_le cka prng fs Δcka qep mo hauth P c c' k hS @ih

/-- Lemma 10 for `DeliverForge`: with a uniform CKA key in epoch `t_heal`, the simulation of
`redCKAAuthDF` is bounded by that of `redPRNGAuthDF` with the real root RNG. -/
theorem lemma10_df (_hc : cka.Correct) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDF cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[PRFPRNG.branch prng false (redPRNGAuthDF cka prng fs lam Δcka qep tL t A)] {true} := by
  by_cases hvg : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · cases htL : tL with
    | none =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch none) true
          (redCKAAuthDF cka prng fs lam Δcka qep none t A) =
          ($ᵗ KC >>= fun kc_ext => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runLDF cka prng fs Δcka qep ⟨true, none, t⟩ A
              (initES_C cka prng fs lam none kr kc)
              (CKA.initState cka kc_ext true)) := by
        unfold CKA.branch redCKAAuthDF authSimDF engRunDF initCKA runLDF initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuthDF cka prng fs lam Δcka qep none 0 A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)) := by
          unfold PRFPRNG.branch redPRNGAuthDF authSimDF engRunDF runRDF initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_zero cka prng fs lam, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, 0⟩ A
                (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
                (initSP_zero prng kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runLDF_le_runRDF cka prng fs Δcka qep ⟨true, none, 0⟩ rfl hvg A
          (sync_init_none_zero cka prng fs lam Δcka kr kc kc_ext)
      · have hR : PRFPRNG.branch prng false
            (redPRNGAuthDF cka prng fs lam Δcka qep none t A) =
            ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)) := by
          unfold PRFPRNG.branch redPRNGAuthDF authSimDF engRunDF runRDF initES_P
          simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
            initPRNG_run_none_pos cka prng fs lam t ht, map_eq_bind_pure_comp,
            bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
          rfl
        rw [hL, hR]
        have hconst :
            𝒟[$ᵗ KC >>= fun _ : KC => $ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} =
            𝒟[$ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
              runRDF cka prng fs Δcka qep ⟨true, none, t⟩ A
                (initES_P cka prng fs lam none kr kc)
                (initSP prng lam none kr)] {true} := by
          rw [OracleComp.evalDist_bind_const]
        rw [← hconst]
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc_ext _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kr _ => ?_
        refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
          fun kc _ => ?_
        exact runLDF_le_runRDF cka prng fs Δcka qep ⟨true, none, t⟩ rfl hvg A
          (sync_init_none_pos cka prng fs lam Δcka t ht kr kc kc_ext)
    | some l =>
      subst htL
      have hL : CKA.branch cka Δcka (healEpoch (some l)) true
          (redCKAAuthDF cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KC >>= fun kc => $ᵗ KR >>= fun kr =>
            runLDF cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_C cka prng fs lam (some l) kr kc)
              (CKA.initState cka kc true)) := by
        unfold CKA.branch redCKAAuthDF authSimDF engRunDF initCKA runLDF initES_C
        simp only [cImpl, Mode.tH, Mode.policy, StateT.run'_eq, StateT.run_lift,
          StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure,
          simulateQ_sampleT_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
          Function.comp_apply]
        rfl
      have hR : PRFPRNG.branch prng false
          (redPRNGAuthDF cka prng fs lam Δcka qep (some l) t A) =
          ($ᵗ KR >>= fun kr => $ᵗ KC >>= fun kc =>
            runRDF cka prng fs Δcka qep ⟨true, some l, t⟩ A
              (initES_P cka prng fs lam (some (prng.up (prng.init kr) lam).1) kr kc)
              (initSP prng lam (some l) kr)) := by
        unfold PRFPRNG.branch redPRNGAuthDF authSimDF engRunDF runRDF initES_P
        simp only [pImpl, Mode.policy, StateT.run'_eq, StateT.run_bind, simulateQ_bind,
          initPRNG_run_some cka prng fs lam Δcka l t hvg, map_eq_bind_pure_comp,
          bind_assoc, pure_bind, simulateQ_pure, StateT.run_pure, Function.comp_apply]
        rfl
      rw [hL, hR, OracleComp.evalDist_bind_bind_swap ($ᵗ KR) ($ᵗ KC)]
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kc _ => ?_
      refine OracleComp.evalDist_bind_apply_mono_of_support _ _ _ (MeasurableSet.singleton true)
        fun kr _ => ?_
      exact runLDF_le_runRDF cka prng fs Δcka qep ⟨true, some l, t⟩ rfl hvg A
        (sync_init_some cka prng fs lam Δcka l t hvg kr kc)
  · have hvg_f : SM.lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hred : redCKAAuthDF cka prng fs lam Δcka qep tL t A =
        (engRunDF (hooksCKA cka prng fs Δcka ⟨true, tL, t⟩) (2 + Δcka) qep fs.maxSkip
          (Config.auth t) ⟨true, tL, t⟩ (initCKA cka prng fs lam ⟨true, tL, t⟩) {} false A >>=
          fun _ => pure false) := by
      dsimp only [redCKAAuthDF, authSimDF]
      congr 1
      funext r
      cases r with
      | none => rfl
      | some p =>
        exact congrArg pure (authOut_of_validGuess_false (2 + Δcka) ⟨true, tL, t⟩ hvg_f p.2)
    have hbranch : 𝒟[CKA.branch cka Δcka (healEpoch tL) true
        (redCKAAuthDF cka prng fs lam Δcka qep tL t A)] = 𝒟[(pure false : ProbComp Bool)] := by
      unfold CKA.branch
      rw [hred]
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
      refine evalDist_bind_false_of_support ($ᵗ KC) _ fun k _ => ?_
      exact OracleComp.evalDist_bind_const _ _
    rw [hbranch]
    simp

end AuthL10DF

end CryptoGames.SM.Construction.DeliverForge

