/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperDefs
public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgeFS

/-!
# Lemma 11 for `DeliverForgePaper` (Hop H2 → FS-AEAD)

**Checked by Lean.** Proves `lemma11_df_paper_proof`, bounding `redPRNGAuthDFPaper` under
`corrAllowedPaper` by the sum of FS-AEAD advantages of `redFSAuthDFPaper j` over `j < q`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.AuthL11

open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
open Engine
open SM

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem eraseSt_corrAllowedPaper {St₁ St₂ : Type} {s₁ : GameState St₁ M (Header T × E)}
    {s₂ : GameState St₂ M (Header T × E)} (h : eraseSt s₁ = eraseSt s₂) (P : Party) :
    s₁.corrAllowedPaper P = s₂.corrAllowedPaper P := by
  unfold GameState.corrAllowedPaper
  rw [show s₁.chall = s₂.chall from congrArg GameState.chall h]

def stepPDFPaper (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateP Γ T Sig SS RS M E K) ×
      PRFPRNG.GameState Sig I K) :=
  (simulateQ (pImpl prng)
    ((implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esP)).run sp

def stepLDFPaper (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFPaper (hooksLocal cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esL)

def runPDFPaper (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) : ProbComp Bool := do
  let r ← (simulateQ (pImpl prng)
    ((simulateQ (implEDFPaper (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy)
      oa).run esP)).run sp
  pure (authOut (2 + Δcka) mo.policy r.1.2)

def runLocDFPaper (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFPaper (hooksLocal cka prng fs mo)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2)

def runLocAtDFPaper (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFPaper (hooksLocal cka prng fs mo)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

def localAuthDFPaper (tL : Option ℕ) (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocDFPaper cka prng fs Δcka qep mo A { g, h }

def localAuthAtDFPaper (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocal cka prng fs lam mo).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtDFPaper cka prng fs Δcka qep mo j A { g, h }

def stepLFixedDFPaper (j : ℕ) (k_fs : K) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    ProbComp ((SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I) :=
  simulateQ lImpl
    ((implEDFPaper (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run esL)

def runLocAtFixedDFPaper (j : ℕ) (k_fs : K) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) : ProbComp Bool := do
  let r ← simulateQ lImpl
    ((simulateQ (implEDFPaper (hooksLocalFixed cka prng fs mo j k_fs)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esL)
  pure (authOut (2 + Δcka) mo.policy r.2 && (r.2.h.lastIdx == some j))

def localAuthAtFixedDFPaper (j : ℕ) (k_fs : K) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) : ProbComp Bool := do
  let mo : Mode := ⟨true, tL, t⟩
  let (vs, h) ← simulateQ lImpl ((initLocalFixed cka prng fs lam mo j k_fs).run {})
  match vs with
  | none => return false
  | some (vA, vB) =>
    let g : Ctx Γ T Sig (SS × Option ℕ) (RS × Option ℕ) M E :=
      { st := fun P => match P with | .A => vA | .B => vB, b := false }
    runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs A { g, h }

def stepFDFPaper (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) :=
  (simulateQ (implFS fs)
    ((implEDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy q).run
      esF)).run st

def runFDFPaper (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) : ProbComp Bool := do
  let r ← (simulateQ (implFS fs)
    ((simulateQ (implEDFPaper (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy) oa).run esF)).run st
  pure r.2.win

omit [SampleableType KR] [SampleableType KC] in
theorem runPDFPaper_pure (b' : Bool) (esP : EStateP Γ T Sig SS RS M E K)
    (sp : PRFPRNG.GameState Sig I K) :
    runPDFPaper cka prng fs Δcka qep mo (pure b') esP sp =
      pure (authOut (2 + Δcka) mo.policy esP) := by
  simp [runPDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFPaper_pure (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFPaper cka prng fs Δcka qep mo (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL) := by
  simp [runLocDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFPaper_pure (j : ℕ) (b' : Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFPaper cka prng fs Δcka qep mo j (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFPaper_pure (j : ℕ) (k_fs : K) (b' : Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs (pure b') esL =
      pure (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) := by
  simp [runLocAtFixedDFPaper, map_eq_bind_pure_comp]

omit [SampleableType KR] [SampleableType KC] in
theorem runPDFPaper_query_bind (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    runPDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esP sp =
      stepPDFPaper cka prng fs Δcka qep mo q esP sp >>= fun r =>
        runPDFPaper cka prng fs Δcka qep mo (k r.1.1) r.1.2 r.2 := by
  simp [runPDFPaper, stepPDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocDFPaper_query_bind (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocDFPaper cka prng fs Δcka qep mo (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFPaper cka prng fs Δcka qep mo q esL >>= fun r =>
        runLocDFPaper cka prng fs Δcka qep mo (k r.1) r.2 := by
  simp [runLocDFPaper, stepLDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtDFPaper_query_bind (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtDFPaper cka prng fs Δcka qep mo j (liftM (OracleSpec.query q) >>= k) esL =
      stepLDFPaper cka prng fs Δcka qep mo q esL >>= fun r =>
        runLocAtDFPaper cka prng fs Δcka qep mo j (k r.1) r.2 := by
  simp [runLocAtDFPaper, stepLDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runLocAtFixedDFPaper_query_bind (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs (liftM (OracleSpec.query q) >>= k) esL =
      stepLFixedDFPaper cka prng fs Δcka qep mo j k_fs q esL >>= fun r =>
        runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs (k r.1) r.2 := by
  simp [runLocAtFixedDFPaper, stepLFixedDFPaper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem runFDFPaper_query_bind (j : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    runFDFPaper cka prng fs Δcka qep mo j (liftM (OracleSpec.query q) >>= k) esF st =
      stepFDFPaper cka prng fs Δcka qep mo j q esF st >>= fun r =>
        runFDFPaper cka prng fs Δcka qep mo j (k r.1.1) r.1.2 r.2 := by
  simp [runFDFPaper, stepFDFPaper, simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp,
    bind_assoc]

theorem stepPDFPaper_abort (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) (hab : esP.abort = true) :
    ∀ r ∈ support (stepPDFPaper cka prng fs Δcka qep mo q esP sp), r.1.2.abort = true := by
  intro r hr
  rcases q with n | ((q14 | P) | df)
  · exact stepPDF_abort cka prng fs Δcka qep mo (.inl n) esP sp hab r hr
  · exact stepPDF_abort cka prng fs Δcka qep mo (.inr (.inl (.inl q14))) esP sp hab r hr
  · simp only [stepPDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
      StateT.run_get, pure_bind, hab, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
      support_pure, Set.mem_singleton_iff] at hr
    subst hr; exact hab
  · exact stepPDF_abort cka prng fs Δcka qep mo (.inr (.inr df)) esP sp hab r hr

theorem runPDFPaper_abort (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true) :
    𝒟[runPDFPaper cka prng fs Δcka qep mo oa esP sp] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esP sp with
  | pure b' =>
    rw [runPDFPaper_pure]
    simp [authOut, hab]
  | query_bind q k ih =>
    rw [runPDFPaper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1.1 (stepPDFPaper_abort cka prng fs Δcka qep mo q esP sp hab r hr)

theorem runPDFPaper_abort_le (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K} (hab : esP.abort = true)
    (rhs : ℝ≥0∞) :
    𝒟[runPDFPaper cka prng fs Δcka qep mo oa esP sp] {true} ≤ rhs := by
  rw [runPDFPaper_abort cka prng fs Δcka qep mo oa hab]
  exact zero_le

omit [Inhabited E] [SampleableType KR] [SampleableType KC] in
theorem leComp_corrEPaper_PRNG_local
    (P : Party)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      ((simulateQ (pImpl prng)
        ((corrEPaper (hooksPRNG cka prng fs mo) mo.policy P).run esP)).run sp)
      (simulateQ lImpl
        ((corrEPaper (hooksLocal cka prng fs mo) mo.policy P).run esL)) := by
  unfold corrEPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rw [hsync.abort_eq, eraseSt_win hsync.g_eq, eraseSt_corrAllowedPaper hsync.g_eq]
  by_cases hguard : (esL.abort || esL.g.win || !esL.g.corrAllowedPaper P) = true
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
        simp only [StateT.run_pure, pure_bind]
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

theorem leComp_stepPDFPaper_stepLDFPaper (hauth : mo.auth = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    LeComp (StepRel Δcka mo)
      (stepPDFPaper cka prng fs Δcka qep mo q esP sp)
      (stepLDFPaper cka prng fs Δcka qep mo q esL) := by
  rcases q with n | ((q14 | P) | df)
  · exact leComp_stepPDF_stepLDF cka prng fs Δcka qep mo hauth (.inl n) hsync
  · exact leComp_stepPDF_stepLDF cka prng fs Δcka qep mo hauth (.inr (.inl (.inl q14))) hsync
  · exact leComp_corrEPaper_PRNG_local cka prng fs Δcka mo P hsync
  · exact leComp_stepPDF_stepLDF cka prng fs Δcka qep mo hauth (.inr (.inr df)) hsync

theorem runPDFPaper_le_runLocDFPaper (hauth : mo.auth = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esP : EStateP Γ T Sig SS RS M E K} {sp : PRFPRNG.GameState Sig I K}
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hsync : SyncPL Δcka mo esP sp esL) :
    𝒟[runPDFPaper cka prng fs Δcka qep mo oa esP sp] {true} ≤
      𝒟[runLocDFPaper cka prng fs Δcka qep mo oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esP sp esL with
  | pure b' =>
    rw [runPDFPaper_pure, runLocDFPaper_pure]
    have hout : authOut (2 + Δcka) mo.policy esP = authOut (2 + Δcka) mo.policy esL := by
      unfold authOut
      rw [hsync.abort_eq, eraseSt_win hsync.g_eq,
        eraseSt_authOK hsync.g_eq (2 + Δcka) mo.policy.tL mo.policy.tStar]
    rw [hout]
  | query_bind q k ih =>
    rw [runPDFPaper_query_bind, runLocDFPaper_query_bind]
    refine leComp_stepPDFPaper_stepLDFPaper cka prng fs Δcka qep mo hauth q hsync _ _ ?_
    rintro ⟨⟨uP, esP'⟩, sp'⟩ ⟨uL, esL'⟩ (hab | ⟨rfl, hsync'⟩)
    · exact runPDFPaper_abort_le cka prng fs Δcka qep mo (k uP) hab _
    · exact ih uP hsync'

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runPDFPaper_eq (tL : Option ℕ) (t : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esP : EStateP Γ T Sig SS RS M E K) (sp : PRFPRNG.GameState Sig I K) :
    𝒟[do
      let x ← (simulateQ (pImpl prng)
        ((simulateQ (implEDFPaper (hooksPRNG cka prng fs ⟨true, tL, t⟩) (2 + Δcka) qep fs.maxSkip
          (Config.auth t) ⟨true, tL, t⟩) oa).run esP)).run sp
      pure (authOut (2 + Δcka) ⟨true, tL, t⟩ x.1.2)] =
    𝒟[runPDFPaper cka prng fs Δcka qep ⟨true, tL, t⟩ oa esP sp] := by
  simp [runPDFPaper, Mode.cfg, Mode.policy, map_eq_bind_pure_comp]

theorem branch_redPRNGAuthDFPaper_le_localAuthDFPaper (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} ≤
      𝒟[localAuthDFPaper cka prng fs lam Δcka qep tL t A] {true} := by
  have hpImpl : (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFPRNG.GameState Sig I K) ProbComp) + prng.oracleImpl = pImpl prng := rfl
  unfold PRFPRNG.branch redPRNGAuthDFPaper authSimDFPaper engRunDFPaper localAuthDFPaper
    initPRNG initLocal
  simp only [hpImpl, StateT.run'_eq, map_eq_bind_pure_comp,
    StateT.run_bind, simulateQ_bind, bind_assoc,
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
  · dsimp only at hnone; subst hnone; simp
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
    rw [evalDist_runPDFPaper_eq]
    refine runPDFPaper_le_runLocDFPaper cka prng fs Δcka qep ⟨true, tL, t⟩ rfl A ?_
    refine ⟨rfl, rfl, ?_, ?_, hb0, htab0.trans htab1.symm, hcorr0', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro P; cases P <;> refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hσ_rel⟩
      · intro t'; dsimp only [mkParties]; split <;> rfl
      · intro t'; rfl
    · intro t'; rw [hc1, hc0]; exact Or.inl ⟨rfl, rfl⟩
    · intro pos hpos; cases hpos
    · intro r hr; cases hr
    · intro P; simp
    · intro P hlt; simp at hlt
    · intro P _ hlt; cases P <;> exact (hlt0 hlt).symm
    · intro hpos P _ _; cases P <;> exact (hlt0 hpos).symm
    · intro Tc σc k idx' hc_eq _; rw [hc1, hc0] at hc_eq; cases hc_eq

theorem stepLDFPaper_sessInv (hauth : mo.auth = true) {q rem : ℕ}
    (q_sm : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    (∀ t, q_sm = .inl t →
      ∀ r ∈ support (stepLDFPaper cka prng fs Δcka qep mo (.inl t) esL),
        SessInv mo q rem r.2) ∧
    (∀ q_inr, q_sm = .inr q_inr → 0 < rem →
      ∀ r ∈ support (stepLDFPaper cka prng fs Δcka qep mo (.inr q_inr) esL),
        SessInv mo q (rem - 1) r.2) := by
  constructor
  · intro t ht r hr
    exact (stepLDF_sessInv cka prng fs Δcka qep mo hauth (.inl t) esL hS).1 t rfl r hr
  · intro q_inr hq_sm hrem r hr
    rcases q_inr with (q14 | P) | df
    · exact (stepLDF_sessInv cka prng fs Δcka qep mo hauth
        (.inr (.inl (.inl q14))) esL hS).2 _ rfl hrem r hr
    · have hrem_mono :
          (esL.g.win = true ∧ ∃ j, j < q ∧ esL.h.lastIdx = some j) ∨
          (esL.g.win = false ∧
            ((mo.tStar = 0 ∧ esL.h.sessions.length ≤ 1 ∧ rem - 1 ≤ q) ∨
             (0 < mo.tStar ∧ esL.h.sessions.length + (rem - 1) ≤ q))) := by
        rcases hS.bound with hwin | ⟨hnw, ⟨ht0, hle1, _⟩ | hpos⟩
        · exact Or.inl hwin
        · exact Or.inr ⟨hnw, Or.inl ⟨ht0, hle1, by omega⟩⟩
        · exact Or.inr ⟨hnw, Or.inr ⟨hpos.1, by omega⟩⟩
      have hS_noop : SessInv mo q (rem - 1) esL := ⟨hS.vR_idx, hS.cache_idx, hrem_mono⟩
      simp only [stepLDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
        StateT.run_get, pure_bind] at hr
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
    · exact (stepLDF_sessInv cka prng fs Δcka qep mo hauth (.inr (.inr df)) esL hS).2
        _ rfl hrem r hr

theorem runLocDFPaper_le_sum_runLocAtDFPaper (hauth : mo.auth = true) {q rem : ℕ}
    {p : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain → Prop} [DecidablePred p]
    (hp_inl : ∀ t, ¬ p (.inl t)) (hp_inr : ∀ t, p (.inr t))
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (hq : oa.IsQueryBoundP p rem)
    (esL : EStateL Γ T Sig SS RS M E K I) (hS : SessInv mo q rem esL) :
    𝒟[runLocDFPaper cka prng fs Δcka qep mo oa esL] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[runLocAtDFPaper cka prng fs Δcka qep mo j oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing rem esL with
  | pure a =>
    simp only [runLocDFPaper, runLocAtDFPaper, simulateQ_pure, StateT.run_pure, pure_bind,
      evalDist_pure]
    by_cases hwin : authOut (2 + Δcka) mo.policy esL = true
    · rw [hwin]
      simp only [Bool.true_and]
      have hwin_g : esL.g.win = true := by
        unfold authOut at hwin
        simp only [Bool.and_eq_true] at hwin
        exact hwin.1.2
      rcases hS.bound with ⟨_, j, hj, hlast⟩ | ⟨hnw, _⟩
      · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr hj))
        simp [hlast]
      · rw [hwin_g] at hnw; cases hnw
    · have hfalse : authOut (2 + Δcka) mo.policy esL = false := Bool.eq_false_iff.mpr hwin
      simp [hfalse]
  | query_bind t r ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    dsimp only [runLocDFPaper, runLocAtDFPaper]
    rw [simulateQ_query_bind]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_eq, StateT.run_bind,
      simulateQ_bind, bind_assoc]
    change 𝒟[stepLDFPaper cka prng fs Δcka qep mo t esL >>= fun x =>
        runLocDFPaper cka prng fs Δcka qep mo (r x.1) x.2] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[stepLDFPaper cka prng fs Δcka qep mo t esL >>= fun x =>
        runLocAtDFPaper cka prng fs Δcka qep mo j (r x.1) x.2] {true}
    refine evalDist_bind_le_sum _ _ _ _ (fun x hx => ?_)
    have hstep := stepLDFPaper_sessInv cka prng fs Δcka qep mo hauth t esL hS
    cases t with
    | inl c =>
      exact ih x.1 (by simpa [hp_inl c] using hq.2 x.1) x.2 (hstep.1 c rfl x hx)
    | inr q_sm =>
      have hpos : 0 < rem := hq.1.resolve_left (not_not.mpr (hp_inr q_sm))
      exact ih x.1 (by simpa [hp_inr q_sm] using hq.2 x.1) x.2 (hstep.2 q_sm rfl hpos x hx)

theorem localAuthDFPaper_le_sum_localAuthAtDFPaper (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[localAuthDFPaper cka prng fs lam Δcka qep tL t A] {true} ≤
      ∑ j ∈ Finset.range q, 𝒟[localAuthAtDFPaper cka prng fs lam Δcka qep j tL t A] {true} := by
  rw [MakesAtMostQueriesDF] at hq
  dsimp only [localAuthDFPaper, localAuthAtDFPaper]
  refine evalDist_bind_le_sum
    (simulateQ lImpl ((initLocal cka prng fs lam ⟨true, tL, t⟩).run {})) q
    (fun x => match x.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocDFPaper cka prng fs Δcka qep ⟨true, tL, t⟩ A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun j x => match x.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAtDFPaper cka prng fs Δcka qep ⟨true, tL, t⟩ j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := x.2 })
    (fun x hx => ?_)
  rcases x with ⟨vs, h⟩
  cases vs with
  | none => simp
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
      · intro P rsv hrsv; cases P <;> dsimp only [mkParties] at hrsv
        · split at hrsv
          · rename_i ht0; injection hrsv with hrsv; subst hrsv
            obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
            obtain ⟨⟨idx, hlt, heq⟩, _⟩ := hsome_reg I' hsid_some
            exact ⟨idx, hlt, heq⟩
          · cases hrsv
        · cases hrsv
      · intro Tc σ' k' idx' hc
        rcases sid with _ | Ik
        · obtain ⟨_, hs4⟩ := hnone_reg rfl; rw [hs4, hc_r] at hc; cases hc
        · obtain ⟨_, _, _, hc_reg, _⟩ := hsome_reg Ik rfl; rw [hc_reg, hc_r] at hc; cases hc
      · refine Or.inr ⟨rfl, ?_⟩
        by_cases ht0 : mo.tStar = 0
        · refine Or.inl ⟨ht0, ?_, le_rfl⟩
          obtain ⟨I', hsid_some⟩ := hsid_r1 ht0.symm
          obtain ⟨_, _, hl2, _, _⟩ := hsome_reg I' hsid_some
          have : h.sessions.length ≤ ({} : LState T Sig K I).sessions.length + 1 := by
            rw [← hl_r]; exact hl2
          exact this
        · have htpos : 0 < mo.tStar := Nat.pos_of_ne_zero ht0
          obtain ⟨_, hs4⟩ := hnone_reg (hsid_r2 (Ne.symm ht0))
          have hlen0 : h.sessions.length = 0 := by rw [hs4, hl_r]; rfl
          exact Or.inr ⟨htpos, by rw [hlen0, Nat.zero_add]⟩
    exact runLocDFPaper_le_sum_runLocAtDFPaper cka prng fs Δcka qep mo rfl (fun _ => by simp)
      (fun _ => by simp) A hq _ hS

theorem stepLFixedDFPaper_eq_of_lt {j : ℕ} (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    stepLFixedDFPaper cka prng fs Δcka qep mo j k_fs q esL =
      stepLDFPaper cka prng fs Δcka qep mo q esL := by
  rcases q with n | ((q14 | P) | df)
  · exact stepLFixedDF_eq_of_lt cka prng fs Δcka qep mo k_fs (.inl n) hlt
  · exact stepLFixedDF_eq_of_lt cka prng fs Δcka qep mo k_fs (.inr (.inl (.inl q14))) hlt
  · simp [stepLFixedDFPaper, stepLDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper,
      hooksLocalFixed, hooksLocal, StateT.run_bind, StateT.run_get, pure_bind]
  · exact stepLFixedDF_eq_of_lt cka prng fs Δcka qep mo k_fs (.inr (.inr df)) hlt

theorem mem_support_stepLDFPaper_sessions_le
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I)
    {r : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q × EStateL Γ T Sig SS RS M E K I}
    (hr : r ∈ support (stepLDFPaper cka prng fs Δcka qep mo q esL)) :
    esL.h.sessions.length ≤ r.2.h.sessions.length := by
  rcases q with n | ((q14 | P) | df)
  · exact mem_support_stepLDF_sessions_le cka prng fs Δcka qep mo (.inl n) esL hr
  · exact mem_support_stepLDF_sessions_le cka prng fs Δcka qep mo (.inr (.inl (.inl q14))) esL hr
  · simp only [stepLDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
      StateT.run_get, pure_bind] at hr
    split at hr
    · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact le_rfl
    · split at hr
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
      · simp only [hooksLocal, run_liftH, pure_bind, StateT.run_bind, StateT.run_pure,
          StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact le_rfl
  · exact mem_support_stepLDF_sessions_le cka prng fs Δcka qep mo (.inr (.inr df)) esL hr

theorem evalDist_runLocAtDFPaper_eq_fixed_of_lt {j : ℕ} (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} (hlt : j < esL.h.sessions.length) :
    𝒟[runLocAtDFPaper cka prng fs Δcka qep mo j oa esL] {true} =
      𝒟[runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtDFPaper_pure, runLocAtFixedDFPaper_pure]
  | query_bind q k ih =>
    rw [runLocAtDFPaper_query_bind, runLocAtFixedDFPaper_query_bind,
      stepLFixedDFPaper_eq_of_lt cka prng fs Δcka qep mo k_fs q hlt]
    refine evalDist_bind_congr_true _ _ _ fun r hr => ?_
    exact ih r.1 (lt_of_lt_of_le hlt
      (mem_support_stepLDFPaper_sessions_le cka prng fs Δcka qep mo q esL hr))

theorem shiftLe_stepLDFPaper {j : ℕ}
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    ShiftLe mo j (fun r => r.2.h)
      (stepLDFPaper cka prng fs Δcka qep mo q esL)
      (fun k_fs => stepLFixedDFPaper cka prng fs Δcka qep mo j k_fs q esL) := by
  rcases q with n | ((q14 | P) | df)
  · exact shiftLe_stepLDF cka prng fs Δcka qep mo (.inl n) hle hinv
  · exact shiftLe_stepLDF cka prng fs Δcka qep mo (.inr (.inl (.inl q14))) hle hinv
  · simp only [stepLDFPaper, stepLFixedDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper,
      StateT.run_bind, StateT.run_get, pure_bind, hooksLocal, hooksLocalFixed]
    split
    · simp only [StateT.run_pure, simulateQ_pure]
      exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure]
        exact ShiftLe.pure mo _ hle hinv
      · simp only [StateT.run_bind]
        exact ShiftLe.pure mo _ hle hinv
  · exact shiftLe_stepLDF cka prng fs Δcka qep mo (.inr (.inr df)) hle hinv

theorem evalDist_runLocAtDFPaper_le_fixed {j : ℕ}
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    𝒟[runLocAtDFPaper cka prng fs Δcka qep mo j oa esL] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    simp only [runLocAtDFPaper_pure, runLocAtFixedDFPaper_pure, OracleComp.evalDist_bind_const,
      le_rfl]
  | query_bind q k ih =>
    simp only [runLocAtDFPaper_query_bind, runLocAtFixedDFPaper_query_bind]
    refine shiftLe_stepLDFPaper cka prng fs Δcka qep mo q hle hinv
      (fun r => runLocAtDFPaper cka prng fs Δcka qep mo j (k r.1) r.2)
      (fun k_fs r => runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs (k r.1) r.2) ?_ ?_
    · intro r hlt k_fs
      exact (evalDist_runLocAtDFPaper_eq_fixed_of_lt cka prng fs Δcka qep mo k_fs (k r.1) hlt).le
    · intro r hle' hinv'
      exact ih r.1 hle' hinv'

theorem localAuthAtDFPaper_le_localAuthAtFixedDFPaper (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFPaper cka prng fs lam Δcka qep j tL t A] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        localAuthAtFixedDFPaper cka prng fs lam Δcka qep j k_fs tL t A] {true} := by
  let mo : Mode := ⟨true, tL, t⟩
  dsimp only [localAuthAtDFPaper, localAuthAtFixedDFPaper]
  have hle0 : ({} : LState T Sig K I).sessions.length ≤ j := Nat.zero_le j
  have hinv0 : TabSessInv mo ({} : LState T Sig K I) := fun _ _ => rfl
  refine shiftLe_initLocal cka prng fs lam mo hle0 hinv0
    (fun r => match r.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAtDFPaper cka prng fs Δcka qep mo j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    (fun k_fs r => match r.1 with
      | none => pure false
      | some (vA, vB) =>
        runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    ?_ ?_
  · intro r hlt k_fs; rcases r with ⟨vs, h⟩; cases vs with
    | none => exact le_rfl
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      exact (evalDist_runLocAtDFPaper_eq_fixed_of_lt cka prng fs Δcka qep mo k_fs A hlt).le
  · intro r hle hinv; rcases r with ⟨vs, h⟩; cases vs with
    | none => simp
    | some vAB =>
      rcases vAB with ⟨vA, vB⟩
      exact evalDist_runLocAtDFPaper_le_fixed cka prng fs Δcka qep mo A hle hinv

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runFDFPaper_eq_one_of_win (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E)
    (hwin : st.win = true) :
    𝒟[runFDFPaper cka prng fs Δcka qep mo j oa esF st] {true} = 1 := by
  unfold runFDFPaper
  refine evalDist_bind_eq_one _ _ fun r hr => ?_
  rw [simulateQ_implFS_preserves_win fs _ st hwin r hr]
  simp

theorem stepLFixedDFPaper_preserves_LHSDead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    ∀ r ∈ support (stepLFixedDFPaper cka prng fs Δcka qep mo j k_fs q esL),
      LHSDead Δcka mo j r.2 := by
  intro r hr
  rcases q with n | ((q14 | P) | df)
  · exact stepLFixedDF_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs (.inl n) esL hdead r hr
  · exact stepLFixedDF_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs
      (.inr (.inl (.inl q14))) esL hdead r hr
  · rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
        StateT.run_get, pure_bind, habw, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure,
        support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · simp only [stepLFixedDFPaper, implEDFPaper, QueryImpl.add_apply, corrEPaper, StateT.run_bind,
        StateT.run_get, pure_bind, hab, hwin, Bool.false_or] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      · split at hr
        · simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact LHSDead.of_abort Δcka mo j rfl
        · simp only [run_liftH, hooksLocalFixed, StateT.run_bind, StateT.run_pure, pure_bind,
            StateT.run_modify, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
  · exact stepLFixedDF_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs
      (.inr (.inr df)) esL hdead r hr

theorem evalDist_runLocAtFixedDFPaper_eq_zero_of_dead (hmo : mo.auth = true) (j : ℕ) (k_fs : K)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka mo j esL) :
    𝒟[runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtFixedDFPaper_pure]
    rcases hdead with ⟨_, hout⟩ | ⟨_, hwin, _, _⟩
    · simp [hout]
    · simp [authOut, hwin]
  | query_bind q k ih =>
    rw [runLocAtFixedDFPaper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr =>
      ih r.1 r.2
        (stepLFixedDFPaper_preserves_LHSDead cka prng fs Δcka qep mo hmo j k_fs q esL hdead r hr)

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runLocAtFixedDFPaper_eq_zero_of_not_validGuess (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = false)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    𝒟[runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs oa esL] {true} = 0 := by
  unfold runLocAtFixedDFPaper
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  have h : authOut (2 + Δcka) mo.policy r.2 = false := by
    simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
  simp [h]

omit [SampleableType KR] [SampleableType KC] in
theorem leComp_corrEPaper (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        ((corrEPaper (hooksLocalFixed cka prng fs mo j k_fs) mo.policy P).run esL))
      ((simulateQ (implFS fs)
        ((corrEPaper (hooksFS cka prng fs Δcka mo j) mo.policy P).run esF)).run st) := by
  have hcorrAll : esF.g.corrAllowedPaper P = esL.g.corrAllowedPaper P := by
    simp only [GameState.corrAllowedPaper, ← hs.hchallF, hs.hchall]
  unfold corrEPaper
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or, hcorrAll]
  by_cases hallow : esL.g.corrAllowedPaper P = true
  · simp only [hallow, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hdoom_eq :
        (mo.policy.leakDoom esF.g (esF.g.afterCorr P) || mo.policy.corrDoom esF.g P) =
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) := by
      simp only [Policy.leakDoom, Policy.corrDoom, GameState.afterCorr, GameState.leak,
        ← hs.hepoch, ← hs.htL, ← hs.hleaks]
    rw [hdoom_eq]
    by_cases hdoom :
        (mo.policy.leakDoom esL.g (esL.g.afterCorr P) || mo.policy.corrDoom esL.g P) = true
    · simp only [hdoom, ↓reduceIte, abortE]
      exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka mo j esL))
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte]
      have hnot_cdoom : mo.policy.corrDoom esL.g P = false := by
        cases h : mo.policy.corrDoom esL.g P
        · rfl
        · simp [h] at hdoom
      have hvR_tStar : (esF.g.st P).vR mo.tStar ≠ some none := by
        by_cases hP : P = Party.receiverOf mo.tStar
        · subst hP
          have hlt : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
            rw [hs.htcur_epoch]
            by_contra hge
            have := corrDoom_true_of_ge Δcka mo hauth hvg esL.g (Nat.le_of_not_lt hge)
            rw [this] at hnot_cdoom; cases hnot_cdoom
          rw [(hs.hvR_target_lt hlt).2.1]; intro h; cases h
        · have hne : (P, mo.tStar) ≠ (Party.receiverOf mo.tStar, mo.tStar) :=
            fun h => hP (Prod.ext_iff.mp h).1
          rcases hs.hvR_other P mo.tStar hne with ⟨_, hF⟩ | ⟨rs, idx?, _, hF, _⟩ <;>
            · rw [hF]; intro h; cases h
      have hvR_eq : ∀ t,
          (match (esF.g.st P).vR t with
            | some (some rs) => some rs
            | some none => none
            | none => none) = ((esL.g.st P).vR t).map Prod.fst := by
        intro t
        by_cases hPt : (P, t) = (Party.receiverOf mo.tStar, mo.tStar)
        · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hPt
          have hlt : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
            rw [hs.htcur_epoch]
            by_contra hge
            have := corrDoom_true_of_ge Δcka mo hauth hvg esL.g (Nat.le_of_not_lt hge)
            rw [this] at hnot_cdoom; cases hnot_cdoom
          obtain ⟨hL, hF, _⟩ := hs.hvR_target_lt hlt
          rw [hL, hF]; rfl
        · rcases hs.hvR_other P t hPt with ⟨hL, hF⟩ | ⟨rs, idx?, hL, hF, _⟩ <;>
            · rw [hL, hF]; rfl
      have hmatch_tStar :
          (match (esF.g.st P).vR mo.tStar with
            | some none =>
              do
                match (← get).ext with
                | some (_, rs) => pure (some (some rs))
                | none =>
                  if mo.auth then pure none
                  else do
                    match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS)
                        (ReceiverState := RS) (AssocData := Header T) (Message := M)
                        (Ciphertext := E)) with
                    | none => pure none
                    | some (ss, rs) =>
                      modify fun (s : FSState T Sig K I SS RS E) => { s with ext := some (ss, rs) }
                      pure (some (some rs))
            | _ => pure (some none) :
                HM (FSAEAD.spec SS RS (Header T) M E) (FSState T Sig K I SS RS E)
                  (Option (Option RS))) = pure (some none) := by
        cases h : (esF.g.st P).vR mo.tStar with
        | none => rfl
        | some v =>
          cases v with
          | none => exact False.elim (hvR_tStar h)
          | some rs => rfl
      have hcorr_pres :
          ∀ corrAt, st.senderCorruptedAt = some corrAt →
            SenderIsJ mo j esL ∧
            mo.tStar ≤ qep ∧
            healedBy (esL.g.afterCorr P).tL (2 + Δcka) mo.tStar = false ∧
            (∀ r ∈ (esL.g.afterCorr P).trans,
              r.pos.epoch = mo.tStar → corrAt < r.pos.idx → r.pos ∈ (esL.g.afterCorr P).comp) := by
        intro corrAt hcorr
        obtain ⟨hsJ, hqep, hheal, hcomp_mem⟩ := hs.hcorr_sync corrAt hcorr
        refine ⟨hsJ, hqep, healedBy_leak_false_of_false hheal, fun r hr hepoch_r hlt_r => ?_⟩
        exact List.mem_append_right _ (hcomp_mem r hr hepoch_r hlt_r)
      have hsync_loc : SyncLFS fs Δcka qep mo j k_fs
          { esL with g := esL.g.afterCorr P } { esF with g := esF.g.afterCorr P } st :=
        { hs with
          htL := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch]
          hcomp := by simp [GameState.afterCorr, GameState.leak, hs.htrans, hs.hcomp]
          hcomp_inv := comp_inv_afterCorr esL.g (2 + Δcka) (by omega) P
            (fun r hr => by rw [← hs.htcur_epoch r.pos.sender]; exact (hs.htrans_wf r hr).2.2.1)
            hs.hcomp_inv
          hleaks := by simp [GameState.afterCorr, GameState.leak, hs.htL, hs.hepoch, hs.hleaks]
          hcorrs := by simp [GameState.afterCorr, GameState.leak, hs.hepoch, hs.hcorrs]
          hcorr_sync := hcorr_pres }
      rcases hs.hvS P with ⟨hvSL, hvSF⟩ | ⟨ss, idx?, hvSL, hvSF, _, _⟩ |
          ⟨hP_s, hle_tcur, hqep_s, hsend_s, hsJ, hvSL, hvSF⟩
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, hsync_loc⟩))
        dsimp only [realParty, Option.map]
        congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
          exact hs.hroot P | exact hs.hγ P |
          exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_pure, StateT.run_modify, pure_bind, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, hsync_loc⟩))
        dsimp only [realParty, Option.map]
        congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
          exact hs.hroot P | exact hs.hγ P |
          exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
      · simp only [run_liftH, hooksLocalFixed, hooksFS, hvSL, hvSF,
          StateT.run_bind, StateT.run_get, hs.hextF, pure_bind,
          simulateQ_bind, simulateQ_implFS_corruptSenderQuery, bind_assoc,
          FSAEAD.corruptSender, hs.hendedFS, Bool.false_eq_true, ↓reduceIte,
          StateT.run_modify, StateT.run_pure, simulateQ_pure]
        refine LeComp.pure (Or.inr (Or.inr ⟨?_, ?_⟩))
        · dsimp only [realParty, Option.map]
          congr 2 <;> first | exact (hs.hidL P).trans (hs.hidF P).symm |
            exact hs.hroot P | exact hs.hγ P |
            exact hs.hTcur P | exact hs.htcur P | (funext t; exact (hvR_eq t).symm)
        · refine { hsync_loc with
            hendedFS := rfl, hextF := rfl, hfsSCorr := rfl
            hnot_senderJ := fun hnot => False.elim (hnot hsJ)
            hcorr_sync := ?_ }
          intro corrAt hcorr; dsimp only at hcorr; injection hcorr with hcorr_eq; subst hcorr_eq
          have hheal : healedBy (esL.g.afterCorr P).tL (2 + Δcka) mo.tStar = false := by
            dsimp only [GameState.afterCorr, GameState.leak]
            have hle_max : mo.tStar ≤ max (esL.g.epoch .A) (esL.g.epoch .B) := by
              have hep : mo.tStar ≤ esL.g.epoch P := by rwa [← hs.htcur_epoch P]
              cases P <;> omega
            exact healedBy_leak_false_of_le (by omega) hle_max
          refine ⟨hsJ, hqep_s, hheal, fun r hr hepoch_r hlt_r => ?_⟩
          cases hsc : st.senderCorruptedAt with
          | none =>
            rw [hsc, Option.getD_none] at hlt_r
            have hle_idx := (hs.htrans_wf r hr).2.2.2.2 hepoch_r hsJ
            omega
          | some c₀ =>
            rw [hsc, Option.getD_some] at hlt_r
            exact (hcorr_pres c₀ hsc).2.2.2 r hr hepoch_r hlt_r
  · simp only [hallow, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))

theorem leComp_stepLFixedDFPaper_stepFDFPaper (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (stepLFixedDFPaper cka prng fs Δcka qep mo j k_fs q esL)
      (stepFDFPaper cka prng fs Δcka qep mo j q esF st) := by
  rcases q with n | ((q14 | P) | df)
  · exact leComp_stepLFixedDF_stepFDF cka prng fs Δcka qep mo j k_fs hauth hvg (.inl n) hs
  · exact leComp_stepLFixedDF_stepFDF cka prng fs Δcka qep mo j k_fs hauth hvg
      (.inr (.inl (.inl q14))) hs
  · exact leComp_corrEPaper cka prng fs Δcka qep mo j k_fs hauth hvg P hs
  · exact leComp_stepLFixedDF_stepFDF cka prng fs Δcka qep mo j k_fs hauth hvg (.inr (.inr df)) hs

theorem runLocAtFixedDFPaper_le_runFDFPaper (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st) :
    𝒟[runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs oa esL] {true} ≤
      𝒟[runFDFPaper cka prng fs Δcka qep mo j oa esF st] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL esF st with
  | pure b' =>
    have hwinL := hs.hwinL
    have hout : (authOut (2 + Δcka) mo.policy esL && (esL.h.lastIdx == some j)) = false := by
      simp [authOut, hwinL]
    simp only [runLocAtFixedDFPaper, simulateQ_pure, StateT.run_pure, pure_bind, hout]
    have hzero : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
    rw [hzero]
    exact zero_le
  | query_bind q k ih =>
    rw [runLocAtFixedDFPaper_query_bind, runFDFPaper_query_bind]
    refine leComp_stepLFixedDFPaper_stepFDFPaper cka prng fs Δcka qep mo j k_fs hauth hvg q hs
      (fun rL => runLocAtFixedDFPaper cka prng fs Δcka qep mo j k_fs (k rL.1) rL.2)
      (fun rF => runFDFPaper cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2) ?_
    intro rL rF hrel
    rcases hrel with hdead | hwin | ⟨heq_ans, hs'⟩
    · rw [evalDist_runLocAtFixedDFPaper_eq_zero_of_dead cka prng fs Δcka qep mo hauth j k_fs
        (k rL.1) rL.2 hdead]
      exact zero_le
    · rw [evalDist_runFDFPaper_eq_one_of_win cka prng fs Δcka qep mo j (k rF.1.1) rF.1.2 rF.2 hwin]
      exact prob_le_one
    · rw [heq_ans]
      exact ih rF.1.1 hs'

def runFSDFPaper (j : ℕ) (b : Bool) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  engRunDFPaper (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initFS cka prng fs lam mo j) {} b A

theorem localAuthAtFixedDFPaper_le_runFSDFPaper (j : ℕ) (k_fs : K) (b_fs : Bool)
    (tL : Option ℕ) (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtFixedDFPaper cka prng fs lam Δcka qep j k_fs tL t A] {true} ≤
      𝒟[(simulateQ (implFS fs) (runFSDFPaper cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A)).run
          (FSAEAD.initState fs k_fs b_fs) >>= fun z => pure z.2.win] {true} := by
  by_cases hvg : lastLeakGuessAdmissible (2 + Δcka) tL t = true
  · unfold localAuthAtFixedDFPaper runFSDFPaper engRunDFPaper
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine leComp_init cka prng fs lam Δcka qep ⟨true, tL, t⟩ j k_fs b_fs _ _ ?_
    intro rL rF ⟨vAL, vBL, vAF, vBF, hrL1, hrF1, hrel⟩
    rcases rL with ⟨vsL, hL⟩
    rcases rF with ⟨⟨vsF, hF⟩, stF⟩
    dsimp only at hrL1 hrF1 ⊢
    subst hrL1 hrF1
    dsimp only at hrel ⊢
    rcases hrel with hdead | hs
    · exact le_of_eq_of_le
        (evalDist_runLocAtFixedDFPaper_eq_zero_of_dead cka prng fs Δcka qep ⟨true, tL, t⟩ rfl
          j k_fs A _ hdead)
        zero_le
    · refine le_trans
        (runLocAtFixedDFPaper_le_runFDFPaper cka prng fs Δcka qep ⟨true, tL, t⟩ j k_fs
          rfl hvg A hs) ?_
      refine le_of_eq (congrArg (fun p => 𝒟[p] {true}) ?_)
      simp only [runFDFPaper, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        bind_assoc, pure_bind]
      rfl
  · have hvg_f : lastLeakGuessAdmissible (2 + Δcka) tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero : 𝒟[localAuthAtFixedDFPaper cka prng fs lam Δcka qep j k_fs tL t A] {true} = 0 := by
      unfold localAuthAtFixedDFPaper
      refine evalDist_bind_eq_zero _ _ fun r hr => ?_
      rcases r with ⟨vs, h⟩
      cases vs with
      | none => simp
      | some vp =>
        rcases vp with ⟨vA, vB⟩
        exact evalDist_runLocAtFixedDFPaper_eq_zero_of_not_validGuess cka prng fs Δcka qep
          ⟨true, tL, t⟩ j k_fs hvg_f A _
    rw [hzero]
    exact zero_le

theorem localAuthAtDFPaper_le_fsWinDFPaper (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFPaper cka prng fs lam Δcka qep j tL t A] {true} ≤
      FSAEAD.advantage fs (redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A) := by
  have hred : redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A =
      (runFSDFPaper cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A >>= fun _ => sampleT Bool) :=
    rfl
  rw [hred, advantage_bind_sampleT_bool]
  refine le_trans (localAuthAtDFPaper_le_localAuthAtFixedDFPaper cka prng fs lam Δcka qep j tL t A)
    ?_
  unfold fsWin
  rw [← OracleComp.evalDist_bind_const ($ᵗ Bool)
        (($ᵗ K : ProbComp K) >>= fun k_fs =>
          localAuthAtFixedDFPaper cka prng fs lam Δcka qep j k_fs tL t A)]
  refine evalDist_bind_mono ($ᵗ Bool) _ _ fun b_fs _ => ?_
  refine evalDist_bind_mono ($ᵗ K) _ _ fun k_fs _ => ?_
  exact localAuthAtFixedDFPaper_le_runFSDFPaper cka prng fs lam Δcka qep j k_fs b_fs tL t A

theorem lemma11_df_paper_proof (tL : Option ℕ) (t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E)
    (hq : MakesAtMostQueriesDF A q) :
    𝒟[PRFPRNG.branch prng true (redPRNGAuthDFPaper cka prng fs lam Δcka qep tL t A)] {true} ≤
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs (redFSAuthDFPaper cka prng fs lam Δcka qep j tL t A) := by
  refine le_trans (branch_redPRNGAuthDFPaper_le_localAuthDFPaper cka prng fs lam Δcka qep tL t A)
    ?_
  refine le_trans (localAuthDFPaper_le_sum_localAuthAtDFPaper cka prng fs lam Δcka qep tL t q A hq)
    ?_
  exact Finset.sum_le_sum fun j _ =>
    localAuthAtDFPaper_le_fsWinDFPaper cka prng fs lam Δcka qep j tL t A

end CryptoGames.SM.Construction.AuthL11
