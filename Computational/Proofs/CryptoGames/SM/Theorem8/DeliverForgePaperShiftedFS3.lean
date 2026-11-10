/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.DeliverForgePaperShiftedFS2
import ProofLib.SepLogic.WP.StateNorm

/-!
# Shifted-Paper Lemma 11 at `Δ = 2`, Part 2

Completes `lemma11_df_shifted_dir2_paper`, coupling `localAuthAtFixedDFShiftedDir2Paper` with
`redFSAuthDFShiftedDir2Paper`.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory OracleComp OracleSpec

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames.SM
open CryptoGames.SM.Engine
open CryptoGames.SM.Construction
open CryptoGames.SM.Construction.AuthL11

section AuthL11ShiftedDir2Paper

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLDFShiftedDir2Paper_q12 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode)
    (q12 : (Party × M × Option CCoins) ⊕ (Party × M × M × Option CCoins))
    (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo
      (.inr (.inl (.inl (.inl (.inl q12))))) esL =
    stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inl (.inl (.inl q12))))) esL := by
  simp only [stepLDFShiftedDir2Paper, stepLDFShiftedPaper,
    implEDFShiftedPaper_q12_congr l (hooksLocal cka prng fs mo)
      (hooksLocal cka prng fs (moAuth mo)) rfl rfl]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLFixedDFShiftedDir2Paper_q12 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (q12 : (Party × M × Option CCoins) ⊕ (Party × M × M × Option CCoins))
    (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs
      (.inr (.inl (.inl (.inl (.inl q12))))) esL =
    stepLFixedDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j k_fs
      (.inr (.inl (.inl (.inl (.inl q12))))) esL := by
  simp only [stepLFixedDFShiftedDir2Paper, stepLFixedDFShiftedPaper,
    implEDFShiftedPaper_q12_congr l (hooksLocalFixed cka prng fs mo j k_fs)
      (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) rfl rfl]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLDFShiftedDir2Paper_corr (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (P : Party) (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo (.inr (.inl (.inr P))) esL =
      stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) (.inr (.inl (.inr P))) esL := by
  simp only [stepLDFShiftedDir2Paper, stepLDFShiftedPaper,
    implEDFShiftedPaper_corr_congr l (hooksLocal cka prng fs mo)
      (hooksLocal cka prng fs (moAuth mo)) rfl]

omit [SampleableType KR] [SampleableType KC] in
theorem stepLFixedDFShiftedDir2Paper_corr (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K) (P : Party)
    (esL : EStateL Γ T Sig SS RS M E K I) :
    stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (.inr (.inl (.inr P))) esL =
      stepLFixedDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j k_fs
        (.inr (.inl (.inr P))) esL := by
  simp only [stepLFixedDFShiftedDir2Paper, stepLFixedDFShiftedPaper,
    implEDFShiftedPaper_corr_congr l (hooksLocalFixed cka prng fs mo j k_fs)
      (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) rfl]

set_option maxHeartbeats 400000 in
theorem shiftLe_stepLDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {j : ℕ} (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} (hle : esL.h.sessions.length ≤ j)
    (hinv : TabSessInv mo esL.h) :
    ShiftLe mo j (fun r => r.2.h)
      (stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q esL)
      (fun k_fs => stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs q esL) := by
  rcases q with n | ((((q12 | q3) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · rw [← shiftLe_moAuth]; simp only [stepLDFShiftedDir2Paper_inl, stepLFixedDFShiftedDir2Paper_inl]
    exact shiftLe_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) (.inl n) hle hinv
  · rw [← shiftLe_moAuth]; simp only [stepLDFShiftedDir2Paper_q12, stepLFixedDFShiftedDir2Paper_q12]
    exact shiftLe_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inl (.inl (.inl q12))))) hle hinv
  · simp only [stepLDFShiftedDir2Paper, stepLFixedDFShiftedDir2Paper, implEDFShiftedPaper_q3_moAuth]
    exact shiftLe_stepL cka prng fs Δcka qep mo (.inr (.inl (.inl (.inr q3)))) hle hinv
  · simp only [stepLDFShiftedDir2Paper, stepLFixedDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, injectEB1, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]; exact ShiftLe.pure mo _ hle hinv
    · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind]
      refine (shiftLe_vRecv cka prng fs mo esL.g P (esL.g.st P) c none hle hinv).post mo _ ?_
      intro a b hb; rcases a with ⟨res_vr, h'⟩; cases res_vr with
      | none =>
        simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
        subst hb; exact ⟨rfl, rfl⟩
      | some res_vr' =>
        cases res_vr' with
        | none =>
          simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
          subst hb; exact ⟨rfl, rfl⟩
        | some val =>
          rcases val with ⟨st', t', i', m'⟩; simp only at hb
          split at hb
          · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          · split at hb
            · simp only [commitE, hooksLocal, run_liftH, StateT.run_bind,
                StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hb
              subst hb; exact ⟨rfl, rfl⟩
            · split at hb
              · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                  simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
                subst hb; exact ⟨rfl, rfl⟩
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩
  · rw [← shiftLe_moAuth]
    simp only [stepLDFShiftedDir2Paper_corr, stepLFixedDFShiftedDir2Paper_corr]
    exact shiftLe_stepLDFShiftedPaper cka prng fs Δcka qep l (moAuth mo)
      (.inr (.inl (.inr P))) hle hinv
  · simp only [stepLDFShiftedDir2Paper, stepLFixedDFShiftedDir2Paper, implEDFShiftedB1,
      QueryImpl.add_apply, deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp only [StateT.run_pure, simulateQ_pure]; exact ShiftLe.pure mo _ hle hinv
    · split
      · simp only [StateT.run_pure, simulateQ_pure]; exact ShiftLe.pure mo _ hle hinv
      · split
        · simp only [StateT.run_pure, simulateQ_pure]; exact ShiftLe.pure mo _ hle hinv
        · simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind]
          refine (shiftLe_vRecv cka prng fs mo esL.g P (esL.g.st P) c' none hle hinv).post mo _ ?_
          intro a b hb; rcases a with ⟨res_vr, h'⟩; cases res_vr with
          | none =>
            simp only [abortE, pure_bind, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
            subst hb; exact ⟨rfl, rfl⟩
          | some res_vr' =>
            cases res_vr' with
            | none =>
              simp only [StateT.run_pure, simulateQ_pure, support_pure,
                Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩
            | some val =>
              rcases val with ⟨st', t', i', m'⟩; simp only at hb
              split at hb
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩
              · split at hb
                · simp only [commitE, hooksLocal, run_liftH, StateT.run_bind,
                    StateT.run_pure, pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hb
                  subst hb; exact ⟨rfl, rfl⟩
                · split at hb
                  · simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hb
                    subst hb; exact ⟨rfl, rfl⟩
                  · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                      Set.mem_singleton_iff] at hb; subst hb; exact ⟨rfl, rfl⟩

theorem evalDist_runLocAtDFShiftedDir2Paper_le_fixed (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) {j : ℕ} (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I}
    (hle : esL.h.sessions.length ≤ j) (hinv : TabSessInv mo esL.h) :
    𝒟[runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j oa esL] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs oa esL] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    simp only [runLocAtDFShiftedDir2Paper_pure, runLocAtFixedDFShiftedDir2Paper_pure,
      OracleComp.evalDist_bind_const, le_rfl]
  | query_bind q k ih =>
    simp only [runLocAtDFShiftedDir2Paper_query_bind, runLocAtFixedDFShiftedDir2Paper_query_bind]
    refine shiftLe_stepLDFShiftedDir2Paper cka prng fs Δcka qep l mo q hle hinv
      (fun r => runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j (k r.1) r.2)
      (fun k_fs r => runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (k r.1) r.2)
      (fun r hlt k_fs => (evalDist_runLocAtDFShiftedDir2Paper_eq_fixed_of_lt cka prng fs Δcka qep l
        mo k_fs (k r.1) hlt).le)
      (fun r hle' hinv' => ih r.1 hle' hinv')

theorem localAuthAtDFShiftedDir2Paper_le_localAuthAtFixedDFShiftedDir2Paper
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (tL : Option ℕ)
    (t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFShiftedDir2Paper cka prng fs lam Δcka qep j l tL t A] {true} ≤
      𝒟[($ᵗ K : ProbComp K) >>= fun k_fs =>
        localAuthAtFixedDFShiftedDir2Paper cka prng fs lam Δcka qep j l k_fs tL t A] {true} := by
  let mo : Mode := ⟨false, tL, t⟩
  dsimp only [localAuthAtDFShiftedDir2Paper, localAuthAtFixedDFShiftedDir2Paper]
  refine shiftLe_initLocal cka prng fs lam mo (Nat.zero_le j) (fun _ _ => rfl)
    (fun r => match r.1 with
      | none => pure false
      | some (vA, vB) => runLocAtDFShiftedDir2Paper cka prng fs Δcka qep l mo j A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    (fun k_fs r => match r.1 with
      | none => pure false
      | some (vA, vB) => runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs A
          { g := { st := fun P => match P with | .A => vA | .B => vB, b := false }, h := r.2 })
    ?_ ?_
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hlt k_fs
    · exact le_rfl
    · exact (evalDist_runLocAtDFShiftedDir2Paper_eq_fixed_of_lt cka prng fs Δcka qep l mo k_fs A
        hlt).le
  · rintro ⟨_ | ⟨vA, vB⟩, h⟩ hle hinv
    · simp
    · exact evalDist_runLocAtDFShiftedDir2Paper_le_fixed cka prng fs Δcka qep l mo A hle hinv

def stepFDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    ProbComp (((SMSpecDF Γ T Sig SS RS M CCoins E).Range q ×
      EStateF Γ T Sig SS RS M E K I) × FSGameState SS RS T M E) :=
  (simulateQ (implFS fs)
    ((implEDFShiftedB1 l (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.tStar (moAuth mo).cfg (moAuth mo).policy q).run esF)).run st

def runFDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) : ProbComp Bool := do
  let r ← (simulateQ (implFS fs)
    ((simulateQ (implEDFShiftedB1 l (hooksFS cka prng fs Δcka mo j)
      (2 + Δcka) qep fs.maxSkip mo.tStar (moAuth mo).cfg (moAuth mo).policy) oa).run esF)).run st
  pure r.2.win

omit [SampleableType KR] [SampleableType KC] in
theorem runFDFShiftedDir2Paper_query_bind (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (k : (SMSpecDF Γ T Sig SS RS M CCoins E).Range q → SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    runFDFShiftedDir2Paper cka prng fs Δcka qep l mo j (liftM (OracleSpec.query q) >>= k) esF st =
      stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j q esF st >>= fun r =>
        runFDFShiftedDir2Paper cka prng fs Δcka qep l mo j (k r.1.1) r.1.2 r.2 := by
  simp [runFDFShiftedDir2Paper, stepFDFShiftedDir2Paper, simulateQ_bind, StateT.run_bind,
    map_eq_bind_pure_comp, bind_assoc]

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runFDFShiftedDir2Paper_eq_one_of_win (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) (hwin : st.win = true) :
    𝒟[runFDFShiftedDir2Paper cka prng fs Δcka qep l mo j oa esF st] {true} = 1 := by
  unfold runFDFShiftedDir2Paper
  refine evalDist_bind_eq_one _ _ fun r hr => ?_
  rw [simulateQ_implFS_preserves_win fs _ st hwin r hr]; simp

set_option maxHeartbeats 400000 in
theorem stepLFixedDFShiftedDir2Paper_preserves_LHSDead (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka (moAuth mo) j esL) :
    ∀ r ∈ support (stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs q esL),
      LHSDead Δcka (moAuth mo) j r.2 := by
  intro r hr
  rcases q with n | ((((q12 | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩)
  · rw [stepLFixedDFShiftedDir2Paper_inl] at hr
    exact stepLFixedDFShiftedPaper_preserves_LHSDead cka prng fs Δcka qep l (moAuth mo) rfl j k_fs
      (.inl n) esL hdead r hr
  · rw [stepLFixedDFShiftedDir2Paper_q12] at hr
    exact stepLFixedDFShiftedPaper_preserves_LHSDead cka prng fs Δcka qep l (moAuth mo) rfl j k_fs
      (.inr (.inl (.inl (.inl (.inl q12))))) esL hdead r hr
  · rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, habw, ↓reduceIte, StateT.run_pure,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · have habw : (esL.abort || esL.g.win) = false := by simp [hab, hwin]
      have hdelWin : ((moAuth mo).cfg : Config M).deliverWin = false := rfl
      simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, deliverE,
        StateT.run_bind, StateT.run_get, pure_bind, habw, Bool.false_eq_true, ↓reduceIte, hdelWin,
        Bool.false_and] at hr
      cases hint : esL.g.inTransit P.other c with
      | none =>
        simp only [hint, StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      | some rec =>
        simp only [hint, run_liftH, StateT.run_bind, simulateQ_bind, pure_bind,
          bind_assoc, MonadAttach.mem_support_bind] at hr
        obtain ⟨out, hout, hr⟩ := hr
        cases hout1 : out.1 with
        | none =>
          rw [hout1] at hr
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact LHSDead.of_abort Δcka (moAuth mo) j rfl
        | some o1 =>
          cases o1 with
          | none =>
            rw [hout1] at hr
            simp only [StateT.run_pure, simulateQ_pure,
              support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
          | some val =>
            rcases val with ⟨vp', t', i', m'⟩; rw [hout1] at hr
            simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind, StateT.run_pure,
              pure_bind, StateT.run_modify,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr
            obtain ⟨hid', hR', _⟩ :=
              vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                c (some rec) esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
            refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
            · by_cases hQP : Q = P
              · subst hQP; simp [Function.update_self, hid']
              · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
            · unfold RWrongSession at hR ⊢
              by_cases hRP : Party.receiverOf (moAuth mo).tStar = P
              · simp only [hRP, Function.update_self]; exact hR' hRP.symm
              · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]; exact hR
  · rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, injectEB1,
        StateT.run_bind, StateT.run_get, pure_bind, habw, Bool.true_or, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · have hinjFull : ((moAuth mo).cfg : Config M).injectFull = fun t => t == mo.tStar := rfl
      simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply, injectEB1,
        StateT.run_bind, StateT.run_get, pure_bind, hab, hwin, Bool.false_or] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      · simp only [run_liftH, StateT.run_bind, simulateQ_bind, pure_bind,
          bind_assoc, MonadAttach.mem_support_bind] at hr
        obtain ⟨out, hout, hr⟩ := hr
        cases hout1 : out.1 with
        | none =>
          rw [hout1] at hr
          simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
            simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact LHSDead.of_abort Δcka (moAuth mo) j rfl
        | some o1 =>
          cases o1 with
          | none =>
            rw [hout1] at hr
            simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
          | some val =>
            rcases val with ⟨vp', t', i', m'⟩; rw [hout1] at hr; simp only at hr
            obtain ⟨hid', hR', hlast⟩ :=
              vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                c none esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
            split at hr
            · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
            · split at hr
              · simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind, StateT.run_pure,
                  pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr
                subst hr
                refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
                · by_cases hQP : Q = P
                  · subst hQP; simp [Function.update_self, hid']
                  · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
                · unfold RWrongSession at hR ⊢
                  by_cases hRP : Party.receiverOf (moAuth mo).tStar = P
                  · simp only [hRP, Function.update_self]; exact hR' hRP.symm
                  · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]
                    exact hR
              · simp only [hinjFull] at hr
                by_cases ht_eq : (t' == mo.tStar) = true
                · simp only [ht_eq, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                    StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr
                  exact LHSDead.of_win_ne Δcka (moAuth mo) j rfl (hlast (beq_iff_eq.mp ht_eq))
                · simp only [ht_eq, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                    simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                  subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
  · rw [stepLFixedDFShiftedDir2Paper_corr] at hr
    exact stepLFixedDFShiftedPaper_preserves_LHSDead cka prng fs Δcka qep l (moAuth mo) rfl j k_fs
      (.inr (.inl (.inr P))) esL hdead r hr
  · rcases hdead with ⟨habw, hout⟩ | ⟨hab, hwin, hid, hR⟩
    · simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply,
        deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind, habw, ↓reduceIte,
        StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr; exact Or.inl ⟨habw, hout⟩
    · have hinjFull : ((moAuth mo).cfg : Config M).injectFull = fun t => t == mo.tStar := rfl
      simp only [stepLFixedDFShiftedDir2Paper, implEDFShiftedB1, QueryImpl.add_apply,
        deliverForgeEB1, StateT.run_bind, StateT.run_get, pure_bind, hab, hwin, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte] at hr
      split at hr
      · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
        subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
      · split at hr
        · simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
          subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
        · simp only [run_liftH, StateT.run_bind, simulateQ_bind, pure_bind,
            bind_assoc, MonadAttach.mem_support_bind] at hr
          obtain ⟨out, hout, hr⟩ := hr
          cases hout1 : out.1 with
          | none =>
            rw [hout1] at hr
            simp only [abortE, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
              simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
            subst hr; exact LHSDead.of_abort Δcka (moAuth mo) j rfl
          | some o1 =>
            cases o1 with
            | none =>
              rw [hout1] at hr
              simp only [StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
              subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
            | some val =>
              rcases val with ⟨vp', t', i', m'⟩; rw [hout1] at hr; simp only at hr
              obtain ⟨hid', hR', hlast⟩ :=
                vRecv_LFixed_preserves_RWrongSession cka prng fs mo j k_fs esL.g P (esL.g.st P)
                  c' none esL.h (hid P) (fun hPR => hPR ▸ hR) out hout vp' t' i' m' hout1
              split at hr
              · simp only [StateT.run_pure, simulateQ_pure, support_pure,
                  Set.mem_singleton_iff] at hr; subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩
              · split at hr
                · simp only [commitE, hooksLocalFixed, run_liftH, StateT.run_bind, StateT.run_pure,
                    pure_bind, StateT.run_modify, simulateQ_pure, support_pure,
                    Set.mem_singleton_iff] at hr
                  subst hr
                  refine Or.inr ⟨hab, hwin, fun Q => ?_, ?_⟩
                  · by_cases hQP : Q = P
                    · subst hQP; simp [Function.update_self, hid']
                    · simp [GameState.accept, GameState.delete, Function.update_of_ne hQP, hid]
                  · unfold RWrongSession at hR ⊢
                    by_cases hRP : Party.receiverOf (moAuth mo).tStar = P
                    · simp only [hRP, Function.update_self]; exact hR' hRP.symm
                    · simp only [GameState.accept, GameState.delete, Function.update_of_ne hRP]
                      exact hR
                · simp only [hinjFull] at hr
                  by_cases ht_eq : (t' == mo.tStar) = true
                  · simp only [ht_eq, ↓reduceIte, StateT.run_bind, StateT.run_modify, pure_bind,
                      StateT.run_pure, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr
                    exact LHSDead.of_win_ne Δcka (moAuth mo) j rfl (hlast (beq_iff_eq.mp ht_eq))
                  · simp only [ht_eq, Bool.false_eq_true, ↓reduceIte, StateT.run_pure,
                      simulateQ_pure, support_pure, Set.mem_singleton_iff] at hr
                    subst hr; exact Or.inr ⟨hab, hwin, hid, hR⟩

theorem evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_dead (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    (esL : EStateL Γ T Sig SS RS M E K I) (hdead : LHSDead Δcka (moAuth mo) j esL) :
    𝒟[runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs oa esL] {true} = 0 := by
  induction oa using OracleComp.inductionOn generalizing esL with
  | pure b' =>
    rw [runLocAtFixedDFShiftedDir2Paper_pure]
    rcases hdead with ⟨_, hout⟩ | ⟨_, hwin, _, _⟩
    · simp [hout]
    · simp [authOut, hwin]
  | query_bind q k ih =>
    rw [runLocAtFixedDFShiftedDir2Paper_query_bind]
    exact evalDist_bind_eq_zero _ _ fun r hr => ih r.1 r.2
      (stepLFixedDFShiftedDir2Paper_preserves_LHSDead cka prng fs Δcka qep l mo j k_fs q esL
        hdead r hr)

omit [SampleableType KR] [SampleableType KC] in
theorem evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_not_validGuess
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = false)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool) (esL : EStateL Γ T Sig SS RS M E K I) :
    𝒟[runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs oa esL] {true} = 0 := by
  unfold runLocAtFixedDFShiftedDir2Paper
  refine evalDist_bind_eq_zero _ _ fun r _ => ?_
  have h : authOut (2 + Δcka) (moAuth mo).policy r.2 = false := by
    simp [authOut, Mode.policy, authLosingConditionsAvoided, hvg]
  simp [h]

omit [SampleableType KR] [SampleableType KC] in
theorem stepFDFShiftedDir2Paper_inl (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j n : ℕ)
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j (.inl n) esF st =
      stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j (.inl n) esF st := by
  simp only [stepFDFShiftedDir2Paper, stepFDFShiftedPaper, implEDFShiftedB1, implEDFShiftedPaper,
    QueryImpl.add_apply]

omit [SampleableType KR] [SampleableType KC] in
theorem stepFDFShiftedDir2Paper_q12 (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ)
    (q12 : (Party × M × Option CCoins) ⊕ (Party × M × M × Option CCoins))
    (esF : EStateF Γ T Sig SS RS M E K I) (st : FSGameState SS RS T M E) :
    stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j
      (.inr (.inl (.inl (.inl (.inl q12))))) esF st =
    stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j
      (.inr (.inl (.inl (.inl (.inl q12))))) esF st := by
  simp only [stepFDFShiftedDir2Paper, stepFDFShiftedPaper,
    implEDFShiftedPaper_q12_congr l (hooksFS cka prng fs Δcka mo j)
      (hooksFS cka prng fs Δcka (moAuth mo) j) rfl rfl]

omit [DecidableEq M] [Inhabited E] [SampleableType KR] [SampleableType KC] in
theorem hooksFS_reveal_eq_moAuth_of_vR_ne_some_none (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka : ℕ) (mo : Mode) (j : ℕ)
    (g : GameState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E))
    (P : Party) (vp : PartyState Γ T Sig (Option SS) (Option RS))
    (hvR : vp.vR mo.tStar ≠ some none) :
    (hooksFS cka prng fs Δcka mo j).reveal g P vp =
      (hooksFS cka prng fs Δcka (moAuth mo) j).reveal g P vp := by
  unfold hooksFS moAuth
  dsimp only
  cases h : vp.vR mo.tStar with
  | none => rfl
  | some val =>
    cases val with
    | none => exact False.elim (hvR h)
    | some rs => rfl

omit [SampleableType KR] [SampleableType KC] in
theorem stepFDFShiftedDir2Paper_corr (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep l : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true) (P : Party)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j (.inr (.inl (.inr P))) esF st =
      stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j (.inr (.inl (.inr P))) esF st := by
  simp only [stepFDFShiftedDir2Paper, stepFDFShiftedPaper, implEDFShiftedB1, implEDFShiftedPaper,
    QueryImpl.add_apply, corrEShiftedPaper, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · split
    · rfl
    · rename_i hnot_ab hnot_doom
      have hvR : (esF.g.st P).vR mo.tStar ≠ some none := by
        intro hvR_eq
        have hc := (syncLFS_corrDoom_true_of_vR_eq_some_none fs Δcka qep (moAuth mo) j k_fs
          hvg P hs hvR_eq).2.2
        change (moAuth mo).policy.corrDoom esF.g P = true at hc
        simp [hc] at hnot_doom
      rw [hooksFS_reveal_eq_moAuth_of_vR_ne_some_none cka prng fs Δcka mo j esF.g P
        (esF.g.st P) hvR]

set_option maxHeartbeats 400000 in
theorem leComp_deliverE_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (q : Party × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep (moAuth mo) j k_fs)
      (simulateQ lImpl
        ((deliverE (hooksLocalFixed cka prng fs mo j k_fs) fs.maxSkip (moAuth mo).cfg q).run esL))
      ((simulateQ (implFS fs)
        ((deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip (moAuth mo).cfg q).run
          esF)).run st) := by
  rcases q with ⟨P, c⟩
  unfold deliverE
  simp only [StateT.run_bind, StateT.run_get, pure_bind,
    hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hin_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  rw [hin_eq]
  cases hin : esL.g.inTransit P.other c with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | some r =>
    obtain ⟨hmem, hct, hpos_eq, hPother_s, hP_recv, hsends_f⟩ :=
      inTransit_some_props fs Δcka qep (moAuth mo) hs P c r hin
    have hdelWin : ((moAuth mo).cfg (M := M)).deliverWin = false := rfl
    have hcondL_eq :
        ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidL P, hsends_f, Bool.false_or]
    have hcondF_eq :
        ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) =
          decide ((esL.g.st P).tcur + 1 < c.1.1) := by
      rw [hs.hidF P, ← hs.htcur P, hsends_f, Bool.false_or]
    by_cases hgt : (esL.g.st P).tcur + 1 < c.1.1
    · have hcondL :
          ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondL_eq, decide_eq_true_eq]; exact hgt
      have hcondF :
          ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = true := by
        rw [hcondF_eq, decide_eq_true_eq]; exact hgt
      dsimp only [vRecv]
      simp only [hcondL, hcondF, ↓reduceIte, StateT.run_bind, run_liftH, StateT.run_pure,
        pure_bind, hdelWin, Bool.false_and, Bool.false_eq_true, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := Nat.le_of_not_lt hgt
      have hcondL :
          ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondL_eq, decide_eq_false_iff_not]; exact hgt
      have hcondF :
          ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = false := by
        rw [hcondF_eq, decide_eq_false_iff_not]; exact hgt
      by_cases heq : c.1.1 = (esL.g.st P).tcur + 1
      · have heqF : c.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
        have hpos_c : 0 < c.1.1 := by omega
        obtain ⟨hepoch_r, _, _, hcache_r, _⟩ := hs.htrans_wf r hmem
        have hepoch_c : r.pos.epoch = c.1.1 := by rw [hepoch_r, hct]
        obtain ⟨Tc, σc, k_c, idx_c, hcache_c, hct1⟩ := hcache_r (hepoch_c ▸ hpos_c)
        have hTn : c.1.2 = some Tc := by
          have : c.1 = (r.pos.epoch, some Tc) := by rw [← hct, hct1]
          rw [this]
        have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
          esL.g P (esL.g.st P) c (some r) Tc hcondL heq hTn
        have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
          esF.g P (esF.g.st P) c (some r) Tc hcondF heqF hTn
        simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind]
        rw [← hs.hγ P, ← hs.hroot P]
        refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c.1.1
          (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
        intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
        rw [hr_st]
        rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
          ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
        · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE, simulateQ_pure]
          exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka (moAuth mo) j _))
        · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind,
            hdelWin, Bool.false_and, Bool.false_eq_true, ↓reduceIte, simulateQ_pure]
          exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
            syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
              (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
        · simp only [hL_some, hF_some]
          have horigin_cache : ∃ σc', esL.h.cache c.1.1 = some (Tc, σc', kL, idx?) ∧
              σ' = σc' ∧ rL.2.sessions = esL.h.sessions := by
            rcases h_origin with h1 | ⟨_, _, hno_c, _⟩
            · exact h1
            · exfalso; exact hno_c Tc σc k_c idx_c (hepoch_c ▸ hcache_c) rfl
          obtain ⟨σc', hcache_c', hσ', hr_sess⟩ := horigin_cache
          have hs₁ : SyncLFS fs Δcka qep (moAuth mo) j k_fs
              { esL with h := rL.2 } { esF with h := rF.1.2 } st :=
            syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
              (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc
          let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
            { esL.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                              vR := Function.update (esL.g.st P).vR c.1.1
                                (some (fs.initReceiver kL, idx?)) }
          let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
            { esF.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                              vR := Function.update (esF.g.st P).vR c.1.1
                                (some (if ext then none else some (fs.initReceiver kF))) }
          have hvR_c :
              (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
              (∃ rs idx₀, s₁L.vR c.1.1 = some (rs, idx₀) ∧
                s₁F.vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c.1.1 = (moAuth mo).tStar ∧ SenderIsJ (moAuth mo) j { esL with h := rL.2 } ∧
                s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none) := by
            by_cases hj : idx? = some j
            · obtain ⟨hkL, ht_star⟩ := h_eq_j hj; right; right
              have hsJ : SenderIsJ mo j { esL with h := rL.2 } :=
                Or.inr ⟨Tc, σc', kL, by dsimp only; rw [hr_cL, ← ht_star, ← hj]; exact hcache_c'⟩
              have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                rw [← ht_star, ← hP_recv]; omega
              have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                (hs.hvR_target_lt hlt_tstar).2.2
              have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
              refine ⟨ht_star, hsJ, ?_, ?_⟩
              · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
              · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
            · right; left
              have hkL : kL = kF := h_ne_j hj
              have hext_false : ext = false := by rw [hext_eq, beq_eq_false_iff_ne]; exact hj
              refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
              · dsimp only [s₁L]; rw [Function.update_self]
              · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
          convert leComp_deliverTail cka prng fs Δcka qep (moAuth mo) j k_fs rfl P c r hs₁ hin
            ht_le s₁L s₁F (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
            (by dsimp only [s₁L]; omega) (by dsimp only [s₁F]; have := hs.htcur P; omega) rfl rfl
            (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                            by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
            hvR_c using 1
          · dsimp only [deliverTail, s₁L]
            simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
              simulateQ_pure]; rfl
          · dsimp only [deliverTail, s₁F]
            simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]; rfl
      · have heqF : c.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
        have ht_le_cur : c.1.1 ≤ (esL.g.st P).tcur := by omega
        have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
          esL.g P (esL.g.st P) c (some r) hcondL heq
        have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
          esF.g P (esF.g.st P) c (some r) hcondF heqF
        have hvR_c :
            ((esL.g.st P).vR c.1.1 = none ∧ (esF.g.st P).vR c.1.1 = none) ∨
            (∃ rs idx₀, (esL.g.st P).vR c.1.1 = some (rs, idx₀) ∧
              (esF.g.st P).vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
            (c.1.1 = (moAuth mo).tStar ∧ SenderIsJ (moAuth mo) j esL ∧
              (esL.g.st P).vR c.1.1 = some (st.receiverState, some j) ∧
              (esF.g.st P).vR c.1.1 = some none) := by
          by_cases ht_star : c.1.1 = mo.tStar
          · right; right
            have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
            have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
              rw [← hP_tstar, ← ht_star]; exact ht_le_cur
            obtain ⟨hsJ, h1, h2⟩ := hs.hvR_target_ge hge
            exact ⟨ht_star, hsJ, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
          · rcases hs.hvR_other P c.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
        convert leComp_deliverTail cka prng fs Δcka qep (moAuth mo) j k_fs rfl P c r hs hin ht_le
          (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P) (hs.hroot P) rfl rfl
          (by omega) (by have := hs.htcur P; omega) rfl rfl (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
        · dsimp only [deliverTail]; simp only [hvRecvL, StateT.run_bind]; congr 2
        · dsimp only [deliverTail]; simp only [hvRecvF, StateT.run_bind]; congr 3

def injectTailB1 {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (qep : ℕ) (mo : Mode)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c : Header T × E) (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    match ← liftH (vRecvTail hk s P s₁ c none) with
    | none =>
      abortE
      return none
    | some none => return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' then return some RecvResult.rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if trivB1 mo.tStar s pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₂ =>
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := s₂ }
          return some (RecvResult.accepted t' i' (some m'))
      else
        if (mo.cfg (M := M)).injectFull t' then
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := { es.g with win := true } }
        return some RecvResult.rejected).run es

def deliverForgeTailB1 {ι : Type} {tspec : OracleSpec.{0, 0} ι} {Γv Sv SSv RSv HS : Type}
    (qep : ℕ) (mo : Mode)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c' : Header T × E) (r : Record M (Header T × E))
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    TComp tspec (Option (RecvResult M) × EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :=
  (do
    let s := es.g
    match ← liftH (vRecvTail hk s P s₁ c' none) with
    | none =>
      abortE
      return none
    | some none => return some RecvResult.rejected
    | some (some (st', t', i', m')) =>
      if qep + 1 < t' || t' != r.pos.epoch then return some RecvResult.rejected
      let pos : Pos := ⟨P.other, t', i'⟩
      if trivB1 mo.tStar s pos then
        match ← commitE hk s P (s.st P) st' pos with
        | none => return none
        | some s₂ =>
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := s₂ }
          return some (RecvResult.accepted t' i' (some m'))
      else
        if (mo.cfg (M := M)).injectFull t' then
          modify fun (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) =>
            { es with g := { es.g with win := true } }
        return some RecvResult.rejected).run es

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem deliverForgeTailB1_eq_injectTailB1 {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv Sv SSv RSv HS : Type} (qep : ℕ) (mo : Mode)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c' : Header T × E) (r : Record M (Header T × E))
    (hr_ep : r.pos.epoch = c'.1.1)
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    deliverForgeTailB1 qep mo hk P c' r s₁ es =
      injectTailB1 qep mo hk P c' s₁ es := by
  dsimp only [deliverForgeTailB1, injectTailB1, vRecvTail]
  cases s₁.vR c'.1.1 with
  | none => rfl
  | some v =>
    simp only [StateT.run_bind, run_liftH, bind_assoc]
    congr 1; funext ⟨res, h'⟩
    cases res with
    | none => rfl
    | some res' =>
      cases res' with
      | none => rfl
      | some val =>
        rcases val with ⟨v', i, m⟩
        have hne_ep : (c'.1.1 != r.pos.epoch) = false := by simp [hr_ep]
        by_cases hqep : qep + 1 < c'.1.1 <;>
          simp only [StateT.run_pure, pure_bind, hne_ep, Bool.or_false, hqep, decide_true,
            decide_false, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K] in
theorem injectTailB1_eq_injectTailDF {ι : Type} {tspec : OracleSpec.{0, 0} ι}
    {Γv Sv SSv RSv HS : Type} (qep : ℕ) (mo : Mode)
    (hk : Hooks tspec HS Γ T Sig SS RS M E CCoins Γv Sv SSv RSv)
    (P : Party) (c' : Header T × E) (ht_star : c'.1.1 = mo.tStar)
    (s₁ : VP Γv T Sv SSv RSv)
    (es : EState (VP Γv T Sv SSv RSv) M (Header T × E) HS) :
    injectTailB1 qep mo hk P c' s₁ es =
      injectTailDF 0 qep mo hk P c' s₁ es := by
  dsimp only [injectTailB1, injectTailDF, vRecvTail]
  cases s₁.vR c'.1.1 with
  | none => rfl
  | some v =>
    simp only [StateT.run_bind, run_liftH, bind_assoc]
    congr 1; funext ⟨res, h'⟩
    cases res with
    | none => rfl
    | some res' =>
      cases res' with
      | none => rfl
      | some val =>
        rcases val with ⟨v', i, m⟩
        have htriv : trivB1 mo.tStar es.g ⟨P.other, c'.1.1, i⟩ =
            es.g.trivial (2 + 0) ⟨P.other, c'.1.1, i⟩ :=
          trivB1_self_epoch mo.tStar es.g ⟨P.other, c'.1.1, i⟩ ht_star
        by_cases hqep : qep + 1 < c'.1.1
        · simp only [StateT.run_pure, pure_bind, hqep, ↓reduceIte]
        · simp only [StateT.run_pure, pure_bind, hqep, ↓reduceIte, htriv]
          by_cases htr : es.g.trivial (2 + 0) ⟨P.other, c'.1.1, i⟩ = true
          · dsimp only [commitE]
            simp only [htr, ↓reduceIte, StateT.run_bind, run_liftH, bind_assoc]
            congr 1
          · simp only [htr, Bool.false_eq_true, ↓reduceIte]

omit [SampleableType KR] [SampleableType KC] in
theorem leComp_injectTailB1 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hauth : mo.auth = true) (hΔ : Δcka = 0)
    (P : Party) (c' : Header T × E)
    {esL : EStateL Γ T Sig SS RS M E K I}
    {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E}
    (hs : SyncLFS fs Δcka qep mo j k_fs esL esF st)
    (hin : esL.g.inTransit P.other c' = none)
    (hsends_f : P.sendsIn c'.1.1 = false)
    (ht_le : c'.1.1 ≤ (esL.g.st P).tcur + 1)
    (s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ))
    (s₁F : VP Γ T Sig (Option SS) (Option RS))
    (hidL' : s₁L.id = P) (hidF' : s₁F.id = P)
    (hγ' : s₁L.γ = s₁F.γ) (hroot' : s₁L.root = s₁F.root)
    (hTcurL' : s₁L.curCkaMsg = (esL.g.st P).curCkaMsg) (hTcurF' : s₁F.curCkaMsg = (esF.g.st P).curCkaMsg)
    (htcurL' : s₁L.tcur = max (esL.g.st P).tcur c'.1.1)
    (htcurF' : s₁F.tcur = max (esF.g.st P).tcur c'.1.1)
    (hvSL' : s₁L.vS = (esL.g.st P).vS) (hvSF' : s₁F.vS = (esF.g.st P).vS)
    (hvR_other' : ∀ t', t' ≠ c'.1.1 →
      s₁L.vR t' = (esL.g.st P).vR t' ∧ s₁F.vR t' = (esF.g.st P).vR t')
    (hvR_c :
      (s₁L.vR c'.1.1 = none ∧ s₁F.vR c'.1.1 = none) ∨
      (∃ rs idx?, s₁L.vR c'.1.1 = some (rs, idx?) ∧
        s₁F.vR c'.1.1 = some (some rs) ∧ idx? ≠ some j) ∨
      (c'.1.1 = mo.tStar ∧
        s₁L.vR c'.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c'.1.1 = some none)) :
    LeComp (StepRelFS fs Δcka qep mo j k_fs)
      (simulateQ lImpl
        (injectTailB1 qep mo (hooksLocalFixed cka prng fs mo j k_fs) P c' s₁L esL))
      ((simulateQ (implFS fs)
        (injectTailB1 qep mo (hooksFS cka prng fs Δcka mo j) P c' s₁F esF)).run st) := by
  subst hΔ
  have hPother_s : P.other = Party.senderOf c'.1.1 := by
    have hother_sends : P.other.sendsIn c'.1.1 = true := by
      cases P <;> cases h : Nat.beq (c'.1.1 % 2) 1 <;> simp_all [Party.other, Party.sendsIn]
    exact eq_senderOf_of_sendsIn hother_sends
  have hP_recv : P = Party.receiverOf c'.1.1 := by
    unfold Party.receiverOf; rw [← hPother_s]; cases P <;> rfl
  have hvRL_upd : ∀ v, Function.update s₁L.vR c'.1.1 v =
      Function.update (esL.g.st P).vR c'.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c'.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').1]
  have hvRF_upd : ∀ v, Function.update s₁F.vR c'.1.1 v =
      Function.update (esF.g.st P).vR c'.1.1 v := by
    intro v; funext t'
    by_cases ht' : t' = c'.1.1
    · subst t'; simp
    · simp [Function.update_of_ne ht', (hvR_other' t' ht').2]
  rcases hvR_c with ⟨hnoneL, hnoneF⟩ | ⟨rs, idx?, hsomeL, hsomeF, hidx_ne⟩ |
      ⟨ht_star, hsomeL, hsomeF⟩
  · dsimp only [injectTailB1, vRecvTail]
    simp only [StateT.run_bind, StateT.run_pure, pure_bind, run_liftH,
      hnoneL, hnoneF, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  · dsimp only [injectTailB1, vRecvTail, hooksLocalFixed, hooksFS]
    simp only [StateT.run_bind, pure_bind, run_liftH, hsomeL, hsomeF]
    cases hrcv : fs.receive rs c'.1 c'.2 with
    | none =>
      simp only [Option.map_none, StateT.run_pure, pure_bind, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    | some val =>
      rcases val with ⟨rs', i', m'⟩
      have hs_book : SyncLFS fs 0 qep mo j k_fs
          { esL with h := { esL.h with lastIdx := idx? } } esF st :=
        syncLFS_with_book fs 0 qep mo j k_fs hs { esL.h with lastIdx := idx? } esF.h
          hs.hbs rfl (fun _ _ => rfl) rfl rfl rfl rfl
      by_cases hqep : qep + 1 < c'.1.1
      · simp only [Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
          pure_bind, hqep, ↓reduceIte, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs_book⟩))
      · have htriv_eq : trivB1 mo.tStar esF.g ⟨P.other, c'.1.1, i'⟩ =
            trivB1 mo.tStar esL.g ⟨P.other, c'.1.1, i'⟩ := by
          unfold trivB1 GameState.trivial
          rw [← hs.hcomp, ← hs.htrans, ← hs.htL, ← hs.hepoch]
        by_cases htriv : trivB1 mo.tStar esL.g ⟨P.other, c'.1.1, i'⟩ = true
        · have htrivF : trivB1 mo.tStar esF.g ⟨P.other, c'.1.1, i'⟩ = true :=
            htriv_eq.trans htriv
          dsimp only [commitE, hooksLocalFixed, hooksFS]
          simp only [Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
            pure_bind, run_liftH, accept_update_self, hqep, ↓reduceIte, htriv, htrivF,
            simulateQ_pure]
          by_cases ht_star : c'.1.1 = mo.tStar
          · refine LeComp.pure (Or.inl (Or.inr ⟨hs.habortL, hs.hwinL, ?_, ?_⟩))
            · intro Q
              simp only [GameState.accept, GameState.delete]
              by_cases hQ : Q = P
              · subst Q; rw [Function.update_self]; exact hidL'
              · rw [Function.update_of_ne hQ]; exact hs.hidL Q
            · dsimp only [RWrongSession]
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              simp only [GameState.accept, GameState.delete, ← hP_tstar, Function.update_self,
                htcurL', ht_star, Nat.le_max_right, true_and]
              intro rs₀ hrs₀
              injection hrs₀ with hpair; injection hpair with _ hidx_eq
              exact hidx_ne hidx_eq
          · refine LeComp.pure (Or.inr (Or.inr ⟨rfl, ?_⟩))
            exact syncLFS_accept_local fs 0 qep mo j k_fs P c'.1.1 i' rs' idx? hs
              hsends_f ht_le ht_star hidx_ne
              { s₁L with vR := Function.update s₁L.vR c'.1.1 (some (rs', idx?)) }
              { s₁F with vR := Function.update s₁F.vR c'.1.1 (some (some rs')) }
              hidL' hidF' hγ' hroot' hTcurL' hTcurF'
              htcurL' htcurF' hvSL' hvSF'
              (hvRL_upd _) (hvRF_upd _)
        · have htrivL_f : trivB1 mo.tStar esL.g ⟨P.other, c'.1.1, i'⟩ = false :=
            Bool.eq_false_iff.mpr htriv
          have htrivF_f : trivB1 mo.tStar esF.g ⟨P.other, c'.1.1, i'⟩ = false :=
            htriv_eq.trans htrivL_f
          by_cases hinjFull : (mo.cfg (M := M)).injectFull c'.1.1 = true
          · simp only [Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull,
              simulateQ_pure]
            exact LeComp.pure (Or.inl (LHSDead.of_win_ne 0 mo j rfl hidx_ne))
          · have hinjFull_f : (mo.cfg (M := M)).injectFull c'.1.1 = false :=
              Bool.eq_false_iff.mpr hinjFull
            simp only [Option.map_some, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, hqep, ↓reduceIte, htrivL_f, htrivF_f, Bool.false_eq_true, hinjFull_f,
              simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs_book⟩))
  · rw [injectTailB1_eq_injectTailDF qep mo _ P c' ht_star,
      injectTailB1_eq_injectTailDF qep mo _ P c' ht_star]
    exact leComp_deliverForgeTail cka prng fs 0 qep mo j k_fs hauth P c' hs hin hsends_f ht_le
      s₁L s₁F hidL' hidF' hγ' hroot' hTcurL' hTcurF' htcurL' htcurF' hvSL' hvSF' hvR_other'
      (Or.inr (Or.inr ⟨ht_star, hsomeL, hsomeF⟩))

set_option maxHeartbeats 400000 in
theorem leComp_injectE_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hΔ : Δcka = 0) (q : Party × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep (moAuth mo) j k_fs)
      (simulateQ lImpl
        ((injectEB1 (hooksLocalFixed cka prng fs mo j k_fs) qep mo.tStar (moAuth mo).cfg q).run
          esL))
      ((simulateQ (implFS fs)
        ((injectEB1 (hooksFS cka prng fs Δcka mo j) qep mo.tStar (moAuth mo).cfg q).run
          esF)).run st) := by
  rcases q with ⟨P, c⟩
  unfold injectEB1
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or]
  have hin_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  have hsafe_eq : esF.g.safeInj 2 = esL.g.safeInj 2 := by
    simp only [GameState.safeInj, hs.htL, hs.hepoch]
  rw [hin_eq, hsafe_eq]
  cases hin : esL.g.inTransit P.other c with
  | some r =>
    simp only [Option.isSome_some, Bool.true_or, ↓reduceIte, StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | none =>
    simp only [Option.isSome_none, Bool.false_or]
    by_cases hsafe : esL.g.safeInj 2 = true
    · simp only [hsafe, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hcond_eq :
          ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) =
            ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) := by
        rw [hs.hidF P, hs.hidL P, ← hs.htcur P]
      by_cases hcondL :
          ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = true
      · have hcondF :
            ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = true :=
          hcond_eq.trans hcondL
        dsimp only [vRecv]
        simp only [hcondL, hcondF, ↓reduceIte, StateT.run_bind, run_liftH, StateT.run_pure,
          pure_bind, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
      · have hcondL_f :
            ((esL.g.st P).id.sendsIn c.1.1 || decide ((esL.g.st P).tcur + 1 < c.1.1)) = false :=
          Bool.eq_false_iff.mpr hcondL
        have hcondF_f :
            ((esF.g.st P).id.sendsIn c.1.1 || decide ((esF.g.st P).tcur + 1 < c.1.1)) = false :=
          hcond_eq.trans hcondL_f
        have hsends_f : P.sendsIn c.1.1 = false := by
          have h := hcondL_f; rw [hs.hidL P, Bool.or_eq_false_iff] at h; exact h.1
        have ht_le : c.1.1 ≤ (esL.g.st P).tcur + 1 := by
          have h := hcondL_f; rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h; omega
        have hPother_s : P.other = Party.senderOf c.1.1 := by
          have hother_sends : P.other.sendsIn c.1.1 = true := by
            cases P <;> cases h : Nat.beq (c.1.1 % 2) 1 <;> simp_all [Party.other, Party.sendsIn]
          exact eq_senderOf_of_sendsIn hother_sends
        have hP_recv : P = Party.receiverOf c.1.1 := by
          unfold Party.receiverOf; rw [← hPother_s]; cases P <;> rfl
        by_cases heq : c.1.1 = (esL.g.st P).tcur + 1
        · have heqF : c.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          cases hTn : c.1.2 with
          | none =>
            have hvL : vRecv (hooksLocalFixed cka prng fs mo j k_fs) esL.g P (esL.g.st P) c none =
                pure (some none) := by simp [vRecv, heq, hTn]
            have hvF : vRecv (hooksFS cka prng fs Δcka mo j) esF.g P (esF.g.st P) c none =
                pure (some none) := by simp [vRecv, heqF, hTn]
            simp only [hvL, hvF, run_liftH, StateT.run_bind, StateT.run_pure, pure_bind,
              simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
          | some Tc =>
            have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
              esL.g P (esL.g.st P) c none Tc hcondL_f heq hTn
            have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
              esF.g P (esF.g.st P) c none Tc hcondF_f heqF hTn
            simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind]
            rw [← hs.hγ P, ← hs.hroot P]
            refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c.1.1
              (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
            intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
            rw [hr_st]
            rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
              ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
            · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE, simulateQ_pure]
              exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka (moAuth mo) j _))
            · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
                syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
                  (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
            · simp only [hL_some, hF_some]
              have hs₁ : SyncLFS fs Δcka qep (moAuth mo) j k_fs
                  { esL with h := rL.2 } { esF with h := rF.1.2 } st := by
                refine syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs
                  hr_cL ?_ hr_ex hr_cnt hr_tr hr_sc
                intro h1 h2
                rcases h_origin with ⟨_, _, _, hsess⟩ | ⟨_, hnot, _, _⟩
                · exact hsess
                · exact absurd ⟨h1, h2⟩ hnot
              let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
                { esL.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                                  vR := Function.update (esL.g.st P).vR c.1.1
                                    (some (fs.initReceiver kL, idx?)) }
              let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
                { esF.g.st P with tcur := c.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                                  vR := Function.update (esF.g.st P).vR c.1.1
                                    (some (if ext then none else some (fs.initReceiver kF))) }
              have hvR_c :
                  (s₁L.vR c.1.1 = none ∧ s₁F.vR c.1.1 = none) ∨
                  (∃ rs idx₀, s₁L.vR c.1.1 = some (rs, idx₀) ∧
                    s₁F.vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
                  (c.1.1 = (moAuth mo).tStar ∧
                    s₁L.vR c.1.1 = some (st.receiverState, some j) ∧ s₁F.vR c.1.1 = some none) := by
                by_cases hj : idx? = some j
                · obtain ⟨hkL, ht_star⟩ := h_eq_j hj; right; right
                  have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                    rw [← ht_star, ← hP_recv]; omega
                  have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                    (hs.hvR_target_lt hlt_tstar).2.2
                  have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
                  refine ⟨ht_star, ?_, ?_⟩
                  · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
                · right; left
                  have hkL : kL = kF := h_ne_j hj
                  have hext_false : ext = false := by rw [hext_eq, beq_eq_false_iff_ne]; exact hj
                  refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
                  · dsimp only [s₁L]; rw [Function.update_self]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
              convert leComp_injectTailB1 cka prng fs Δcka qep (moAuth mo) j k_fs rfl hΔ P c hs₁ hin
                hsends_f ht_le s₁L s₁F (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
                (by dsimp only [s₁L]; omega) (by dsimp only [s₁F]; have := hs.htcur P; omega) rfl
                rfl (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                                    by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
                hvR_c using 1
              · dsimp only [injectTailB1, s₁L]
                simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                  simulateQ_pure]; congr 1
              · dsimp only [injectTailB1, s₁F]
                simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]; congr 1
        · have heqF : c.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          have ht_le_cur : c.1.1 ≤ (esL.g.st P).tcur := by omega
          have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
            esL.g P (esL.g.st P) c none hcondL_f heq
          have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
            esF.g P (esF.g.st P) c none hcondF_f heqF
          have hvR_c :
              ((esL.g.st P).vR c.1.1 = none ∧ (esF.g.st P).vR c.1.1 = none) ∨
              (∃ rs idx₀, (esL.g.st P).vR c.1.1 = some (rs, idx₀) ∧
                (esF.g.st P).vR c.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c.1.1 = (moAuth mo).tStar ∧
                (esL.g.st P).vR c.1.1 = some (st.receiverState, some j) ∧
                (esF.g.st P).vR c.1.1 = some none) := by
            by_cases ht_star : c.1.1 = mo.tStar
            · right; right
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
                rw [← hP_tstar, ← ht_star]; exact ht_le_cur
              obtain ⟨_, h1, h2⟩ := hs.hvR_target_ge hge
              exact ⟨ht_star, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
            · rcases hs.hvR_other P c.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
          convert leComp_injectTailB1 cka prng fs Δcka qep (moAuth mo) j k_fs rfl hΔ P c hs hin
            hsends_f ht_le (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P)
            (hs.hroot P) rfl rfl (by omega) (by have := hs.htcur P; omega) rfl rfl
            (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
          · dsimp only [injectTailB1]; simp only [hvRecvL, StateT.run_bind]; congr 2
          · dsimp only [injectTailB1]; simp only [hvRecvF, StateT.run_bind]; congr 3
    · have hsafe_f : esL.g.safeInj 2 = false := Bool.eq_false_iff.mpr hsafe
      simp only [hsafe_f, Bool.not_false, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))

set_option maxHeartbeats 400000 in
theorem leComp_deliverForgeE_dir2 (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (mo : Mode) (j : ℕ) (k_fs : K)
    (hΔ : Δcka = 0) (q : Party × (Header T × E) × (Header T × E))
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep (moAuth mo) j k_fs)
      (simulateQ lImpl
        ((deliverForgeEB1 (hooksLocalFixed cka prng fs mo j k_fs) qep mo.tStar (moAuth mo).cfg
          q).run esL))
      ((simulateQ (implFS fs)
        ((deliverForgeEB1 (hooksFS cka prng fs Δcka mo j) qep mo.tStar (moAuth mo).cfg q).run
          esF)).run st) := by
  rcases q with ⟨P, c, c'⟩
  unfold deliverForgeEB1
  rw [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_bind, StateT.run_get, pure_bind]
  simp only [hs.habortL, hs.habortF, hs.hwinL, hs.hwinF, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte]
  have hin_c_eq : esF.g.inTransit P.other c = esL.g.inTransit P.other c := by
    simp only [GameState.inTransit, hs.htrans]
  have hin_c'_eq : esF.g.inTransit P.other c' = esL.g.inTransit P.other c' := by
    simp only [GameState.inTransit, hs.htrans]
  rw [hin_c_eq]
  cases hin_c : esL.g.inTransit P.other c with
  | none =>
    simp only [StateT.run_pure, simulateQ_pure]
    exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
  | some r =>
    dsimp only; rw [hin_c'_eq, ← hs.hcomp]
    by_cases hguard :
        ((esL.g.inTransit P.other c').isSome || esL.g.comp.contains r.pos || c.1 != c'.1) = true
    · simp only [hguard, ↓reduceIte, StateT.run_pure, simulateQ_pure]
      exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
    · simp only [hguard, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hguard
      rcases hguard with ⟨⟨htrans0, _⟩, hhdr⟩
      have hin : esL.g.inTransit P.other c' = none := by
        cases h : esL.g.inTransit P.other c' with
        | none => rfl
        | some _ => simp [h] at htrans0
      obtain ⟨hmem, hct, hpos_eq, _, _, _⟩ :=
        inTransit_some_props fs Δcka qep (moAuth mo) hs P c r hin_c
      have hr_ep : r.pos.epoch = c'.1.1 := by
        have h1 : r.pos.epoch = c.1.1 := by rw [hpos_eq]
        rw [h1, hhdr]
      have hcond_eq :
          ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) =
            ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) := by
        rw [hs.hidF P, hs.hidL P, ← hs.htcur P]
      by_cases hcondL :
          ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) = true
      · have hcondF :
            ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) = true :=
          hcond_eq.trans hcondL
        dsimp only [vRecv]
        simp only [hcondL, hcondF, ↓reduceIte, StateT.run_bind, run_liftH, StateT.run_pure,
          pure_bind, simulateQ_pure]
        exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
      · have hcondL_f :
            ((esL.g.st P).id.sendsIn c'.1.1 || decide ((esL.g.st P).tcur + 1 < c'.1.1)) = false :=
          Bool.eq_false_iff.mpr hcondL
        have hcondF_f :
            ((esF.g.st P).id.sendsIn c'.1.1 || decide ((esF.g.st P).tcur + 1 < c'.1.1)) = false :=
          hcond_eq.trans hcondL_f
        have hsends_f : P.sendsIn c'.1.1 = false := by
          have h := hcondL_f; rw [hs.hidL P, Bool.or_eq_false_iff] at h; exact h.1
        have ht_le : c'.1.1 ≤ (esL.g.st P).tcur + 1 := by
          have h := hcondL_f; rw [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h; omega
        have hPother_s : P.other = Party.senderOf c'.1.1 := by
          have hother_sends : P.other.sendsIn c'.1.1 = true := by
            revert hsends_f
            cases P <;> cases h : Nat.beq (c'.1.1 % 2) 1 <;> simp [Party.other, Party.sendsIn]
          exact eq_senderOf_of_sendsIn hother_sends
        have hP_recv : P = Party.receiverOf c'.1.1 := by
          unfold Party.receiverOf; rw [← hPother_s]; cases P <;> rfl
        by_cases heq : c'.1.1 = (esL.g.st P).tcur + 1
        · have heqF : c'.1.1 = (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          cases hTn : c'.1.2 with
          | none =>
            have hvL : vRecv (hooksLocalFixed cka prng fs mo j k_fs) esL.g P (esL.g.st P) c' none =
                pure (some none) := by simp [vRecv, heq, hTn]
            have hvF : vRecv (hooksFS cka prng fs Δcka mo j) esF.g P (esF.g.st P) c' none =
                pure (some none) := by simp [vRecv, heqF, hTn]
            simp only [hvL, hvF, run_liftH, StateT.run_bind, StateT.run_pure, pure_bind,
              simulateQ_pure]
            exact LeComp.pure (Or.inr (Or.inr ⟨rfl, hs⟩))
          | some Tc =>
            have hvRecvL := vRecv_eq_bind_vRecvTail_of_eq (hooksLocalFixed cka prng fs mo j k_fs)
              esL.g P (esL.g.st P) c' none Tc hcondL_f heq hTn
            have hvRecvF := vRecv_eq_bind_vRecvTail_of_eq (hooksFS cka prng fs Δcka mo j)
              esF.g P (esF.g.st P) c' none Tc hcondF_f heqF hTn
            simp only [hvRecvL, hvRecvF, run_liftH, StateT.run_bind, bind_assoc, simulateQ_bind]
            rw [← hs.hγ P, ← hs.hroot P]
            refine LeComp.bind (leComp_startRecv cka prng fs Δcka mo j k_fs esL.g esF.g P c'.1.1
              (esL.g.st P).γ (esL.g.st P).root Tc hs.hbs st) ?_
            intro rL rF ⟨hr_st, hr_cL, hr_cF, hr_tr, hr_cnt, hr_sc, hr_ex, hr_bs, hcases⟩
            rw [hr_st]
            rcases hcases with ⟨hL_none, hF_none⟩ | ⟨hL_snone, hF_snone, hr_sess⟩ |
              ⟨σ', kL, kF, idx?, ext, hL_some, hF_some, hext_eq, h_eq_j, h_ne_j, h_ne_t, h_origin⟩
            · simp only [hL_none, hF_none, StateT.run_pure, pure_bind, abortE, simulateQ_pure]
              exact LeComp.pure (Or.inl (lhsDead_of_abort Δcka (moAuth mo) j _))
            · simp only [hL_snone, hF_snone, StateT.run_pure, pure_bind, simulateQ_pure]
              exact LeComp.pure (Or.inr (Or.inr ⟨rfl,
                syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs hr_cL
                  (fun _ _ => hr_sess) hr_ex hr_cnt hr_tr hr_sc⟩))
            · simp only [hL_some, hF_some]
              have hs₁ : SyncLFS fs Δcka qep (moAuth mo) j k_fs
                  { esL with h := rL.2 } { esF with h := rF.1.2 } st := by
                refine syncLFS_with_book fs Δcka qep (moAuth mo) j k_fs hs rL.2 rF.1.2 hr_bs
                  hr_cL ?_ hr_ex hr_cnt hr_tr hr_sc
                intro h1 h2
                rcases h_origin with ⟨_, _, _, hsess⟩ | ⟨_, hnot, _, _⟩
                · exact hsess
                · exact absurd ⟨h1, h2⟩ hnot
              let s₁L : PartyState Γ T Sig (SS × Option ℕ) (RS × Option ℕ) :=
                { esL.g.st P with
                  tcur := c'.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                  vR := Function.update (esL.g.st P).vR c'.1.1 (some (fs.initReceiver kL, idx?)) }
              let s₁F : VP Γ T Sig (Option SS) (Option RS) :=
                { esF.g.st P with
                  tcur := c'.1.1, γ := (cka.receive (esL.g.st P).γ Tc).1, root := σ',
                  vR := Function.update (esF.g.st P).vR c'.1.1
                    (some (if ext then none else some (fs.initReceiver kF))) }
              have hvR_c :
                  (s₁L.vR c'.1.1 = none ∧ s₁F.vR c'.1.1 = none) ∨
                  (∃ rs idx₀, s₁L.vR c'.1.1 = some (rs, idx₀) ∧
                    s₁F.vR c'.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
                  (c'.1.1 = (moAuth mo).tStar ∧
                    s₁L.vR c'.1.1 = some (st.receiverState, some j) ∧
                    s₁F.vR c'.1.1 = some none) := by
                by_cases hj : idx? = some j
                · obtain ⟨hkL, ht_star⟩ := h_eq_j hj; right; right
                  have hlt_tstar : (esL.g.st (Party.receiverOf mo.tStar)).tcur < mo.tStar := by
                    rw [← ht_star, ← hP_recv]; omega
                  have hrs_init : st.receiverState = fs.initReceiver k_fs :=
                    (hs.hvR_target_lt hlt_tstar).2.2
                  have hext_true : ext = true := by rw [hext_eq, hj, beq_self_eq_true]
                  refine ⟨ht_star, ?_, ?_⟩
                  · dsimp only [s₁L]; rw [Function.update_self, hj, hkL, hrs_init]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_true]; rfl
                · right; left
                  have hkL : kL = kF := h_ne_j hj
                  have hext_false : ext = false := by rw [hext_eq, beq_eq_false_iff_ne]; exact hj
                  refine ⟨fs.initReceiver kL, idx?, ?_, ?_, hj⟩
                  · dsimp only [s₁L]; rw [Function.update_self]
                  · dsimp only [s₁F]; rw [Function.update_self, hext_false, hkL]; rfl
              have htailL := deliverForgeTailB1_eq_injectTailB1 qep (moAuth mo)
                (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) P c' r hr_ep s₁L
                { esL with h := rL.2 }
              have htailF := deliverForgeTailB1_eq_injectTailB1 qep (moAuth mo)
                (hooksFS cka prng fs Δcka (moAuth mo) j) P c' r hr_ep s₁F { esF with h := rF.1.2 }
              convert leComp_injectTailB1 cka prng fs Δcka qep (moAuth mo) j k_fs rfl hΔ P c' hs₁
                hin hsends_f ht_le s₁L s₁F (hs.hidL P) (hs.hidF P) rfl rfl rfl rfl
                (by dsimp only [s₁L]; omega) (by dsimp only [s₁F]; have := hs.htcur P; omega) rfl
                rfl (fun t' ht' => ⟨by dsimp only [s₁L]; rw [Function.update_of_ne ht'],
                                    by dsimp only [s₁F]; rw [Function.update_of_ne ht']⟩)
                hvR_c using 1
              · rw [← htailL]; dsimp only [deliverForgeTailB1, s₁L]
                simp only [StateT.run_bind, run_liftH, bind_assoc, pure_bind, simulateQ_bind,
                  simulateQ_pure]; congr 1
              · rw [← htailF]; dsimp only [deliverForgeTailB1, s₁F]
                simp only [StateT.run_bind, run_liftH, bind_assoc, simulateQ_bind]; congr 1
        · have heqF : c'.1.1 ≠ (esF.g.st P).tcur + 1 := by rw [← hs.htcur P]; exact heq
          have ht_le_cur : c'.1.1 ≤ (esL.g.st P).tcur := by omega
          have hvRecvL := vRecv_eq_vRecvTail_of_ne (hooksLocalFixed cka prng fs mo j k_fs)
            esL.g P (esL.g.st P) c' none hcondL_f heq
          have hvRecvF := vRecv_eq_vRecvTail_of_ne (hooksFS cka prng fs Δcka mo j)
            esF.g P (esF.g.st P) c' none hcondF_f heqF
          have hvR_c :
              ((esL.g.st P).vR c'.1.1 = none ∧ (esF.g.st P).vR c'.1.1 = none) ∨
              (∃ rs idx₀, (esL.g.st P).vR c'.1.1 = some (rs, idx₀) ∧
                (esF.g.st P).vR c'.1.1 = some (some rs) ∧ idx₀ ≠ some j) ∨
              (c'.1.1 = (moAuth mo).tStar ∧
                (esL.g.st P).vR c'.1.1 = some (st.receiverState, some j) ∧
                (esF.g.st P).vR c'.1.1 = some none) := by
            by_cases ht_star : c'.1.1 = mo.tStar
            · right; right
              have hP_tstar : P = Party.receiverOf mo.tStar := ht_star ▸ hP_recv
              have hge : mo.tStar ≤ (esL.g.st (Party.receiverOf mo.tStar)).tcur := by
                rw [← hP_tstar, ← ht_star]; exact ht_le_cur
              obtain ⟨_, h1, h2⟩ := hs.hvR_target_ge hge
              exact ⟨ht_star, ht_star ▸ hP_tstar ▸ h1, ht_star ▸ hP_tstar ▸ h2⟩
            · rcases hs.hvR_other P c'.1.1 (fun h => ht_star (congrArg Prod.snd h)) with h1 | h2
              · exact Or.inl h1
              · exact Or.inr (Or.inl h2)
          have htailL := deliverForgeTailB1_eq_injectTailB1 qep (moAuth mo)
            (hooksLocalFixed cka prng fs (moAuth mo) j k_fs) P c' r hr_ep (esL.g.st P) esL
          have htailF := deliverForgeTailB1_eq_injectTailB1 qep (moAuth mo)
            (hooksFS cka prng fs Δcka (moAuth mo) j) P c' r hr_ep (esF.g.st P) esF
          convert leComp_injectTailB1 cka prng fs Δcka qep (moAuth mo) j k_fs rfl hΔ P c' hs hin
            hsends_f ht_le (esL.g.st P) (esF.g.st P) (hs.hidL P) (hs.hidF P) (hs.hγ P)
            (hs.hroot P) rfl rfl (by omega) (by have := hs.htcur P; omega) rfl rfl
            (fun _ _ => ⟨rfl, rfl⟩) hvR_c using 1
          · rw [← htailL]; dsimp only [deliverForgeTailB1]; simp only [hvRecvL, StateT.run_bind]
            congr 2
          · rw [← htailF]; dsimp only [deliverForgeTailB1]; simp only [hvRecvF, StateT.run_bind]
            congr 3

theorem leComp_stepLFixedDFShiftedDir2Paper_stepFDFShiftedDir2Paper
    (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (hΔ : Δcka = 0)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (q : (SMSpecDF Γ T Sig SS RS M CCoins E).Domain)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    LeComp (StepRelFS fs Δcka qep (moAuth mo) j k_fs)
      (stepLFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs q esL)
      (stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j q esF st) := by
  rcases q with n | ((((q12 | q3) | q4) | P) | q6)
  · rw [stepLFixedDFShiftedDir2Paper_inl, stepFDFShiftedDir2Paper_inl]
    exact leComp_stepLFixedDFShiftedPaper_stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j
      k_fs rfl hvg (.inl n) hs
  · rw [stepLFixedDFShiftedDir2Paper_q12, stepFDFShiftedDir2Paper_q12]
    exact leComp_stepLFixedDFShiftedPaper_stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j
      k_fs rfl hvg (.inr (.inl (.inl (.inl (.inl q12))))) hs
  · exact leComp_deliverE_dir2 cka prng fs Δcka qep mo j k_fs q3 hs
  · exact leComp_injectE_dir2 cka prng fs Δcka qep mo j k_fs hΔ q4 hs
  · rw [stepLFixedDFShiftedDir2Paper_corr,
      stepFDFShiftedDir2Paper_corr cka prng fs Δcka qep l mo j k_fs hvg P hs]
    exact leComp_stepLFixedDFShiftedPaper_stepFDFShiftedPaper cka prng fs Δcka qep l (moAuth mo) j
      k_fs rfl hvg (.inr (.inl (.inr P))) hs
  · exact leComp_deliverForgeE_dir2 cka prng fs Δcka qep mo j k_fs hΔ q6 hs

theorem runLocAtFixedDFShiftedDir2Paper_le_runFDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep l : ℕ)
    (mo : Mode) (j : ℕ) (k_fs : K) (hΔ : Δcka = 0)
    (hvg : lastLeakGuessAdmissible (2 + Δcka) mo.tL mo.tStar = true)
    (oa : SMCompDF Γ T Sig SS RS M CCoins E Bool)
    {esL : EStateL Γ T Sig SS RS M E K I} {esF : EStateF Γ T Sig SS RS M E K I}
    {st : FSGameState SS RS T M E} (hs : SyncLFS fs Δcka qep (moAuth mo) j k_fs esL esF st) :
    𝒟[runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs oa esL] {true} ≤
      𝒟[runFDFShiftedDir2Paper cka prng fs Δcka qep l mo j oa esF st] {true} := by
  induction oa using OracleComp.inductionOn generalizing esL esF st with
  | pure b' =>
    have hout : (authOut (2 + Δcka) (moAuth mo).policy esL && (esL.h.lastIdx == some j)) =
        false := by
      simp [authOut, hs.hwinL]
    simp only [runLocAtFixedDFShiftedDir2Paper, simulateQ_pure, StateT.run_pure, pure_bind, hout]
    have hzero : 𝒟[(pure false : ProbComp Bool)] {true} = 0 := by simp
    rw [hzero]; exact zero_le
  | query_bind q k ih =>
    rw [runLocAtFixedDFShiftedDir2Paper_query_bind, runFDFShiftedDir2Paper_query_bind]
    refine leComp_stepLFixedDFShiftedDir2Paper_stepFDFShiftedDir2Paper cka prng fs Δcka qep l mo j
      k_fs hΔ hvg q hs
      (fun rL => runLocAtFixedDFShiftedDir2Paper cka prng fs Δcka qep l mo j k_fs (k rL.1) rL.2)
      (fun rF => runFDFShiftedDir2Paper cka prng fs Δcka qep l mo j (k rF.1.1) rF.1.2 rF.2) ?_
    rintro rL rF (hdead | hwin | ⟨heq_ans, hs'⟩)
    · rw [evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_dead cka prng fs Δcka qep l mo j k_fs
        (k rL.1) rL.2 hdead]; exact zero_le
    · rw [evalDist_runFDFShiftedDir2Paper_eq_one_of_win cka prng fs Δcka qep l mo j (k rF.1.1)
        rF.1.2 rF.2 hwin]; exact prob_le_one
    · rw [heq_ans]; exact ih rF.1.1 hs'

def runFSDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep l : ℕ) (mo : Mode)
    (j : ℕ) (b : Bool) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  engRunDFShiftedDir2Paper l (hooksFS cka prng fs Δcka mo j) qep fs.maxSkip
    mo.tStar (moAuth mo).cfg (moAuth mo).policy (initFS cka prng fs lam mo j) {} b A

theorem localAuthAtFixedDFShiftedDir2Paper_le_runFSDFShiftedDir2Paper
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep j l : ℕ) (k_fs : K)
    (b_fs : Bool) (tL : Option ℕ) (t : ℕ) (hΔ : Δcka = 0)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtFixedDFShiftedDir2Paper cka prng fs lam Δcka qep j l k_fs tL t A] {true} ≤
      𝒟[(simulateQ (implFS fs)
        (runFSDFShiftedDir2Paper cka prng fs lam Δcka qep l ⟨false, tL, t⟩ j false A)).run
          (FSAEAD.initState fs k_fs b_fs) >>= fun z => pure z.2.win] {true} := by
  subst hΔ
  by_cases hvg : lastLeakGuessAdmissible 2 tL t = true
  · unfold localAuthAtFixedDFShiftedDir2Paper runFSDFShiftedDir2Paper engRunDFShiftedDir2Paper
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine leComp_init cka prng fs lam 0 qep ⟨false, tL, t⟩ j k_fs b_fs _ _ ?_
    rintro ⟨vsL, hL⟩ ⟨⟨vsF, hF⟩, stF⟩ ⟨vAL, vBL, vAF, vBF, rfl, rfl, hdead | hs⟩
    · let esL₀ : EStateL Γ T Sig SS RS M E K I :=
        { g := { st := fun P => match P with | .A => vAL | .B => vBL, b := false }, h := hL }
      have hdead' : LHSDead 0 (moAuth ⟨false, tL, t⟩) j esL₀ := by
        rcases hdead with ⟨habw, _⟩ | ⟨hab, hwin, hid, hR⟩
        · cases habw
        · exact Or.inr ⟨hab, hwin, hid, hR⟩
      exact le_of_eq_of_le (evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_dead cka prng fs
        0 qep l ⟨false, tL, t⟩ j k_fs A esL₀ hdead') zero_le
    · refine le_trans (runLocAtFixedDFShiftedDir2Paper_le_runFDFShiftedDir2Paper cka prng fs 0
        qep l ⟨false, tL, t⟩ j k_fs rfl hvg A { hs with })
        (le_of_eq (congrArg (fun p => 𝒟[p] {true}) ?_))
      simp only [runFDFShiftedDir2Paper, implEDFShiftedB1, implEDFShiftedDir2Paper, simulateQ_bind,
        simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]; rfl
  · have hvg_f : lastLeakGuessAdmissible 2 tL t = false := Bool.eq_false_iff.mpr hvg
    have hzero :
        𝒟[localAuthAtFixedDFShiftedDir2Paper cka prng fs lam 0 qep j l k_fs tL t A] {true} =
          0 := by
      unfold localAuthAtFixedDFShiftedDir2Paper
      refine evalDist_bind_eq_zero _ _ fun r _ => ?_
      rcases r with ⟨_ | ⟨vA, vB⟩, h⟩
      · simp
      · exact evalDist_runLocAtFixedDFShiftedDir2Paper_eq_zero_of_not_validGuess cka prng fs 0
          qep l ⟨false, tL, t⟩ j k_fs hvg_f A _
    rw [hzero]; exact zero_le

theorem localAuthAtDFShiftedDir2Paper_le_fsWinDFShiftedDir2Paper (cka : CKAScheme KC Γ CCoins T I)
    (prng : PRFPRNG KR Sig I K) (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I)
    (qep j l t : ℕ) (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) :
    𝒟[localAuthAtDFShiftedDir2Paper cka prng fs lam 0 qep j l (some (l - 1)) t A] {true} ≤
      FSAEAD.advantage fs (redFSAuthDFShiftedDir2Paper cka prng fs lam qep j l t A) := by
  have hred : redFSAuthDFShiftedDir2Paper cka prng fs lam qep j l t A =
      (runFSDFShiftedDir2Paper cka prng fs lam 0 qep l ⟨false, some (l - 1), t⟩ j false A >>=
        fun _ => sampleT Bool) := rfl
  rw [hred, advantage_bind_sampleT_bool]
  refine le_trans (localAuthAtDFShiftedDir2Paper_le_localAuthAtFixedDFShiftedDir2Paper cka prng fs
    lam 0 qep j l (some (l - 1)) t A) ?_
  unfold fsWin
  rw [← OracleComp.evalDist_bind_const ($ᵗ Bool)
        (($ᵗ K : ProbComp K) >>= fun k_fs =>
          localAuthAtFixedDFShiftedDir2Paper cka prng fs lam 0 qep j l k_fs (some (l - 1)) t A)]
  refine evalDist_bind_mono ($ᵗ Bool) _ _ fun b_fs _ =>
    evalDist_bind_mono ($ᵗ K) _ _ fun k_fs _ =>
      localAuthAtFixedDFShiftedDir2Paper_le_runFSDFShiftedDir2Paper cka prng fs lam 0 qep j l k_fs
        b_fs (some (l - 1)) t rfl A

end AuthL11ShiftedDir2Paper

/-- Shifted-paper Lemma 11 at `Δ = 2`: the PRF-PRNG branch of `redPRNGAuthDFShiftedDir2Paper` is
bounded by the sum over `j < q` of the FS-AEAD advantages of `redFSAuthDFShiftedDir2Paper j`. -/
theorem lemma11_df_shifted_dir2_paper {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E]
    [DecidableEq I] [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (qep l t q : ℕ)
    (A : SchemeAdversaryDF Γ T Sig SS RS M CCoins E) (hq : MakesAtMostQueriesDF A q) :
    𝒟[PRFPRNG.branch prng true
        (redPRNGAuthDFShiftedDir2Paper cka prng fs lam qep l t A)] {true} ≤
      ∑ j ∈ Finset.range q,
        FSAEAD.advantage fs (redFSAuthDFShiftedDir2Paper cka prng fs lam qep j l t A) := by
  refine le_trans (branch_redPRNGAuthDFShiftedDir2Paper_le_localAuthDFShiftedDir2Paper cka prng fs
    lam qep l t A) ?_
  refine le_trans (localAuthDFShiftedDir2Paper_le_sum_localAuthAtDFShiftedDir2Paper cka prng fs lam
    0 qep l (some (l - 1)) t q A hq) ?_
  exact Finset.sum_le_sum fun j _ =>
    localAuthAtDFShiftedDir2Paper_le_fsWinDFShiftedDir2Paper cka prng fs lam qep j l t A

end CryptoGames.SM.Construction.DeliverForge
