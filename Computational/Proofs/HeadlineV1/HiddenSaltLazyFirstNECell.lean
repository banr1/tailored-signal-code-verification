/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECoupleT
public import Computational.Specifications.Pqxdh.Game
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple3
import ProofLib.SepLogic.WP.StateNorm
import VCVio.EvalDist.Monad.Basic

/-!
# Per-Cell Paper-Engine Reductions and Runner

Defines the 3-way per-cell paper `DeliverForge` advantage `forgeGuessedAdvantageCellPaper`, the
per-cell reductions, and the unified runner `runBaseDFCellTPaper`, and proves their equivalence.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.SM.Construction.DeliverForge

open CryptoGames CryptoGames.SM CryptoGames.SM.Construction

/-- Three-way per-cell paper `DeliverForge` advantage dispatching between `Dir2` (`tL = some (t - 2)`),
shifted (`tL = some (t - 3)`), and unshifted cells. -/
noncomputable def forgeGuessedAdvantageCellPaper {Key St Msg Coins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) : ℝ≥0∞ :=
  if 2 ≤ t ∧ tL = some (t - 2) then
    DeliverForge.forgeGuessedAdvantageShiftedDir2Paper sm qep sameHdr (t - 1) t B
  else if 3 ≤ t ∧ tL = some (t - 3) then
    DeliverForge.forgeGuessedAdvantageShiftedPaper sm (2 + 1) qep sameHdr (t - 2) t B
  else
    DeliverForge.forgeGuessedAdvantagePaper sm (2 + 1) qep sameHdr tL t B

end CryptoGames.SM.Construction.DeliverForge

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.SendTotal (Encaps1Total TopState)
open CryptoVerification.LibsignalProtoCodec
open CryptoGames CryptoGames.LibsignalSM CryptoGames.LibsignalSM.Inst
open CryptoGames.Ratchet CryptoGames.CKA CryptoGames.SM CryptoGames.SM.Construction
open CryptoGames.SM.Engine CryptoGames.SM.Thm1
open CryptoGames.LibsignalSession CryptoGames.Ratchet.LibsignalInst
open CryptoGames.Ratchet.LibsignalSim CryptoGames.Ratchet.LibsignalSimC
open CryptoGames.LibsignalSM.Proofs CryptoGames.LibsignalSM.Proofs.Refinement
open CryptoVerification.LibsignalSession
open HMAC HKDF CBC LibsignalAead AEADScheme MACScheme WireAEAD FSAEAD

theorem cellTrivialT_some_sub_two_eq_trivB1 {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    (t : ℕ) (ht : 2 ≤ t) (s : SM.GameState St Msg C) :
    cellTrivialT (some (t - 2)) t s =
      CryptoGames.SM.Construction.DeliverForge.trivB1 t s := by
  funext pos
  unfold cellTrivialT CryptoGames.SM.Construction.DeliverForge.trivB1
  simp [ht]

theorem authOKDir2_eq_refinement_authOKDir2 {St Msg C : Type} (tL : Option ℕ) (tStar : ℕ)
    (s : SM.GameState St Msg C) :
    authOKDir2 tL tStar s =
      CryptoGames.LibsignalSM.Proofs.Refinement.authOKDir2 tL tStar s := by
  unfold authOKDir2 CryptoGames.LibsignalSM.Proofs.Refinement.authOKDir2
  congr 2
  induction s.corrs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨p, e⟩
    simp only [List.any_cons, List.contains_cons, ih]
    congr 1
    cases p <;> cases Party.senderOf tStar <;> simp [BEq.beq, eq_comm]

def injectImplCellT {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (cfg : SM.Config Msg) :
    QueryImpl ((Party × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c⟩ => do
  let s ← get
  if s.win || (s.inTransit P.other c).isSome || !(s.safeInj (cellDelta tL tStar)) then return none
  match sm.receive (s.st P) c with
  | none => return some .rejected
  | some (st', t', i', m') =>
    if qep + 1 < t' then return some .rejected
    let pos : SM.Pos := ⟨P.other, t', i'⟩
    if cellTrivialT tL tStar s pos then
      set (s.accept P st' pos); return some (.accepted t' i' (some m'))
    else
      if cfg.injectFull t' then set { s with win := true }
      return some .rejected

def deliverForgeBaseImplCellT {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl ((Party × C × C) →ₒ Option (SM.RecvResult Msg))
      (StateT (SM.GameState St Msg C) ProbComp) := fun ⟨P, c, c'⟩ => do
  let s ← get
  if s.win then return none
  match s.inTransit P.other c with
  | none => return none
  | some r =>
    if (s.inTransit P.other c').isSome || s.comp.contains r.pos || !(sameHdr c c') then return none
    match sm.receive (s.st P) c' with
    | none => return some .rejected
    | some (st', t', i', m') =>
      if qep + 1 < t' || t' != r.pos.epoch then return some .rejected
      let pos : SM.Pos := ⟨P.other, t', i'⟩
      if cellTrivialT tL tStar s pos then
        set (s.accept P st' pos); return some (.accepted t' i' (some m'))
      else
        if cfg.injectFull t' then set { s with win := true }
        return some .rejected

def oracleImplCellTPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (cfg : SM.Config Msg) :
    QueryImpl (SM.spec St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  SM.transmitImpl sm (cellDelta tL tStar) qep + SM.challImpl sm (cellDelta tL tStar) qep cfg +
    SM.deliverImpl sm cfg + injectImplCellT sm qep tL tStar cfg +
    DeliverForge.corrImplShiftedPaper (St := St) (Msg := Msg) (C := C) (cellShift tL tStar)

def oracleImplBaseDFCellTPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (DeliverForge.specDF St Msg Coins C) (StateT (SM.GameState St Msg C) ProbComp) :=
  oracleImplCellTPaper sm qep tL tStar cfg +
    deliverForgeBaseImplCellT sm qep tL tStar sameHdr cfg

abbrev fullImplBaseDFCellTPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Coins] (sm : SMScheme Key St Msg Coins C) (qep : ℕ)
    (tL : Option ℕ) (tStar : ℕ) (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    QueryImpl (unifSpec + DeliverForge.specDF St Msg Coins C)
      (StateT (SM.GameState St Msg C) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (SM.GameState St Msg C) ProbComp) +
    oracleImplBaseDFCellTPaper sm qep tL tStar sameHdr cfg

/-- Unified per-cell `DeliverForge` runner parameterized by `cellDelta`, `cellTrivialT`, and `cellShift`. -/
def runBaseDFCellTPaper {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    ProbComp (Bool × SM.GameState St Msg C) := do
  let k ← $ᵗ Key
  (simulateQ (fullImplBaseDFCellTPaper sm qep tL tStar sameHdr cfg) B).run (SM.initState sm k b)

theorem injectImplCellT_some_sub_two_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tStar : ℕ} (ht2 : 2 ≤ tStar)
    (cfg : SM.Config Msg) :
    injectImplCellT sm qep (some (tStar - 2)) tStar cfg =
      DeliverForge.injectImplB1 sm qep tStar cfg := by
  funext ⟨P, c⟩
  unfold injectImplCellT DeliverForge.injectImplB1
  have hdelta : cellDelta (some (tStar - 2)) tStar = 2 := by
    unfold cellDelta
    simp only [ht2, and_self, ↓reduceIte]
  rw [hdelta]
  refine congrArg (get >>= ·) (funext fun s => ?_)
  split_ifs
  · rfl
  · cases sm.receive (s.st P) c with
    | none => rfl
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only
      rw [cellTrivialT_some_sub_two_eq_trivB1 tStar ht2]

theorem deliverForgeBaseImplCellT_some_sub_two_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tStar : ℕ} (ht2 : 2 ≤ tStar)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    deliverForgeBaseImplCellT sm qep (some (tStar - 2)) tStar sameHdr cfg =
      DeliverForge.deliverForgeBaseImplB1 sm qep tStar sameHdr cfg := by
  funext ⟨P, c, c'⟩
  unfold deliverForgeBaseImplCellT DeliverForge.deliverForgeBaseImplB1
  refine congrArg (get >>= ·) (funext fun s => ?_)
  split_ifs
  · rfl
  · cases s.inTransit P.other c with
    | none => rfl
    | some r =>
      dsimp only
      split_ifs
      · rfl
      · cases sm.receive (s.st P) c' with
        | none => rfl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          dsimp only
          rw [cellTrivialT_some_sub_two_eq_trivB1 tStar ht2]

theorem fullImplBaseDFCellTPaper_some_sub_two_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tStar : ℕ} (ht2 : 2 ≤ tStar)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    fullImplBaseDFCellTPaper sm qep (some (tStar - 2)) tStar sameHdr cfg =
      DeliverForge.fullImplBaseDFShiftedDir2Paper sm (tStar - 1) qep tStar sameHdr cfg := by
  have hdelta : cellDelta (some (tStar - 2)) tStar = 2 := by
    unfold cellDelta
    simp only [ht2, and_self, ↓reduceIte]
  have hshift : cellShift (some (tStar - 2)) tStar = tStar - 1 := by
    unfold cellShift
    simp only [ht2, and_self, ↓reduceIte]
  unfold fullImplBaseDFCellTPaper DeliverForge.fullImplBaseDFShiftedDir2Paper
    oracleImplBaseDFCellTPaper DeliverForge.oracleImplBaseDFShiftedDir2Paper
    oracleImplCellTPaper DeliverForge.oracleImplShiftedDir2Paper
  rw [hdelta, hshift, injectImplCellT_some_sub_two_eq sm qep ht2 cfg,
    deliverForgeBaseImplCellT_some_sub_two_eq sm qep ht2 sameHdr cfg]

theorem runBaseDFCellTPaper_some_sub_two_eq
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) {tStar : ℕ} (ht2 : 2 ≤ tStar)
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    runBaseDFCellTPaper sm qep (some (tStar - 2)) tStar sameHdr cfg b B =
      DeliverForge.runBaseDFShiftedDir2Paper sm (tStar - 1) qep tStar sameHdr cfg b B := by
  unfold runBaseDFCellTPaper DeliverForge.runBaseDFShiftedDir2Paper
  rw [fullImplBaseDFCellTPaper_some_sub_two_eq sm qep ht2 sameHdr cfg]

theorem injectImplCellT_of_not_B1
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (h1 : ¬(2 ≤ tStar ∧ tL = some (tStar - 2))) (cfg : SM.Config Msg) :
    injectImplCellT sm qep tL tStar cfg = SM.injectImpl sm (2 + 1) qep cfg := by
  funext ⟨P, c⟩
  unfold injectImplCellT SM.injectImpl
  have hdelta : cellDelta tL tStar = 2 + 1 := by
    unfold cellDelta
    simp only [h1, ↓reduceIte]
  rw [hdelta]
  refine congrArg (get >>= ·) (funext fun s => ?_)
  split_ifs
  · rfl
  · cases sm.receive (s.st P) c with
    | none => rfl
    | some val =>
      rcases val with ⟨st', t', i', m'⟩
      dsimp only
      rw [cellTrivialT_of_not_B1 h1]

theorem deliverForgeBaseImplCellT_of_not_B1
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (h1 : ¬(2 ≤ tStar ∧ tL = some (tStar - 2)))
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    deliverForgeBaseImplCellT sm qep tL tStar sameHdr cfg =
      DeliverForge.deliverForgeBaseImpl sm (2 + 1) qep sameHdr cfg := by
  funext ⟨P, c, c'⟩
  unfold deliverForgeBaseImplCellT DeliverForge.deliverForgeBaseImpl
  refine congrArg (get >>= ·) (funext fun s => ?_)
  split_ifs
  · rfl
  · cases s.inTransit P.other c with
    | none => rfl
    | some r =>
      dsimp only
      split_ifs
      · rfl
      · cases sm.receive (s.st P) c' with
        | none => rfl
        | some val =>
          rcases val with ⟨st', t', i', m'⟩
          dsimp only
          rw [cellTrivialT_of_not_B1 h1]

theorem fullImplBaseDFCellTPaper_of_not_B1
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (h1 : ¬(2 ≤ tStar ∧ tL = some (tStar - 2)))
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) :
    fullImplBaseDFCellTPaper sm qep tL tStar sameHdr cfg =
      DeliverForge.fullImplBaseDFShiftedPaper sm (2 + 1) (cellShift tL tStar) qep
        sameHdr cfg := by
  have hdelta : cellDelta tL tStar = 2 + 1 := by
    unfold cellDelta
    simp only [h1, ↓reduceIte]
  unfold fullImplBaseDFCellTPaper DeliverForge.fullImplBaseDFShiftedPaper
    oracleImplBaseDFCellTPaper DeliverForge.oracleImplBaseDFShiftedPaper
    oracleImplCellTPaper DeliverForge.oracleImplShiftedPaper
  rw [hdelta, injectImplCellT_of_not_B1 sm qep tL tStar h1 cfg,
    deliverForgeBaseImplCellT_of_not_B1 sm qep tL tStar h1 sameHdr cfg]

theorem runBaseDFCellTPaper_of_not_B1
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (h1 : ¬(2 ≤ tStar ∧ tL = some (tStar - 2)))
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    runBaseDFCellTPaper sm qep tL tStar sameHdr cfg b B =
      DeliverForge.runBaseDFShiftedPaper sm (2 + 1) (cellShift tL tStar) qep
        sameHdr cfg b B := by
  unfold runBaseDFCellTPaper DeliverForge.runBaseDFShiftedPaper
  rw [fullImplBaseDFCellTPaper_of_not_B1 sm qep tL tStar h1 sameHdr cfg]

theorem runBaseDFCellTPaper_of_not_B1_not_B2
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (tL : Option ℕ) (tStar : ℕ)
    (h1 : ¬(2 ≤ tStar ∧ tL = some (tStar - 2)))
    (h2 : ¬(3 ≤ tStar ∧ tL = some (tStar - 3)))
    (sameHdr : C → C → Bool) (cfg : SM.Config Msg) (b : Bool)
    (B : DeliverForge.AdversaryDF St Msg Coins C) :
    runBaseDFCellTPaper sm qep tL tStar sameHdr cfg b B =
      DeliverForge.runBaseDFPaper sm (2 + 1) qep sameHdr cfg b B := by
  have hshift : cellShift tL tStar = 0 := by
    unfold cellShift
    simp only [h1, h2, ↓reduceIte]
  rw [runBaseDFCellTPaper_of_not_B1 sm qep tL tStar h1 sameHdr cfg b B, hshift]
  exact runBaseDFShiftedPaper_zero_eq_runBaseDFPaper sm (2 + 1) qep sameHdr cfg b B

theorem forgeGuessedAdvantageCellPaperT_eq_runBaseDFCellTPaper
    {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
    [SampleableType Key] [SampleableType Coins]
    (sm : SMScheme Key St Msg Coins C) (qep : ℕ) (sameHdr : C → C → Bool)
    (tL : Option ℕ) (t : ℕ) (B : DeliverForge.AdversaryDF St Msg Coins C) :
    DeliverForge.forgeGuessedAdvantageCellPaper sm (qep + 1) sameHdr tL t B =
      𝒟[do
        let (_, s') ←
          runBaseDFCellTPaper sm (qep + 1) tL t sameHdr (SM.Config.auth t) false B
        return cellWinPred tL t s'] {true} := by
  by_cases h1 : 2 ≤ t ∧ tL = some (t - 2)
  · rcases h1 with ⟨ht2, rfl⟩
    have hwin : ∀ s' : SM.GameState St Msg C, cellWinPred (some (t - 2)) t s' =
        (s'.win && CryptoGames.LibsignalSM.Proofs.Refinement.authOKDir2
          (some (t - 1 - 1)) t s') := by
      intro s'
      have hsub : t - 1 - 1 = t - 2 := by omega
      unfold cellWinPred
      simp only [ht2, and_self, ↓reduceIte, hsub, authOKDir2_eq_refinement_authOKDir2]
    rw [runBaseDFCellTPaper_some_sub_two_eq sm (qep + 1) ht2 sameHdr (SM.Config.auth t) false B]
    simp only [hwin]
    unfold DeliverForge.forgeGuessedAdvantageCellPaper
    simp only [ht2, and_self, ↓reduceIte]
    rfl
  · by_cases h2 : 3 ≤ t ∧ tL = some (t - 3)
    · have hshift : cellShift tL t = t - 2 := by
        unfold cellShift
        simp only [h1, ↓reduceIte]
        simp only [h2.1, h2.2, and_self, ↓reduceIte]
      have hwin : ∀ s' : SM.GameState St Msg C, cellWinPred tL t s' =
          (s'.win && SM.authLosingConditionsAvoided (2 + 1) (some (t - 2 - 1)) t s') := by
        intro s'
        have hsub : t - 2 - 1 = t - 3 := by omega
        unfold cellWinPred
        simp only [h1, ↓reduceIte]
        rw [h2.2, hsub]
      rw [runBaseDFCellTPaper_of_not_B1 sm (qep + 1) tL t h1 sameHdr (SM.Config.auth t) false B,
        hshift]
      simp only [hwin]
      unfold DeliverForge.forgeGuessedAdvantageCellPaper
      simp only [h1, ↓reduceIte]
      simp only [h2.1, h2.2, and_self, ↓reduceIte]
      rfl
    · have hwin : ∀ s' : SM.GameState St Msg C, cellWinPred tL t s' =
          (s'.win && SM.authLosingConditionsAvoided (2 + 1) tL t s') := by
        intro s'
        unfold cellWinPred
        simp only [h1, ↓reduceIte]
      rw [runBaseDFCellTPaper_of_not_B1_not_B2 sm (qep + 1) tL t h1 h2 sameHdr (SM.Config.auth t)
        false B]
      simp only [hwin]
      unfold DeliverForge.forgeGuessedAdvantageCellPaper
      simp only [h1, h2, ↓reduceIte]
      rfl

end CryptoVerification.LibsignalSession.HeadlineV1

end
