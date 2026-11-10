/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs

/-!
# Equivalence of the Unrestricted `LibsignalGame` with ACD19 Fig. 2

**Checked by Lean.** Proves `toR_hybridAdvantageR_eq_proof` (re-exported by
`LibsignalGameSanity.lean`): for an `SMScheme` lifted without receive coins (`SMScheme.toR`),
disabling `r1` and using `GameState.mustBeCorrect` reduces `hybridAdvantageR` to the standard ACD19
Fig. 2 `hybridAdvantage`, isolating the libsignal game deviations (DEV-LS1–DEV-LS7).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal CryptoGames.Lazy

namespace CryptoGames.LibsignalSM.Proofs.UnrestrictedEq

open CryptoGames.SM

variable {Key St Msg Coins RCoins C : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins] [SampleableType RCoins]

/-- Pointwise `DEq` of state-transformed query implementations lifts through `simulateQ`. -/
theorem deq_simulateQ_run {ι : Type} {ospec : OracleSpec ι} {S α : Type}
    {impl₁ impl₂ : QueryImpl ospec (StateT S ProbComp)}
    (h : ∀ t s, DEq ((impl₁ t).run s) ((impl₂ t).run s))
    (oa : OracleComp ospec α) (s : S) :
    DEq ((simulateQ impl₁ oa).run s) ((simulateQ impl₂ oa).run s) := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a =>
    simp only [simulateQ_pure]
    exact DEq.refl _
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    exact DEq.bind (h t s) fun z => ih z.1 z.2

/-- Lifts an unrestricted `SM.Config` into `ConfigR` with `r1 = false` and `mustBeCorrect`. -/
def toRConfig (sm : SMScheme Key St Msg Coins C) (cfg : Config Msg) : ConfigR St Msg C :=
  { base := cfg, r1 := false, must := fun s P r => s.mustBeCorrect sm.maxSkip P r }

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins] in
theorem transmitImpl_toR_sendPart (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ)
    [SampleableType Coins] :
    transmitImpl (sm.toR RCoins).sendPart Δ qep = transmitImpl sm Δ qep :=
  rfl

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins] in
theorem challImpl_toR_sendPart (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    [SampleableType Coins] :
    challImpl (sm.toR RCoins).sendPart Δ qep cfg = challImpl sm Δ qep cfg :=
  rfl

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins] in
theorem transmitR_toR_run (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (x : Party × Msg × Option Coins) (s : GameState St Msg C) :
    (transmitR (sm.toR RCoins) Δ qep (toRConfig sm cfg) x).run s =
      (transmitImpl sm Δ qep x).run s := by
  simp [transmitR, toRConfig, transmitImpl_toR_sendPart]

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins] in
theorem challR_toR_run (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (x : Party × Msg × Msg × Option Coins) (s : GameState St Msg C) :
    (challR (sm.toR RCoins) Δ qep (toRConfig sm cfg) x).run s =
      (challImpl sm Δ qep cfg x).run s := by
  simp [challR, toRConfig, challImpl_toR_sendPart]

omit [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins] in
theorem corrR_toR_run (sm : SMScheme Key St Msg Coins C) (cfg : Config Msg)
    (P : Party) (s : GameState St Msg C) :
    (corrR (toRConfig sm cfg) P).run s = (corrImpl P).run s := by
  simp [corrR, corrImpl, toRConfig]

omit [SampleableType Key] [SampleableType Coins] in
theorem deliverR_toR_deq (sm : SMScheme Key St Msg Coins C) (cfg : Config Msg)
    (x : Party × C) (s : GameState St Msg C) :
    DEq ((deliverR (sm.toR RCoins) (toRConfig sm cfg) x).run s)
      ((deliverImpl sm cfg x).run s) := by
  rcases x with ⟨P, c⟩
  unfold deliverR deliverImpl toRConfig SMScheme.toR
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  by_cases hwin : s.win = true
  · simp [hwin]
    exact DEq.refl _
  · simp only [hwin, Bool.false_eq_true, ↓reduceIte]
    cases hin : s.inTransit P.other c with
    | none =>
      simp
      exact DEq.refl _
    | some r =>
      simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
      exact DEq.bind_const ($ᵗ RCoins : ProbComp RCoins) _

omit [DecidableEq Msg] [SampleableType Key] [SampleableType Coins] in
theorem injectR_toR_deq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (x : Party × C) (s : GameState St Msg C) :
    DEq ((injectR (sm.toR RCoins) Δ qep (toRConfig sm cfg) x).run s)
      ((injectImpl sm Δ qep cfg x).run s) := by
  rcases x with ⟨P, c⟩
  unfold injectR injectImpl toRConfig SMScheme.toR
  simp only [StateT.run_bind, StateT.run_get, pure_bind, Bool.not_true, Bool.or_false]
  by_cases hcond : (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ)) = true
  · simp [hcond]
    exact DEq.refl _
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_liftM,
      bind_assoc, pure_bind]
    exact DEq.bind_const ($ᵗ RCoins : ProbComp RCoins) _

omit [SampleableType Key] in
theorem oracleImplR_toR_deq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (q : (spec St Msg Coins C).Domain) (s : GameState St Msg C) :
    DEq ((oracleImplR (sm.toR RCoins) Δ qep (toRConfig sm cfg) q).run s)
      ((oracleImpl sm Δ qep cfg q).run s) := by
  rcases q with (((x | x) | x) | x) | P
  · exact DEq.of_eq (transmitR_toR_run sm Δ qep cfg x s)
  · exact DEq.of_eq (challR_toR_run sm Δ qep cfg x s)
  · exact deliverR_toR_deq sm cfg x s
  · exact injectR_toR_deq sm Δ qep cfg x s
  · exact DEq.of_eq (corrR_toR_run sm cfg P s)

theorem runR_toR_deq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (b : Bool) (A : Adversary St Msg Coins C) :
    DEq (runR (sm.toR RCoins) Δ qep (toRConfig sm cfg) b A)
      (run sm Δ qep cfg b A) := by
  unfold runR run
  refine DEq.bind_right ($ᵗ Key) fun k => ?_
  refine deq_simulateQ_run (fun t s => ?_) A (initState sm k b)
  rcases t with u | q
  · exact DEq.refl _
  · exact oracleImplR_toR_deq sm Δ qep cfg q s

theorem gameR_toR_deq (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (A : Adversary St Msg Coins C) :
    DEq (gameR (sm.toR RCoins) Δ qep (toRConfig sm cfg) A)
      (game sm Δ qep cfg A) := by
  unfold gameR game
  refine DEq.bind_right ($ᵗ Bool) fun b => ?_
  exact DEq.bind_left (runR_toR_deq sm Δ qep cfg b A) _

theorem toR_hybridAdvantageR_eq_proof (RCoins : Type) [SampleableType RCoins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (A : Adversary St Msg Coins C) :
    hybridAdvantageR (sm.toR RCoins) Δ qep
        { base := cfg, r1 := false, must := fun s P r => s.mustBeCorrect sm.maxSkip P r } A
      = hybridAdvantage sm Δ qep cfg A := by
  change hybridAdvantageR (sm.toR RCoins) Δ qep (toRConfig sm cfg) A = hybridAdvantage sm Δ qep cfg A
  unfold hybridAdvantageR hybridAdvantage
  rw [DEq.evalDist_eq (gameR_toR_deq (RCoins := RCoins) sm Δ qep cfg A)]

end CryptoGames.LibsignalSM.Proofs.UnrestrictedEq
