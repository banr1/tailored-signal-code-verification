/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Correctness game for libsignal with SPQR (no injections, honest send coins)

**Checked by Lean.** Defines the no-injection, honest-coins correctness R-game `corrGameNoInjR` and
predicate `CorrectWithinNoInj` for the SPQR-on correctness proof (`DEV-LS6`, `DEV-LS35`), matching
DJKPS25 Lemma 4.4 and Remark 2.13.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

variable {Key St Msg Coins RCoins C : Type}

/-- Whether oracle query `t` passes adversary-chosen send coins (`r = some _`) to `transmit` or
`chall`. -/
def choosesCoins :
    ℕ ⊕ (((((Party × Msg × Option Coins) ⊕ (Party × Msg × Msg × Option Coins)) ⊕ (Party × C)) ⊕
      (Party × C)) ⊕ Party) → Bool
  | .inr (.inl (.inl (.inl (.inl (_, _, r))))) => r.isSome
  | .inr (.inl (.inl (.inl (.inr (_, _, _, r))))) => r.isSome
  | _ => false

/-- Adversary `A` never passes explicit send coins (`choosesCoins`) to `transmit` or `chall`
(DEV-LS1, DEV-LS35). -/
def HonestCoins (A : Adversary St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => choosesCoins t = true) 0

/-- Configuration of the correctness R-game with `injOK := fun _ => false`, disabling all
injections (DEV-LS5). -/
def configCorrNoInj (must : GameState St Msg C → Party → Record Msg C → Bool) :
    ConfigR St Msg C :=
  { base := Config.corr, r1 := false, must := must, injOK := fun _ => false }

section Game

variable (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins]

/-- **DEV-LS35 (formalization): correctness against adversaries that do not inject and use honest
send coins.** Correctness R-game (`configCorrNoInj`) matching DJKPS25 SM-corr (Lemma 4.4,
Remark 2.13) without injections or adversary-chosen send coins. -/
def corrGameNoInjR (must : GameState St Msg C → Party → Record Msg C → Bool)
    (A : Adversary St Msg Coins C) : ProbComp Bool := do
  let (_, s) ← runR sm Δ qep (configCorrNoInj must) false A
  return s.win

/-- Correctness advantage of `A` in `corrGameNoInjR` for `must`. -/
noncomputable def corrAdvantageNoInjR (must : GameState St Msg C → Party → Record Msg C → Bool)
    (A : Adversary St Msg Coins C) : ℝ≥0∞ :=
  𝒟[corrGameNoInjR sm Δ qep must A] {true}

end Game

/-- Every `HonestCoins` adversary making at most `q` queries has `corrAdvantageNoInjR` at most
`ε`. -/
def CorrectWithinNoInj {Key' St' Msg' Coins' RCoins' C' : Type} [DecidableEq Msg'] [DecidableEq C']
    [SampleableType Key'] [SampleableType Coins'] [SampleableType RCoins']
    (smR : SMSchemeR Key' St' Msg' Coins' RCoins' C') (Δ qep : ℕ)
    (must : GameState St' Msg' C' → Party → Record Msg' C' → Bool) (q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A, MakesAtMostQueries A q → HonestCoins A → corrAdvantageNoInjR smR Δ qep must A ≤ ε

end CryptoGames.SM
