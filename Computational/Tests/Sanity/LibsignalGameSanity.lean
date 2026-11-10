/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import Computational.Proofs.CryptoGames.SM.GameProofDefs
public import Computational.Proofs.CryptoGames.SM.LibsignalGameProofDefs
import Computational.Tests.Sanity.UnrestrictedEq

/-!
# Reduction of the Randomized Libsignal SM Game to ACD19 Figure 2

**Checked by Lean.**

Shows that for a deterministic-receive `SMScheme` lifted via `SMScheme.toR`, disabling `r1` and
using `GameState.mustBeCorrect` reduces `hybridAdvantageR` (`LibsignalGame.lean`) to the ACD19
Figure 2 advantage `hybridAdvantage` (`Game.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM

variable {Key St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]
  [SampleableType Key] [SampleableType Coins]

/-- With `r1 = false` and `GameState.mustBeCorrect`, `hybridAdvantageR` on `sm.toR RCoins` equals
`hybridAdvantage` on `sm` because `sm.toR` ignores sampled receive coins. -/
theorem toR_hybridAdvantageR_eq (RCoins : Type) [SampleableType RCoins]
    (sm : SMScheme Key St Msg Coins C) (Δ qep : ℕ) (cfg : Config Msg)
    (A : Adversary St Msg Coins C) :
    hybridAdvantageR (sm.toR RCoins) Δ qep { base := cfg, r1 := false, must := fun s P r => s.mustBeCorrect sm.maxSkip P r } A
      = hybridAdvantage sm Δ qep cfg A := by
  exact CryptoGames.LibsignalSM.Proofs.UnrestrictedEq.toR_hybridAdvantageR_eq_proof RCoins sm Δ qep cfg A

end CryptoGames.SM
