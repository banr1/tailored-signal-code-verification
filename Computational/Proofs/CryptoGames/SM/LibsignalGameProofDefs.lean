/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.CryptoGames.SM.Game
public import Computational.Proofs.CryptoGames.SM.GameProofDefs

/-!
# Proof-side definitions for `LibsignalGame`

Proof-side helpers for `SM/LibsignalGame.lean`: `SMScheme.toR`, bounded-receiver correctness
predicates (`mustBounded`, `mustLibsignal`), and `hybridAdvantageR`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames

/-- Embeds a deterministic-receive `SMScheme` as an `SMSchemeR` ignoring receive coins. -/
def SMScheme.toR {Key St Msg Coins C : Type} (RCoins : Type) (sm : SMScheme Key St Msg Coins C) :
    SMSchemeR Key St Msg Coins RCoins C :=
  { initA := sm.initA, initB := sm.initB, send := sm.send,
    receive := fun s c _ => sm.receive s c }

namespace SM
variable {Key St Msg Coins RCoins C : Type}

/-- Correctness predicate for a receiver with bounded forward jump, skipped-key, and chain
limits. -/
def mustBounded (maxJump maxKeys maxChains : ℕ) (s : GameState St Msg C) (P : Party)
    (r : Record Msg C) : Bool :=
  !(s.comp.contains r.pos)
    && decide (r.pos.idx ≤ s.maxAcc P r.pos.epoch + maxJump + 1)
    && decide (s.maxAcc P r.pos.epoch ≤ r.pos.idx + maxKeys)
    && decide (s.epoch P < r.pos.epoch + 2 * maxChains)

/-- `mustBounded` at libsignal's limits (`25000`, `2000`, `5`; DEV-LS6, DEV-LS10). -/
def mustLibsignal (s : GameState St Msg C) (P : Party) (r : Record Msg C) : Bool :=
  mustBounded 25000 2000 5 s P r

section Game
variable (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ)
  [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
  [SampleableType RCoins]

/-- Bias `2·|Pr[win] − 1/2|` in the R-game variant `cfg` (DEV-LS1, DEV-LS6, DEV-SM1, DEV-SM10). -/
noncomputable def hybridAdvantageR (cfg : ConfigR St Msg C) (A : Adversary St Msg Coins C) :
    ℝ≥0∞ :=
  𝒟[gameR sm Δ qep cfg A].boolBias

end Game
end SM
end CryptoGames
