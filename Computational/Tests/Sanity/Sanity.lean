/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs

/-!
# FS-AEAD Game Non-Vacuity Check

**Checked by Lean.** Verifies that the FS-AEAD security game (`CryptoGames.FSAEAD.game`) is
non-vacuous: against the identity scheme `idScheme`, a single `challengeQuery () false true`
recovers the challenge bit `b` with advantage `1` (`advantage_idAdv`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD.Sanity

/-- Trivial `FSAEADScheme` whose ciphertexts equal the plaintexts. -/
def idScheme : FSAEADScheme Unit Unit Unit Unit Bool Bool where
  initSender _ := ()
  initReceiver _ := ()
  send _ _ m := ((), m)
  receive _ _ e := some ((), 0, e)
  maxSkip := 0

def idAdv : Adversary Unit Unit Unit Bool Bool :=
  -- Without `show`, `do` would take `Adversary Unit Unit Unit Bool` as the monad.
  show AdversaryComp Unit Unit Unit Bool Bool Bool from do
  let e ← challengeQuery () false true
  return e.getD false

theorem game_idAdv : game idScheme idAdv = (do let _ ← $ᵗ Bool; let _ ← $ᵗ Unit; pure true) := by
  simp [game, idAdv, challengeQuery, oracleImpl, challengeImpl, challenge, initState, idScheme]

theorem advantage_idAdv : advantage idScheme idAdv = 1 := by
  rw [advantage, game_idAdv]
  simp [MeasureTheory.Measure.boolBias]

end CryptoGames.FSAEAD.Sanity
