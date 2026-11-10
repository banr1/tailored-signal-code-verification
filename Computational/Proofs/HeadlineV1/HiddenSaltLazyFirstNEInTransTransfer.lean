/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple
import Computational.Proofs.HeadlineV1.HiddenSaltLazyFirstNECouple2

/-!
# In-Transit Non-Trivial `Δ = 3` Transfer Lemma

**Checked by Lean.** Shows that an uncompromised in-transit record at epoch `t'` determines an
admissible `Δ = 3` canonical guess `SM.canon t' g ≠ some (t' - 2)` with `cellDelta = 2 + 1`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped ENNReal BigOperators
open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoVerification.LibsignalSession.HeadlineV1

open CryptoGames CryptoGames.SM CryptoGames.SM.Thm1 CryptoGames.SM.Thm1L17

theorem targetsL_three_ne_sub_two {t' : ℕ} {tLStar : Option ℕ}
    (hmem3 : tLStar ∈ SM.admissibleLastLeakGuesses (2 + 1) t') :
    tLStar ≠ some (t' - 2) := by
  simp only [SM.admissibleLastLeakGuesses, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hmem3
  rcases hmem3 with rfl | ⟨a, ha_lt, rfl⟩
  · intro h; nomatch h
  · intro hsome; injection hsome with ha_eq; omega

/-- Under `WFState (2 + 1) g`, an uncompromised in-transit record at epoch `t'` has admissible
canonical guess `SM.canon t' g ≠ some (t' - 2)` with `cellDelta = 2 + 1`. -/
theorem canon_ne_sub_two_of_mem_trans_uncomp {St Msg C : Type} [DecidableEq Msg] [DecidableEq C]
    {t' : ℕ} {g : SM.GameState St Msg C} {r : SM.Record Msg C}
    (hwf : SM.Thm1L17.WFState (2 + 1) g) (hr : r ∈ g.trans) (hep : r.pos.epoch = t')
    (huncomp : r.pos ∉ g.comp) :
    SM.lastLeakGuessAdmissible (2 + 1) (SM.canon t' g) t' = true ∧
    SM.canon t' g ∈ SM.admissibleLastLeakGuesses (2 + 1) t' ∧
    SM.canon t' g ∈ SM.admissibleLastLeakGuesses 2 t' ∧
    ¬(2 ≤ t' ∧ SM.canon t' g = some (t' - 2)) ∧
    SM.canon t' g ≠ some (t' - 2) ∧
    cellDelta (SM.canon t' g) t' = 2 + 1 := by
  have hvg : SM.lastLeakGuessAdmissible (2 + 1) (SM.canon t' g) t' = true := by
    rw [← hep]
    exact (hwf.trans_uncomp r hr huncomp).1
  have hmem3 : SM.canon t' g ∈ SM.admissibleLastLeakGuesses (2 + 1) t' :=
    SM.Thm1L17.mem_targetsL_of_validGuess (by omega : 0 < 2 + 1) hvg
  rcases targetsL_three_subset_targetsL_two hmem3 with ⟨hmem2, hnot_B1⟩
  have hne : SM.canon t' g ≠ some (t' - 2) := targetsL_three_ne_sub_two hmem3
  have hdelta : cellDelta (SM.canon t' g) t' = 2 + 1 := by
    unfold cellDelta
    simp [hnot_B1]
  exact ⟨hvg, hmem3, hmem2, hnot_B1, hne, hdelta⟩

end CryptoVerification.LibsignalSession.HeadlineV1

end
