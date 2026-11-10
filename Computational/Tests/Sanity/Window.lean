/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction

/-!
# Windowed FS-AEAD Correctness under Out-of-Window Reordering

**Checked by Lean.** Concrete trace of the FS-AEAD game (DEV-FS5) on the Fig. 6 construction with
`maxSkip = 0`. Delivering message 2 before message 1 is rejected as out of window without setting
`win = true` and leaves message 2 in transit (blocking `inject`), after which delivering message 1
and re-delivering message 2 both succeed with `win = false`.
-/

@[expose] public section

namespace CryptoGames.FSAEAD.Window

/-- Toy AEAD encrypting `m` under key `k` and header `h` as `(k, h.1, m)`. -/
def toyAE : AEADScheme ℕ (ℕ × Unit) ℕ (ℕ × ℕ × ℕ) where
  enc k h m := (k, h.1, m)
  dec k h c := if c.1 = k ∧ c.2.1 = h.1 then some c.2.2 else none

/-- Toy PRG mapping chain key `w` to `(w + 1, w)` (next chain key, message key). -/
def toyG : PRGScheme ℕ (ℕ × ℕ) := ⟨fun w => (w + 1, w)⟩

/-- Fig. 6 FS-AEAD instance with `maxSkip = 0` (strict in-order delivery). -/
abbrev toyFS := fromAEADPRG toyAE (fun _ => toyG) 0

def st₀ := initState (Key := ℕ) toyFS 0 false

def st₁ := (transmit toyFS st₀ () 10).2

def st₂ := (transmit toyFS st₁ () 20).2

/-- Honest ciphertexts have the form `(index, messageKey, index, message)`. -/
theorem transmit_ciphertexts :
    (transmit toyFS st₀ () 10).1 = some (1, 0, 1, 10) ∧
      (transmit toyFS st₁ () 20).1 = some (2, 1, 2, 20) := by
  decide

def st₃ := (deliver toyFS st₂ () (2, 1, 2, 20)).2

/-- Delivering index 2 before index 1 exceeds `receiverIdx + maxSkip + 1 = 1`: delivery rejects
without setting `win`, and the ciphertext remains in transit so `inject` returns `none`. -/
theorem deliver_out_of_window :
    (deliver toyFS st₂ () (2, 1, 2, 20)).1 = some .rejected ∧ st₃.win = false ∧
      st₃.inTransit.any (·.idx == 2) = true ∧ (inject toyFS st₃ () (2, 1, 2, 20)).1 = none := by
  decide

def st₄ := (deliver toyFS st₃ () (1, 0, 1, 10)).2

def st₅ := (deliver toyFS st₄ () (2, 1, 2, 20)).2

theorem deliver_in_order_after_reorder :
    (deliver toyFS st₃ () (1, 0, 1, 10)).1 = some (.accepted 1 (some 10)) ∧ st₄.win = false ∧
      (deliver toyFS st₄ () (2, 1, 2, 20)).1 = some (.accepted 2 (some 20)) ∧
      st₅.win = false ∧ st₅.receiverIdx = 2 ∧ st₅.inTransit.isEmpty = true := by
  decide

end CryptoGames.FSAEAD.Window
