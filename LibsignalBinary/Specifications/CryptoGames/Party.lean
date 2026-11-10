/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Protocol parties and alternating epoch ownership

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `Party.senderOf`: read them. `Party.senderOf` and the theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines the two participants (`Party`), partner swap (`Party.other`), and alternating epoch
ownership (`Party.sendsIn`, `Party.senderOf`: `A` sends in odd epochs, `B` in even epochs) shared
by the CKA and SM games (ACD19 §3.2.1, §4.1.1).
-/

@[expose] public section

namespace CryptoGames

/-- Two-party protocol participant (`A` or `B`). -/
inductive Party
  | A
  | B
  deriving DecidableEq, Repr

namespace Party

/-- Partner of a party (`A ↔ B`). -/
def other : Party → Party
  | A => B
  | B => A

@[simp] theorem other_A : A.other = B := rfl
@[simp] theorem other_B : B.other = A := rfl
@[simp] theorem other_other (P : Party) : P.other.other = P := by cases P <;> rfl
theorem other_ne (P : Party) : P.other ≠ P := by cases P <;> decide

/-- Whether `P` sends in epoch `t` (`A` in odd epochs, `B` in even epochs). -/
def sendsIn : Party → ℕ → Bool
  | A, t => t % 2 == 1
  | B, t => t % 2 == 0

/-- Sender of epoch `t`. -/
def senderOf (t : ℕ) : Party := if t % 2 == 1 then A else B

end Party

end CryptoGames
