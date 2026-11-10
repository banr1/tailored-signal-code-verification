/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs

/-!
# The effective 32-byte HKDF salt (DEV-LS25)

**Trusted in part.** The theorems of `Computational/Theorems/` use the general-length normaliser
`effectiveHkdfSalt` and `fit32` (Lemma 1's one-key first-message `Auth` game,
`Computational/Specifications/Pqxdh/Security/Auth/Game.lean`, `effectiveHkdfSaltBytes`): read them.
`effectiveHkdfSalt32` is checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

In `MessageKeys::derive_keys`, `HKDF-Extract` computes `HMAC-SHA256(salt, ikm)` with `None` mapped
to 32 zero bytes. Because HMAC zero-pads keys of length at most 64 to the 64-byte block, any salt
of at most 32 bytes acts solely through its 32-byte zero-padded form (`None`, `Some([])`, and
`Some(0^32)` coincide); PRF assumptions on salts are stated over this effective 32-byte salt.
-/

@[expose] public section

namespace CryptoGames

/-- Pad with zeros (or truncate) a list to 32 entries. -/
def fit32 {α : Type} [OfNat α 0] (s : List α) : List.Vector α 32 :=
  ⟨s.take 32 ++ List.replicate (32 - s.length) 0, by simp; omega⟩

/-- Effective 32-byte HKDF salt of an optional salt (`none ↦ 0^32`, `some s ↦ fit32 s`). -/
def effectiveHkdfSalt {α : Type} [OfNat α 0] (salt? : Option (List α)) : List.Vector α 32 :=
  (salt?.map fit32).getD (List.Vector.replicate 32 0)

/-- Effective 32-byte HKDF salt on 32-byte salts (`none ↦ 0^32`, `some s ↦ s`). -/
def effectiveHkdfSalt32 {α : Type} [OfNat α 0] (salt : Option (List.Vector α 32)) : List.Vector α 32 :=
  salt.getD (List.Vector.replicate 32 0)

end CryptoGames
