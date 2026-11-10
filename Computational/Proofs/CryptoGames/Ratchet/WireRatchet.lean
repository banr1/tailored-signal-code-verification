/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtM
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs

/-!
# Lemmas for libsignal's symmetric wire ratchet

**Checked by Lean.** Proves `fitPlain_toList` for `padOrTruncatePlain` from `WireRatchetDefs.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

namespace Ratchet

open HMAC HKDF CBC LibsignalAead MACScheme AEADScheme WireAEAD FSAEAD

variable {H : Type} [DecidableEq H]

/-- `padOrTruncatePlain` is the identity on `ℓ`-byte plaintexts. -/
theorem fitPlain_toList (ℓ : ℕ) (m : Plain ℓ) : padOrTruncatePlain ℓ m.toList = m := by
  apply List.Vector.toList_injective
  simp [padOrTruncatePlain]

end Ratchet
end CryptoGames
