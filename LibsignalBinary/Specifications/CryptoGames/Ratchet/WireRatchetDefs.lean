/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction

/-!
# libsignal's symmetric ratchet with the counter inside the wire bytes

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. See `Computational/docs/TRUSTED_BASE.md`.

Plaintext normalization `padOrTruncatePlain` used to fit decrypted byte lists into the fixed-length
message type `Plain ℓ` of ACD19 Theorem 5.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames

namespace Ratchet

open HMAC HKDF CBC LibsignalAead MACScheme AEADScheme WireAEAD

variable {H : Type}

/-- Truncate or zero-pad a received plaintext to `ℓ` bytes (identity on `ℓ`-byte inputs). -/
def padOrTruncatePlain (ℓ : ℕ) (bs : List (BitVec 8)) : Plain ℓ :=
  ⟨(bs ++ List.replicate ℓ 0).take ℓ, by simp⟩

end Ratchet
end CryptoGames
