/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import Computational.Proofs.CryptoGames.AEAD.EffSaltProofDefs

/-!
# HKDF and Ratchet Chain PRG Definitions

Proof-side PRG wrappers (`kdfPRG`, `chainPRG`) and effective-salt lemma for HKDF message-key
derivation.
-/

@[expose] public section

namespace CryptoGames
namespace HKDF
open HMAC CBC

/-- `deriveMessageKeys` on a 32-byte salt is `deriveMessageKeys` at its effective salt (`none` = `0^32`; DEV-LS25). -/
theorem msgKeys_effSalt (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt)
    (seed : List (BitVec 8)) : deriveMessageKeys F salt seed = deriveMessageKeys F (some (effectiveHkdfSalt32 salt)) seed := by
  cases salt <;> rfl

/-- **DEV-AEAD6 (formalization): the HKDF message-key derivation is assumed a PRG.** Wraps
`s ↦ deriveMessageKeys F salt (keyToBytes32 s)` as a `PRGScheme` rather than deriving it from HMAC
extract-and-expand. -/
def kdfPRG (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt) :
    PRGScheme (BitVec 256) DerivedMessageKeys :=
  ⟨fun s => deriveMessageKeys F salt (keyToBytes32 s)⟩

end HKDF

namespace Ratchet
open HMAC HKDF

/-- Ratchet chain PRG at position `p`, mapping `ck` to the next chain key and derived message keys. -/
def chainPRG (F : ShaState → List (BitVec 8) → ShaState) (salts : ℕ → Salt) (p : ℕ) :
    PRGScheme ChainKey (ChainKey × DerivedMessageKeys) :=
  ⟨fun ck => ((hmacPRF F).tag ck chainKeySeed,
    (kdfPRG F (salts p)).gen ((hmacPRF F).tag ck messageKeySeed))⟩

end Ratchet
end CryptoGames
