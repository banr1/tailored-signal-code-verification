/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs

/-!
# libsignal's root KDF as a PRF-PRNG

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models the HKDF-SHA256 step of libsignal v0.105.4 `RootKey::create_chain`
(`rust/protocol/src/ratchet/keys.rs:199–218`, info `"WhisperRatchet"`, 64-byte output split into
32-byte root and chain keys) as `rootKdf`, packages it as the ACD19 PRF-PRNG `rootPRNG` (a named
assumption of the session theorem, DEV-LS30), and defines its single-step PRG/PRF components
`expandPRG` and `extractPRF`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet

open HMAC HKDF CBC MACScheme

/-- 256-bit root key as its 32 LE bytes (`RootKey.key : [u8; 32]`, `keys.rs:185–188`). -/
abbrev RootKey := BitVec 256

/-- HKDF info `"WhisperRatchet"` (14 ASCII bytes, `keys.rs:207`). -/
def whisperRatchetInfo : List (BitVec 8) :=
  "WhisperRatchet".toList.map fun c => BitVec.ofNat 8 c.toNat

/-- HKDF salt `Some(&self.key)` (`keys.rs:206`). -/
def rootSalt (rk : RootKey) : Salt :=
  some ⟨keyToBytes32 rk, by simp [keyToBytes32]⟩

/-- `HKDF-Expand(prk, "WhisperRatchet", 64)` split into `(rootKey, chainKey)` (`keys.rs:205–209`). -/
def rootExpand (F : ShaState → List (BitVec 8) → ShaState) (prk : List (BitVec 8)) :
    RootKey × ChainKey :=
  let okm := hkdfExpand F prk whisperRatchetInfo 64
  (bytesToKey32 (okm.take 32), bytesToKey32 ((okm.drop 32).take 32))

/-- `RootKey::create_chain` KDF step (`keys.rs:204–217`): `HKDF(salt = rk, ikm, "WhisperRatchet", 64)`
split into `(okm[0..32], okm[32..64])`. -/
def rootKdf (F : ShaState → List (BitVec 8) → ShaState) (rk : RootKey) (ikm : List (BitVec 8)) :
    RootKey × ChainKey :=
  let okm := hkdf F (rootSalt rk) ikm whisperRatchetInfo 64
  (bytesToKey32 (okm.take 32), bytesToKey32 ((okm.drop 32).take 32))

/-- Root KDF packaged as an ACD19 `PRFPRNG` (`init = id`, `up σ I = rootKdf F σ (enc I)`). -/
def rootPRNG (F : ShaState → List (BitVec 8) → ShaState) {Pt : Type} (enc : Pt → List (BitVec 8)) :
    PRFPRNG RootKey RootKey Pt ChainKey where
  init := id
  up σ I := rootKdf F σ (enc I)

/-- `rootExpand` as a PRG from a uniform 256-bit PRK to `RootKey × ChainKey`. -/
def expandPRG (F : ShaState → List (BitVec 8) → ShaState) :
    PRGScheme (BitVec 256) (RootKey × ChainKey) :=
  ⟨fun prk => rootExpand F (keyToBytes32 prk)⟩

/-- `HKDF-Extract` keyed by the root key in the salt slot as a PRF `RootKey → Pt → BitVec 256`. -/
def extractPRF (F : ShaState → List (BitVec 8) → ShaState) {Pt : Type}
    (enc : Pt → List (BitVec 8)) : MACScheme RootKey Pt (BitVec 256) :=
  ⟨fun σ I => bytesToKey32 (hkdfExtract F (rootSalt σ) (enc I))⟩

end Ratchet
end CryptoGames
