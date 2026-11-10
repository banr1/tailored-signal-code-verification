/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import VCVio.CryptoFoundations.PRG

/-!
# HKDF-SHA256 and libsignal message-key derivation

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. They also use `Salt`, which this file imports from
`LibsignalBinary/Specifications/HkdfSalt.lean`. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Specifies RFC 5869 HKDF-SHA256 (`hkdfExtract`, `hkdfExpand`, `hkdf`) over the abstract SHA-256
compression function `F` of `HMACDefs.lean` (DEV-AEAD14) and libsignal's `MessageKeys::derive_keys`
(`deriveMessageKeys`), which splits `HKDF-SHA256(salt, seed, "WhisperMessageKeys", 80)` into
`((cipher_key, iv), mac_key)` (32 / 16 / 32 little-endian bytes).
-/

@[expose] public section

namespace CryptoGames
namespace HKDF

open HMAC CBC

/-- HKDF-Extract (RFC 5869 §2.2): `PRK = HMAC(salt, ikm)`, defaulting a missing salt to 32 zero
bytes. -/
def hkdfExtract (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt) (ikm : List (BitVec 8)) :
    List (BitVec 8) :=
  hmacWith F ((salt.map List.Vector.toList).getD (List.replicate 32 0)) ikm

/-- HKDF-Expand blocks `[T(1), …, T(n)]` (RFC 5869 §2.3), where
`T(i) = HMAC(prk, T(i−1) ‖ info ‖ [i])` and `T(0) = []`. -/
def hkdfBlocks (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) :
    ℕ → List (List (BitVec 8))
  | 0 => []
  | n + 1 =>
    let ts := hkdfBlocks F prk info n
    ts ++ [hmacWith F prk ((ts.getLastD []) ++ info ++ [BitVec.ofNat 8 (n + 1)])]

/-- HKDF-Expand (RFC 5869 §2.3): the first `L` bytes of `T(1) ‖ T(2) ‖ …`, using `⌈L / 32⌉`
blocks. -/
def hkdfExpand (F : ShaState → List (BitVec 8) → ShaState) (prk info : List (BitVec 8)) (L : ℕ) :
    List (BitVec 8) :=
  ((hkdfBlocks F prk info ((L + 31) / 32)).flatten).take L

/-- HKDF (RFC 5869 §2): `Expand(Extract(salt, ikm), info, L)`. -/
def hkdf (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt) (ikm info : List (BitVec 8))
    (L : ℕ) : List (BitVec 8) :=
  hkdfExpand F (hkdfExtract F salt ikm) info L

/-- The 18-byte ASCII `info` string `"WhisperMessageKeys"` used by `MessageKeys::derive_keys`. -/
def whisperMessageKeys : List (BitVec 8) :=
  "WhisperMessageKeys".toList.map fun c => BitVec.ofNat 8 c.toNat

/-- Pack up to 32 little-endian bytes into a 256-bit word (inverse of `keyToBytes32` on 32-byte
lists). -/
def bytesToKey32 (bs : List (BitVec 8)) : BitVec 256 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 256) 0

/-- Per-message AEAD key tuple `((cipher_key, iv), mac_key)`. -/
abbrev DerivedMessageKeys := (AesKey × Block) × BitVec 256

/-- `MessageKeys::derive_keys`: `okm = HKDF(salt, seed, "WhisperMessageKeys", 80)`, split into
`cipher_key = okm[0..32]`, `mac_key = okm[32..64]`, and `iv = okm[64..80]`. -/
def deriveMessageKeys (F : ShaState → List (BitVec 8) → ShaState) (salt : Salt) (seed : List (BitVec 8)) :
    DerivedMessageKeys :=
  let okm := hkdf F salt seed whisperMessageKeys 80
  ((bytesToKey32 (okm.take 32), bytesToBlock ((okm.drop 64).take 16)),
    bytesToKey32 ((okm.drop 32).take 32))

end HKDF
end CryptoGames
