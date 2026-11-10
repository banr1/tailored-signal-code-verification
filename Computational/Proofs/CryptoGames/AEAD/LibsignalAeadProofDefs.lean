/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs

/-!
# Libsignal Per-Message AEAD Definitions

Proof-side definitions for libsignal's Encrypt-then-MAC message AEAD (`msgAead`) and wire
send/receive operations (`send`, `recv`).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalAead
open CBC HMAC

/-- Left-inverse property `parse ∘ encode = some` for a wire encoding. -/
def RoundTrip {H : Type} {n : ℕ} (enc : WireEnc H n) : Prop :=
  ∀ h c, enc.parse (enc.encode h c) = some (h, c)

/-- MAC input bytes `ids ‖ encode h c` authenticated by `msgAead`. -/
def macInput {H : Type} {n : ℕ} (enc : WireEnc H n) :
    (SerializedIdentityKeys × H) × List.Vector Block n → List (BitVec 8)
  | ((ids, h), c) => ids.toList ++ enc.encode h c

/-- Per-message Encrypt-then-MAC AEAD combining `cbcPkcs7` with 8-byte HMAC-SHA256 over `macInput enc`. -/
def msgAead {H : Type} (E D : AesKey → Block → Block) (F : ShaState → List (BitVec 8) → ShaState)
    (ℓ : ℕ) (enc : WireEnc H (nBlocks ℓ)) :
    AEADScheme ((AesKey × Block) × BitVec 256) (SerializedIdentityKeys × H) (Plain ℓ)
      (List.Vector Block (nBlocks ℓ) × BitVec 64) :=
  AEADScheme.etm (cbcPkcs7 E D ℓ) ((hmacScheme F).precomp (macInput enc))

/-- Receiver wire decryption returning both header and plaintext (DEV-AEAD9): verifies the MAC over
`ids ‖ wire.1`, parses the header and body, decrypts, and checks addresses. -/
def recv {H : Type} (E D : AesKey → Block → Block) (F : ShaState → List (BitVec 8) → ShaState)
    (ℓ : ℕ) (enc : WireEnc H (nBlocks ℓ)) (addrs : H → Option (List (BitVec 8)))
    (k : (AesKey × Block) × BitVec 256) (ids : SerializedIdentityKeys) (expected : Option (List (BitVec 8)))
    (wire : List (BitVec 8) × BitVec 64) : Option (H × Plain ℓ) :=
  if (hmacScheme F).tag k.2 (ids.toList ++ wire.1) == wire.2 then
    match enc.parse wire.1 with
    | none => none
    | some (h, c) =>
      match (cbcPkcs7 E D ℓ).dec k.1 c with
      | none => none
      | some m => if addressCheckPasses (addrs h) expected then some (h, m) else none
  else none

/-- Encrypts and MACs `(h, m)` under `msgAead` and serializes the header and ciphertext body. -/
def send {H : Type} (E D : AesKey → Block → Block) (F : ShaState → List (BitVec 8) → ShaState)
    (ℓ : ℕ) (enc : WireEnc H (nBlocks ℓ)) (k : (AesKey × Block) × BitVec 256) (ids : SerializedIdentityKeys)
    (h : H) (m : Plain ℓ) : List (BitVec 8) × BitVec 64 :=
  let ct := (msgAead E D F ℓ enc).enc k (ids, h) m
  (enc.encode h ct.1, ct.2)

end LibsignalAead
end CryptoGames
