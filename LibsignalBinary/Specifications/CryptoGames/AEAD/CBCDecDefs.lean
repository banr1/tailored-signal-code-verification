/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs

/-!
# AES-256-CBC decryption with strict PKCS#7 unpadding

**Trusted in part.** The theorems of `Computational/Theorems/` use only `blockToBytesLE`,
`cbcDecRaw`, `cbcDecryptBlocks`, `chunks16`, `pkcs7Unpad` from this file: read those. Everything
else here is checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Specifies libsignal's `signal_crypto::aes_256_cbc_decrypt` over an abstract inverse block cipher
`D : AesKey → Block → Block` on arbitrary input byte strings, and packages it with encryption into
the full `CipherScheme` `cbcPkcs7`.
-/

@[expose] public section

namespace CryptoGames
namespace CBC

/-! ### Bytes and blocks -/

/-- The 16 little-endian bytes of a block: byte `j` is bits `8j .. 8j+7`, inverse of
`bytesToBlock` on 16-byte lists. -/
def blockToBytesLE (b : Block) : List (BitVec 8) :=
  List.ofFn fun j : Fin 16 => b.extractLsb' (8 * j.val) 8

/-- Split a byte string into 16-byte blocks via `bytesToBlock`, dropping any trailing partial
chunk. -/
def chunks16 (bs : List (BitVec 8)) : List Block :=
  List.ofFn fun i : Fin (bs.length / 16) => bytesToBlock ((bs.drop (16 * i.val)).take 16)

/-! ### CBC decryption and PKCS#7 unpadding -/

/-- CBC decryption with inverse block function `g` from initial chaining value `prev` (the IV):
`P₁ = g C₁ ⊕ prev`, `Pᵢ₊₁ = g Cᵢ₊₁ ⊕ Cᵢ`. -/
def cbcDecryptBlocks (g : Block → Block) (prev : Block) : List Block → List Block
  | [] => []
  | c :: cs => (g c ^^^ prev) :: cbcDecryptBlocks g c cs

/-- Strict PKCS#7 unpadding (`block-padding` `Pkcs7::unpad`): with `n` the last byte, reject if
`bs` is empty, `n = 0`, `n > 16`, or any of the last `n` bytes differs from `n`; otherwise drop the
last `n` bytes. -/
def pkcs7Unpad (bs : List (BitVec 8)) : Option (List (BitVec 8)) :=
  match bs.getLast? with
  | none => none
  | some last =>
    let n := last.toNat
    if n = 0 ∨ 16 < n ∨ bs.length < n then none
    else if (bs.drop (bs.length - n)).all (· == last) then some (bs.take (bs.length - n))
    else none

/-- libsignal's `aes_256_cbc_decrypt` over abstract inverse cipher `D`: reject if `ct` is empty or
its length is not a multiple of 16; otherwise CBC-decrypt the 16-byte blocks from `iv` and apply
strict PKCS#7 unpadding. -/
def cbcDecRaw (D : AesKey → Block → Block) (k : AesKey) (iv : Block)
    (ct : List (BitVec 8)) : Option (List (BitVec 8)) :=
  if ct = [] ∨ ct.length % 16 ≠ 0 then none
  else pkcs7Unpad ((cbcDecryptBlocks (D k) iv (chunks16 ct)).flatMap blockToBytesLE)

/-! ### The full cipher -/

/-- AES-256-CBC with PKCS#7 padding on `ℓ`-byte plaintexts as a `CipherScheme`: `enc` is
`cbcPkcs7EncryptOnly E ℓ`, and `dec` runs `cbcDecRaw D` on the little-endian ciphertext bytes and
accepts iff the unpadded output has length `ℓ`. -/
def cbcPkcs7 (E D : AesKey → Block → Block) (ℓ : ℕ) :
    CipherScheme (AesKey × Block) (Plain ℓ) (List.Vector Block (nBlocks ℓ)) where
  enc := (cbcPkcs7EncryptOnly E ℓ).enc
  dec k c :=
    match cbcDecRaw D k.1 k.2 (c.toList.flatMap blockToBytesLE) with
    | none => none
    | some bs => if h : bs.length = ℓ then some ⟨bs, h⟩ else none

end CBC
end CryptoGames
