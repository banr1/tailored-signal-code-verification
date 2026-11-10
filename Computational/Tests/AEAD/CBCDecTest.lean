/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs -- shake: keep
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs -- shake: keep

/-!
# CBC Decryption and PKCS#7 Unpadding Tests

Interpreter `#guard` tests for `CryptoGames.CBC` (`CBCDecDefs.lean`), using an invertible toy
block permutation `toyE k x = rotl₈ (x ⊕ k)` to exercise CBC chaining, little-endian block
encoding, length checks, and strict PKCS#7 unpadding.
-/

@[expose] public section

namespace CryptoGames.CBC.Tests

def bs (l : List ℕ) : List (BitVec 8) := l.map (BitVec.ofNat 8)

-- Strict PKCS#7 unpadding (`block-padding` 0.4.2): all `n` trailing bytes must equal `n` (`1 ≤ n ≤ 16`).
#guard pkcs7Unpad (bs (List.range 13 ++ [3, 3, 3])) == some (bs (List.range 13))
#guard pkcs7Unpad (bs (List.replicate 15 7 ++ [0])) == none
#guard pkcs7Unpad (bs (List.replicate 15 7 ++ [17])) == none
#guard pkcs7Unpad (bs (List.replicate 13 7 ++ [2, 3, 3])) == none
#guard pkcs7Unpad (bs (List.replicate 16 16)) == some []
#guard pkcs7Unpad (bs (List.replicate 15 9 ++ [1])) == some (bs (List.replicate 15 9))
#guard pkcs7Unpad (bs (List.replicate 16 16 ++ List.replicate 16 16)) ==
  some (bs (List.replicate 16 16))
#guard pkcs7Unpad [] == none

#guard bytesToBlock (blockToBytesLE 0x00112233445566778899aabbccddeeff) ==
  0x00112233445566778899aabbccddeeff
#guard blockToBytesLE 0x00112233445566778899aabbccddeeff ==
  bs [0xff, 0xee, 0xdd, 0xcc, 0xbb, 0xaa, 0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x00]
#guard chunks16 (bs (List.range 32)) ==
  [bytesToBlock (bs (List.range 16)), bytesToBlock (bs ((List.range 32).drop 16))]

/-- Toy invertible 128-bit block permutation `(x ⊕ k[0..128]) ⋘ 8`. -/
def toyE (k : AesKey) (x : Block) : Block := (x ^^^ k.truncate 128).rotateLeft 8

/-- Inverse of `toyE`. -/
def toyD (k : AesKey) (y : Block) : Block := y.rotateRight 8 ^^^ k.truncate 128

def key : AesKey := 0x4e22eb16d964779994222e82192ce9f747da72dc4abe49dfdeeb71d0ffe3796e
def iv : Block := 0x6f8a557ddc0a140c878063a6d5f31d3d

-- Ciphertext must be a non-empty multiple of 16 bytes (`aes_cbc.rs`).
#guard cbcDecRaw toyD key iv [] == none
#guard cbcDecRaw toyD key iv (bs (List.replicate 15 1)) == none
#guard cbcDecRaw toyD key iv (bs (List.replicate 17 1)) == none

/-- Little-endian ciphertext bytes of `m` under CBC-PKCS#7 with `toyE key` and `iv`. -/
def encBytes {ℓ : ℕ} (m : Plain ℓ) : List (BitVec 8) :=
  (cbcEncrypt (toyE key) iv (pkcs7Blocks m)).toList.flatMap blockToBytesLE

/-- Plaintext vector from libsignal's `aes_cbc.rs` unit test. -/
def m10 : Plain 10 := ⟨bs [0x30, 0x73, 0x62, 0x94, 0xa1, 0x24, 0x48, 0x2a, 0x41, 0x59], rfl⟩
def m16 : Plain 16 := ⟨bs (List.range 16), rfl⟩
def m0 : Plain 0 := ⟨[], rfl⟩

#guard (encBytes m10).length == 16
#guard (encBytes m16).length == 32
#guard cbcDecRaw toyD key iv (encBytes m10) == some m10.toList
#guard cbcDecRaw toyD key iv (encBytes m16) == some m16.toList
#guard cbcDecRaw toyD key iv (encBytes m0) == some []
#guard cbcDecRaw toyD key 0 (encBytes m10) != some m10.toList

#guard (cbcPkcs7 toyE toyD 10).dec (key, iv) ((cbcPkcs7 toyE toyD 10).enc (key, iv) m10) ==
  some m10
#guard (cbcPkcs7 toyE toyD 16).dec (key, iv) ((cbcPkcs7 toyE toyD 16).enc (key, iv) m16) ==
  some m16
-- Decryption under `ℓ = 11` rejects a 10-byte plaintext ciphertext on unpadded length mismatch.
#guard (cbcPkcs7 toyE toyD 11).dec (key, iv) ((cbcPkcs7 toyE toyD 10).enc (key, iv) m10) ==
  none

end CryptoGames.CBC.Tests
