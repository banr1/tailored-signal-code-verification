/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.Vector.Defs
public import Mathlib.Tactic.ToAdditive

/-!
# Byte-Level SHA-256 and HMAC-SHA256

Pure byte-list specifications of SHA-256 and HMAC-SHA256 parameterized by a 64-byte block
compression function `F`.
-/

@[expose] public section

namespace ByteSpecs

/-- SHA-256 chaining state: eight 32-bit words `H₀ … H₇`. -/
abbrev ShaState := List.Vector (BitVec 32) 8

/-- FIPS 180-4 §5.3.3 initial hash value for SHA-256. -/
def sha256IV : ShaState :=
  ⟨[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19], rfl⟩

/-- Big-endian `n`-byte encoding of `x`. -/
def toBEBytes (n : ℕ) {w : ℕ} (x : BitVec w) : List (BitVec 8) :=
  List.ofFn fun j : Fin n => x.extractLsb' (8 * (n - 1 - j.val)) 8

/-- FIPS 180-4 §5.1.1 message padding to a multiple of 64 bytes. -/
def sha256Pad (m : List (BitVec 8)) : List (BitVec 8) :=
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * m.length))

/-- Splits `bs` into 64-byte blocks, dropping any trailing partial block. -/
def chunks64 (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  List.ofFn fun i : Fin (bs.length / 64) => (bs.drop (64 * i.val)).take 64

/-- SHA-256 of `m` under compression function `F`. -/
def sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    List (BitVec 8) :=
  ((chunks64 (sha256Pad m)).foldl F sha256IV).toList.flatMap (toBEBytes 4)

/-- RFC 2104 HMAC-SHA256 under compression function `F`. -/
def hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    List (BitVec 8) :=
  let k' := if 64 < k.length then sha256With F k else k
  let k₀ := k' ++ List.replicate (64 - k'.length) 0
  let inner := sha256With F (k₀.map (· ^^^ 0x36) ++ m)
  sha256With F (k₀.map (· ^^^ 0x5c) ++ inner)

end ByteSpecs
