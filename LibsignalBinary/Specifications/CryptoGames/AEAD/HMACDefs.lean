/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs

/-!
# HMAC-SHA256 truncated to 8 bytes

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use the
definitions in this file, so they are part of what you must read to trust them. The theorems here
are checked by Lean. See `Computational/docs/TRUSTED_BASE.md`.

Specifies SHA-256 (`sha256Pad`, `sha256With`), RFC 2104 HMAC-SHA256 (`hmacWith`), and libsignal's
8-byte truncated MAC (`hmacSha256Trunc8`, `hmacScheme`) over an abstract 64-byte compression
function `F : ShaState → List (BitVec 8) → ShaState` (DEV-AEAD14).
-/

@[expose] public section

namespace CryptoGames
namespace HMAC

/-! ### SHA-256 over an abstract compression function -/

/-- SHA-256 chaining state: eight 32-bit words `H₀ … H₇`. -/
abbrev ShaState := List.Vector (BitVec 32) 8

/-- SHA-256 initial hash value `H⁽⁰⁾` (FIPS 180-4 §5.3.3). -/
def sha256IV : ShaState :=
  ⟨[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19], rfl⟩

/-- Big-endian `n`-byte representation of `x`. -/
def toBEBytes (n : ℕ) {w : ℕ} (x : BitVec w) : List (BitVec 8) :=
  List.ofFn fun j : Fin n => x.extractLsb' (8 * (n - 1 - j.val)) 8

/-- SHA-256 message padding (FIPS 180-4 §5.1.1): `m ‖ 0x80 ‖ 0…0 ‖ BE₆₄(8·|m| mod 2⁶⁴)`, padded to
a multiple of 64 bytes. -/
def sha256Pad (m : List (BitVec 8)) : List (BitVec 8) :=
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * m.length))

/-- Split a byte string into 64-byte blocks, dropping any trailing partial block. -/
def chunks64 (bs : List (BitVec 8)) : List (List (BitVec 8)) :=
  List.ofFn fun i : Fin (bs.length / 64) => (bs.drop (64 * i.val)).take 64

/-- SHA-256 of `m` with compression function `F` (FIPS 180-4 §6.2), outputting 32 big-endian
bytes. -/
def sha256With (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) :
    List (BitVec 8) :=
  ((chunks64 (sha256Pad m)).foldl F sha256IV).toList.flatMap (toBEBytes 4)

/-! ### HMAC -/

/-- HMAC-SHA256 (RFC 2104 §2): hash keys longer than 64 bytes, zero-pad to `k₀` of length 64, and
compute `H((k₀ ⊕ 0x5c) ‖ H((k₀ ⊕ 0x36) ‖ m))`. -/
def hmacWith (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) :
    List (BitVec 8) :=
  let k' := if 64 < k.length then sha256With F k else k
  let k₀ := k' ++ List.replicate (64 - k'.length) 0
  let inner := sha256With F (k₀.map (· ^^^ 0x36) ++ m)
  sha256With F (k₀.map (· ^^^ 0x5c) ++ inner)

/-- HMAC-SHA256 truncated to its first 8 bytes (`SignalMessage::compute_mac`). -/
def hmacSha256Trunc8 (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8)) : List (BitVec 8) :=
  (hmacWith F k m).take 8

/-! ### As a `MACScheme` -/

/-- Pack up to 8 little-endian bytes into a 64-bit word. -/
def bytesToWord64LE (bs : List (BitVec 8)) : BitVec 64 :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 64) 0

/-- Extract the 32 little-endian bytes of a 256-bit key. -/
def keyToBytes32 (k : BitVec 256) : List (BitVec 8) :=
  List.ofFn fun j : Fin 32 => k.extractLsb' (8 * j.val) 8

/-- HMAC-SHA256/8 with compression function `F` as a `MACScheme` on byte strings:
`tag k m = bytesToWord64LE (hmacSha256Trunc8 F (keyToBytes32 k) m)`.

**DEV-AEAD5 (formalization): HMAC-SHA256/8 is assumed a PRF.** The bound uses the PRF advantage
of `hmacScheme F` as an assumption. It is not derived from the compression function `F` (Bellare
2006 gives such a derivation). Effect: none (a named assumption). -/
def hmacScheme (F : ShaState → List (BitVec 8) → ShaState) :
    MACScheme (BitVec 256) (List (BitVec 8)) (BitVec 64) where
  tag k m := bytesToWord64LE (hmacSha256Trunc8 F (keyToBytes32 k) m)

end HMAC
end CryptoGames
