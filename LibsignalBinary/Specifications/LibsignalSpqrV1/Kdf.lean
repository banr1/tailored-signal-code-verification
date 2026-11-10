/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
import all Init.Data.Range.Basic

/-!
# SPQR V1: HKDF-SHA256 key derivation (`spqr/src/kdf.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use the HKDF functions of this file
(`hkdfToVec`, `hkdfToSlice`, `hkdfToVecUnchecked`, `hkdfToSliceUnchecked`, `hkdfExtractBytes`,
`hkdfMaxOkmLen`, `kdfInvalidLengthPanic`, with bridges `hkdfToSlice_of_le` and `hkdfToVec_of_le`);
the test helpers in `Tests` are checked by Lean (see `Computational/docs/TRUSTED_BASE.md`).

Panic-explicit model of `spqr/src/kdf.rs:4–18` over an abstract SHA-256 compression function `F`,
returning `Except SpqrPanic Bytes` with `.error kdfInvalidLengthPanic` when `okmLen > 255 * 32`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HMAC CryptoGames.HKDF

/-- Maximum HKDF-SHA256 output length in bytes (`255 * 32 = 8160`, RFC 5869 §2.3). -/
abbrev hkdfMaxOkmLen : ℕ := 255 * 32

/-- Panic site of `spqr::kdf::hkdf_to_slice` (`src/kdf.rs:17`) when `okm_len > 255 * 32`. -/
abbrev kdfInvalidLengthPanic : SpqrPanic :=
  .site "src/kdf.rs:17 InvalidLength"

/-- HKDF-Extract (`HMAC-SHA256(salt, ikm)`, `src/kdf.rs:15`). -/
def hkdfExtractBytes (F : ShaState → List (BitVec 8) → ShaState) (salt ikm : Bytes) : Bytes :=
  hmacWith F salt ikm

theorem hkdfExtractBytes_of_salt (F : ShaState → List (BitVec 8) → ShaState)
    (salt : Salt) (ikm : Bytes) :
    hkdfExtractBytes F ((salt.map List.Vector.toList).getD (List.replicate 32 0)) ikm =
      hkdfExtract F salt ikm :=
  rfl

def hkdfToSliceUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) (okmLen : ℕ) : Bytes :=
  hkdfExpand F (hkdfExtractBytes F salt ikm) info okmLen

/-- `spqr::kdf::hkdf_to_slice` (`src/kdf.rs:14–18`), panicking with `kdfInvalidLengthPanic` when
`okmLen > hkdfMaxOkmLen`. -/
def hkdfToSlice (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) (okmLen : ℕ) : Except SpqrPanic Bytes :=
  if okmLen ≤ hkdfMaxOkmLen then
    .ok (hkdfToSliceUnchecked F salt ikm info okmLen)
  else
    .error kdfInvalidLengthPanic

def hkdfToVecUnchecked (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) (okmLen : ℕ) : Bytes :=
  hkdfToSliceUnchecked F salt ikm info okmLen

/-- `spqr::kdf::hkdf_to_vec` (`src/kdf.rs:6–10`). -/
def hkdfToVec (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) (okmLen : ℕ) : Except SpqrPanic Bytes :=
  hkdfToSlice F salt ikm info okmLen

theorem hkdfToSlice_of_le (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) {okmLen : ℕ} (h : okmLen ≤ hkdfMaxOkmLen) :
    hkdfToSlice F salt ikm info okmLen = .ok (hkdfToSliceUnchecked F salt ikm info okmLen) := by
  simp [hkdfToSlice, h]

theorem hkdfToVec_of_le (F : ShaState → List (BitVec 8) → ShaState)
    (salt ikm info : Bytes) {okmLen : ℕ} (h : okmLen ≤ hkdfMaxOkmLen) :
    hkdfToVec F salt ikm info okmLen = .ok (hkdfToVecUnchecked F salt ikm info okmLen) :=
  hkdfToSlice_of_le F salt ikm info h

/-! ## RFC 5869 test vectors -/

namespace Tests

/-- SHA-256 round constants `K₀ … K₆₃` (FIPS 180-4 §4.2.2). -/
def K256 : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def bigS0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bigS1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def smallS0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def smallS1 (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

def be32 (b : List (BitVec 8)) : BitVec 32 :=
  b.foldl (fun acc x => (acc <<< 8) ||| x.zeroExtend 32) 0

def schedule (blk : List (BitVec 8)) : Array (BitVec 32) := Id.run do
  let mut w : Array (BitVec 32) := #[]
  for t in [0:16] do
    w := w.push (be32 ((blk.drop (4 * t)).take 4))
  for t in [16:64] do
    w := w.push (smallS1 w[t-2]! + w[t-7]! + smallS0 w[t-15]! + w[t-16]!)
  return w

/-- Reference SHA-256 compression function (FIPS 180-4 §6.2.2) for test vectors. -/
def sha256Compress (H : ShaState) (blk : List (BitVec 8)) : ShaState := Id.run do
  let w := schedule blk
  let h0 := H.toList
  let mut a := h0[0]!; let mut b := h0[1]!; let mut c := h0[2]!; let mut d := h0[3]!
  let mut e := h0[4]!; let mut f := h0[5]!; let mut g := h0[6]!; let mut h := h0[7]!
  for t in [0:64] do
    let t1 := h + bigS1 e + ((e &&& f) ^^^ (~~~e &&& g)) + K256[t]! + w[t]!
    let t2 := bigS0 a + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  let out := [a, b, c, d, e, f, g, h]
  return List.Vector.ofFn fun i => h0[i.val]! + out[i.val]!

def hexBytes (n : ℕ) (v : ℕ) : Bytes := toBEBytes n (BitVec.ofNat (8 * n) v)

/-- RFC 5869 Appendix A.1 (Test Case 1): HKDF-Extract. -/
theorem rfc5869_tc1_prk :
    hkdfExtractBytes sha256Compress
      ((List.range 13).map (BitVec.ofNat 8))
      (List.replicate 22 0x0b#8) =
    hexBytes 32 0x077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5 := by
  decide +kernel

/-- RFC 5869 Appendix A.1 (Test Case 1): HKDF-Expand (`L = 42`). -/
theorem rfc5869_tc1_okm :
    hkdfToVec sha256Compress
      ((List.range 13).map (BitVec.ofNat 8))
      (List.replicate 22 0x0b#8)
      ((List.range 10).map fun i => BitVec.ofNat 8 (0xf0 + i))
      42 =
    .ok (hexBytes 42
      0x3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865) := by
  decide +kernel

/-- RFC 5869 Appendix A.2 (Test Case 2): 80-byte inputs, `L = 82`. -/
theorem rfc5869_tc2_okm :
    hkdfToVec sha256Compress
      ((List.range 80).map fun i => BitVec.ofNat 8 (0x60 + i))
      ((List.range 80).map (BitVec.ofNat 8))
      ((List.range 80).map fun i => BitVec.ofNat 8 (0xb0 + i))
      82 =
    .ok (hexBytes 82
      0xb11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87) := by
  decide +kernel

/-- RFC 5869 Appendix A.3 (Test Case 3): empty `salt` and `info`, `L = 42`. -/
theorem rfc5869_tc3_okm :
    hkdfToVec sha256Compress
      []
      (List.replicate 22 0x0b#8)
      []
      42 =
    .ok (hexBytes 42
      0x8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8) := by
  decide +kernel

theorem hkdfToSlice_invalidLength :
    hkdfToSlice sha256Compress [] [] [] (hkdfMaxOkmLen + 1) = .error kdfInvalidLengthPanic := by
  decide +kernel

end Tests

end CryptoVerification.LibsignalSpqrV1
