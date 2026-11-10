/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public meta import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs -- shake: keep

/-!
# SHA-256 and HMAC-SHA256 Known-Answer Tests

Defines a test-only reference FIPS 180-4 §6.2.2 compression function `sha256Compress` and checks
`sha256With`, `hmacWith`, `hmacSha256Trunc8`, and `hmacScheme` (`HMACDefs.lean`) via `#guard`
against FIPS 180-4 and RFC 4231 test vectors.
-/

@[expose] public section

namespace CryptoGames.HMAC.Tests

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

/-- Big-endian 32-bit word from 4 bytes. -/
def be32 (b : List (BitVec 8)) : BitVec 32 :=
  b.foldl (fun acc x => (acc <<< 8) ||| x.zeroExtend 32) 0

/-- Message schedule `W₀ … W₆₃` of a 64-byte block. -/
def schedule (blk : List (BitVec 8)) : Array (BitVec 32) := Id.run do
  let mut w : Array (BitVec 32) := #[]
  for t in [0:16] do
    w := w.push (be32 ((blk.drop (4 * t)).take 4))
  for t in [16:64] do
    w := w.push (smallS1 w[t-2]! + w[t-7]! + smallS0 w[t-15]! + w[t-16]!)
  return w

/-- FIPS 180-4 §6.2.2 SHA-256 compression function. -/
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

def bs (l : List ℕ) : List (BitVec 8) := l.map (BitVec.ofNat 8)

def ascii (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- The `n` big-endian bytes of `v`. -/
def hex (n : ℕ) (v : ℕ) : List (BitVec 8) := toBEBytes n (BitVec.ofNat (8 * n) v)

-- FIPS 180-4 SHA-256 padding and digest vectors.
#guard sha256IV.toList.length == 8
#guard (sha256Pad (ascii "abc")).length == 64
#guard (sha256Pad (bs (List.replicate 55 0))).length == 64
#guard (sha256Pad (bs (List.replicate 56 0))).length == 128
#guard (sha256Pad (bs (List.replicate 64 0))).length == 128
-- 64-bit big-endian bit length: 3 bytes = 24 = 0x18 bits.
#guard (sha256Pad (ascii "abc")).drop 56 == bs [0, 0, 0, 0, 0, 0, 0, 0x18]

#guard sha256With sha256Compress (ascii "abc") ==
  hex 32 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
#guard sha256With sha256Compress [] ==
  hex 32 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
-- FIPS 180-4 two-block 56-byte message.
#guard sha256With sha256Compress (ascii "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") ==
  hex 32 0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1

-- RFC 4231 HMAC-SHA256 test cases 1, 2, and 6 (131-byte key hashed first).
#guard hmacWith sha256Compress (bs (List.replicate 20 0x0b)) (ascii "Hi There") ==
  hex 32 0xb0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7
#guard hmacWith sha256Compress (ascii "Jefe") (ascii "what do ya want for nothing?") ==
  hex 32 0x5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843
#guard hmacWith sha256Compress (bs (List.replicate 131 0xaa))
    (ascii "Test Using Larger Than Block-Size Key - Hash Key First") ==
  hex 32 0x60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54
#guard hmacWith sha256Compress (bs (List.range 32)) (ascii "Hi There") ==
  hex 32 0x278639ec02309d3afded1b273f1349ba63b9089c12476d716bee3ecc94673e9e
#guard hmacSha256Trunc8 sha256Compress (bs (List.range 32)) (ascii "Hi There") == hex 8 0x278639ec02309d3a

/-- Reconstructs a 256-bit key from 32 little-endian bytes (inverse of `keyToBytes32`). -/
def keyOf (l : List (BitVec 8)) : BitVec 256 :=
  l.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend 256) 0

#guard bytesToWord64LE (bs [1, 2, 3, 4, 5, 6, 7, 8]) == 0x0807060504030201
#guard keyToBytes32 (keyOf (bs (List.range 32))) == bs (List.range 32)

-- Wire-shaped MAC input: `idA (33 B) ‖ idB (33 B) ‖ ser (36 B)`.
def idA : List (BitVec 8) := bs ([5] ++ List.range' 1 32)
def idB : List (BitVec 8) := bs ([5] ++ List.range' 101 32)
def ser : List (BitVec 8) := bs ([0x44, 0x0a, 0x21] ++ List.range 33)

#guard (idA ++ idB ++ ser).length == 102
#guard hmacWith sha256Compress (bs (List.range 32)) (idA ++ idB ++ ser) ==
  hex 32 0xabd9dd64207798e7397302f295b03dfd926fe94295015de204a8a613d2e5d369
-- Tag is the first 8 HMAC bytes `ab d9 dd 64 20 77 98 e7` read as a little-endian `BitVec 64`.
#guard (hmacScheme sha256Compress).tag (keyOf (bs (List.range 32))) (idA ++ idB ++ ser) ==
  0xe798772064ddd9ab

end CryptoGames.HMAC.Tests
