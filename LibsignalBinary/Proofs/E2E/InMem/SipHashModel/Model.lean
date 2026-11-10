/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# Pure Model of SipHash-1-3, `ProtocolAddress` Hashing, and `hashbrown` Split

Pure functional specification of Rust's `DefaultHasher` (`core::hash::sip::Hasher<Sip13Rounds>`,
1 compression round per 8-byte little-endian block and 3 finalization rounds), the derived
`Hash` encoding of `libsignal_core::ProtocolAddress` (`write(name); write_u8(0xff); write_u8(dev)`),
and `hashbrown`'s 64-bit `(h1, h2)` probe/control-tag split.
-/

@[expose] public section

namespace CryptoVerification.E2E.InMem.SipHashModel

/-! ## SipHash-1-3 Constants and Round Function -/

/-- SipHash initialization constant `c0` (`"somepseu"`). -/
def c0 : UInt64 := 0x736f6d6570736575

/-- SipHash initialization constant `c1` (`"dorandom"`). -/
def c1 : UInt64 := 0x646f72616e646f6d

/-- SipHash initialization constant `c2` (`"lygenera"`). -/
def c2 : UInt64 := 0x6c7967656e657261

/-- SipHash initialization constant `c3` (`"tedbytes"`). -/
def c3 : UInt64 := 0x7465646279746573

/-- Four-word SipHash state (`#[repr(C)] struct State { v0, v2, v1, v3 }`). -/
structure State where
  v0 : UInt64
  v2 : UInt64
  v1 : UInt64
  v3 : UInt64
  deriving DecidableEq, Repr, Inhabited

@[inline]
def rotl64 (x : UInt64) (k : UInt64) : UInt64 :=
  (x <<< k) ||| (x >>> (64 - k))

/-- Single SipRound permutation. -/
@[inline]
def compress (s : State) : State :=
  let v0 := s.v0 + s.v1
  let v2 := s.v2 + s.v3
  let v1 := rotl64 s.v1 13 ^^^ v0
  let v3 := rotl64 s.v3 16 ^^^ v2
  let v0 := rotl64 v0 32
  let v2 := v2 + v1
  let v0 := v0 + v3
  let v1 := rotl64 v1 17 ^^^ v2
  let v3 := rotl64 v3 21 ^^^ v0
  let v2 := rotl64 v2 32
  { v0, v2, v1, v3 }

@[inline] def cRounds (s : State) : State := compress s

@[inline] def dRounds (s : State) : State := compress (compress (compress s))

/-- Compress one 64-bit little-endian message word `m` (`v3 ^= m; compress; v0 ^= m`). -/
@[inline]
def compressBlock (s : State) (m : UInt64) : State :=
  let s1 := { s with v3 := s.v3 ^^^ m }
  let s2 := cRounds s1
  { s2 with v0 := s2.v0 ^^^ m }

/-! ## Little-Endian Byte Packing -/

def asciiBytes (s : String) : List UInt8 :=
  s.toList.map fun c => UInt8.ofNat c.toNat

@[inline] def byteAt64 (buf : List UInt8) (i : Nat) : UInt64 := (buf.getD i 0).toUInt64

/-- Pack `len < 8` bytes starting at `start` into the low bytes of a `UInt64` in little-endian order. -/
def u8to64Le (buf : List UInt8) (start : Nat) : Nat → UInt64
  | 0 => 0
  | k + 1 => u8to64Le buf start k ||| (byteAt64 buf (start + k) <<< (UInt64.ofNat (8 * k)))

/-- Load an 8-byte little-endian `UInt64` starting at `start`. -/
@[inline]
def loadU64Le (buf : List UInt8) (start : Nat) : UInt64 :=
  byteAt64 buf start |||
  (byteAt64 buf (start + 1) <<< 8) |||
  (byteAt64 buf (start + 2) <<< 16) |||
  (byteAt64 buf (start + 3) <<< 24) |||
  (byteAt64 buf (start + 4) <<< 32) |||
  (byteAt64 buf (start + 5) <<< 40) |||
  (byteAt64 buf (start + 6) <<< 48) |||
  (byteAt64 buf (start + 7) <<< 56)

/-! ## Streaming `SipHasher13` -/

/-- Streaming state of `core::hash::sip::Hasher<Sip13Rounds>`. -/
structure SipHasher13 where
  k0 : UInt64
  k1 : UInt64
  length : Nat
  state : State
  tail : UInt64
  ntail : Nat
  deriving DecidableEq, Repr, Inhabited

namespace SipHasher13

@[inline]
def initState (k0 k1 : UInt64) : State :=
  { v0 := k0 ^^^ c0, v2 := k0 ^^^ c2, v1 := k1 ^^^ c1, v3 := k1 ^^^ c3 }

@[inline]
def newWithKeys (k0 k1 : UInt64) : SipHasher13 :=
  { k0, k1, length := 0, state := initState k0 k1, tail := 0, ntail := 0 }

@[inline] def new : SipHasher13 := newWithKeys 0 0

/-- Compress `count` consecutive 8-byte little-endian blocks starting at byte offset `i`. -/
def writeBlocks (s : State) (msg : List UInt8) (i : Nat) : Nat → State
  | 0 => s
  | count + 1 => writeBlocks (compressBlock s (loadU64Le msg i)) msg (i + 8) count

/-- Stream an arbitrary byte slice into `SipHasher13` (`Hasher::write`). -/
def write (h : SipHasher13) (msg : List UInt8) : SipHasher13 :=
  if h.ntail != 0 then
    if msg.length < 8 - h.ntail then
      let fill := u8to64Le msg 0 (min msg.length (8 - h.ntail))
      let tail' := h.tail ||| (fill <<< (UInt64.ofNat (8 * h.ntail)))
      { h with length := h.length + msg.length, tail := tail', ntail := h.ntail + msg.length }
    else
      let needed := 8 - h.ntail
      let fill := u8to64Le msg 0 (min msg.length needed)
      let tail' := h.tail ||| (fill <<< (UInt64.ofNat (8 * h.ntail)))
      let stateAfterTail := compressBlock h.state tail'
      let len := msg.length - needed
      let left := len % 8
      let nblocks := (len - left) / 8
      let stateAfterBlocks := writeBlocks stateAfterTail msg needed nblocks
      let endIdx := needed + nblocks * 8
      { h with
        length := h.length + msg.length
        state := stateAfterBlocks
        tail := u8to64Le msg endIdx left
        ntail := left }
  else
    let len := msg.length
    let left := len % 8
    let nblocks := (len - left) / 8
    let stateAfterBlocks := writeBlocks h.state msg 0 nblocks
    let endIdx := nblocks * 8
    { h with
      length := h.length + msg.length
      state := stateAfterBlocks
      tail := u8to64Le msg endIdx left
      ntail := left }

@[inline] def writeU8 (h : SipHasher13) (i : UInt8) : SipHasher13 := h.write [i]

@[inline]
def writeU16 (h : SipHasher13) (i : UInt16) : SipHasher13 :=
  h.write [i.toUInt8, (i >>> 8).toUInt8]

@[inline]
def writeU32 (h : SipHasher13) (i : UInt32) : SipHasher13 :=
  h.write [i.toUInt8, (i >>> 8).toUInt8, (i >>> 16).toUInt8, (i >>> 24).toUInt8]

@[inline]
def writeU64 (h : SipHasher13) (i : UInt64) : SipHasher13 :=
  h.write [
    i.toUInt8, (i >>> 8).toUInt8, (i >>> 16).toUInt8, (i >>> 24).toUInt8,
    (i >>> 32).toUInt8, (i >>> 40).toUInt8, (i >>> 48).toUInt8, (i >>> 56).toUInt8
  ]

/-- Hash a `&str` slice via `Hasher::write_str` (`write s` followed by `0xff`). -/
@[inline] def writeStr (h : SipHasher13) (s : List UInt8) : SipHasher13 := (h.write s).writeU8 0xff

@[inline] def writeString (h : SipHasher13) (s : String) : SipHasher13 := h.writeStr (asciiBytes s)

/-- Finalize `SipHasher13`, folding `(length & 0xff) << 56 | tail` with 1 c-round and 3 d-rounds. -/
@[inline]
def finish (h : SipHasher13) : UInt64 :=
  let b : UInt64 := (((UInt64.ofNat h.length) &&& 0xff) <<< 56) ||| h.tail
  let s1 := compressBlock h.state b
  let s2 := { s1 with v2 := s1.v2 ^^^ 0xff }
  let s3 := dRounds s2
  s3.v0 ^^^ s3.v1 ^^^ s3.v2 ^^^ s3.v3

end SipHasher13

/-! ## `ProtocolAddress` Hash and `hashbrown` Split -/

@[inline]
def hashBytes (k0 k1 : UInt64) (msg : List UInt8) : UInt64 :=
  ((SipHasher13.newWithKeys k0 k1).write msg).finish

@[inline]
def hashStr (k0 k1 : UInt64) (s : List UInt8) : UInt64 :=
  ((SipHasher13.newWithKeys k0 k1).writeStr s).finish

/-- Hash of `libsignal_core::ProtocolAddress { name, device_id }` under `RandomState` keys
`(k0, k1)`: writes `name`, the `0xff` string terminator, and `dev`, then finalizes. -/
@[inline]
def hashAddr (k0 k1 : UInt64) (name : List UInt8) (dev : UInt8) : UInt64 :=
  (((SipHasher13.newWithKeys k0 k1).writeStr name).writeU8 dev).finish

/-- `BitVec`-typed wrapper around `hashAddr` for binary specifications. -/
@[inline]
def hashAddrBv (k0 k1 : BitVec 64) (name : List (BitVec 8)) (dev : BitVec 8) : BitVec 64 :=
  (hashAddr (UInt64.ofBitVec k0) (UInt64.ofBitVec k1)
    (name.map UInt8.ofBitVec) (UInt8.ofBitVec dev)).toBitVec

/-- `hashbrown` primary hash `h1` (identity on 64-bit targets). -/
@[inline] def h1 (hash : UInt64) : UInt64 := hash

@[inline] def h1Bv (hash : BitVec 64) : BitVec 64 := hash

/-- `hashbrown` secondary control tag `h2` (`Tag::full`: top 7 bits `(hash >> 57) & 0x7f`). -/
@[inline] def h2 (hash : UInt64) : UInt8 := (hash >>> 57).toUInt8 &&& 0x7f

@[inline] def h2Bv (hash : BitVec 64) : BitVec 8 := (h2 (UInt64.ofBitVec hash)).toBitVec

/-- Initial `hashbrown` triangular-probe index `h1 hash &&& mask`. -/
@[inline] def probeStart (hash mask : UInt64) : UInt64 := h1 hash &&& mask

end CryptoVerification.E2E.InMem.SipHashModel
