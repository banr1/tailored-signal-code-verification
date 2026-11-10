/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.Accept
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ContractsExt
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import LibsignalBinary.Specifications.AsmConstants
import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth

/-!
# Cryptographic Primitive Bridge (`Crypto` ↔ `Initiator.Primitives`)

Connects the binary-hook primitives `C : Crypto` (`C.X` and `C.F`) to the functional-model
primitives `P : Initiator.Primitives` (`PrimitivesMatchCrypto`), and discharges
`PqxdhCalculateAgreementOk` (`0x3e5fc`) as well as `pqxdhHkdfExpandCellsSpec` (`0x1a874`) for
`k = 8` (`64` B) and `k = 10` (`80` B) on `trTrapProgAt`, `tripleRatchetProgAt`, and
`tripleRatchetProgAtExt`.
-/

@[expose] public section

set_option maxRecDepth 400000
set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.Initiator

/-! ## 1. Cryptographic Primitive Compatibility (`PrimitivesMatchCrypto` & `modelPrims`) -/

/-- Convert trusted `SignalPqxdh.Primitives` (such as `modelPrims X W`) to
`Initiator.Primitives`. -/
def ofSignalPqxdhPrimitives (P : SignalPqxdh.Primitives) : Primitives where
  x25519 := P.x25519
  x25519Base := P.x25519Base
  isCanonical := P.isCanonical
  sigPkGen := P.sigPkGen
  sigSign := P.sigSign
  sigVerify := P.sigVerify
  sha512 := P.sha512
  scalarMul := P.scalarMul
  scalarAdd := P.scalarAdd
  scalarFromBytesModOrder := P.scalarFromBytesModOrder
  scalarFromWide := P.scalarFromWide
  montToEd := P.montToEd
  isTorsionFree := P.isTorsionFree
  edNeg := P.edNeg
  doubleScalarMulBasepoint := P.doubleScalarMulBasepoint
  compress := P.compress
  kemKeyGen := P.kemKeyGen
  kemEncaps := P.kemEncaps
  kemDecaps := P.kemDecaps
  hkdfDerive96 := fun s =>
    let dk := P.hkdfDerive96 s
    ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩
  rootCreateChain := P.rootCreateChain
  chainKdfSeed := P.chainKdfSeed
  chainKdfNext := P.chainKdfNext
  spqrInitSend := P.spqrInitSend
  spqrInitRecv := P.spqrInitRecv
  deriveMsgKeys := fun s salt =>
    let mk := P.deriveMsgKeys s salt
    ⟨mk.cipherKey, mk.macKey, mk.iv⟩
  aeadEnc := fun mk ad pt =>
    P.aeadEnc ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad pt
  aeadDec := fun mk ad ct =>
    P.aeadDec ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad ct
  pow8 := P.pow8
  isValidDhTriple := P.isValidDhTriple
  sha256Compress := P.sha256Compress
  sha512Compress := P.sha512Compress
  aesEncBlock := P.aesEncBlock
  aesDecBlock := P.aesDecBlock

instance : Coe SignalPqxdh.Primitives Initiator.Primitives := ⟨ofSignalPqxdhPrimitives⟩

/-- Compatibility predicate stating that `P.x25519` and `P.sha256Compress` match the binary-hook
primitives `C.X` and `C.F` under `PqxdhModelLink`'s trusted byte/state encodings (`u8Vec`, `vecU8`,
`sha256StateOf`, `sha256StateBytes`, `ofU8`). -/
structure PrimitivesMatchCrypto (P : Initiator.Primitives) (C : Crypto) : Prop where
  x25519_eq : ∀ a pk : Bytes,
    P.x25519 a pk = vecU8 (C.X (Ratchet.clampScalar (u8Vec 32 a)) (u8Vec 32 pk))
  sha256Compress_eq : ∀ st blk : Bytes,
    P.sha256Compress st blk = sha256StateBytes (C.F (sha256StateOf st) (ofU8 blk))

/-- `modelPrims X W` unconditionally satisfies `PrimitivesMatchCrypto` against `W.C`. -/
theorem primitivesMatchCrypto_modelPrims (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    PrimitivesMatchCrypto (modelPrims X W) W.C where
  x25519_eq _ _ := rfl
  sha256Compress_eq _ _ := rfl

/-! ## 2. Byte, Vector, and SHA-256 State Bridge Lemmas -/

@[simp]
theorem bytesToBv8_length (bs : Bytes) : (bytesToBv8 bs).length = bs.length := by
  simp [bytesToBv8]

@[simp]
theorem toU8_length (bs : List (BitVec 8)) : (toU8 bs).length = bs.length := by
  simp [toU8]

@[simp]
theorem ofU8_length (bs : Bytes) : (ofU8 bs).length = bs.length := by
  simp [ofU8]

theorem bv8_of_bv8_toNat (b : BitVec 8) : BitVec.ofNat 8 b.toNat = b := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem bytesToBv8_eq_ofU8 (bs : Bytes) : bytesToBv8 bs = ofU8 bs := by
  unfold bytesToBv8 ofU8
  congr 1; funext b
  rcases b with ⟨v⟩
  simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem toU8_ofU8 (bs : Bytes) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [toU8, ofU8, List.map_cons] at *
    rw [ih]

theorem ofU8_toU8 (bs : List (BitVec 8)) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [toU8, ofU8, List.map_cons] at *
    rw [ih]

theorem toU8_bytesToBv8 (bs : Bytes) : toU8 (bytesToBv8 bs) = bs := by
  rw [bytesToBv8_eq_ofU8, toU8_ofU8]

theorem bytesToBv8_toU8 (bs : List (BitVec 8)) : bytesToBv8 (toU8 bs) = bs := by
  rw [bytesToBv8_eq_ofU8, ofU8_toU8]

theorem bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    bytesToBv8 (vecU8 v) = v.toList :=
  bytesToBv8_toU8 v.toList

@[simp]
theorem vecU8_length {n : Nat} (v : List.Vector (BitVec 8) n) :
    (vecU8 v).length = n := by
  simp [vecU8, toU8]

theorem u8Vec_toList_of_length {n : Nat} {bs : Bytes} (h : bs.length = n) :
    (u8Vec n bs).toList = bytesToBv8 bs := by
  subst h
  dsimp only [u8Vec, fitVec, List.Vector.toList]
  rw [← bytesToBv8_eq_ofU8, ← bytesToBv8_length bs,
    List.take_append_of_le_length (Nat.le_refl _),
    List.take_of_length_le (Nat.le_refl _)]

theorem u8Vec_eq_of_length {n : Nat} {bs : Bytes} (h : bs.length = n) :
    u8Vec n bs = ⟨bytesToBv8 bs, by rw [bytesToBv8_length, h]⟩ :=
  Subtype.ext (u8Vec_toList_of_length h)

theorem bytesToBv8_take (n : Nat) (bs : Bytes) :
    bytesToBv8 (bs.take n) = (bytesToBv8 bs).take n := by
  unfold bytesToBv8
  exact List.map_take

theorem bytesToBv8_drop (n : Nat) (bs : Bytes) :
    bytesToBv8 (bs.drop n) = (bytesToBv8 bs).drop n := by
  unfold bytesToBv8
  exact List.map_drop

theorem bytesToBv8_reverse (bs : Bytes) :
    bytesToBv8 bs.reverse = (bytesToBv8 bs).reverse := by
  unfold bytesToBv8
  exact List.map_reverse

theorem beWord32_toBEBytes4 (w : BitVec 32) :
    beWord 32 (HMAC.toBEBytes 4 w) 0 = w := by
  change ((((0#32 <<< 8 ||| (w.extractLsb' 24 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 16 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 8 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 0 8).zeroExtend 32) = w
  bv_bits

theorem sha256StateBytes_length : ∀ h : ShaState, (sha256StateBytes h).length = 32
  | ⟨[_w0, _w1, _w2, _w3, _w4, _w5, _w6, _w7], _⟩ => rfl

theorem fitBytesRef_32_sha256StateBytes (h : ShaState) :
    fitBytesRef 32 (sha256StateBytes h) = sha256StateBytes h :=
  fitBytesRef_of_length_eq (sha256StateBytes_length h)

theorem sha256StateOf_sha256StateBytes : ∀ h : ShaState,
    sha256StateOf (sha256StateBytes h) = h
  | ⟨[w0, w1, w2, w3, w4, w5, w6, w7], _⟩ => by
    apply Subtype.ext
    unfold sha256StateOf sha256StateBytes
    rw [ofU8_toU8]
    change [beWord 32 (HMAC.toBEBytes 4 w0) 0,
            beWord 32 (HMAC.toBEBytes 4 w1) 0,
            beWord 32 (HMAC.toBEBytes 4 w2) 0,
            beWord 32 (HMAC.toBEBytes 4 w3) 0,
            beWord 32 (HMAC.toBEBytes 4 w4) 0,
            beWord 32 (HMAC.toBEBytes 4 w5) 0,
            beWord 32 (HMAC.toBEBytes 4 w6) 0,
            beWord 32 (HMAC.toBEBytes 4 w7) 0] =
      [w0, w1, w2, w3, w4, w5, w6, w7]
    rw [beWord32_toBEBytes4, beWord32_toBEBytes4, beWord32_toBEBytes4, beWord32_toBEBytes4,
        beWord32_toBEBytes4, beWord32_toBEBytes4, beWord32_toBEBytes4, beWord32_toBEBytes4]

theorem bytesToBv8_sha256StateBytes (h : ShaState) :
    bytesToBv8 (sha256StateBytes h) = h.toList.flatMap (HMAC.toBEBytes 4) := by
  unfold sha256StateBytes
  exact bytesToBv8_toU8 _

theorem bytesToBv8_revWords32 (bs : Bytes) :
    bytesToBv8 (revWords32 bs) =
      ((bytesToBv8 bs).drop  0 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop  4 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop  8 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop 12 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop 16 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop 20 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop 24 |>.take 4).reverse ++
      ((bytesToBv8 bs).drop 28 |>.take 4).reverse := by
  unfold revWords32
  simp only [bytesToBv8_append, bytesToBv8_reverse, bytesToBv8_take, bytesToBv8_drop]
  rfl

theorem bytesToBv8_revWords32_sha256StateBytes (h : ShaState) :
    bytesToBv8 (revWords32 (sha256StateBytes h)) = LibsignalHmac.shaStateBytes h := by
  rw [bytesToBv8_revWords32, bytesToBv8_sha256StateBytes]
  match h with
  | ⟨[_w0, _w1, _w2, _w3, _w4, _w5, _w6, _w7], _⟩ => rfl

theorem sha256InitState_eq_sha256StateBytes :
    sha256InitState = sha256StateBytes HMAC.sha256IV := rfl

theorem sha256Step_sha256StateBytes {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (h : ShaState) (blk : Bytes) :
    sha256Step P (sha256StateBytes h) blk = sha256StateBytes (C.F h (bytesToBv8 blk)) := by
  unfold sha256Step
  rw [fitBytesRef_32_sha256StateBytes, hP.sha256Compress_eq, sha256StateOf_sha256StateBytes,
    ← bytesToBv8_eq_ofU8, fitBytesRef_32_sha256StateBytes]

theorem foldl_sha256Step_sha256StateBytes {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (blks : List Bytes) (h : ShaState) :
    blks.foldl (sha256Step P) (sha256StateBytes h) =
      sha256StateBytes ((blks.map bytesToBv8).foldl C.F h) := by
  induction blks generalizing h with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [sha256Step_sha256StateBytes hP, ih]

/-! ## 3. SHA-256 Padding, Chunking, HMAC, and HKDF Bridge Lemmas -/

theorem zeroPadLen_sha256_fin : ∀ m : Fin 64,
    (if (m.val + 9) % 64 == 0 then 0 else 64 - (m.val + 9) % 64) = (119 - m.val) % 64 := by
  decide

theorem zeroPadLen_sha256_eq (n : Nat) :
    (if (n + 9) % 64 == 0 then 0 else 64 - (n + 9) % 64) = (119 - n % 64) % 64 := by
  rw [Nat.add_mod n 9 64]
  exact zeroPadLen_sha256_fin ⟨n % 64, Nat.mod_lt n (by decide)⟩

theorem bv8_of_uint64_toUInt8 (u : UInt64) :
    BitVec.ofNat 8 u.toUInt8.toNat = u.toBitVec.setWidth 8 := by
  rcases u with ⟨v⟩
  exact bv8_of_bv8_toNat (v.setWidth 8)

theorem bytesToBv8_u64_be (u : UInt64) :
    bytesToBv8
      [ ((u >>> 56) &&& 0xFF).toUInt8
      , ((u >>> 48) &&& 0xFF).toUInt8
      , ((u >>> 40) &&& 0xFF).toUInt8
      , ((u >>> 32) &&& 0xFF).toUInt8
      , ((u >>> 24) &&& 0xFF).toUInt8
      , ((u >>> 16) &&& 0xFF).toUInt8
      , ((u >>>  8) &&& 0xFF).toUInt8
      , (u          &&& 0xFF).toUInt8 ] =
      HMAC.toBEBytes 8 u.toBitVec := by
  rcases u with ⟨w⟩
  simp only [bytesToBv8, List.map, bv8_of_uint64_toUInt8, UInt64.toBitVec_and,
    UInt64.toBitVec_shiftRight]
  change [ (w >>> 56#64 &&& 0xFF#64).setWidth 8,
           (w >>> 48#64 &&& 0xFF#64).setWidth 8,
           (w >>> 40#64 &&& 0xFF#64).setWidth 8,
           (w >>> 32#64 &&& 0xFF#64).setWidth 8,
           (w >>> 24#64 &&& 0xFF#64).setWidth 8,
           (w >>> 16#64 &&& 0xFF#64).setWidth 8,
           (w >>>  8#64 &&& 0xFF#64).setWidth 8,
           (w           &&& 0xFF#64).setWidth 8 ] =
    [ w.extractLsb' 56 8,
      w.extractLsb' 48 8,
      w.extractLsb' 40 8,
      w.extractLsb' 32 8,
      w.extractLsb' 24 8,
      w.extractLsb' 16 8,
      w.extractLsb'  8 8,
      w.extractLsb'  0 8 ]
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits
  congr 1; · bv_bits

theorem bytesToBv8_encodeBitLen64BE (n : Nat) :
    bytesToBv8 (encodeBitLen64BE n) = HMAC.toBEBytes 8 (BitVec.ofNat 64 (8 * n)) := by
  unfold encodeBitLen64BE
  rw [bytesToBv8_u64_be]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toBitVec_mul, Nat.toUInt64, BitVec.toNat_ofNat, Nat.mul_comm]

theorem bytesToBv8_replicate (k : Nat) (b : UInt8) :
    bytesToBv8 (List.replicate k b) = List.replicate k b.toBitVec := by
  simp [bytesToBv8]

theorem bytesToBv8_sha256Pad (msg : Bytes) :
    bytesToBv8 (Initiator.sha256Pad msg) = HMAC.sha256Pad (bytesToBv8 msg) := by
  unfold Initiator.sha256Pad HMAC.sha256Pad
  dsimp only
  rw [zeroPadLen_sha256_eq, bytesToBv8_append, bytesToBv8_append, bytesToBv8_append,
    bytesToBv8_replicate, bytesToBv8_encodeBitLen64BE, bytesToBv8_length]
  rfl

theorem map_bytesToBv8_chunkBlocks_64 (bs : Bytes) :
    (chunkBlocks 64 bs).map bytesToBv8 = HMAC.chunks64 (bytesToBv8 bs) := by
  unfold chunkBlocks HMAC.chunks64
  apply List.ext_getElem
  · simp [bytesToBv8_length]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn,
      bytesToBv8_drop, bytesToBv8_take]
    rw [Nat.mul_comm]

theorem bytesToBv8_sha256Ref {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (msg : Bytes) :
    bytesToBv8 (sha256Ref P msg) = HMAC.sha256With C.F (bytesToBv8 msg) := by
  unfold sha256Ref HMAC.sha256With
  dsimp only
  rw [sha256InitState_eq_sha256StateBytes, foldl_sha256Step_sha256StateBytes hP,
    fitBytesRef_32_sha256StateBytes, bytesToBv8_sha256StateBytes,
    map_bytesToBv8_chunkBlocks_64, bytesToBv8_sha256Pad]

theorem bytesToBv8_fitBytesRef_of_le {n : Nat} {bs : Bytes} (h : bs.length ≤ n) :
    bytesToBv8 (fitBytesRef n bs) =
      bytesToBv8 bs ++ List.replicate (n - (bytesToBv8 bs).length) 0#8 := by
  unfold fitBytesRef
  rw [List.take_of_length_le h, bytesToBv8_append, bytesToBv8_replicate, bytesToBv8_length]
  rfl

theorem bv8_xor_u8 (x b : UInt8) :
    BitVec.ofNat 8 (x ^^^ b).toNat = BitVec.ofNat 8 x.toNat ^^^ b.toBitVec := by
  rcases x with ⟨x⟩
  rcases b with ⟨b⟩
  change BitVec.ofNat 8 (x ^^^ b).toNat = BitVec.ofNat 8 x.toNat ^^^ b
  rw [bv8_of_bv8_toNat, bv8_of_bv8_toNat]

theorem bytesToBv8_xorBytes_replicate (xs : Bytes) (b : UInt8) :
    bytesToBv8 (xorBytes xs (List.replicate xs.length b)) =
      (bytesToBv8 xs).map (· ^^^ b.toBitVec) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change BitVec.ofNat 8 (x ^^^ b).toNat ::
      bytesToBv8 (xorBytes xs (List.replicate xs.length b)) =
      (BitVec.ofNat 8 x.toNat ^^^ b.toBitVec) :: (bytesToBv8 xs).map (· ^^^ b.toBitVec)
    rw [bv8_xor_u8, ih]

theorem bytesToBv8_xorBytes_replicate_of_length {xs : Bytes} {k : Nat} (b : UInt8)
    (h : xs.length = k) :
    bytesToBv8 (xorBytes xs (List.replicate k b)) =
      (bytesToBv8 xs).map (· ^^^ b.toBitVec) := by
  subst h
  exact bytesToBv8_xorBytes_replicate xs b

theorem bytesToBv8_pqxdhHmacKeyBlock {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (key : Bytes) :
    bytesToBv8 (pqxdhHmacKeyBlock P key) =
      let k' := if 64 < (bytesToBv8 key).length then
        HMAC.sha256With C.F (bytesToBv8 key) else bytesToBv8 key
      k' ++ List.replicate (64 - k'.length) 0#8 := by
  unfold pqxdhHmacKeyBlock
  have hle : (if key.length > 64 then sha256Ref P key else key).length ≤ 64 := by
    split
    · rw [sha256Ref_length]; decide
    · omega
  rw [bytesToBv8_fitBytesRef_of_le hle]
  split <;> rename_i hk
  · have hk' : 64 < (bytesToBv8 key).length := by rwa [bytesToBv8_length]
    simp only [hk', ↓reduceIte, bytesToBv8_sha256Ref hP]
  · have hk' : ¬ (64 < (bytesToBv8 key).length) := by rwa [bytesToBv8_length]
    simp only [hk', ↓reduceIte]

theorem bytesToBv8_pqxdhHmacKeyBlock_of_le {key : Bytes} (P : Primitives)
    (hk : key.length ≤ 64) :
    bytesToBv8 (pqxdhHmacKeyBlock P key) = hmacKeyBlock (bytesToBv8 key) := by
  unfold pqxdhHmacKeyBlock hmacKeyBlock
  have hnot : ¬ (key.length > 64) := by omega
  simp only [hnot, ↓reduceIte, bytesToBv8_fitBytesRef_of_le hk]

theorem pqxdhHmacInnerInit_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) {key : Bytes} (hk : key.length ≤ 64) :
    pqxdhHmacInnerInit P key = sha256StateBytes (hmacInnerInit C.F (bytesToBv8 key)) := by
  unfold pqxdhHmacInnerInit hmacInnerInit
  have hlen : (pqxdhHmacKeyBlock P key).length = 64 := fitBytesRef_length 64 _
  rw [sha256InitState_eq_sha256StateBytes, sha256Step_sha256StateBytes hP,
    bytesToBv8_xorBytes_replicate_of_length 0x36 hlen, bytesToBv8_pqxdhHmacKeyBlock_of_le P hk]
  rfl

theorem pqxdhHmacOuterInit_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) {key : Bytes} (hk : key.length ≤ 64) :
    pqxdhHmacOuterInit P key = sha256StateBytes (hmacOuterInit C.F (bytesToBv8 key)) := by
  unfold pqxdhHmacOuterInit hmacOuterInit
  have hlen : (pqxdhHmacKeyBlock P key).length = 64 := fitBytesRef_length 64 _
  rw [sha256InitState_eq_sha256StateBytes, sha256Step_sha256StateBytes hP,
    bytesToBv8_xorBytes_replicate_of_length 0x5c hlen, bytesToBv8_pqxdhHmacKeyBlock_of_le P hk]
  rfl

theorem pqxdhHmacStateFullAt_eq (a : BitVec 64) (innerSt : ShaState) (nBlocks : Nat)
    (outerSt : ShaState) (tail : List (BitVec 8)) :
    pqxdhHmacStateFullAt a (sha256StateBytes innerSt) nBlocks (sha256StateBytes outerSt) tail =
      hmacStateAt a innerSt nBlocks outerSt tail := by
  unfold pqxdhHmacStateFullAt hmacStateAt
  rw [bytesToBv8_revWords32_sha256StateBytes, bytesToBv8_revWords32_sha256StateBytes]

theorem pqxdhHmacCoreAt_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (a : BitVec 64) {key : Bytes} (hk : key.length ≤ 64)
    (msg : List (BitVec 8)) :
    pqxdhHmacCoreAt P a key msg = hmacCoreAt C.F a (bytesToBv8 key) msg := by
  unfold pqxdhHmacCoreAt hmacCoreAt
  rw [pqxdhHmacInnerInit_eq hP hk, pqxdhHmacOuterInit_eq hP hk, pqxdhHmacStateFullAt_eq]

theorem pqxdhHmacStateAt_eq {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (a : BitVec 64) {key : Bytes} (hk : key.length ≤ 64) :
    pqxdhHmacStateAt P a key = hmacCoreAt C.F a (bytesToBv8 key) [] :=
  pqxdhHmacCoreAt_eq hP a hk []

theorem bytesToBv8_hmacSha256Ref {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (key msg : Bytes) :
    bytesToBv8 (hmacSha256Ref P key msg) = HMAC.hmacWith C.F (bytesToBv8 key) (bytesToBv8 msg) := by
  unfold hmacSha256Ref HMAC.hmacWith
  dsimp only
  have hkpad_len :
      (fitBytesRef 64 (if key.length > 64 then sha256Ref P key else key)).length = 64 :=
    fitBytesRef_length 64 _
  rw [bytesToBv8_sha256Ref hP, bytesToBv8_append, bytesToBv8_sha256Ref hP, bytesToBv8_append,
    bytesToBv8_xorBytes_replicate_of_length 0x5c hkpad_len,
    bytesToBv8_xorBytes_replicate_of_length 0x36 hkpad_len]
  have hk0 :
      bytesToBv8 (fitBytesRef 64 (if key.length > 64 then sha256Ref P key else key)) =
        (let k' := if 64 < (bytesToBv8 key).length then
          HMAC.sha256With C.F (bytesToBv8 key) else bytesToBv8 key
         k' ++ List.replicate (64 - k'.length) 0#8) :=
    bytesToBv8_pqxdhHmacKeyBlock hP key
  rw [hk0]
  rfl

theorem bytesToBv8_hkdfExtractRef_none {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (ikm : Bytes) :
    bytesToBv8 (hkdfExtractRef P none ikm) = HKDF.hkdfExtract C.F none (bytesToBv8 ikm) := by
  unfold hkdfExtractRef HKDF.hkdfExtract
  dsimp only
  rw [bytesToBv8_hmacSha256Ref hP, bytesToBv8_replicate]
  rfl

theorem bytesToBv8_hkdfExtractRef_some {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) {salt : Bytes} (hs : salt.length = 32) (ikm : Bytes) :
    bytesToBv8 (hkdfExtractRef P (some salt) ikm) =
      HKDF.hkdfExtract C.F (some (u8Vec 32 salt)) (bytesToBv8 ikm) := by
  unfold hkdfExtractRef HKDF.hkdfExtract
  simp only [Option.map_some, Option.getD_some, bytesToBv8_hmacSha256Ref hP,
    u8Vec_toList_of_length hs]

theorem hkdfExpand_96_eq (F : ShaState → List (BitVec 8) → ShaState)
    (prk info : List (BitVec 8)) :
    hkdfExpand F prk info 96 =
      Expand.t1 F prk info ++ Expand.t2 F prk info ++ Expand.t3 F prk info := by
  dsimp only [hkdfExpand]
  have h3 : (96 + 31) / 32 = 3 := rfl
  have hblocks : (hkdfBlocks F prk info 3).flatten =
      Expand.t1 F prk info ++ Expand.t2 F prk info ++ Expand.t3 F prk info := by
    simp [hkdfBlocks, Expand.t1, Expand.t2, Expand.t3, List.append_assoc]
  rw [h3, hblocks, List.take_of_length_le]
  simp [Expand.t1, Expand.t2, Expand.t3]

theorem bytesToBv8_t1 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hmacSha256Ref P prk (info ++ [0x01])) =
      Expand.t1 C.F (bytesToBv8 prk) (bytesToBv8 info) := by
  unfold Expand.t1
  rw [bytesToBv8_hmacSha256Ref hP, bytesToBv8_append]
  rfl

theorem bytesToBv8_t2 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hmacSha256Ref P prk (hmacSha256Ref P prk (info ++ [0x01]) ++ info ++ [0x02])) =
      Expand.t2 C.F (bytesToBv8 prk) (bytesToBv8 info) := by
  unfold Expand.t2
  rw [bytesToBv8_hmacSha256Ref hP, bytesToBv8_append, bytesToBv8_append, bytesToBv8_t1 hP]
  rfl

theorem bytesToBv8_t3 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hmacSha256Ref P prk
      (hmacSha256Ref P prk (hmacSha256Ref P prk (info ++ [0x01]) ++ info ++ [0x02]) ++
        info ++ [0x03])) =
      Expand.t3 C.F (bytesToBv8 prk) (bytesToBv8 info) := by
  unfold Expand.t3
  rw [bytesToBv8_hmacSha256Ref hP, bytesToBv8_append, bytesToBv8_append, bytesToBv8_t2 hP]
  rfl

theorem bytesToBv8_hkdfExpandRef_64 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hkdfExpandRef P prk info 64) =
      hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64 := by
  unfold hkdfExpandRef
  dsimp only
  rw [bytesToBv8_take, bytesToBv8_append, bytesToBv8_append,
    bytesToBv8_t1 hP, bytesToBv8_t2 hP, bytesToBv8_t3 hP, Expand.hkdfExpand_64_eq]
  have hlen : (Expand.t1 C.F (bytesToBv8 prk) (bytesToBv8 info) ++
      Expand.t2 C.F (bytesToBv8 prk) (bytesToBv8 info)).length = 64 := by
    simp [Expand.t1_length, Expand.t2_length]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

theorem bytesToBv8_hkdfExpandRef_80 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hkdfExpandRef P prk info 80) =
      hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80 := by
  unfold hkdfExpandRef
  dsimp only
  rw [bytesToBv8_take, bytesToBv8_append, bytesToBv8_append,
    bytesToBv8_t1 hP, bytesToBv8_t2 hP, bytesToBv8_t3 hP, Expand.hkdfExpand_80_eq]
  have hlen : (Expand.t1 C.F (bytesToBv8 prk) (bytesToBv8 info) ++
      Expand.t2 C.F (bytesToBv8 prk) (bytesToBv8 info)).length = 64 := by
    simp [Expand.t1_length, Expand.t2_length]
  rw [List.take_append, List.take_of_length_le (by omega), hlen]

theorem bytesToBv8_hkdfExpandRef_96 {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (prk info : Bytes) :
    bytesToBv8 (hkdfExpandRef P prk info 96) =
      hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 96 := by
  unfold hkdfExpandRef
  dsimp only
  rw [bytesToBv8_take, bytesToBv8_append, bytesToBv8_append,
    bytesToBv8_t1 hP, bytesToBv8_t2 hP, bytesToBv8_t3 hP, hkdfExpand_96_eq]
  rw [List.take_of_length_le]
  simp [Expand.t1_length, Expand.t2_length, Expand.t3_length]

/-! ## 4. Discharging `PqxdhCalculateAgreementOk` (`0x3e6e0`) -/

theorem byte3_memRegion7_entails_hi56 (a : BitVec 64) :
    (a ↦₈ 3#8) ∗ memRegion (a + 1#64) 7 ⊢
      ∃∗ hi : BitVec 56, a ↦₆₄ (hi ++ 3#8) := by
  rw [memRegion_eq_exists_bytes (a + 1#64) 7 (by decide), sepExists_sepConj_right]
  refine Entails.sepExists_elim fun bs => ?_
  rw [sepConj_comm (a ↦₈ 3#8), sepConj_assoc]
  refine Entails.pure_left fun hlen => ?_
  match bs, hlen with
  | [b1, b2, b3, b4, b5, b6, b7], _ =>
    rw [sepConj_comm, ← pointsToBytes_cons, pointsToBytes8_eq_pointsTo64]
    exact Entails.sepExists_right (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1) (Entails.refl _)

theorem boxU8At_entails_boxSliceU8 (A : RustAlloc) (a : BitVec 64) {bs : List (BitVec 8)}
    (hne : bs ≠ []) :
    (∃∗ ptr : BitVec 64, boxU8At A a ptr bs) ⊢ boxSliceU8 A a bs := by
  dsimp only [boxU8At, boxSliceU8]
  refine Entails.sepExists_elim fun ptr => ?_
  simp only [hne, ↓reduceIte]
  rw [show (a + asm64% boxSliceLenOff) = a + 8#64 from rfl]
  refine Entails.trans ?_ (Entails.sepExists_right ptr (Entails.refl _))
  have hcomm :
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗ A.live ptr bs.length 1 ∗ (ptr ↦ₛ bs) =
      ⌜ptr ≠ 0 ∧ bs.length < 2 ^ 63⌝ ∗
        ((a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗ A.live ptr bs.length 1) := by
    ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun h => ?_
  rw [← sepConj_assoc]
  exact Entails.pure_right h.1 (Entails.refl _)

theorem calculateAgreementResultAt_entails_pqxdh {P : Primitives} {C : Crypto}
    (hP : PrimitivesMatchCrypto P C) (A : RustAlloc) (r : BitVec 64)
    (ourSk32 theirPk32 : Bytes) :
    let our : PrivateKey := ⟨u8Vec 32 ourSk32⟩
    let their : PublicKey := ⟨u8Vec 32 theirPk32⟩
    calculateAgreementResultAt A r (calculateAgreement C.X their our) ⊢
      pqxdhCalculateAgreementResultAt P A r ourSk32 theirPk32 := by
  dsimp only
  let ss := C.X (Ratchet.clampScalar (u8Vec 32 ourSk32)) (u8Vec 32 theirPk32)
  have hx25519 : P.x25519 ourSk32 theirPk32 = vecU8 ss := hP.x25519_eq ourSk32 theirPk32
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement C.X ⟨u8Vec 32 theirPk32⟩ ⟨u8Vec 32 ourSk32⟩ = none :=
      Keys.calculateAgreement_eq_none hzero
    have hp_zero : P.x25519 ourSk32 theirPk32 = List.replicate 32 0 := by
      rw [hx25519, ← toU8_bytesToBv8 (List.replicate 32 0), bytesToBv8_replicate]
      unfold vecU8
      rw [hzero]
      rfl
    rw [hres, pqxdhCalculateAgreementResultAt]
    simp only [hp_zero, ↓reduceIte, calculateAgreementResultAt]
    have hsplit : memRegion (r + 9#64) 15 =
        memRegion (r + 8#64 + 1#64) 7 ∗ (∃∗ u2 : BitVec 64, (r + 16#64) ↦₆₄ u2) := by
      rw [memRegion_split (r + 9#64) 7 8 (by decide), memRegion_eight]
      have h9 : r + 8#64 + 1#64 = r + 9#64 := by bv_arith
      have h16 : r + 9#64 + 7#64 = r + 16#64 := by bv_arith
      rw [h9, h16]
    rw [hsplit, ← sepConj_assoc ((r + 8#64) ↦₈ 3#8)]
    exact sepConj_mono_right (sepConj_mono_left (byte3_memRegion7_entails_hi56 (r + 8#64)))
  · have hres : calculateAgreement C.X ⟨u8Vec 32 theirPk32⟩ ⟨u8Vec 32 ourSk32⟩ = some ss :=
      Keys.calculateAgreement_eq_some hzero
    have hp_ne : P.x25519 ourSk32 theirPk32 ≠ List.replicate 32 0 := by
      intro h
      apply hzero
      have hb := congrArg bytesToBv8 h
      rw [hx25519, bytesToBv8_vecU8, bytesToBv8_replicate] at hb
      exact hb
    have hss_ne : ss.toList ≠ [] := by
      have hlen : ss.toList.length = 32 := List.Vector.toList_length ss
      intro h; rw [h] at hlen; contradiction
    rw [hres, pqxdhCalculateAgreementResultAt, ite_eq_right_iff.mpr fun h => (hp_ne h).elim]
    dsimp only [calculateAgreementResultAt]
    rw [hx25519, bytesToBv8_vecU8]
    exact sepConj_mono_right (boxU8At_entails_boxSliceU8 A (r + 8#64) hss_ne)

section CalculateAgreementRodata

open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre
  AgreeStateSimp.readReg_setPC_pre AgreeStateSimp.readReg_setMem_setPC_pre
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  calculateAgreement_fnOff ctEq_fnOff dh_fnOff sharedDrop_fnOff staticDrop_fnOff
  handleAllocError_fnOff
  libsignalSessionCode_fnOff_0x3e6e0
  libsignalSessionCode_fnOff_0x3eda8
  (ls_stub% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")
  (ls_stub% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "alloc::alloc::handle_alloc_error")
  (ls_hook% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")
  (ls_hook% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_hook% "alloc::alloc::handle_alloc_error")

theorem calculateAgreement_rodata_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : CtEqROOk_trap img.base C abs)
    (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr calculateAgreementName)
      { calculateAgreementSpec C.X A with
        pre := fun x s =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpec C.X A).pre x s
        post := fun x s0 sf =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpec C.X A).post x s0 sf } := by
  have hfn : libsignalSessionCode.fnOff calculateAgreementName = 0x3e6e0 :=
    calculateAgreement_fnOff
  have hadrp : ((trTrapProgAt img.base C abs).fnAddr calculateAgreementName + 104#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x3e748 0x3e74c - 0x3e000) =
      img.base + bv% (ls_xref% 0x3e748 0x3e74c) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    bv_arith
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics (trTrapExterns C abs)) hfn 0x3e6e0 224
  have h_dh := dh_ok_at_tripleRatchet_trap (b := img.base) (C := C) (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, dh_fnOff])
  have h_shdrop := sharedDrop_ok_at_tripleRatchet_trap (b := img.base) (C := C) (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off%
      "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, sharedDrop_fnOff])
  have h_cteq := ctEqROAllocStack_ok_at_tripleRatchet_trap (b := img.base) (C := C) (abs := abs) hct (name := calculateAgreementName) (k := 1736)
    (by rw [calculateAgreement_fnOff, ctEq_fnOff])
  have h_shim := noAllocShim_ok_at_trap (b := img.base) (C := C) (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have h_alloc := alloc_ok_at_norm_trap (b := img.base) (C := C) (abs := abs) hA (name := calculateAgreementName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  have h_stdrop := staticDrop_ok_at_tripleRatchet_trap (b := img.base) (C := C) (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off%
      "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, staticDrop_fnOff])
  have h_pan := panic_at_handle_alloc_error2_trap (b := img.base) (C := C) (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, handleAllocError_fnOff])
  dsimp only [trTrapProgAt] at h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop h_pan hadrp ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))).fnAddr
      calculateAgreementName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (trTrapExterns C abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  subst h_1 h_2 h
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := C.X (Ratchet.clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (Ratchet.clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq
      (List.Vector.toList_length (Ratchet.clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreement_split s0.sp,
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP (mid := entry + 120#64) ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  wp_call h_dh
    (s0.sp - 160#64, Ratchet.clampScalar our.bytes, s0.sp - 64#64, their.bytes, s0.sp - 96#64)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  wp_call h_shdrop (s0.sp - 96#64)
  wp_steps
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq
    (s0.sp - 128#64, ss.toList, img.base + bv% (ls_xref% 0x3e748 0x3e74c), List.replicate 32 0#8, s0.sp - 160#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement C.X their our = none := calculateAgreement_eq_none hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    wp_call h_stdrop (s0.sp - 160#64)
    wp_steps
    refine SepWP.fold (rejoin_stack_calculateAgreement s0.sp hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement C.X their our = some ss := calculateAgreement_eq_some hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP (mid := entry + 160#64) ?_
    wp_steps
    wp_call h_shim ()
    wp_steps
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 160#64) (by wp_norm_lhs)
      (fun halloc htr_alloc => ?_) (fun halloc halign htr_alloc => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0)) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.rw_pre (by
        rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
          memRegion_32_cells,
          ← hss_sp128]) ?_
      sep_elim_exists
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
      refine SepWP.fold hclamp_mem (by sep_focus) ?_
      wp_call h_stdrop (s0.sp - 160#64)
      wp_steps
      refine SepWP.fold (rejoin_stack_calculateAgreement s0.sp hzero_len hss_len hzero_len
        (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (calculateAgreementResultAt_some_intro A (s0.readReg64 (.gpr 8#5))
        _ ss halloc) (by sep_focus) ?_
      rw [hres]
      wp_done

theorem calculateAgreement_rodata_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : CtEqROOk img.base C ctl abs)
    (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr calculateAgreementName)
      { calculateAgreementSpec C.X A with
        pre := fun x s =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpec C.X A).pre x s
        post := fun x s0 sf =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpec C.X A).post x s0 sf } := by
  have hfn : libsignalSessionCode.fnOff calculateAgreementName = 0x3e6e0 :=
    calculateAgreement_fnOff
  have hadrp : ((tripleRatchetProgAt img.base C ctl abs).fnAddr calculateAgreementName + 104#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x3e748 0x3e74c - 0x3e000) =
      img.base + bv% (ls_xref% 0x3e748 0x3e74c) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    bv_arith
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3e6e0 224
  have h_dh := dh_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, dh_fnOff])
  have h_shdrop := sharedDrop_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off%
      "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, sharedDrop_fnOff])
  have h_cteq := ctEqROAllocStack_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) hct (name := calculateAgreementName) (k := 1736)
    (by rw [calculateAgreement_fnOff, ctEq_fnOff])
  have h_shim := noAllocShim_ok_at (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have h_alloc := alloc_ok_at_norm (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) hA (name := calculateAgreementName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  have h_stdrop := staticDrop_ok_at_tripleRatchet (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off%
      "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, staticDrop_fnOff])
  have h_pan := panic_at_handle_alloc_error2 (b := img.base) (C := C) (ctl := ctl)
    (abs := abs) (name := calculateAgreementName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, handleAllocError_fnOff])
  dsimp only [tripleRatchetProgAt] at h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop h_pan hadrp ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr
      calculateAgreementName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics (tripleRatchetExterns C ctl abs))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  subst h_1 h_2 h
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := C.X (Ratchet.clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (Ratchet.clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq
      (List.Vector.toList_length (Ratchet.clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreement_split s0.sp,
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP (mid := entry + 120#64) ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  wp_call h_dh
    (s0.sp - 160#64, Ratchet.clampScalar our.bytes, s0.sp - 64#64, their.bytes, s0.sp - 96#64)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  wp_call h_shdrop (s0.sp - 96#64)
  wp_steps
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq
    (s0.sp - 128#64, ss.toList, img.base + bv% (ls_xref% 0x3e748 0x3e74c), List.replicate 32 0#8, s0.sp - 160#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement C.X their our = none := calculateAgreement_eq_none hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    wp_call h_stdrop (s0.sp - 160#64)
    wp_steps
    refine SepWP.fold (rejoin_stack_calculateAgreement s0.sp hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement C.X their our = some ss := calculateAgreement_eq_some hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP (mid := entry + 160#64) ?_
    wp_steps
    wp_call h_shim ()
    wp_steps
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 160#64) (by wp_norm_lhs)
      (fun halloc htr_alloc => ?_) (fun halloc halign htr_alloc => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0)) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.rw_pre (by
        rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
          memRegion_32_cells,
          ← hss_sp128]) ?_
      sep_elim_exists
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
      refine SepWP.fold hclamp_mem (by sep_focus) ?_
      wp_call h_stdrop (s0.sp - 160#64)
      wp_steps
      refine SepWP.fold (rejoin_stack_calculateAgreement s0.sp hzero_len hss_len hzero_len
        (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (calculateAgreementResultAt_some_intro A (s0.readReg64 (.gpr 8#5))
        _ ss halloc) (by sep_focus) ?_
      rw [hres]
      wp_done

end CalculateAgreementRodata

/-- Discharges `PqxdhCalculateAgreementOk_trap P A img C absHooks` (`0x3e5fc`). -/
theorem pqxdhCalculateAgreement_ok_trap {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A absHooks) :
    PqxdhCalculateAgreementOk_trap P A img C absHooks := by
  have hct : CtEqROOk_trap img.base C absHooks :=
    ConsumeMessageKeyTransfer.ctEqRO_ok_trap img.base C absHooks
  have hraw := calculateAgreement_rodata_ok_trap himg hct hA
  unfold PqxdhCalculateAgreementOk_trap
  refine subroutine_ok_outcome_intro
    fun ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhCalculateAgreementSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hpre' : s0.mem ⊨
      (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
        (calculateAgreementSpec C.X A).pre xg s0) ∗ R := by
    dsimp only [calculateAgreementSpec]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            memRegion ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStack)) ∗ R =
        ⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((theirA ↦ₛ bytesToBv8 theirPk32) ∗
            (memRegion ret 24 ∗ (A.pool ∗ (stackAt sp calculateAgreementStack ∗
              (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ R)))))) := by
      ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hpre⟩
  refine hraw.mono_outcome xg R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [calculateAgreementSpec, pqxdhCalculateAgreementSpec] at hq ⊢
    rw [hour_list, htheir_list, hsp_eq] at hq
    have hE := calculateAgreementResultAt_entails_pqxdh hP A ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A ret (calculateAgreement C.X xg.their xg.our) ∗
          (⌜sf.trace = s0.trace⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool ∗ stackAt sp calculateAgreementStack ∗
            ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ R) := by
      ac_nf at hq ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢
  · exact Or.inr hrest

/-! ## 5. Discharging `pqxdhHkdfExpandCellsSpec` for `k = 8` (`64` B) and `k = 10` (`80` B) -/

/-- Discharges `PqxdhCalculateAgreementOk P A img C ctl absHooks` (`0x3e5fc`). -/
theorem pqxdhCalculateAgreement_ok {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A absHooks) :
    PqxdhCalculateAgreementOk P A img C ctl absHooks := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhCalculateAgreement_ok_trap hP himg hA)

/-- `pqxdhHkdfExpandCellsSpec P img 8` (`64` B, `info = INFO_RATCHET`) from
`Expand.expand_multi_info_ok_trap`. -/
theorem pqxdhHkdfExpand_8_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 8) := by
  have hexp := expand_multi_info_ok_trap img.base C absHooks
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_RATCHET := by
    rcases hcases with ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
    · exact hinfo
    · omega
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 14 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 64⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfoSpec, pqxdhHkdfExpandCellsSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- `pqxdhHkdfExpandCellsSpec P img 8` (`64` B, `info = INFO_RATCHET`) from
`Expand.expand_multi_info_ok`. -/
theorem pqxdhHkdfExpand_8_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 8) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExpand_8_ok_trap hP)

/-- `pqxdhHkdfExpandCellsSpec P img 10` (`80` B, `info = INFO_MSG_KEYS`) from
`Expand.expand_multi_info_ok_trap`. -/
theorem pqxdhHkdfExpand_10_ok_trap {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 10) := by
  have hexp := expand_multi_info_ok_trap img.base C absHooks
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpec] at hpre
  rw [Keys.stackAt_alloc_expand sp, ← memRegion_cells okmA 10 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_MSG_KEYS := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩
    · omega
    · exact hinfo
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 18 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 80⟩,
    memRegion (sp - 8192#64) 3936 ∗ memRegion (sp - 4256#64) 160 ∗
      memRegion (sp - 4096#64) 3456 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfoSpec]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfoSpec, pqxdhHkdfExpandCellsSpec] at hpost ⊢
    rw [Keys.stackAt_alloc_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStack ∗
        memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
        memRegion (s0.sp - 4096#64) 3456) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- `pqxdhHkdfExpandCellsSpec P img 10` (`80` B, `info = INFO_MSG_KEYS`) from
`Expand.expand_multi_info_ok`. -/
theorem pqxdhHkdfExpand_10_ok {P : Primitives} {C : Crypto}
    {img : Obj.Image} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img 10) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExpand_10_ok_trap hP)

/-- For any `k ∉ {8, 10, 12}`, `pqxdhHkdfExpandCellsSpec P img k` has a contradictory
precondition. -/
theorem pqxdhHkdfExpand_other_ok_trap (P : Primitives) (C : Crypto)
    (img : Obj.Image)
    (absHooks : String → Option (State → State)) (k : Nat)
    (hk8 : k ≠ 8) (hk10 : k ≠ 10) (hk12 : k ≠ 12) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img k) := by
  refine subroutine_ok_outcome_intro
    fun ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 _ _ hpre _ => ?_
  dsimp only [pqxdhHkdfExpandCellsSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.2.2.2.2.2.2.2 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact (hk8 rfl).elim
  · exact (hk10 rfl).elim
  · exact (hk12 rfl).elim

/-- For any `k ∉ {8, 10, 12}`, `pqxdhHkdfExpandCellsSpec P img k` has a contradictory
precondition. -/
theorem pqxdhHkdfExpand_other_ok (P : Primitives) (C : Crypto)
    (img : Obj.Image) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) (k : Nat)
    (hk8 : k ≠ 8) (hk10 : k ≠ 10) (hk12 : k ≠ 12) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpec P img k) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (pqxdhHkdfExpand_other_ok_trap P C img absHooks k hk8 hk10 hk12)

/-! ## 6. Contract-Backed `tripleRatchetProgAtExt` Bridges -/

section Ext

private theorem fitBv8_vecU8_eq_ext {n : Nat} (v : List.Vector (BitVec 8) n) :
    Initiator.fitBv8 n (E2E.vecU8 v) = v.toList := by
  have hlen : (E2E.vecU8 v).length = n := vecU8_length v
  change E2E.Pqxdh.Shared.fitBv8 n (E2E.vecU8 v) = v.toList
  rw [E2E.Pqxdh.Shared.fitBv8_eq_bytesToBv8 hlen]
  exact bytesToBv8_vecU8 v

private theorem optEdAt_entails_dalekMontToEdOutAt_ext
    (X : E2E.UnreachedPqxdhPrimitives) (P0 : E2E.PEParams) (outPtr : BitVec 64)
    (inBytes : Bytes) (signBit : UInt8) :
    SignalSession.CliExt.optionEdwardsPointAt outPtr
      (P0.Q.montToEd (u8Vec 32 inBytes) (BitVec.ofNat 8 signBit.toNat &&& 1#8)) ⊢
      dalekMontToEdOutAt
        (ofSignalPqxdhPrimitives (E2E.modelPrims X P0))
        outPtr inBytes (signBit &&& 1) := by
  have hsign : BitVec.ofNat 8 signBit.toNat &&& 1#8 = (signBit &&& 1).toBitVec := by
    rcases signBit with ⟨v⟩
    simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, UInt8.toBitVec_and]
    rfl
  have hmte :
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)).montToEd inBytes (signBit &&& 1) =
        (P0.Q.montToEd (u8Vec 32 inBytes) (signBit &&& 1).toBitVec).map E2E.vecU8 := rfl
  unfold dalekMontToEdOutAt
  rw [hsign, hmte]
  cases hres : P0.Q.montToEd (u8Vec 32 inBytes) (signBit &&& 1).toBitVec with
  | none =>
    exact Entails.of_eq rfl
  | some ed =>
    dsimp only [SignalSession.CliExt.optionEdwardsPointAt, Option.map]
    have hu64 : Initiator.u64le 1#64 = unpack64 1#64 := by decide
    rw [fitBv8_vecU8_eq_ext ed, hu64, pointsToBytes_append, unpack64_length,
      ← pointsTo64_eq_pointsToBytes]
    exact Entails.of_eq rfl

/-- Build `PqxdhHookContractsExt` on raw `ext` directly from `CliExternsOk P0 A ext`. -/
theorem PqxdhHookContractsExt.of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHookContractsExt
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img ext where
  alloc := hOk.alloc
  shim := hOk.shim
  memcpy := hOk.memcpy
  kyberDecaps := by
    rcases hOk.kemDecaps with ⟨f, hf, hok⟩
    have hname : kyberDecapsStub = E2E.kemDecapsName := rfl
    refine ⟨f, hname ▸ hf, hookOk_map_ext
      (fun (g : KyberDecapsCall) =>
        (g.skPtr, u8Vec 3168 g.sk3168, g.ctPtr, u8Vec 1568 g.ct1568, g.outPtr))
      hok ?_ ?_⟩
    · intro g R s0 hpre
      simp only [kyberDecapsStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.kemDecapsSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx8, hsk, hct, _⟩, hmem⟩
      rw [u8Vec_toList_of_length hsk, u8Vec_toList_of_length hct]
      exact ⟨⟨hx0, hx1, hx8⟩, by ac_nf at hmem ⊢⟩
    · intro g R s0 sf hpre hpost
      simp only [kyberDecapsStubSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, _, _, hsk, hct, _⟩, _⟩
      simp only [kyberDecapsStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.kemDecapsSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hmem⟩
      have hout : Initiator.fitBv8 32 (Initiator.kyberDecapsOutBytes
          (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) g.sk3168 g.ct1568) =
          (P0.Q.decaps (u8Vec 3168 g.sk3168) (u8Vec 1568 g.ct1568)).toList := by
        have hdec : (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)).kemDecaps
            g.sk3168 g.ct1568 =
            some (E2E.vecU8 (P0.Q.decaps (u8Vec 3168 g.sk3168) (u8Vec 1568 g.ct1568))) := by
          simp only [ofSignalPqxdhPrimitives, E2E.modelPrims, E2E.blockLevelPrims,
            SignalPqxdh.kyberCtLen, hct, beq_self_eq_true, ↓reduceIte]
        unfold Initiator.kyberDecapsOutBytes
        rw [hdec, Option.getD_some]
        exact fitBv8_vecU8_eq_ext _
      rw [u8Vec_toList_of_length hsk, u8Vec_toList_of_length hct] at hmem
      rw [hout]
      exact ⟨htr, by ac_nf at hmem ⊢⟩
  dalekMontToEd := by
    rcases hOk.toEdwards with ⟨f, hf, hok⟩
    have hname : dalekMontToEdStub = E2E.toEdwardsName := rfl
    refine ⟨f, hname ▸ hf, hookOk_map_ext
      (fun (g : DalekMontToEdGhost) =>
        (g.inPtr, u8Vec 32 g.inBytes, BitVec.ofNat 8 g.signBit.toNat, g.outPtr))
      hok ?_ ?_⟩
    · intro g R s0 hpre
      simp only [dalekMontToEdStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.toEdwardsSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hx1, hx8, hlen⟩, hmem⟩
      rw [u8Vec_toList_of_length hlen]
      exact ⟨⟨hx0, hx1, hx8⟩, by ac_nf at hmem ⊢⟩
    · intro g R s0 sf hpre hpost
      simp only [dalekMontToEdStubSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, _, _, hlen⟩, _⟩
      simp only [dalekMontToEdStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.toEdwardsSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hmem⟩
      rw [u8Vec_toList_of_length hlen] at hmem
      refine ⟨htr, ?_⟩
      have hmem' : sf.mem ⊨
          SignalSession.CliExt.optionEdwardsPointAt g.outPtr
            (P0.Q.montToEd (u8Vec 32 g.inBytes) (BitVec.ofNat 8 g.signBit.toNat &&& 1#8)) ∗
          ((g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ stackAt s0.sp extHookStack ∗ R) := by
        ac_nf at hmem ⊢
      have hmem'' := Satisfies.mono
        (sepConj_mono_left (optEdAt_entails_dalekMontToEdOutAt_ext X P0 g.outPtr g.inBytes g.signBit))
        hmem'
      ac_nf at hmem'' ⊢
  dalekTorsionFree := by
    rcases hOk.torsionFree with ⟨f, hf, hok⟩
    have hname : dalekTorsionFreeStub = E2E.torsionFreeName := rfl
    refine ⟨f, hname ▸ hf, hookOk_map_ext
      (fun (g : CryptoUnaryGhost) => (g.inPtr, u8Vec 160 g.inBytes))
      hok ?_ ?_⟩
    · intro g R s0 hpre
      simp only [cryptoBoolRegStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.torsionFreeSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
      rcases hpre with ⟨⟨hx0, hlen⟩, hmem⟩
      rw [u8Vec_toList_of_length hlen]
      exact ⟨hx0, by ac_nf at hmem ⊢⟩
    · intro g R s0 sf hpre hpost
      simp only [cryptoBoolRegStubSpecExt, sepConj_assoc, satisfies_pure_sepConj] at hpre
      rcases hpre with ⟨⟨_, hlen⟩, _⟩
      simp only [cryptoBoolRegStubSpecExt, pqxdhHookStackExt,
        SignalSession.CliExt.torsionFreeSpec, SignalSession.CliExt.withStack,
        extHookStack, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨⟨htr, hx0⟩, hmem⟩
      have htf : (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)).isTorsionFree g.inBytes =
          P0.Q.isTorsionFree (u8Vec 160 g.inBytes) := rfl
      rw [u8Vec_toList_of_length hlen] at hmem
      rw [htf]
      exact ⟨⟨htr, hx0⟩, by ac_nf at hmem ⊢⟩

/-- Build `PqxdhHookContractsExt` on `SignalSession.cliExternsWith ext` from `CliExternsOk P0 A ext`. -/
theorem PqxdhHookContractsExt.of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhHookContractsExt
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img
      (SignalSession.cliExternsWith ext) := by
  have heq : ∀ s, E2E.isImagePanicSymbol s = false → SignalSession.cliExternsWith ext s = ext s := by
    intro s hs; simp [SignalSession.cliExternsWith, hs]
  exact (PqxdhHookContractsExt.of_externsOk X hOk).of_hooks_eq
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))
    (heq _ (by decide +kernel))

private theorem stackAt_subStackExt_eq_extHook (sp : BitVec 64) :
    stackAt sp calculateAgreementSubStackExt =
      memRegion (sp - 16448#64) 64 ∗ stackAt sp extHookStack := by
  change memRegion (sp - 16448#64) 16448 =
    memRegion (sp - 16448#64) 64 ∗ memRegion (sp - 16384#64) 16384
  exact ProofLib.memRegion_split' (b := sp - 16448#64) (n := 64) (k := 16384)
    (b' := sp - 16384#64) rfl (by bv_omega) (by decide)

private theorem hookSat_subStackExt_of_extHook {α : Type}
    {ext : String → Option (State → State)} {name : String} {spec : Spec α}
    (hsat : HookSat ext name (SignalSession.CliExt.withStack spec extHookStack)) :
    HookSat ext name (SignalSession.CliExt.withStack spec calculateAgreementSubStackExt) := by
  rcases hsat with ⟨f, hf, hh⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  let F : SepProp := memRegion (s0.sp - 16448#64) 64
  have hpre' : s0.mem ⊨ (SignalSession.CliExt.withStack spec extHookStack).pre x s0 ∗ (F ∗ R) := by
    dsimp only [SignalSession.CliExt.withStack, F] at hpre ⊢
    rw [stackAt_subStackExt_eq_extHook s0.sp] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x (F ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hp⟩ | ⟨code, hex, he⟩ | ⟨hoom, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [SignalSession.CliExt.withStack, F] at hpost ⊢
    rw [stackAt_subStackExt_eq_extHook s0.sp]
    ac_nf at hpost ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    have hp' : (f s0).mem ⊨ F ∗ (spec.onPanic x s0 (f s0) ∗ R) := by
      dsimp only [SignalSession.CliExt.withStack] at hp
      ac_nf at hp ⊢
    exact Satisfies.of_sep_right hp'
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex, ?_⟩))
    have he' : (f s0).mem ⊨ F ∗ (spec.onExit x code s0 (f s0) ∗ R) := by
      dsimp only [SignalSession.CliExt.withStack] at he
      ac_nf at he ⊢
    exact Satisfies.of_sep_right he'
  · refine Or.inr (Or.inr (Or.inr ⟨hoom, ?_⟩))
    have ho' : (f s0).mem ⊨ F ∗ (spec.onOom x s0 (f s0) ∗ R) := by
      dsimp only [SignalSession.CliExt.withStack] at ho
      ac_nf at ho ⊢
    exact Satisfies.of_sep_right ho'

private theorem stackAt_subStackExt_eq_allocHook (sp : BitVec 64) :
    stackAt sp calculateAgreementSubStackExt =
      memRegion (sp - 16448#64) 12352 ∗ stackAt sp allocHookStack := by
  change memRegion (sp - 16448#64) 16448 =
    memRegion (sp - 16448#64) 12352 ∗ memRegion (sp - 4096#64) 4096
  exact ProofLib.memRegion_split' (b := sp - 16448#64) (n := 12352) (k := 4096)
    (b' := sp - 4096#64) rfl (by bv_omega) (by decide)

private theorem alloc_subStackExt_of_allocSpec {A : RustAlloc} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustAllocSpec A)) :
    subroutine_ok prog entry (rustAllocSpecWithStack A calculateAgreementSubStackExt) := by
  rw [← rustAllocSpecWithStack_eq_rustAllocSpec A] at h
  refine subroutine_ok_map h ?_
  rintro ⟨size, align⟩ R s0 hpre
  dsimp only [rustAllocSpecWithStack] at hpre
  rw [stackAt_subStackExt_eq_allocHook s0.sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨(size, align), memRegion (s0.sp - 16448#64) 12352 ∗ R, ?_, ?_⟩
  · dsimp only [rustAllocSpecWithStack]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [rustAllocSpecWithStack] at hpost ⊢
    rw [stackAt_subStackExt_eq_allocHook s0.sp]
    ac_nf at hpost ⊢

private def ctEqROSubStackExtSpec :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp calculateAgreementSubStackExt
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = (if k1 = k2 then 1#32 else 0#32) ∧
      (sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ stackAt sp calculateAgreementSubStackExt

private theorem stackAt_subStackExt_eq_ctEq (sp : BitVec 64) :
    stackAt sp calculateAgreementSubStackExt =
      memRegion (sp - 16448#64) 16 ∗
        (stackFrameFor libsignalSessionImage ctEqName sp ∗
          stackAt (sp - 48#64) LibsignalSession.FindReceiverChainIndex.extHookStack32) := by
  rw [← Keys.memRegion_48_eq_stackFrameFor_ct_eq sp]
  change memRegion (sp - 16448#64) 16448 =
    memRegion (sp - 16448#64) 16 ∗
      (memRegion (sp - 48#64) 48 ∗ memRegion (sp - 48#64 - 16384#64) 16384)
  have hsub : sp - 48#64 - 16384#64 = sp - 16432#64 := by bv_omega
  rw [hsub, sepConj_comm (memRegion (sp - 48#64) 48)]
  have h1 := ProofLib.memRegion_split' (b := sp - 16448#64) (n := 16) (k := 16432)
    (b' := sp - 16432#64) rfl (by bv_omega) (by decide)
  have h2 := ProofLib.memRegion_split' (b := sp - 16432#64) (n := 16384) (k := 48)
    (b' := sp - 48#64) rfl (by bv_omega) (by decide)
  rw [h1, h2]

private theorem ctEqROSubStackExt_of_ext32 {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry ConsumeMessageKeyTransfer.ctEqSliceROSpecExt) :
    subroutine_ok prog entry ctEqROSubStackExtSpec := by
  refine subroutine_ok_map h ?_
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  dsimp only [ctEqROSubStackExtSpec] at hpre
  rw [stackAt_subStackExt_eq_ctEq sp] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hpure, hpre⟩
  refine ⟨(p1, k1, p2, k2, sp), memRegion (sp - 16448#64) 16 ∗ R, ?_, ?_⟩
  · dsimp only [ConsumeMessageKeyTransfer.ctEqSliceROSpecExt]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, by ac_nf at hpre ⊢⟩
  · intro sf hpost
    dsimp only [ConsumeMessageKeyTransfer.ctEqSliceROSpecExt, ctEqROSubStackExtSpec] at hpost ⊢
    rw [stackAt_subStackExt_eq_ctEq sp]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨⟨h32, htr⟩, hpost⟩
    have h8 : (sf.readReg64 .x0).setWidth 8 = (if k1 = k2 then 1#8 else 0#8) := by
      have hcongr := congrArg (fun v : BitVec 32 => v.setWidth 8) h32
      have hsw : ((sf.readReg64 .x0).setWidth 32).setWidth 8 = (sf.readReg64 .x0).setWidth 8 :=
        BitVec.setWidth_setWidth_of_le (sf.readReg64 .x0) (by decide)
      rw [hsw] at hcongr
      rw [hcongr]
      split <;> rfl
    exact ⟨⟨h32, h8, htr⟩, by ac_nf at hpost ⊢⟩

section CalculateAgreementRodataExt

open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalTripleRatchet.Keys.AgreeStateSimp

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem dh_subStackExt_ok_at {C : Crypto} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman" -
          0x3e6e0)))
      (SignalSession.CliExt.withStack (diffieHellmanSpec C.X) calculateAgreementSubStackExt) :=
  hook_ok_at (hname := dhName) rfl
    (show libsignalSessionCode.fnOff calculateAgreementName + _ = libsignalSessionCode.fnOff dhName
      by rw [calculateAgreement_fnOff, dh_fnOff])
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, dhName])
    (hookSat_subStackExt_of_extHook hdh)

private theorem sharedDrop_subStackExt_ok_at {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off%
          "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop" - 0x3e6e0)))
      (SignalSession.CliExt.withStack zeroizeSecretSpec calculateAgreementSubStackExt) :=
  hook_ok_at (hname := sharedDropName) rfl
    (show libsignalSessionCode.fnOff calculateAgreementName + _ =
        libsignalSessionCode.fnOff sharedDropName
      by rw [calculateAgreement_fnOff, sharedDrop_fnOff])
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, sharedDropName])
    (hookSat_subStackExt_of_extHook hsh)

private theorem staticDrop_subStackExt_ok_at {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off%
          "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop" - 0x3e6e0)))
      (SignalSession.CliExt.withStack zeroizeSecretSpec calculateAgreementSubStackExt) :=
  hook_ok_at (hname := staticDropName) rfl
    (show libsignalSessionCode.fnOff calculateAgreementName + _ =
        libsignalSessionCode.fnOff staticDropName
      by rw [calculateAgreement_fnOff, staticDrop_fnOff])
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol, staticDropName])
    (hookSat_subStackExt_of_extHook hst)

private theorem shim_ok_at_ag_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      SignalSession.CliExt.shimSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr calculateAgreementName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e6e0)))
      SignalSession.CliExt.shimSpec :=
  hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
    (show libsignalSessionCode.fnOff calculateAgreementName + _ =
        libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
    (by fnoff_eq) (by fnoff_eq) (by simp [Rust.isPanicSymbol]) hshim

private theorem ctEqRO_subStackExt_ok_at {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hct : ConsumeMessageKeyTransfer.CtEqROOkExt32 b ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr calculateAgreementName + BitVec.ofNat 64 1736)
      ctEqROSubStackExtSpec :=
  ctEqROSubStackExt_of_ext32
    (subroutine_ok_rel_pqxdh_ext hct ctEq_fnOff calculateAgreement_fnOff (by decide))

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  AgreeStateSimp.sp_setPC_pre AgreeStateSimp.sp_setMem_setPC_pre
  AgreeStateSimp.readReg64_setPC_pre AgreeStateSimp.readReg64_setMem_setPC_pre
  AgreeStateSimp.readReg32_setPC_pre AgreeStateSimp.readReg32_setMem_setPC_pre
  AgreeStateSimp.readReg_setPC_pre AgreeStateSimp.readReg_setMem_setPC_pre
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  calculateAgreement_fnOff ctEq_fnOff dh_fnOff sharedDrop_fnOff staticDrop_fnOff
  handleAllocError_fnOff
  libsignalSessionCode_fnOff_0x3e6e0
  libsignalSessionCode_fnOff_0x3eda8
  (ls_stub% "<x25519_dalek::x25519::StaticSecret>::diffie_hellman")
  (ls_stub% "<x25519_dalek::x25519::SharedSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
  (ls_stub% "alloc::alloc::handle_alloc_error")

theorem calculateAgreement_rodata_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hct : ConsumeMessageKeyTransfer.CtEqROOkExt32 img.base ext)
    (hA : AllocHooks A ext)
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C))
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec)
    (hshim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      SignalSession.CliExt.shimSpec)
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName)
      { calculateAgreementSpecAt C.X A calculateAgreementSubStackExt with
        pre := fun x s =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpecAt C.X A calculateAgreementSubStackExt).pre x s
        post := fun x s0 sf =>
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (calculateAgreementSpecAt C.X A calculateAgreementSubStackExt).post x s0 sf } := by
  have hfn : libsignalSessionCode.fnOff calculateAgreementName = 0x3e6e0 :=
    calculateAgreement_fnOff
  have hadrp : ((tripleRatchetProgAtExt img.base ext).fnAddr calculateAgreementName + 104#64 &&&
      18446744073709547520#64) + bv% (ls_xref% 0x3e748 0x3e74c - 0x3e000) =
      img.base + bv% (ls_xref% 0x3e748 0x3e74c) := by
    have hb := base_aligned_of_loads himg
    rw [Program.fnAddr_rebase, hfn]
    bv_arith
  code_fetches libsignalSessionCode libsignalSessionBin img.base
    (Rust.withPanics ext) hfn 0x3e6e0 224
  have h_dh := dh_subStackExt_ok_at (b := img.base) hdh
  have h_shdrop := sharedDrop_subStackExt_ok_at (b := img.base) hsh
  have h_cteq := ctEqRO_subStackExt_ok_at (b := img.base) hct
  have h_shim := shim_ok_at_ag_ext (b := img.base) hshim
  have h_alloc := pqxdh_alloc_ok_at_ext (b := img.base) hA (name := calculateAgreementName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  have h_stdrop := staticDrop_subStackExt_ok_at (b := img.base) hst
  have h_pan := pqxdh_panic_at_handle_alloc_error_ext (b := img.base) (ext := ext)
    (name := calculateAgreementName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0))
    (by rw [calculateAgreement_fnOff, handleAllocError_fnOff])
  dsimp only [tripleRatchetProgAtExt, SignalSession.CliExt.withStack] at h_dh h_shdrop h_cteq h_shim h_alloc h_stdrop h_pan hadrp ⊢
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
      calculateAgreementName = entry
  generalize_entry
    (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨ourA, our, theirA, their, ret⟩
  dsimp only at *
  subst h_1 h_2 h
  obtain ⟨t0, t1, t2, t3, _, htheir_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length their.bytes)
  have htheir_sp : ∀ sp : BitVec 64,
      ((sp - 64#64) ↦₆₄ t0) ∗ ((sp - 56#64) ↦₆₄ t1) ∗
        ((sp - 48#64) ↦₆₄ t2) ∗ ((sp - 40#64) ↦₆₄ t3) =
      ((sp - 64#64) ↦ₛ their.bytes.toList) := by
    intro sp; simpa [bv_sub_add_lit] using (htheir_pts (sp - 64#64)).symm
  let ss := C.X (Ratchet.clampScalar our.bytes) their.bytes
  obtain ⟨ss0, ss1, ss2, ss3, _, hss_pts⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length ss)
  have hss_sp96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) =
      ((s0.sp - 96#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 96#64)).symm
  have hss_sp128 :
      ((s0.sp - 128#64) ↦₆₄ ss0) ∗ ((s0.sp - 120#64) ↦₆₄ ss1) ∗
        ((s0.sp - 112#64) ↦₆₄ ss2) ∗ ((s0.sp - 104#64) ↦₆₄ ss3) =
      ((s0.sp - 128#64) ↦ₛ ss.toList) := by
    simpa [bv_sub_add_lit] using (hss_pts (s0.sp - 128#64)).symm
  have hss_mem96 :
      ((s0.sp - 96#64) ↦₆₄ ss0) ∗ ((s0.sp - 88#64) ↦₆₄ ss1) ∗
        ((s0.sp - 80#64) ↦₆₄ ss2) ∗ ((s0.sp - 72#64) ↦₆₄ ss3) ⊢
      memRegion (s0.sp - 96#64) 32 := by
    rw [hss_sp96]
    exact pointsToBytes_entails_memRegion_of_eq (List.Vector.toList_length ss)
  have hclamp_mem :
      ((s0.sp - 160#64) ↦ₛ (Ratchet.clampScalar our.bytes).toList) ⊢
      memRegion (s0.sp - 160#64) 32 :=
    pointsToBytes_entails_memRegion_of_eq
      (List.Vector.toList_length (Ratchet.clampScalar our.bytes))
  refine SepWPp.rw_pre (by
    rw [stackAt_calculateAgreementAt_split (subStack := calculateAgreementSubStackExt) s0.sp
        (by decide),
      memRegion_32_view1_sp s0.sp,
      vec32_view1 (s0.readReg64 (.gpr 0#5)) our.bytes,
      htheir_pts (s0.readReg64 (.gpr 1#5))]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP (mid := entry + 120#64) ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view1_to_view2 (s0.readReg64 (.gpr 0#5)) our.bytes)) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (stur_q0_reframe_sp s0.sp our.bytes) (by sep_focus) ?_
  sep_elim_exists
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (vec32_view2 (s0.readReg64 (.gpr 0#5)) our.bytes).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_pts (s0.readReg64 (.gpr 1#5))).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (clampScalar_view2_sp s0.sp our.bytes)) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (htheir_sp s0.sp)) (by sep_focus) ?_
  wp_call h_dh
    (s0.sp - 160#64, Ratchet.clampScalar our.bytes, s0.sp - 64#64, their.bytes, s0.sp - 96#64)
  refine SepWP.fold (Entails.of_eq hss_sp96.symm) (by sep_focus) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
  refine SepWP.fold hss_mem96 (by sep_focus) ?_
  wp_call h_shdrop (s0.sp - 96#64)
  wp_steps
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length ss
  have hzero_len : (List.replicate 32 0#8).length = 32 := by decide
  wp_call h_cteq
    (s0.sp - 128#64, ss.toList, img.base + bv% (ls_xref% 0x3e748 0x3e74c), List.replicate 32 0#8,
      s0.sp - 160#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  by_cases hzero : ss.toList = List.replicate 32 0#8
  · have hres : calculateAgreement C.X their our = none := calculateAgreement_eq_none hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.rw_pre (by rw [memRegion_24_err (s0.readReg64 (.gpr 8#5))]) ?_
    sep_elim_exists
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold hclamp_mem (by sep_focus) ?_
    wp_call h_stdrop (s0.sp - 160#64)
    wp_steps
    refine SepWP.fold (rejoin_stack_calculateAgreementAt (subStack := calculateAgreementSubStackExt)
      s0.sp (by decide) hzero_len hzero_len hzero_len
      (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
    simp only [hres, calculateAgreementResultAt]
    wp_done
  · have hres : calculateAgreement C.X their our = some ss := calculateAgreement_eq_some hzero
    simp only [hzero, ↓reduceIte] at *
    refine SepWPp.of_sepWP (mid := entry + 160#64) ?_
    wp_steps
    wp_call h_shim ()
    wp_steps
    refine SepWP.fold (Entails.of_eq (stackAt_subStackExt_eq_allocHook (s0.sp - 160#64)))
      (by sep_focus) ?_
    have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call h_alloc (32, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.split_alloc (sp' := s0.sp - 160#64) (by wp_norm_lhs)
      (fun halloc htr_alloc => ?_) (fun halloc halign htr_alloc => ?_)
    · refine SepWPp.of_sepWP
        (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" - 0x3e6e0)) ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      apply SepWPp.panic (by wp_norm_goal) (by wp_norm_lhs)
      exact allowPanic_panicked (allocFailedIn_panicked_of_append (by wp_norm_lhs))
    · refine SepWPp.rw_pre (by
        rw [memRegion_24_ok (s0.readReg64 (.gpr 8#5)),
          memRegion_32_cells,
          ← hss_sp128]) ?_
      sep_elim_exists
      apply SepWPp.of_sepWP_ret
      wp_steps
      refine SepWP.fold (Entails.of_eq hss_sp128) (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (hss_pts _).symm) (by sep_focus) ?_
      refine SepWP.fold hclamp_mem (by sep_focus) ?_
      refine SepWP.fold (Entails.of_eq (stackAt_subStackExt_eq_allocHook (s0.sp - 160#64)).symm)
        (by sep_focus) ?_
      wp_call h_stdrop (s0.sp - 160#64)
      wp_steps
      refine SepWP.fold (rejoin_stack_calculateAgreementAt
        (subStack := calculateAgreementSubStackExt) s0.sp (by decide) hzero_len hss_len hzero_len
        (List.Vector.toList_length their.bytes) _ _ _ _) (by sep_focus) ?_
      refine SepWP.fold (calculateAgreementResultAt_some_intro A (s0.readReg64 (.gpr 8#5))
        _ ss halloc) (by sep_focus) ?_
      rw [hres]
      wp_done

end CalculateAgreementRodataExt

/-- Discharges `PqxdhCalculateAgreementOkExt P A img ext` (`0x3e5fc`) on
`tripleRatchetProgAtExt img.base ext` from `HookSat` contracts at `extHookStack` (`16384` B). -/
theorem pqxdhCalculateAgreement_ok_ext {P : Primitives} {C : Crypto} {A : RustAlloc}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A ext)
    (hbb : HookSat ext "subtle::black_box::<u8>" SignalSession.CliExt.blackBoxSpec)
    (hdh : HookSat ext dhName (SignalSession.CliExt.dhSpec C))
    (hsh : HookSat ext sharedDropName SignalSession.CliExt.zeroizeSpec)
    (hshim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      SignalSession.CliExt.shimSpec)
    (hst : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec) :
    PqxdhCalculateAgreementOkExt P A img ext := by
  have hct : ConsumeMessageKeyTransfer.CtEqROOkExt32 img.base ext :=
    ConsumeMessageKeyTransfer.ctEqRO_ok_ext32 img.base hbb
  have hraw := calculateAgreement_rodata_ok_ext himg hct hA hdh hsh hshim hst
  unfold PqxdhCalculateAgreementOkExt
  refine subroutine_ok_outcome_intro
    fun ⟨ourA, ourSk32, theirA, theirPk32, ret, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhCalculateAgreementSpecExt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx8, hsp_eq, hour, htheir⟩, hpre⟩
  let xg : CalculateAgreementGhost := ⟨ourA, ⟨u8Vec 32 ourSk32⟩, theirA, ⟨u8Vec 32 theirPk32⟩, ret⟩
  have hour_list : xg.our.bytes.toList = bytesToBv8 ourSk32 := u8Vec_toList_of_length hour
  have htheir_list : xg.their.bytes.toList = bytesToBv8 theirPk32 := u8Vec_toList_of_length htheir
  have hpre' : s0.mem ⊨
      (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
        (Keys.calculateAgreementSpecAt C.X A calculateAgreementSubStackExt).pre xg s0) ∗ R := by
    dsimp only [Keys.calculateAgreementSpecAt]
    rw [hour_list, htheir_list, hsp_eq]
    have hcomm :
        (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            memRegion ret 24 ∗ A.pool ∗ stackAt sp calculateAgreementStackExt)) ∗ R =
        ⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
          ((ourA ↦ₛ bytesToBv8 ourSk32) ∗ ((theirA ↦ₛ bytesToBv8 theirPk32) ∗
            (memRegion ret 24 ∗ (A.pool ∗ (stackAt sp calculateAgreementStackExt ∗
              (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ R)))))) := by
      ac_rfl
    rw [hcomm, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx8⟩, hpre⟩
  refine hraw.mono_outcome xg R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Keys.calculateAgreementSpecAt, pqxdhCalculateAgreementSpecExt] at hq ⊢
    rw [hour_list, htheir_list, hsp_eq] at hq
    have hE := calculateAgreementResultAt_entails_pqxdh hP A ret ourSk32 theirPk32
    have hq1 : sf.mem ⊨
        calculateAgreementResultAt A ret (calculateAgreement C.X xg.their xg.our) ∗
          (⌜sf.trace = s0.trace⌝ ∗
            (ourA ↦ₛ bytesToBv8 ourSk32) ∗ (theirA ↦ₛ bytesToBv8 theirPk32) ∗
            A.pool ∗ stackAt sp calculateAgreementStackExt ∗
            ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗ R) := by
      ac_nf at hq ⊢
    have hq2 := Satisfies.mono (sepConj_mono_left hE) hq1
    ac_nf at hq2 ⊢
  · exact Or.inr hrest

private theorem hookSat_cliExternsWith_ag {α : Type} {s : String} {sp : Spec α}
    {ext : String → Option (State → State)}
    (hs : E2E.isImagePanicSymbol s = false)
    (h : HookSat ext s sp) :
    HookSat (SignalSession.cliExternsWith ext) s sp := by
  rcases h with ⟨fn, hfn, hok⟩
  refine ⟨fn, ?_, hok⟩
  simp [SignalSession.cliExternsWith, hs, hfn]

/-- Discharges `PqxdhCalculateAgreementOkExt` on raw `ext` from `CliExternsOk P0 A ext`. -/
theorem pqxdhCalculateAgreement_ok_of_externsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhCalculateAgreementOkExt
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img ext :=
  pqxdhCalculateAgreement_ok_ext (primitivesMatchCrypto_modelPrims X P0) himg
    hOk.alloc hOk.blackBox hOk.dh hOk.sharedDrop hOk.shim hOk.staticDrop

/-- Discharges `PqxdhCalculateAgreementOkExt` on `SignalSession.cliExternsWith ext` from
`CliExternsOk P0 A ext`. -/
theorem pqxdhCalculateAgreement_ok_of_cliExternsOk
    (X : E2E.UnreachedPqxdhPrimitives) {P0 : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    PqxdhCalculateAgreementOkExt
      (ofSignalPqxdhPrimitives (E2E.modelPrims X P0)) A img
      (SignalSession.cliExternsWith ext) :=
  pqxdhCalculateAgreement_ok_ext (primitivesMatchCrypto_modelPrims X P0) himg
    ⟨hookSat_cliExternsWith_ag (by decide +kernel) hOk.alloc.alloc,
     hookSat_cliExternsWith_ag (by decide +kernel) hOk.alloc.dealloc,
     hookSat_cliExternsWith_ag (by decide +kernel) hOk.alloc.realloc⟩
    (hookSat_cliExternsWith_ag (by decide +kernel) hOk.blackBox)
    (hookSat_cliExternsWith_ag (by decide +kernel) hOk.dh)
    (hookSat_cliExternsWith_ag (by decide +kernel) hOk.sharedDrop)
    (hookSat_cliExternsWith_ag (by decide +kernel) hOk.shim)
    (hookSat_cliExternsWith_ag (by decide +kernel) hOk.staticDrop)

private theorem stackAt_pqxdhHkdfExt_expand (sp : BitVec 64) :
    stackAt sp pqxdhHkdfStackExt =
      memRegion (sp - 24576#64) 7552 ∗ stackAt sp expandMultiInfoStackExt := by
  change memRegion (sp - 24576#64) 24576 =
    memRegion (sp - 24576#64) 7552 ∗ memRegion (sp - 17024#64) 17024
  exact ProofLib.memRegion_split' (b := sp - 24576#64) (n := 7552) (k := 17024)
    (b' := sp - 17024#64) rfl (by bv_omega) (by decide)

/-- `pqxdhHkdfExpandCellsSpecExt P img 8` (`64` B, `info = INFO_RATCHET`) on
`tripleRatchetProgAtExt img.base ext` from `expandMultiInfoSpecExt C.F`. -/
theorem pqxdhHkdfExpand_8_ok_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hexp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfoSpecExt C.F)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img 8) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpecExt, pqxdhHkdfExpandCellsSpecAt] at hpre
  rw [stackAt_pqxdhHkdfExt_expand sp, ← memRegion_cells okmA 8 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_RATCHET := by
    rcases hcases with ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩ | ⟨_, _, hk⟩
    · exact hinfo
    · omega
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 14 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 64⟩,
    memRegion (sp - 24576#64) 7552 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfoSpecExt]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inl trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfoSpecExt, pqxdhHkdfExpandCellsSpecExt,
      pqxdhHkdfExpandCellsSpecAt] at hpost ⊢
    rw [stackAt_pqxdhHkdfExt_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 8 = 64 from rfl, bytesToBv8_hkdfExpandRef_64 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 64) ∗
        stackAt s0.sp expandMultiInfoStackExt ∗
        memRegion (s0.sp - 24576#64) 7552) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- `pqxdhHkdfExpandCellsSpecExt P img 10` (`80` B, `info = INFO_MSG_KEYS`) on
`tripleRatchetProgAtExt img.base ext` from `expandMultiInfoSpecExt C.F`. -/
theorem pqxdhHkdfExpand_10_ok_ext {P : Primitives} {C : Crypto}
    {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hP : PrimitivesMatchCrypto P C)
    (hexp : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (expandMultiInfoSpecExt C.F)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img 10) := by
  refine subroutine_ok_map hexp ?_
  rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
  dsimp only [pqxdhHkdfExpandCellsSpecExt, pqxdhHkdfExpandCellsSpecAt] at hpre
  rw [stackAt_pqxdhHkdfExt_expand sp, ← memRegion_cells okmA 10 (by decide)] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨_hF, hx0, hx1, hx2, hx3, hsp, hprk, hcases⟩, hpre⟩
  have hinfo : info = INFO_MSG_KEYS := by
    rcases hcases with ⟨_, _, hk⟩ | ⟨_, hinfo, _⟩ | ⟨_, _, hk⟩
    · omega
    · exact hinfo
    · omega
  have hprk_le : prk.length ≤ 64 := by rw [hprk]; decide
  have hinfo_len : info.length = 18 := by subst hinfo; rfl_kernel
  have hinfo_lt : info.length < 23 := by omega
  rw [pqxdhHmacStateAt_eq hP hkdfA (by omega)] at hpre
  refine ⟨⟨hkdfA, bytesToBv8 prk, infoHdrA, infoA, bytesToBv8 info, okmA, 80⟩,
    memRegion (sp - 24576#64) 7552 ∗ R, ?_, ?_⟩
  · dsimp only [expandMultiInfoSpecExt]
    subst hsp
    repeat rw [bytesToBv8_length]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_lt, Or.inr trivial⟩, by arm64_sep_close⟩
  · intro sf hpost
    dsimp only [expandMultiInfoSpecExt, pqxdhHkdfExpandCellsSpecExt,
      pqxdhHkdfExpandCellsSpecAt] at hpost ⊢
    rw [stackAt_pqxdhHkdfExt_expand sp]
    subst hsp
    repeat rw [bytesToBv8_length] at hpost
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨htr, hpost⟩
    rw [show 8 * 10 = 80 from rfl, bytesToBv8_hkdfExpandRef_80 hP prk info]
    have hE := sepConj_mono_left
      (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
        (infoA ↦ᵣ bytesToBv8 info) ∗
        (okmA ↦ₛ hkdfExpand C.F (bytesToBv8 prk) (bytesToBv8 info) 80) ∗
        stackAt s0.sp expandMultiInfoStackExt ∗
        memRegion (s0.sp - 24576#64) 7552) ∗ R)
      (Keys.hmacCore_entails_cells C.F hkdfA (bytesToBv8 prk))
    replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
    exact ⟨htr, by arm64_sep_close⟩

/-- For any `k ∉ {8, 10, 12}`, `pqxdhHkdfExpandCellsSpecExt P img k` has a contradictory
precondition. -/
theorem pqxdhHkdfExpand_other_ok_ext (P : Primitives) (img : Obj.Image)
    (ext : String → Option (State → State)) (k : Nat)
    (hk8 : k ≠ 8) (hk10 : k ≠ 10) (hk12 : k ≠ 12) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr hkdfExpandMultiInfoSym)
      (pqxdhHkdfExpandCellsSpecExt P img k) := by
  refine subroutine_ok_outcome_intro
    fun ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 _ _ hpre _ => ?_
  dsimp only [pqxdhHkdfExpandCellsSpecExt, pqxdhHkdfExpandCellsSpecAt] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre.1.2.2.2.2.2.2.2 with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · exact (hk8 rfl).elim
  · exact (hk10 rfl).elim
  · exact (hk12 rfl).elim

end Ext

end CryptoVerification.E2E.Pqxdh.ResponderCore
