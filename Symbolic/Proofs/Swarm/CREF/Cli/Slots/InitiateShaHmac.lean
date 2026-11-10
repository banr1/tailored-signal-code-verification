/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhModelLink
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateDefs

/-!
# CLI `init` Byte Conversion, SHA-256, HMAC, and HKDF-96 Bridges

Proves equivalence between `SignalPqxdh` SHA-256, HMAC-SHA256, and `hkdfDerive96`
at `modelPrims X P` and the corresponding `CryptoGames.HMAC` and `pqxdhKdfBytes`
operations.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E
open DY.Libsignal (HwBytes)
open Symbolic.Swarm.CREF.TR (pqxdhKdfBytes pqxdhLabelBytes discontinuityBytes)

@[simp]
theorem ofU8_length (bs : SignalPqxdh.Bytes) : (ofU8 bs).length = bs.length := by
  simp [ofU8]

@[simp]
theorem toU8_length (bs : HwBytes) : (toU8 bs).length = bs.length := by
  simp [toU8]

theorem toU8_ofU8 (bs : SignalPqxdh.Bytes) : toU8 (ofU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    rcases b with ⟨v⟩
    exact congrArg (⟨v⟩ :: ·) ih

theorem ofU8_toU8 (bs : HwBytes) : ofU8 (toU8 bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b tl ih =>
    exact congrArg (b :: ·) ih

theorem ofU8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    ofU8 (vecU8 v) = v.toList :=
  ofU8_toU8 v.toList

theorem u8Vec_toList_of_len {n : Nat} {bs : SignalPqxdh.Bytes} (h : bs.length = n) :
    (u8Vec n bs).toList = ofU8 bs :=
  fitVec_toList_of_len (by simp [h])

theorem u8Vec_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    u8Vec n (vecU8 v) = v := by
  apply List.Vector.eq
  rw [u8Vec_toList_of_len (by simp [vecU8]), ofU8_vecU8]

theorem ofU8_append (a b : SignalPqxdh.Bytes) :
    ofU8 (a ++ b) = ofU8 a ++ ofU8 b := by
  simp [ofU8]

theorem ofU8_take (n : Nat) (bs : SignalPqxdh.Bytes) :
    ofU8 (bs.take n) = (ofU8 bs).take n :=
  List.map_take

theorem ofU8_drop (n : Nat) (bs : SignalPqxdh.Bytes) :
    ofU8 (bs.drop n) = (ofU8 bs).drop n :=
  List.map_drop

theorem ofU8_replicate (k : Nat) (b : UInt8) :
    ofU8 (List.replicate k b) = List.replicate k b.toBitVec := by
  simp [ofU8]

private theorem fitBytesRef_of_len {n : Nat} {bs : SignalPqxdh.Bytes} (h : bs.length = n) :
    SignalPqxdh.fitBytesRef n bs = bs := by
  unfold SignalPqxdh.fitBytesRef
  simp [h]

private theorem or_shift8_extract8 (acc w : BitVec 32) (s i : Nat) (hi : i < 32) :
    ((acc <<< 8) ||| (w.extractLsb' s 8).zeroExtend 32).getLsbD i =
      if i < 8 then w.getLsbD (s + i) else acc.getLsbD (i - 8) := by
  simp only [BitVec.zeroExtend, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h8 : i < 8 <;> simp [h8]

private theorem beWord32_toBEBytes4 (w : BitVec 32) :
    beWord 32 (HMAC.toBEBytes 4 w) 0 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change ((((0#32 <<< 8 ||| (w.extractLsb' 24 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 16 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 8 8).zeroExtend 32) <<< 8 |||
    (w.extractLsb' 0 8).zeroExtend 32).getLsbD i = w.getLsbD i
  rw [or_shift8_extract8 _ _ _ _ hi]
  split_ifs with h8
  · simp
  · rw [or_shift8_extract8 _ _ _ _ (by omega)]
    split_ifs with h16
    · congr 1; omega
    · rw [or_shift8_extract8 _ _ _ _ (by omega)]
      split_ifs with h24
      · congr 1; omega
      · rw [or_shift8_extract8 _ _ _ _ (by omega)]
        have h32 : i - 8 - 8 - 8 < 8 := by omega
        simp [h32, show 24 + (i - 8 - 8 - 8) = i by omega]

private theorem sha256StateBytes_length : ∀ h : HMAC.ShaState, (sha256StateBytes h).length = 32
  | ⟨[_w0, _w1, _w2, _w3, _w4, _w5, _w6, _w7], _⟩ => rfl

private theorem sha256StateOf_sha256StateBytes :
    ∀ h : HMAC.ShaState, sha256StateOf (sha256StateBytes h) = h
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
    simp only [beWord32_toBEBytes4]

private theorem ofU8_sha256StateBytes (h : HMAC.ShaState) :
    ofU8 (sha256StateBytes h) = h.toList.flatMap (HMAC.toBEBytes 4) :=
  ofU8_toU8 _

private theorem sha256Step_of_compress {P : SignalPqxdh.Primitives} {F : ShaCompress}
    (hcomp : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (h : HMAC.ShaState) (blk : SignalPqxdh.Bytes) :
    SignalPqxdh.sha256Step P (sha256StateBytes h) blk = sha256StateBytes (F h (ofU8 blk)) := by
  unfold SignalPqxdh.sha256Step
  rw [fitBytesRef_of_len (sha256StateBytes_length h), hcomp, sha256StateOf_sha256StateBytes,
      fitBytesRef_of_len (sha256StateBytes_length _)]

private theorem foldl_sha256Step_of_compress {P : SignalPqxdh.Primitives} {F : ShaCompress}
    (hcomp : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (blks : List SignalPqxdh.Bytes) (h : HMAC.ShaState) :
    blks.foldl (SignalPqxdh.sha256Step P) (sha256StateBytes h) =
      sha256StateBytes ((blks.map ofU8).foldl F h) := by
  induction blks generalizing h with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [sha256Step_of_compress hcomp, ih]

private theorem zeroPadLen_sha256_fin : ∀ m : Fin 64,
    (if (m.val + 9) % 64 == 0 then 0 else 64 - (m.val + 9) % 64) = (119 - m.val) % 64 := by
  decide

private theorem zeroPadLen_sha256_eq (n : Nat) :
    (if (n + 9) % 64 == 0 then 0 else 64 - (n + 9) % 64) = (119 - n % 64) % 64 := by
  rw [Nat.add_mod n 9 64]
  exact zeroPadLen_sha256_fin ⟨n % 64, Nat.mod_lt n (by decide)⟩

private theorem shr_and_ff_setWidth8 (w : BitVec 64) (k : Nat) (hk : k ≤ 56) :
    ((w >>> BitVec.ofNat 64 k) &&& 0xFF#64).setWidth 8 = w.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hff : (0xFF#64).getLsbD i = true := by
    revert i hi; decide
  have hk64 : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]; omega
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
    BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, hff, Bool.and_true]
  change (w >>> (BitVec.ofNat 64 k).toNat).getLsbD i = w.getLsbD (k + i)
  rw [hk64, BitVec.getLsbD_ushiftRight, Nat.add_comm]

private theorem toBitVec_toUInt8_u64 (u : UInt64) :
    u.toUInt8.toBitVec = u.toBitVec.setWidth 8 := by
  rcases u with ⟨w⟩
  rfl

private theorem ofU8_u64_be (u : UInt64) :
    ofU8
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
  simp only [ofU8, List.map, toBitVec_toUInt8_u64, UInt64.toBitVec_and,
    UInt64.toBitVec_shiftRight]
  change [ (w >>> 56#64 &&& 0xFF#64).setWidth 8,
           (w >>> 48#64 &&& 0xFF#64).setWidth 8,
           (w >>> 40#64 &&& 0xFF#64).setWidth 8,
           (w >>> 32#64 &&& 0xFF#64).setWidth 8,
           (w >>> 24#64 &&& 0xFF#64).setWidth 8,
           (w >>> 16#64 &&& 0xFF#64).setWidth 8,
           (w >>>  8#64 &&& 0xFF#64).setWidth 8,
           (w >>>  0#64 &&& 0xFF#64).setWidth 8 ] =
    [ w.extractLsb' 56 8, w.extractLsb' 48 8, w.extractLsb' 40 8, w.extractLsb' 32 8,
      w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb'  8 8, w.extractLsb'  0 8 ]
  rw [shr_and_ff_setWidth8 w 56 (by omega), shr_and_ff_setWidth8 w 48 (by omega),
      shr_and_ff_setWidth8 w 40 (by omega), shr_and_ff_setWidth8 w 32 (by omega),
      shr_and_ff_setWidth8 w 24 (by omega), shr_and_ff_setWidth8 w 16 (by omega),
      shr_and_ff_setWidth8 w  8 (by omega), shr_and_ff_setWidth8 w  0 (by omega)]

private theorem ofU8_encodeBitLen64BE (n : Nat) :
    ofU8 (SignalPqxdh.encodeBitLen64BE n) = HMAC.toBEBytes 8 (BitVec.ofNat 64 (8 * n)) := by
  unfold SignalPqxdh.encodeBitLen64BE
  rw [ofU8_u64_be]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [UInt64.toBitVec_mul, Nat.toUInt64, BitVec.toNat_ofNat, Nat.mul_comm]

private theorem ofU8_sha256Pad (msg : SignalPqxdh.Bytes) :
    ofU8 (SignalPqxdh.sha256Pad msg) = HMAC.sha256Pad (ofU8 msg) := by
  unfold SignalPqxdh.sha256Pad HMAC.sha256Pad
  dsimp only
  rw [zeroPadLen_sha256_eq, ofU8_append, ofU8_append, ofU8_append,
      ofU8_replicate, ofU8_encodeBitLen64BE, ofU8_length]
  rfl

private theorem map_ofU8_chunkBlocks_64 (bs : SignalPqxdh.Bytes) :
    (SignalPqxdh.chunkBlocks 64 bs).map ofU8 = HMAC.chunks64 (ofU8 bs) := by
  unfold SignalPqxdh.chunkBlocks HMAC.chunks64
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, ofU8_drop, ofU8_take]
  rw [Nat.mul_comm]

private theorem sha256InitState_eq :
    SignalPqxdh.sha256InitState = sha256StateBytes HMAC.sha256IV := rfl

private theorem ofU8_sha256Ref_of_compress {P : SignalPqxdh.Primitives} {F : ShaCompress}
    (hcomp : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (msg : SignalPqxdh.Bytes) :
    ofU8 (SignalPqxdh.sha256Ref P msg) = HMAC.sha256With F (ofU8 msg) := by
  unfold SignalPqxdh.sha256Ref HMAC.sha256With
  dsimp only
  rw [sha256InitState_eq, foldl_sha256Step_of_compress hcomp,
      fitBytesRef_of_len (sha256StateBytes_length _), ofU8_sha256StateBytes,
      map_ofU8_chunkBlocks_64, ofU8_sha256Pad]

private theorem sha256Ref_length (P : SignalPqxdh.Primitives) (msg : SignalPqxdh.Bytes) :
    (SignalPqxdh.sha256Ref P msg).length = 32 :=
  SignalPqxdh.fitBytesRef_length 32 _

private theorem ofU8_fitBytesRef_of_le {n : Nat} {bs : SignalPqxdh.Bytes} (h : bs.length ≤ n) :
    ofU8 (SignalPqxdh.fitBytesRef n bs) =
      ofU8 bs ++ List.replicate (n - (ofU8 bs).length) (0 : BitVec 8) := by
  unfold SignalPqxdh.fitBytesRef
  rw [List.take_of_length_le h, ofU8_append, ofU8_replicate, ofU8_length]
  rfl

private theorem ofU8_xorBytes_replicate (xs : SignalPqxdh.Bytes) (b : UInt8) :
    ofU8 (SignalPqxdh.xorBytes xs (List.replicate xs.length b)) =
      (ofU8 xs).map (· ^^^ b.toBitVec) := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    rcases x with ⟨vx⟩
    rcases b with ⟨vb⟩
    change (vx ^^^ vb) :: ofU8 (SignalPqxdh.xorBytes tl (List.replicate tl.length ⟨vb⟩)) =
      (vx ^^^ vb) :: (ofU8 tl).map (· ^^^ vb)
    rw [ih]

private theorem ofU8_hmacSha256Ref_of_compress {P : SignalPqxdh.Primitives} {F : ShaCompress}
    (hcomp : ∀ st blk, P.sha256Compress st blk = sha256StateBytes (F (sha256StateOf st) (ofU8 blk)))
    (key msg : SignalPqxdh.Bytes) :
    ofU8 (SignalPqxdh.hmacSha256Ref P key msg) = HMAC.hmacWith F (ofU8 key) (ofU8 msg) := by
  unfold SignalPqxdh.hmacSha256Ref HMAC.hmacWith
  let k' := if key.length > 64 then SignalPqxdh.sha256Ref P key else key
  let kpad := SignalPqxdh.fitBytesRef 64 k'
  change ofU8 (SignalPqxdh.sha256Ref P (SignalPqxdh.xorBytes kpad (List.replicate 64 0x5c) ++
      SignalPqxdh.sha256Ref P (SignalPqxdh.xorBytes kpad (List.replicate 64 0x36) ++ msg))) = _
  have hkpad_len : kpad.length = 64 := SignalPqxdh.fitBytesRef_length 64 k'
  rw [ofU8_sha256Ref_of_compress hcomp, ofU8_append, ofU8_sha256Ref_of_compress hcomp, ofU8_append]
  have hxor_opad : ofU8 (SignalPqxdh.xorBytes kpad (List.replicate 64 0x5c)) =
      (ofU8 kpad).map (· ^^^ (0x5c : BitVec 8)) := by
    rw [show (64 : Nat) = kpad.length from hkpad_len.symm]
    exact ofU8_xorBytes_replicate kpad 0x5c
  have hxor_ipad : ofU8 (SignalPqxdh.xorBytes kpad (List.replicate 64 0x36)) =
      (ofU8 kpad).map (· ^^^ (0x36 : BitVec 8)) := by
    rw [show (64 : Nat) = kpad.length from hkpad_len.symm]
    exact ofU8_xorBytes_replicate kpad 0x36
  rw [hxor_opad, hxor_ipad]
  have hle : k'.length ≤ 64 := by
    dsimp only [k']; split
    · rw [sha256Ref_length]; omega
    · omega
  have hkpad_eq : ofU8 kpad = ofU8 k' ++ List.replicate (64 - (ofU8 k').length) (0 : BitVec 8) :=
    ofU8_fitBytesRef_of_le hle
  rw [hkpad_eq]
  dsimp only [k']
  split <;> rename_i hk
  · have hk' : 64 < (ofU8 key).length := by simpa using hk
    simp only [hk', ↓reduceIte, ofU8_sha256Ref_of_compress hcomp]
  · have hk' : ¬ (64 < (ofU8 key).length) := by simpa using hk
    simp only [hk', ↓reduceIte]

private theorem byteArray_toList_loop_eq (data : Array UInt8) :
    ∀ (i : Nat) (acc : List UInt8), i ≤ data.size →
      ByteArray.toList.loop ⟨data⟩ i acc = acc.reverse ++ data.toList.drop i := by
  intro i
  induction hrem : data.size - i generalizing i with
  | zero =>
    intro acc hi
    have heq : i = data.size := by omega
    subst heq
    rw [ByteArray.toList.loop.eq_1]
    have hns : ¬ (data.size < (⟨data⟩ : ByteArray).size) := by
      change ¬ (data.size < data.size); omega
    simp only [hns, ↓reduceIte]
    rw [List.drop_of_length_le (by simp), List.append_nil]
  | succ m ih =>
    intro acc hi
    have hlt : i < data.size := by omega
    have hlts : i < (⟨data⟩ : ByteArray).size := hlt
    rw [ByteArray.toList.loop.eq_1]
    simp only [hlts, ↓reduceIte]
    rw [ih (i + 1) (by omega) ((⟨data⟩ : ByteArray).get! i :: acc) (by omega)]
    have hget : (⟨data⟩ : ByteArray).get! i = data.toList[i]'(by simpa using hlt) := by
      change data[i]! = data.toList[i]'(by simpa using hlt)
      simp [getElem!_pos data i hlt]
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, hget,
        ← List.drop_eq_getElem_cons (by simpa using hlt)]

private theorem byteArray_toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  rcases bs with ⟨data⟩
  rw [ByteArray.toList.eq_1, byteArray_toList_loop_eq data 0 [] (Nat.zero_le _)]
  simp

theorem ofU8_info_pqxdh_eq :
    ofU8 SignalPqxdh.INFO_PQXDH = pqxdhLabelBytes := by
  unfold SignalPqxdh.INFO_PQXDH pqxdhLabelBytes DY.Libsignal.Composed.Refinement.ofByteArray ofU8
  rw [byteArray_toList_eq_data_toList]

theorem ofU8_f_x25519_eq :
    ofU8 SignalPqxdh.F_X25519 = discontinuityBytes :=
  ofU8_replicate 32 0xFF

theorem ofU8_hkdfDerive96_modelPrims (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (secrets : SignalPqxdh.Bytes) :
    let dk := (modelPrims X P).hkdfDerive96 secrets
    (ofU8 dk.rootKey, ofU8 dk.chainKey, ofU8 dk.pqrKey) =
      pqxdhKdfBytes P.C.F (ofU8 secrets) ∧
    (ofU8 dk.rootKey).length = 32 ∧
    (ofU8 dk.chainKey).length = 32 ∧
    (ofU8 dk.pqrKey).length = 32 := by
  intro dk
  let B1 : SignalPqxdh.Primitives :=
    { blockLevelPrims X P with sha512 := SignalPqxdh.sha512Ref (blockLevelPrims X P) }
  have hcomp : ∀ st blk, B1.sha256Compress st blk =
      sha256StateBytes (P.C.F (sha256StateOf st) (ofU8 blk)) := fun _ _ => rfl
  have hdk : dk = SignalPqxdh.hkdfDerive96Ref B1 secrets := rfl
  have hlen1 : (ofU8 dk.rootKey).length = 32 := by
    rw [hdk]; unfold SignalPqxdh.hkdfDerive96Ref SignalPqxdh.hkdfExpand96Ref SignalPqxdh.hmacSha256Ref
    simp [sha256Ref_length]
  have hlen2 : (ofU8 dk.chainKey).length = 32 := by
    rw [hdk]; unfold SignalPqxdh.hkdfDerive96Ref SignalPqxdh.hkdfExpand96Ref SignalPqxdh.hmacSha256Ref
    simp [sha256Ref_length]
  have hlen3 : (ofU8 dk.pqrKey).length = 32 := by
    rw [hdk]; unfold SignalPqxdh.hkdfDerive96Ref SignalPqxdh.hkdfExpand96Ref SignalPqxdh.hmacSha256Ref
    simp [sha256Ref_length]
  refine ⟨?_, hlen1, hlen2, hlen3⟩
  rw [hdk]
  unfold SignalPqxdh.hkdfDerive96Ref SignalPqxdh.hkdfExpand96Ref SignalPqxdh.hkdfExtractRef
    pqxdhKdfBytes Symbolic.Swarm.CREF.TR.hkdfBlock1Bytes
    Symbolic.Swarm.CREF.TR.hkdfBlock2Bytes Symbolic.Swarm.CREF.TR.hkdfBlock3Bytes
  dsimp only
  simp only [ofU8_hmacSha256Ref_of_compress hcomp, ofU8_replicate, ofU8_append,
    ofU8_info_pqxdh_eq, List.append_assoc]
  rfl

end Symbolic.Swarm.CREF.Cli.Slots
