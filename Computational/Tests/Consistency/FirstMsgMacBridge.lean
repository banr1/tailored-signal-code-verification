/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhInputs
public import LibsignalBinary.Specifications.SignalPqxdh.Model
import Computational.Proofs.SignalPqxdh.Security.AeadMacInputInj

/-!
# First-Message MAC Input Bridge Between PQXDH and Session Models

Proves that `SignalPqxdh.aeadMacInput (firstMsgAD ikA ikB rk pq) ct` equals, byte for byte, the
session layer's `computeMac` input `macIds sender receiver ++ serializeContent protoSignalCodec
currentVersion rk 0 0 ct pq none` for every `pq` and ciphertext shorter than `2^64` bytes
(`addresses = none`, DEV-PQ31).
-/

@[expose] public section

namespace CryptoVerification.E2E

open CryptoGames CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

private theorem toU8_append (a b : List (BitVec 8)) : toU8 (a ++ b) = toU8 a ++ toU8 b := by
  simp [toU8]

private theorem toU8_cons (x : BitVec 8) (a : List (BitVec 8)) :
    toU8 (x :: a) = UInt8.ofBitVec x :: toU8 a := rfl

/-- `encodeVarintAux` agrees with `SignalPqxdh.pbVarint` on bounded `BitVec 64` values. -/
private theorem toU8_encodeVarintAux (k : Nat) (v : BitVec 64)
    (hk : v.toNat < 2 ^ (7 * (k + 1))) :
    toU8 (encodeVarintAux (k + 1) v) = SignalPqxdh.pbVarint v.toNat := by
  induction k generalizing v with
  | zero =>
    have h : v.toNat < 128 := by simpa using hk
    simp only [encodeVarintAux, show v.toNat < 0x80 from h, ↓reduceIte,
      SignalPqxdh.pbVarint_lt h, toU8, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    apply UInt8.toNat_inj.mp
    simp [Nat.toUInt8]
  | succ k ih =>
    by_cases h : v.toNat < 128
    · simp only [encodeVarintAux, show v.toNat < 0x80 from h, ↓reduceIte,
        SignalPqxdh.pbVarint_lt h, toU8, List.map_cons, List.map_nil, List.cons.injEq, and_true]
      apply UInt8.toNat_inj.mp
      simp [Nat.toUInt8]
    · have hs : (v >>> 7).toNat = v.toNat / 128 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have hp : 2 ^ (7 * (k + 1 + 1)) = 2 ^ (7 * (k + 1)) * 128 := by
        rw [show 7 * (k + 1 + 1) = 7 * (k + 1) + 7 by omega, Nat.pow_add]
      have hk' : (v >>> 7).toNat < 2 ^ (7 * (k + 1)) := by
        rw [hs, Nat.div_lt_iff_lt_mul (by omega)]
        omega
      have ih' := ih (v >>> 7) hk'
      rw [hs] at ih'
      simp only [encodeVarintAux, show ¬ v.toNat < 0x80 from h, ↓reduceIte,
        SignalPqxdh.pbVarint_ge h, toU8, List.map_cons, List.cons.injEq]
      refine ⟨?_, ih'⟩
      apply UInt8.toNat_inj.mp
      simp [Nat.toUInt8]
      have h127 : UInt8.toNat (OfNat.ofNat 127) = 2 ^ 7 - 1 := rfl
      have h128 : UInt8.toNat (OfNat.ofNat 128) = 2 ^ 7 * 1 := rfl
      have hm : v.toNat % 128 < 2 ^ 7 := Nat.mod_lt _ (by omega)
      have hmm : v.toNat % 256 % 2 ^ 7 = v.toNat % 128 := Nat.mod_mod_of_dvd _ (by decide)
      rw [h127, h128, Nat.and_two_pow_sub_one_eq_mod, hmm, Nat.or_comm,
        ← Nat.two_pow_add_eq_or_of_lt hm]
      omega

private theorem toU8_encodeVarint_len (n : Nat) (hn : n < 2 ^ 64) :
    toU8 (encodeVarint (BitVec.ofNat 64 n)) = SignalPqxdh.pbVarint n := by
  have h := toU8_encodeVarintAux 9 (BitVec.ofNat 64 n)
    (by simp only [BitVec.toNat_ofNat]; omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  exact h

/-- `encodeBytesField` agrees with `SignalPqxdh.pbBytesField` for single-byte tags (`t < 16`). -/
private theorem toU8_encodeBytesField (t : Nat) (ht : t < 16) (v : List (BitVec 8))
    (hv : v.length < 2 ^ 64) :
    toU8 (encodeBytesField t (some v)) = SignalPqxdh.pbBytesField t (toU8 v) := by
  have hkey : toU8 (encodeKey t .lengthDelimited) = [(8 * t + 2).toUInt8] := by
    rw [encodeKey, WireType.toNat, show t * 8 + 2 = 8 * t + 2 by omega,
      toU8_encodeVarint_len _ (by omega), SignalPqxdh.pbVarint_lt (by omega)]
  have hlen : (toU8 v).length = v.length := by simp [toU8]
  rw [encodeBytesField, toU8_append, toU8_append, hkey, toU8_encodeVarint_len _ hv,
    SignalPqxdh.pbBytesField, hlen]
  rfl

private theorem toU8_encodeBytesField_pq (pq : List (BitVec 8)) (hpq : pq.length < 2 ^ 64) :
    toU8 (encodeBytesField 5 (if pq.isEmpty then none else some pq)) =
      if (toU8 pq).isEmpty then [] else SignalPqxdh.pbBytesField 5 (toU8 pq) := by
  have he : (toU8 pq).isEmpty = pq.isEmpty := by simp [toU8]
  rw [he]
  by_cases h : pq.isEmpty
  · simp [h, encodeBytesField, toU8]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact toU8_encodeBytesField 5 (by omega) pq hpq

private theorem toU8_publicKey_serialize (k : PublicKey) :
    toU8 k.serialize = SignalPqxdh.encodeEC (toU8 k.bytes.toList) := rfl

/-- Session-layer `computeMac` input (version 4, counters 0, `addresses = none`) equals
`SignalPqxdh.aeadMacInput` on `firstMsgAD`. -/
theorem firstMsg_macInput_eq_aeadMacInput (sender receiver : IdentityKey) (rk : PublicKey)
    (ct pq : List (BitVec 8)) (hct : ct.length < 2 ^ 64) (hpq : pq.length < 2 ^ 64) :
    toU8 ((macIds sender receiver).toList ++
        serializeContent protoSignalCodec currentVersion rk 0#32 0#32 ct pq none) =
      SignalPqxdh.aeadMacInput
        (SignalPqxdh.firstMsgAD (toU8 sender.publicKey.bytes.toList)
          (toU8 receiver.publicKey.bytes.toList) (toU8 rk.bytes.toList) (toU8 pq))
        (toU8 ct) := by
  have hl : ∀ k : PublicKey, (toU8 k.bytes.toList).length = 32 := fun k => by
    simp [toU8, List.Vector.toList_length]
  have hrk : rk.serialize.length < 2 ^ 64 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  rw [SignalPqxdh.aeadMacInput_firstMsgAD _ _ _ _ _ (hl _) (hl _) (hl _)]
  have hids : (macIds sender receiver).toList = sender.publicKey.serialize ++
      receiver.publicKey.serialize := rfl
  have h2 : toU8 (encodeUint32Field 2 (some 0#32)) = [0x10, 0x00] := by decide
  have h3 : toU8 (encodeUint32Field 3 (some 0#32)) = [0x18, 0x00] := by decide
  have hv : UInt8.ofBitVec (versionByte currentVersion) = 0x44 := by decide
  have he : toU8 (encodeBytesField 6 none) = [] := rfl
  rw [hids]
  dsimp only [serializeContent, protoSignalCodec, encode]
  simp only [toU8_append, toU8_cons]
  simp only [hv, toU8_publicKey_serialize, toU8_encodeBytesField 1 (by omega) _ hrk,
    h2, h3, toU8_encodeBytesField 4 (by omega) _ hct, toU8_encodeBytesField_pq pq hpq, he,
    List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- When `pq_ratchet = []` (DEV-PQ3), `serializeContent` equals `aeadMacInput` after dropping the
66-byte identity-key prefix. -/
theorem firstMsg_serializeContent_eq_aeadMacInput_drop (ikA ikB : IdentityKey) (rk : PublicKey)
    (ct : List (BitVec 8)) (hct : ct.length < 2 ^ 64) :
    toU8 (serializeContent protoSignalCodec currentVersion rk 0#32 0#32 ct [] none) =
      (SignalPqxdh.aeadMacInput
        (SignalPqxdh.firstMsgAD (toU8 ikA.publicKey.bytes.toList)
          (toU8 ikB.publicKey.bytes.toList) (toU8 rk.bytes.toList) [])
        (toU8 ct)).drop 66 := by
  have h := firstMsg_macInput_eq_aeadMacInput ikA ikB rk ct [] hct (by simp)
  rw [toU8_append] at h
  have hlen : (toU8 (macIds ikA ikB).toList).length = 66 := by
    simp [toU8, List.Vector.toList_length]
  rw [show toU8 ([] : List (BitVec 8)) = [] from rfl] at h
  rw [← h, List.drop_left' hlen]

end CryptoVerification.E2E
