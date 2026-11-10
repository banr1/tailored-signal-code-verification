/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto -- shake: keep
public import Mathlib.Algebra.Group.Nat.Defs
import LibsignalBinary.Proofs.SpqrV1Sync.Codec.Varint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ProofLib.BV.WidthNorm
import VCVio.Prelude.Core

/-!
# Prost Field Key and Scalar Round-Trip Lemmas

Round-trip lemmas showing that each `Proto.merge*` scalar and bytes decoder inverts the
corresponding `Proto.encode*Field` writer on the field payload with arbitrary trailing bytes.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Codec

open CryptoVerification.LibsignalSpqrV1 hiding WireType DecodeErr decodeVarint encodeVarint
open CryptoVerification.LibsignalSpqrV1.Proto (WireType DecodeErr)

private theorem cdk_wt_toNat_lt (wt : WireType) : wt.toU32.toNat < 8 := by
  cases wt <;> decide

private theorem cdk_ofU64_toU32 (wt : WireType) :
    WireType.ofU64? (wt.toU32.zeroExtend 64) = some wt := by
  cases wt <;> rfl

private theorem cdk_key_toNat (tag : BitVec 32) (wt : WireType) (h2 : tag.toNat < 2 ^ 29) :
    (((tag <<< 3) ||| wt.toU32).zeroExtend 64).toNat = 8 * tag.toNat + wt.toU32.toNat := by
  have hw := cdk_wt_toNat_lt wt
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := wt.toU32.toNat) (by omega) tag.toNat
  simp only [Nat.reducePow] at hor
  rw [BitVec.toNat_setWidth, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  rw [show tag.toNat * 8 % 4294967296 = 8 * tag.toNat by omega, ← hor]
  omega

/-- Field keys round-trip for every valid prost tag (`1 ≤ tag.toNat < 2 ^ 29`). -/
theorem decodeKey_encodeKey (tag : BitVec 32) (wt : WireType) (rest : Bytes)
    (h1 : 1 ≤ tag.toNat) (h2 : tag.toNat < 2 ^ 29) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  let key : BitVec 64 := ((tag <<< 3) ||| wt.toU32).zeroExtend 64
  have hw := cdk_wt_toNat_lt wt
  have hkey : key.toNat = 8 * tag.toNat + wt.toU32.toNat := cdk_key_toNat tag wt h2
  have hle : ¬ (key > 0xffffffff#64) := by
    simp only [gt_iff_lt, BitVec.lt_def, hkey]
    change ¬ (4294967295 < 8 * tag.toNat + wt.toU32.toNat)
    omega
  have hand : key &&& 0x7#64 = wt.toU32.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7#64).toNat = 7 from rfl,
      Nat.and_two_pow_sub_one_eq_mod key.toNat 3, hkey, BitVec.toNat_setWidth]
    omega
  have hshr : (key >>> 3).truncate 32 = tag := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hkey]
    omega
  have hmin : ¬ (tag < Proto.MIN_TAG) := by
    simp only [Proto.MIN_TAG, BitVec.lt_def]
    change ¬ (tag.toNat < 1)
    omega
  simp only [Proto.decodeKey, Proto.encodeKey, proto_decodeVarint_encodeVarint,
    Bind.bind, Except.bind, key, hle, ↓reduceIte, hand, cdk_ofU64_toU32, hshr, hmin]

theorem takeExact_append (v rest : Bytes) :
    Proto.takeExact v.length (v ++ rest) = .ok (v, rest) := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [Proto.takeExact, ih, Bind.bind, Except.bind]

/-- Length-delimited byte fields round-trip when the payload length fits in 64 bits. -/
theorem mergeBytes_encode (v rest : Bytes) (h : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by
    rw [BitVec.toNat_ofNat]; omega
  simp only [Proto.mergeBytes, Proto.checkWireType, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, proto_decodeVarint_encodeVarint, hl, takeExact_append, Bind.bind, Except.bind]

theorem mergeUint32_encode (v : BitVec 32) (rest : Bytes) :
    Proto.mergeUint32 .varint (Proto.encodeVarint (v.zeroExtend 64) ++ rest) = .ok (v, rest) := by
  simp only [Proto.mergeUint32, Proto.checkWireType, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, proto_decodeVarint_encodeVarint, Bind.bind, Except.bind]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

theorem mergeUint64_encode (v : BitVec 64) (rest : Bytes) :
    Proto.mergeUint64 .varint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  simp only [Proto.mergeUint64, Proto.checkWireType, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, proto_decodeVarint_encodeVarint, Bind.bind, Except.bind]

/-- Prost encodes `int32` fields by sign-extending to 64 bits before varint encoding. -/
theorem mergeInt32_encode (v : BitVec 32) (rest : Bytes) :
    Proto.mergeInt32 .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) = .ok (v, rest) := by
  simp only [Proto.mergeInt32, Proto.checkWireType, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, proto_decodeVarint_encodeVarint, Bind.bind, Except.bind]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend, hi]
  omega

/-- `encodeBoolField` omits `false` and writes `true` as the single byte `1`. -/
theorem mergeBool_encode_true (rest : Bytes) :
    Proto.mergeBool .varint (1#8 :: rest) = .ok (true, rest) := by
  have h : Proto.encodeVarint 1#64 = [1#8] := by decide
  rw [show (1#8 :: rest) = Proto.encodeVarint 1#64 ++ rest by rw [h]; rfl]
  simp only [Proto.mergeBool, Proto.checkWireType, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, proto_decodeVarint_encodeVarint, Bind.bind, Except.bind]
  rfl

/-! ## Field writers after the key -/

theorem encodeUint32Field_of_ne (tag v : BitVec 32) (h : v ≠ 0#32) :
    Proto.encodeUint32Field tag v = Proto.encodeKey tag .varint ++ Proto.encodeVarint (v.zeroExtend 64) := by
  simp [Proto.encodeUint32Field, h]

theorem encodeUint64Field_of_ne (tag : BitVec 32) (v : BitVec 64) (h : v ≠ 0#64) :
    Proto.encodeUint64Field tag v = Proto.encodeKey tag .varint ++ Proto.encodeVarint v := by
  simp [Proto.encodeUint64Field, h]

theorem encodeInt32Field_of_ne (tag v : BitVec 32) (h : v ≠ 0#32) :
    Proto.encodeInt32Field tag v = Proto.encodeKey tag .varint ++ Proto.encodeVarint (v.signExtend 64) := by
  simp [Proto.encodeInt32Field, h]

theorem encodeBytesField_of_ne (tag : BitVec 32) (v : Bytes) (h : v ≠ []) :
    Proto.encodeBytesField tag v = Proto.encodeBytesUncond tag v := by
  cases v with
  | nil => exact absurd rfl h
  | cons b v => rfl

/-! ## Sanity checks -/

#guard Proto.decodeKey (Proto.encodeKey 11#32 .lengthDelimited ++ [5#8]) = .ok ((11#32, .lengthDelimited), [5#8])
#guard Proto.decodeKey (Proto.encodeKey 0x1fffffff#32 .varint) = .ok ((0x1fffffff#32, .varint), [])
#guard Proto.mergeUint32 .varint (Proto.encodeVarint ((0xffffffff#32).zeroExtend 64) ++ [3#8]) =
  .ok (0xffffffff#32, [3#8])
#guard Proto.mergeInt32 .varint (Proto.encodeVarint ((-5 : BitVec 32).signExtend 64)) = .ok ((-5 : BitVec 32), [])
#guard Proto.mergeBool .varint [1#8, 0#8] = .ok (true, [0#8])
#guard Proto.mergeBytes .lengthDelimited (Proto.encodeVarint 3#64 ++ ([1#8, 2#8, 3#8] ++ [4#8])) =
  .ok ([1#8, 2#8, 3#8], [4#8])

end CryptoVerification.SpqrV1Sync.Codec
