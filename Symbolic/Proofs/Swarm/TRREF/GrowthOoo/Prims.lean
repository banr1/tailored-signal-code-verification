/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# SPQR V1 Protobuf Primitive Roundtrip Lemmas

Roundtrip and field-peeling lemmas for `Proto.encodeVarint`, `Proto.encodeKey`, scalar and
length-delimited field mergers, and `Proto.mergeFieldsLoop` on encoded protobuf fields.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthOoo

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

/-! ## Varint and Key Roundtrips -/

private theorem toNat_and7F_64 (x : BitVec 64) : (x &&& 0x7f#64).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#64).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem toNat_and7F_8 (x : BitVec 8) : (x &&& 0x7f#8).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#8).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem toNat_and7_64 (x : BitVec 64) : (x &&& 0x7#64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (0x7#64).toNat = 7 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 3

private theorem or_80_not_lt_80 (b : BitVec 8) : ¬ ((b ||| 0x80#8) < 0x80#8) := by revert b; decide
private theorem or_80_and_7f (b : BitVec 8) : (b ||| 0x80#8) &&& 0x7f#8 = b &&& 0x7f#8 := by revert b; decide

private theorem truncate8_and7f_zeroExtend64 (w : BitVec 64) :
    (w.truncate 8 &&& 0x7f#8).zeroExtend 64 = w &&& 0x7f#64 := by
  apply BitVec.eq_of_toNat_eq
  change ((w.setWidth 8 &&& 0x7f#8).setWidth 64).toNat = (w &&& 0x7f#64).toNat
  rw [BitVec.toNat_setWidth, toNat_and7F_8, BitVec.toNat_setWidth, toNat_and7F_64]; omega

private theorem and7f_eq_self {w : BitVec 64} (hw : w < 0x80#64) : w &&& 0x7f#64 = w := by
  have hlt : w.toNat < 128 := hw
  apply BitVec.eq_of_toNat_eq; rw [toNat_and7F_64]; omega

private theorem truncate8_lt_80 {w : BitVec 64} (hw : w < 0x80#64) : w.truncate 8 < 0x80#8 := by
  have hlt : w.toNat < 128 := hw
  change (w.setWidth 8).toNat < 128; rw [BitVec.toNat_setWidth]; omega

private theorem truncate8_not_ge_2 {w : BitVec 64} (hw : w.toNat < 2) : ¬ (w.truncate 8 ≥ 0x02#8) := by
  change ¬ (2 ≤ (w.setWidth 8).toNat); rw [BitVec.toNat_setWidth]; omega

private theorem low_or_high (w : BitVec 64) :
    (w &&& 0x7f#64) ||| (w >>> 7) <<< 7 = w := by
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega) (w.toNat / 128)
  have hlt := w.isLt
  simp only [Nat.reducePow] at hor hlt
  rw [BitVec.toNat_or, toNat_and7F_64, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  rw [show w.toNat / 128 * 128 % 18446744073709551616 = 128 * (w.toNat / 128) by omega,
    Nat.or_comm, ← hor]; omega

private theorem varint_split (w : BitVec 64) (i : Nat) :
    ((w &&& 0x7f#64) <<< (i * 7)) ||| ((w >>> 7) <<< ((i + 1) * 7)) = w <<< (i * 7) := by
  have h : (i + 1) * 7 = 7 + i * 7 := by omega
  rw [h, BitVec.shiftLeft_add, ← BitVec.shiftLeft_or_distrib, low_or_high]

theorem decodeVarintAux_encodeVarintAux (k : Nat) :
    ∀ (i : Nat) (acc w : BitVec 64) (rest : Bytes),
      i + k = 10 → 0 < k → w.toNat < 2 ^ (7 * k - 6) →
      Proto.decodeVarintAux k i acc (Proto.encodeVarintAux k w ++ rest) =
        .ok (acc ||| (w <<< (i * 7)), rest) := by
  induction k with
  | zero => intro _ _ _ _ _ hk; omega
  | succ k ih =>
    intro i acc w rest hik _ hw
    by_cases hlt : w < 0x80#64
    · simp only [Proto.encodeVarintAux, hlt, ↓reduceIte, List.cons_append, List.nil_append]
      have hbyte : (w.truncate 8 &&& 0x7f#8).zeroExtend 64 = w := by
        rw [truncate8_and7f_zeroExtend64, and7f_eq_self hlt]
      by_cases hi9 : i = 9
      · subst hi9; have hk0 : k = 0 := by omega
        subst hk0; have hw2 : w.toNat < 2 := by simpa using hw
        have hng2 := truncate8_not_ge_2 hw2
        simp [Proto.decodeVarintAux, hng2, hbyte]
      · have hbeq : (i == 9) = false := beq_false_of_ne hi9
        have hb80 := truncate8_lt_80 hlt
        simp [Proto.decodeVarintAux, hbeq, hb80, hbyte]
    · simp only [Proto.encodeVarintAux, hlt, ↓reduceIte, List.cons_append]
      have hw_ge : 128 ≤ w.toNat := by change ¬ (w.toNat < 128) at hlt; omega
      have hk : 0 < k := by rcases Nat.eq_zero_or_pos k with rfl | h; (simp at hw; omega); exact h
      have hi9 : (i == 9) = false := beq_false_of_ne (by omega)
      have hnot_lt80 := or_80_not_lt_80 (w.truncate 8)
      have hbyte : ((w.truncate 8 ||| 0x80#8) &&& 0x7f#8).zeroExtend 64 = w &&& 0x7f#64 := by
        rw [or_80_and_7f, truncate8_and7f_zeroExtend64]
      have hw' : (w >>> 7).toNat < 2 ^ (7 * k - 6) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        have he : 7 * (k + 1) - 6 = 7 + (7 * k - 6) := by omega
        rw [he, Nat.pow_add] at hw; exact hw
      simp only [Proto.decodeVarintAux, hi9, Bool.false_eq_true, ↓reduceIte, hnot_lt80, hbyte]
      rw [ih (i + 1) _ (w >>> 7) rest (by omega) hk hw', BitVec.or_assoc, varint_split]

theorem decodeVarint_encodeVarint_append (v : BitVec 64) (rest : Bytes) :
    Proto.decodeVarint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  have h := decodeVarintAux_encodeVarintAux 10 0 0#64 v rest (by omega) (by omega)
    (by have := v.isLt; simpa using this)
  simpa [Proto.decodeVarint, Proto.encodeVarint] using h

theorem encodeVarint_ne_nil (v : BitVec 64) : Proto.encodeVarint v ≠ [] := by
  unfold Proto.encodeVarint Proto.encodeVarintAux; split <;> simp

theorem encodeKey_ne_nil (tag : BitVec 32) (wt : Proto.WireType) :
    Proto.encodeKey tag wt ≠ [] := encodeVarint_ne_nil _

theorem decodeKey_encodeKey_append (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  unfold Proto.decodeKey Proto.encodeKey
  rw [decodeVarint_encodeVarint_append]; dsimp only [Bind.bind, Except.bind]
  have htag_le : tag.toNat ≤ 0x1fffffff := h2
  have hwt_lt : wt.toU32.toNat < 8 := by cases wt <;> decide
  have hsh : (tag <<< 3).toNat = 8 * tag.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; simp only [Nat.reducePow]; omega
  have hor_nat : ((tag <<< 3) ||| wt.toU32).toNat = 8 * tag.toNat + wt.toU32.toNat := by
    have hor := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := wt.toU32.toNat) hwt_lt tag.toNat
    simp only [Nat.reducePow] at hor; rw [BitVec.toNat_or, hsh, ← hor]
  have hkey_nat : (((tag <<< 3) ||| wt.toU32).zeroExtend 64).toNat = 8 * tag.toNat + wt.toU32.toNat := by
    change (((tag <<< 3) ||| wt.toU32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, hor_nat]; omega
  have hnot_gt : ¬ ((((tag <<< 3) ||| wt.toU32).zeroExtend 64) > 0xffffffff#64) := by
    change ¬ (0xffffffff < (((tag <<< 3) ||| wt.toU32).zeroExtend 64).toNat); rw [hkey_nat]; omega
  have hand : (((tag <<< 3) ||| wt.toU32).zeroExtend 64) &&& 0x7#64 = wt.toU32.zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_and7_64, hkey_nat]
    change (8 * tag.toNat + wt.toU32.toNat) % 8 = (wt.toU32.setWidth 64).toNat
    rw [BitVec.toNat_setWidth]; omega
  have hwt_of : Proto.WireType.ofU64? (wt.toU32.zeroExtend 64) = some wt := by cases wt <;> rfl
  have hshr : (((((tag <<< 3) ||| wt.toU32).zeroExtend 64) >>> 3).truncate 32) = tag := by
    apply BitVec.eq_of_toNat_eq
    change (((((tag <<< 3) ||| wt.toU32).zeroExtend 64) >>> 3).setWidth 32).toNat = tag.toNat
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hkey_nat, Nat.shiftRight_eq_div_pow]
    simp only [Nat.reducePow]; omega
  have hnot_lt_min : ¬ (tag < Proto.MIN_TAG) := Nat.not_lt.mpr h1
  simp only [hnot_gt, ↓reduceIte, hand, hwt_of, hshr, hnot_lt_min]

/-! ## Scalar, Bytes, and Submessage Mergers -/

theorem takeExact_append (v rest : Bytes) :
    Proto.takeExact v.length (v ++ rest) = .ok (v, rest) := by
  rw [takeExact_eq_take_drop]; simp

theorem mergeUint64_encodeVarint_append (v : BitVec 64) (rest : Bytes) :
    Proto.mergeUint64 .varint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  unfold Proto.mergeUint64 Proto.checkWireType
  simp [Bind.bind, Except.bind, decodeVarint_encodeVarint_append]

theorem mergeInt32_encodeVarint_append (v : BitVec 32) (rest : Bytes) :
    Proto.mergeInt32 .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) = .ok (v, rest) := by
  unfold Proto.mergeInt32 Proto.checkWireType
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
    decodeVarint_encodeVarint_append, Except.ok.injEq, Prod.mk.injEq, and_true]
  ext i hi; simp [BitVec.getLsbD_signExtend, hi]; omega

theorem mergeBytes_encode_append (v rest : Bytes) (hv : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  unfold Proto.mergeBytes Proto.checkWireType
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by rw [BitVec.toNat_ofNat]; omega
  simp [Bind.bind, Except.bind, decodeVarint_encodeVarint_append, hl, takeExact_append]

theorem mergeMessage_encodeMessage_append {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (encodeRaw : M → Bytes) (m0 sub : M) (rest : Bytes) (depth' : Nat)
    (hsub : (encodeRaw sub).length < 2 ^ 64) :
    Proto.mergeMessage mergeField .lengthDelimited m0
      (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest))
      (depth' + 1) =
    (do let m' ← Proto.mergeFieldsLoop mergeField (encodeRaw sub).length m0 (encodeRaw sub) depth'; .ok (m', rest)) := by
  unfold Proto.mergeMessage Proto.checkWireType
  have hl : (BitVec.ofNat 64 (encodeRaw sub).length).toNat = (encodeRaw sub).length := by
    rw [BitVec.toNat_ofNat]; omega
  simp [decodeVarint_encodeVarint_append, hl, takeExact_append, Bind.bind, Except.bind]

theorem mergeOptMessage_encodeMessage_append {M : Type} [Inhabited M]
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (encodeRaw : M → Bytes) (opt : Option M) (sub : M) (rest : Bytes) (depth' : Nat)
    (hsub : (encodeRaw sub).length < 2 ^ 64) :
    Proto.mergeOptMessage mergeField .lengthDelimited opt
      (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest))
      (depth' + 1) =
    (do let m' ← Proto.mergeFieldsLoop mergeField (encodeRaw sub).length (opt.getD default) (encodeRaw sub) depth'; .ok (some m', rest)) := by
  unfold Proto.mergeOptMessage
  rw [mergeMessage_encodeMessage_append mergeField encodeRaw (opt.getD default) sub rest depth' hsub]
  rcases Proto.mergeFieldsLoop mergeField (encodeRaw sub).length (opt.getD default) (encodeRaw sub) depth' <;> rfl

/-! ## `mergeFieldsLoop` Field-Peeling Steps -/

theorem mergeFieldsLoop_nil {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (fuel : Nat) (m : M) (depth : Nat) :
    Proto.mergeFieldsLoop mergeField fuel m [] depth = .ok m := by cases fuel <;> rfl

theorem mergeFieldsLoop_encodeKey_step {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeKey tag wt ++ rest).length
      m (Proto.encodeKey tag wt ++ rest) depth =
    (do let (m', rest') ← mergeField m tag wt rest depth; Proto.mergeFieldsLoop mergeField rest'.length m' rest' depth) := by
  have hdk := decodeKey_encodeKey_append tag wt rest h1 h2
  rcases hmf_res : mergeField m tag wt rest depth with e | ⟨m', rest'⟩
  · obtain ⟨b, tl, hcons⟩ := List.exists_cons_of_ne_nil
      (List.append_ne_nil_of_left_ne_nil (encodeKey_ne_nil tag wt) rest)
    rw [hcons] at hdk ⊢; simp [Proto.mergeFieldsLoop, hdk, hmf_res, Bind.bind, Except.bind]
  · exact (mergeFieldsLoop_step_of_ok hmf m m' depth hdk hmf_res).2

theorem mergeFieldsLoop_encodeUint64Field {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → BitVec 64 → M) (m : M) (tag : BitVec 32) (v : BitVec 64) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hupd0 : v = 0#64 → upd m 0#64 = m)
    (hfield : ∀ bs, mergeField m tag .varint bs depth = (do let (x, bs') ← Proto.mergeUint64 .varint bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeUint64Field tag v ++ rest).length
      m (Proto.encodeUint64Field tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeUint64Field
  by_cases hv : v = 0#64
  · subst hv; simp [hupd0 rfl]
  · have hbeq : (v == 0#64) = false := beq_false_of_ne hv
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [mergeFieldsLoop_encodeKey_step hmf m tag .varint (Proto.encodeVarint v ++ rest) depth h1 h2,
        hfield, mergeUint64_encodeVarint_append]; rfl

theorem mergeFieldsLoop_encodeInt32Field {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → BitVec 32 → M) (m : M) (tag : BitVec 32) (v : BitVec 32) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hupd0 : v = 0#32 → upd m 0#32 = m)
    (hfield : ∀ bs, mergeField m tag .varint bs depth = (do let (x, bs') ← Proto.mergeInt32 .varint bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeInt32Field tag v ++ rest).length
      m (Proto.encodeInt32Field tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeInt32Field
  by_cases hv : v = 0#32
  · subst hv; simp [hupd0 rfl]
  · have hbeq : (v == 0#32) = false := beq_false_of_ne hv
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [mergeFieldsLoop_encodeKey_step hmf m tag .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) depth h1 h2,
        hfield, mergeInt32_encodeVarint_append]; rfl

theorem mergeFieldsLoop_encodeBytesField {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → Bytes → M) (m : M) (tag : BitVec 32) (v rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hv_len : v.length < 2 ^ 64) (hupd0 : v = [] → upd m [] = m)
    (hfield : ∀ bs, mergeField m tag .lengthDelimited bs depth = (do let (x, bs') ← Proto.mergeBytes .lengthDelimited bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeBytesField tag v ++ rest).length
      m (Proto.encodeBytesField tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  cases hv : v.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [mergeFieldsLoop_encodeKey_step hmf m tag .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) depth h1 h2,
        hfield, mergeBytes_encode_append v rest hv_len]; rfl
  · have hv_nil : v = [] := List.isEmpty_iff.mp hv
    subst hv_nil; simp [hupd0 rfl]

theorem mergeFieldsLoop_encodeMessage {M S : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (subMergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes))
    (encodeRaw : S → Bytes) (upd : M → S → M) (m : M) (s0 sub : S) (tag : BitVec 32) (rest : Bytes) (depth' : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hsub : (encodeRaw sub).length < 2 ^ 64)
    (hfield : ∀ bs, mergeField m tag .lengthDelimited bs (depth' + 1) = (do let (s', bs') ← Proto.mergeMessage subMergeField .lengthDelimited s0 bs (depth' + 1); .ok (upd m s', bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeMessage encodeRaw tag sub ++ rest).length
      m (Proto.encodeMessage encodeRaw tag sub ++ rest) (depth' + 1) =
    (do let s' ← Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length s0 (encodeRaw sub) depth'; Proto.mergeFieldsLoop mergeField rest.length (upd m s') rest (depth' + 1)) := by
  unfold Proto.encodeMessage; simp only [List.append_assoc]
  rw [mergeFieldsLoop_encodeKey_step hmf m tag .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest)) (depth' + 1) h1 h2,
      hfield, mergeMessage_encodeMessage_append subMergeField encodeRaw s0 sub rest depth' hsub]
  rcases Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length s0 (encodeRaw sub) depth' <;> rfl

theorem mergeFieldsLoop_encodeOptMessage {M S : Type} [Inhabited S]
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (subMergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes))
    (encodeRaw : S → Bytes) (getOpt : M → Option S) (upd : M → Option S → M)
    (m : M) (opt : Option S) (tag : BitVec 32) (rest : Bytes) (depth' : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hsub : ∀ sub, opt = some sub → (encodeRaw sub).length < 2 ^ 64)
    (hfield : ∀ bs, mergeField m tag .lengthDelimited bs (depth' + 1) = (do let (s', bs') ← Proto.mergeOptMessage subMergeField .lengthDelimited (getOpt m) bs (depth' + 1); .ok (upd m s', bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeOptMessage encodeRaw tag opt ++ rest).length
      m (Proto.encodeOptMessage encodeRaw tag opt ++ rest) (depth' + 1) =
    match opt with
    | none => Proto.mergeFieldsLoop mergeField rest.length m rest (depth' + 1)
    | some sub =>
      (do let s' ← Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length ((getOpt m).getD default) (encodeRaw sub) depth'; Proto.mergeFieldsLoop mergeField rest.length (upd m (some s')) rest (depth' + 1)) := by
  cases opt with
  | none => simp [Proto.encodeOptMessage]
  | some sub =>
    unfold Proto.encodeOptMessage Proto.encodeMessage; simp only [List.append_assoc]
    rw [mergeFieldsLoop_encodeKey_step hmf m tag .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest)) (depth' + 1) h1 h2,
        hfield, mergeOptMessage_encodeMessage_append subMergeField encodeRaw (getOpt m) sub rest depth' (hsub sub rfl)]
    rcases Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length ((getOpt m).getD default) (encodeRaw sub) depth' <;> rfl

end Symbolic.Swarm.TRREF.GrowthOoo
