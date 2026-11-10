/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.CREF.Initiate.Is1aRunPure
import Symbolic.Proofs.Swarm.SHARED.StateSizePure
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX

/-!
# `SpqrOooBounded` and Encoding Equations for Initial SPQR States

Identifies `spqrInitOf` on `.a2b` and `.b2a` with `PqRatchetState.encodeRaw (is1StateRaw F d k)`
and proves `SpqrOooBounded` for encoded `is1StateRaw` states via protobuf wire-decoding roundtrip
lemmas when `chain = none`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Grow

open CryptoVerification
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (sha256CompressFunction)
open Symbolic.Swarm.CREF (is1StateRaw is1StateRaw_encodeRaw_length_lt)
open Symbolic.Swarm.SHARED.SpqrBytes (spqrInitOf)

@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

/-! ## `spqrInitOf` equations with `is1StateRaw` -/

theorem spqrInitOf_a2b_eq_is1StateRaw (i : ExternInterpretation) (k : Bytes) :
    spqrInitOf i k [0#8] =
      PqRatchetState.encodeRaw (is1StateRaw (sha256CompressFunction i) .a2b k) := rfl

theorem spqrInitOf_b2a_eq_is1StateRaw (i : ExternInterpretation) (k : Bytes) :
    spqrInitOf i k [1#8] =
      PqRatchetState.encodeRaw (is1StateRaw (sha256CompressFunction i) .b2a k) := rfl

/-! ## Protobuf roundtrip helpers for `chain = none` -/

private theorem pqi_toNat_and7F_64 (x : BitVec 64) : (x &&& 0x7f#64).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#64).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem pqi_toNat_and7F_8 (x : BitVec 8) : (x &&& 0x7f#8).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#8).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem pqi_toNat_and7_64 (x : BitVec 64) : (x &&& 0x7#64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (0x7#64).toNat = 7 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 3

private theorem pqi_or_80_not_lt_80 (b : BitVec 8) : ¬ ((b ||| 0x80#8) < 0x80#8) := by
  revert b; decide

private theorem pqi_or_80_and_7f (b : BitVec 8) : (b ||| 0x80#8) &&& 0x7f#8 = b &&& 0x7f#8 := by
  revert b; decide

private theorem pqi_truncate8_and7f_zeroExtend64 (w : BitVec 64) :
    (w.truncate 8 &&& 0x7f#8).zeroExtend 64 = w &&& 0x7f#64 := by
  apply BitVec.eq_of_toNat_eq
  change ((w.setWidth 8 &&& 0x7f#8).setWidth 64).toNat = (w &&& 0x7f#64).toNat
  rw [BitVec.toNat_setWidth, pqi_toNat_and7F_8, BitVec.toNat_setWidth, pqi_toNat_and7F_64]; omega

private theorem pqi_and7f_eq_self {w : BitVec 64} (hw : w < 0x80#64) : w &&& 0x7f#64 = w := by
  have hlt : w.toNat < 128 := hw
  apply BitVec.eq_of_toNat_eq; rw [pqi_toNat_and7F_64]; omega

private theorem pqi_truncate8_lt_80 {w : BitVec 64} (hw : w < 0x80#64) : w.truncate 8 < 0x80#8 := by
  have hlt : w.toNat < 128 := hw
  change (w.setWidth 8).toNat < 128; rw [BitVec.toNat_setWidth]; omega

private theorem pqi_truncate8_not_ge_2 {w : BitVec 64} (hw : w.toNat < 2) : ¬ (w.truncate 8 ≥ 0x02#8) := by
  change ¬ (2 ≤ (w.setWidth 8).toNat); rw [BitVec.toNat_setWidth]; omega

private theorem pqi_low_or_high (w : BitVec 64) :
    (w &&& 0x7f#64) ||| (w >>> 7) <<< 7 = w := by
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega) (w.toNat / 128)
  have hlt := w.isLt
  simp only [Nat.reducePow] at hor hlt
  rw [BitVec.toNat_or, pqi_toNat_and7F_64, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow]
  rw [show w.toNat / 128 * 128 % 18446744073709551616 = 128 * (w.toNat / 128) by omega,
    Nat.or_comm, ← hor]; omega

private theorem pqi_varint_split (w : BitVec 64) (i : Nat) :
    ((w &&& 0x7f#64) <<< (i * 7)) ||| ((w >>> 7) <<< ((i + 1) * 7)) = w <<< (i * 7) := by
  have h : (i + 1) * 7 = 7 + i * 7 := by omega
  rw [h, BitVec.shiftLeft_add, ← BitVec.shiftLeft_or_distrib, pqi_low_or_high]

private theorem pqi_decodeVarintAux_encodeVarintAux (k : Nat) :
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
        rw [pqi_truncate8_and7f_zeroExtend64, pqi_and7f_eq_self hlt]
      by_cases hi9 : i = 9
      · subst hi9; have hk0 : k = 0 := by omega
        subst hk0; have hw2 : w.toNat < 2 := by simpa using hw
        have hng2 := pqi_truncate8_not_ge_2 hw2
        simp [Proto.decodeVarintAux, hng2, hbyte]
      · have hbeq : (i == 9) = false := beq_false_of_ne hi9
        have hb80 := pqi_truncate8_lt_80 hlt
        simp [Proto.decodeVarintAux, hbeq, hb80, hbyte]
    · simp only [Proto.encodeVarintAux, hlt, ↓reduceIte, List.cons_append]
      have hw_ge : 128 ≤ w.toNat := by change ¬ (w.toNat < 128) at hlt; omega
      have hk : 0 < k := by rcases Nat.eq_zero_or_pos k with rfl | h; (simp at hw; omega); exact h
      have hi9 : (i == 9) = false := beq_false_of_ne (by omega)
      have hnot_lt80 := pqi_or_80_not_lt_80 (w.truncate 8)
      have hbyte : ((w.truncate 8 ||| 0x80#8) &&& 0x7f#8).zeroExtend 64 = w &&& 0x7f#64 := by
        rw [pqi_or_80_and_7f, pqi_truncate8_and7f_zeroExtend64]
      have hw' : (w >>> 7).toNat < 2 ^ (7 * k - 6) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        have he : 7 * (k + 1) - 6 = 7 + (7 * k - 6) := by omega
        rw [he, Nat.pow_add] at hw; exact hw
      simp only [Proto.decodeVarintAux, hi9, Bool.false_eq_true, ↓reduceIte, hnot_lt80, hbyte]
      rw [ih (i + 1) _ (w >>> 7) rest (by omega) hk hw', BitVec.or_assoc, pqi_varint_split]

private theorem pqi_decodeVarint_encodeVarint_append (v : BitVec 64) (rest : Bytes) :
    Proto.decodeVarint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  have h := pqi_decodeVarintAux_encodeVarintAux 10 0 0#64 v rest (by omega) (by omega)
    (by have := v.isLt; simpa using this)
  simpa [Proto.decodeVarint, Proto.encodeVarint] using h

private theorem pqi_encodeVarint_ne_nil (v : BitVec 64) : Proto.encodeVarint v ≠ [] := by
  unfold Proto.encodeVarint Proto.encodeVarintAux; split <;> simp

private theorem pqi_encodeKey_ne_nil (tag : BitVec 32) (wt : Proto.WireType) :
    Proto.encodeKey tag wt ≠ [] := pqi_encodeVarint_ne_nil _

private theorem pqi_decodeKey_encodeKey_append (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  unfold Proto.decodeKey Proto.encodeKey
  rw [pqi_decodeVarint_encodeVarint_append]; dsimp only [Bind.bind, Except.bind]
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
    apply BitVec.eq_of_toNat_eq; rw [pqi_toNat_and7_64, hkey_nat]
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

private theorem pqi_takeExact_append (v rest : Bytes) :
    Proto.takeExact v.length (v ++ rest) = .ok (v, rest) := by
  rw [takeExact_eq_take_drop]; simp

private theorem pqi_mergeUint32_encodeVarint_append (v : BitVec 32) (rest : Bytes) :
    Proto.mergeUint32 .varint (Proto.encodeVarint (v.zeroExtend 64) ++ rest) = .ok (v, rest) := by
  unfold Proto.mergeUint32 Proto.checkWireType
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
    pqi_decodeVarint_encodeVarint_append, Except.ok.injEq, Prod.mk.injEq, and_true]
  apply BitVec.eq_of_toNat_eq
  change ((v.setWidth 64).setWidth 32).toNat = v.toNat
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; have := v.isLt; omega

private theorem pqi_mergeInt32_encodeVarint_append (v : BitVec 32) (rest : Bytes) :
    Proto.mergeInt32 .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) = .ok (v, rest) := by
  unfold Proto.mergeInt32 Proto.checkWireType
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind,
    pqi_decodeVarint_encodeVarint_append, Except.ok.injEq, Prod.mk.injEq, and_true]
  ext i hi; simp [BitVec.getLsbD_signExtend, hi]; omega

private theorem pqi_mergeBytes_encode_append (v rest : Bytes) (hv : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  unfold Proto.mergeBytes Proto.checkWireType
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by rw [BitVec.toNat_ofNat]; omega
  simp [Bind.bind, Except.bind, pqi_decodeVarint_encodeVarint_append, hl, pqi_takeExact_append]

private theorem pqi_mergeMessage_encodeMessage_append {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (encodeRaw : M → Bytes) (m0 sub : M) (rest : Bytes) (depth' : Nat)
    (hsub : (encodeRaw sub).length < 2 ^ 64) :
    Proto.mergeMessage mergeField .lengthDelimited m0
      (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest))
      (depth' + 1) =
    (do
      let m' ← Proto.mergeFieldsLoop mergeField (encodeRaw sub).length m0 (encodeRaw sub) depth'
      .ok (m', rest)) := by
  unfold Proto.mergeMessage Proto.checkWireType
  have hl : (BitVec.ofNat 64 (encodeRaw sub).length).toNat = (encodeRaw sub).length := by
    rw [BitVec.toNat_ofNat]; omega
  simp [pqi_decodeVarint_encodeVarint_append, hl, pqi_takeExact_append, Bind.bind, Except.bind]

private theorem pqi_mergeFieldsLoop_nil {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (fuel : Nat) (m : M) (depth : Nat) :
    Proto.mergeFieldsLoop mergeField fuel m [] depth = .ok m := by
  cases fuel <;> rfl

private theorem pqi_mergeFieldsLoop_encodeKey_step {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (m : M) (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeKey tag wt ++ rest).length
      m (Proto.encodeKey tag wt ++ rest) depth =
    (do
      let (m', rest') ← mergeField m tag wt rest depth
      Proto.mergeFieldsLoop mergeField rest'.length m' rest' depth) := by
  have hdk := pqi_decodeKey_encodeKey_append tag wt rest h1 h2
  rcases hmf_res : mergeField m tag wt rest depth with e | ⟨m', rest'⟩
  · obtain ⟨b, tl, hcons⟩ := List.exists_cons_of_ne_nil
      (List.append_ne_nil_of_left_ne_nil (pqi_encodeKey_ne_nil tag wt) rest)
    rw [hcons] at hdk ⊢
    simp [Proto.mergeFieldsLoop, hdk, hmf_res, Bind.bind, Except.bind]
  · exact (mergeFieldsLoop_step_of_ok hmf m m' depth hdk hmf_res).2

private theorem pqi_mergeFieldsLoop_encodeUint32Field {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → BitVec 32 → M) (m : M) (tag : BitVec 32) (v : BitVec 32) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hupd0 : v = 0#32 → upd m 0#32 = m)
    (hfield : ∀ bs, mergeField m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeUint32 .varint bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeUint32Field tag v ++ rest).length
      m (Proto.encodeUint32Field tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeUint32Field
  by_cases hv : v = 0#32
  · subst hv; simp [hupd0 rfl]
  · have hbeq : (v == 0#32) = false := beq_false_of_ne hv
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [pqi_mergeFieldsLoop_encodeKey_step hmf m tag .varint
          (Proto.encodeVarint (v.zeroExtend 64) ++ rest) depth h1 h2,
        hfield, pqi_mergeUint32_encodeVarint_append]; rfl

private theorem pqi_mergeFieldsLoop_encodeInt32Field {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → BitVec 32 → M) (m : M) (tag : BitVec 32) (v : BitVec 32) (rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hupd0 : v = 0#32 → upd m 0#32 = m)
    (hfield : ∀ bs, mergeField m tag .varint bs depth =
      (do let (x, bs') ← Proto.mergeInt32 .varint bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeInt32Field tag v ++ rest).length
      m (Proto.encodeInt32Field tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeInt32Field
  by_cases hv : v = 0#32
  · subst hv; simp [hupd0 rfl]
  · have hbeq : (v == 0#32) = false := beq_false_of_ne hv
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [pqi_mergeFieldsLoop_encodeKey_step hmf m tag .varint
          (Proto.encodeVarint (v.signExtend 64) ++ rest) depth h1 h2,
        hfield, pqi_mergeInt32_encodeVarint_append]; rfl

private theorem pqi_mergeFieldsLoop_encodeBytesField {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (upd : M → Bytes → M) (m : M) (tag : BitVec 32) (v rest : Bytes) (depth : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hv_len : v.length < 2 ^ 64)
    (hupd0 : v = [] → upd m [] = m)
    (hfield : ∀ bs, mergeField m tag .lengthDelimited bs depth =
      (do let (x, bs') ← Proto.mergeBytes .lengthDelimited bs; .ok (upd m x, bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeBytesField tag v ++ rest).length
      m (Proto.encodeBytesField tag v ++ rest) depth =
    Proto.mergeFieldsLoop mergeField rest.length (upd m v) rest depth := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  cases hv : v.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [pqi_mergeFieldsLoop_encodeKey_step hmf m tag .lengthDelimited
          (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) depth h1 h2,
        hfield, pqi_mergeBytes_encode_append v rest hv_len]; rfl
  · have hv_nil : v = [] := List.isEmpty_iff.mp hv
    subst hv_nil; simp [hupd0 rfl]

private theorem pqi_mergeFieldsLoop_encodeMessage {M S : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    (hmf : ∀ m tag wt depth', ProtoPrefixStep (fun bs => mergeField m tag wt bs depth'))
    (subMergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes))
    (encodeRaw : S → Bytes) (upd : M → S → M) (m : M) (s0 sub : S) (tag : BitVec 32)
    (rest : Bytes) (depth' : Nat)
    (h1 : 1#32 ≤ tag) (h2 : tag ≤ 0x1fffffff#32) (hsub : (encodeRaw sub).length < 2 ^ 64)
    (hfield : ∀ bs, mergeField m tag .lengthDelimited bs (depth' + 1) =
      (do
        let (s', bs') ← Proto.mergeMessage subMergeField .lengthDelimited s0 bs (depth' + 1)
        .ok (upd m s', bs'))) :
    Proto.mergeFieldsLoop mergeField (Proto.encodeMessage encodeRaw tag sub ++ rest).length
      m (Proto.encodeMessage encodeRaw tag sub ++ rest) (depth' + 1) =
    (do
      let s' ← Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length s0 (encodeRaw sub) depth'
      Proto.mergeFieldsLoop mergeField rest.length (upd m s') rest (depth' + 1)) := by
  unfold Proto.encodeMessage; simp only [List.append_assoc]
  rw [pqi_mergeFieldsLoop_encodeKey_step hmf m tag .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 (encodeRaw sub).length) ++ (encodeRaw sub ++ rest))
        (depth' + 1) h1 h2,
      hfield, pqi_mergeMessage_encodeMessage_append subMergeField encodeRaw s0 sub rest depth' hsub]
  rcases Proto.mergeFieldsLoop subMergeField (encodeRaw sub).length s0 (encodeRaw sub) depth' <;> rfl

private theorem pqi_chainParamsPB_mergeFieldsLoop_encodeRaw (p : ChainParamsPB) (depth' : Nat) :
    Proto.mergeFieldsLoop ChainParamsPB.mergeField
      (ChainParamsPB.encodeRaw p).length default (ChainParamsPB.encodeRaw p) depth' = .ok p := by
  unfold ChainParamsPB.encodeRaw
  rw [← List.append_nil (Proto.encodeUint32Field 2#32 p.maxOooKeys)]
  rw [pqi_mergeFieldsLoop_encodeUint32Field protoPrefixStep_chainParamsPB_mergeField
        (fun m v => { m with maxJump := v }) default 1#32 p.maxJump _ depth'
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  rw [pqi_mergeFieldsLoop_encodeUint32Field protoPrefixStep_chainParamsPB_mergeField
        (fun m v => { m with maxOooKeys := v }) _ 2#32 p.maxOooKeys [] depth'
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  rw [pqi_mergeFieldsLoop_nil]

private theorem pqi_encodeBytesField_val_len_le (tag : BitVec 32) (v : Bytes) :
    v.length ≤ (Proto.encodeBytesField tag v).length := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  cases hv : v.isEmpty
  · simp [List.length_append]; omega
  · have hv0 : v = [] := List.isEmpty_iff.mp hv
    subst hv0; simp

private theorem pqi_encodeOptMessage_sub_len_le {S : Type} (encodeRaw : S → Bytes)
    (tag : BitVec 32) (opt : Option S) (sub : S) (h : opt = some sub) :
    (encodeRaw sub).length ≤ (Proto.encodeOptMessage encodeRaw tag opt).length := by
  subst h; unfold Proto.encodeOptMessage Proto.encodeMessage; simp [List.length_append]; omega

private theorem pqi_versionNegotiationPB_mergeFieldsLoop_encodeRaw
    (vn : VersionNegotiationPB) {depth' : Nat}
    (hlen : (VersionNegotiationPB.encodeRaw vn).length < 2 ^ 64) (hdepth : 1 ≤ depth') :
    Proto.mergeFieldsLoop VersionNegotiationPB.mergeField
      (VersionNegotiationPB.encodeRaw vn).length default (VersionNegotiationPB.encodeRaw vn) depth' =
    .ok vn := by
  obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
  have hauth_len : vn.authKey.length < 2 ^ 64 := by
    have hle := pqi_encodeBytesField_val_len_le 1#32 vn.authKey
    unfold VersionNegotiationPB.encodeRaw at hlen
    simp only [List.length_append] at hlen; omega
  have hcp_len : ∀ sub, vn.chainParams = some sub → (ChainParamsPB.encodeRaw sub).length < 2 ^ 64 := by
    intro sub hsub
    have hle := pqi_encodeOptMessage_sub_len_le ChainParamsPB.encodeRaw 4#32 vn.chainParams sub hsub
    unfold VersionNegotiationPB.encodeRaw at hlen
    simp only [List.length_append] at hlen; omega
  unfold VersionNegotiationPB.encodeRaw
  rw [← List.append_nil (Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams)]
  simp only [List.append_assoc]
  rw [pqi_mergeFieldsLoop_encodeBytesField protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with authKey := v }) default 1#32 vn.authKey _ (d + 1)
        (by decide) (by decide) hauth_len (by intro _; rfl) (by intro _; rfl)]
  rw [pqi_mergeFieldsLoop_encodeInt32Field protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with direction := v }) _ 2#32 vn.direction _ (d + 1)
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  rw [pqi_mergeFieldsLoop_encodeInt32Field protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with minVersion := v }) _ 3#32 vn.minVersion _ (d + 1)
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [Proto.encodeOptMessage, List.nil_append]
    rw [pqi_mergeFieldsLoop_nil]
    cases vn; simp at hcp; subst hcp; rfl
  | some sub =>
    have hsub_len : (ChainParamsPB.encodeRaw sub).length < 2 ^ 64 := hcp_len sub hcp
    dsimp only [Proto.encodeOptMessage]
    rw [pqi_mergeFieldsLoop_encodeMessage protoPrefixStep_versionNegotiationPB_mergeField
          ChainParamsPB.mergeField ChainParamsPB.encodeRaw
          (fun m v => { m with chainParams := some v })
          _ ((default : VersionNegotiationPB).chainParams.getD default) sub 4#32 [] d
          (by decide) (by decide) hsub_len
          (by intro bs
              simp only [VersionNegotiationPB.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage ChainParamsPB.mergeField .lengthDelimited
                ((default : VersionNegotiationPB).chainParams.getD default) bs (d + 1) <;> rfl)]
    have hdef : ((default : VersionNegotiationPB).chainParams.getD default) =
        (default : ChainParamsPB) := rfl
    rw [hdef, pqi_chainParamsPB_mergeFieldsLoop_encodeRaw sub d]
    dsimp only [Bind.bind, Except.bind]
    rw [pqi_mergeFieldsLoop_nil]
    cases vn; simp at hcp; subst hcp; rfl

private def pqi_encodeOptInner : Option PqRatchetState.Inner → Bytes
  | none => []
  | some i => PqRatchetState.Inner.encode i

private theorem pqi_pqRatchetState_step_tag1 (m0 : PqRatchetState)
    (opt : Option VersionNegotiationPB) (rest : Bytes) (d : Nat)
    (hm0 : m0.versionNegotiation = none)
    (hlen : (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest).length < 2 ^ 64)
    (hd : 1 ≤ d) :
    Proto.mergeFieldsLoop PqRatchetState.mergeField
      (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest).length
      m0 (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest) (d + 1) =
    Proto.mergeFieldsLoop PqRatchetState.mergeField
      rest.length { m0 with versionNegotiation := opt } rest (d + 1) := by
  cases opt with
  | none =>
    have hmeq : { m0 with versionNegotiation := none } = m0 := by
      cases m0; simp at hm0; subst hm0; rfl
    dsimp only [Proto.encodeOptMessage, List.nil_append]; rw [hmeq]
  | some vn =>
    have hsub : (VersionNegotiationPB.encodeRaw vn).length < 2 ^ 64 := by
      have hle := pqi_encodeOptMessage_sub_len_le VersionNegotiationPB.encodeRaw 1#32 (some vn) vn rfl
      simp only [List.length_append] at hlen; omega
    dsimp only [Proto.encodeOptMessage]
    rw [pqi_mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
          VersionNegotiationPB.mergeField VersionNegotiationPB.encodeRaw
          (fun m v => { m with versionNegotiation := some v })
          m0 (m0.versionNegotiation.getD default) vn 1#32 rest d
          (by decide) (by decide) hsub
          (by intro bs
              simp only [PqRatchetState.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage VersionNegotiationPB.mergeField .lengthDelimited
                (m0.versionNegotiation.getD default) bs (d + 1) <;> rfl)]
    rw [hm0]; dsimp only [Option.getD]
    rw [pqi_versionNegotiationPB_mergeFieldsLoop_encodeRaw vn hsub hd]; rfl

private theorem pqi_pqRatchetState_step_tag3 (m1 st : PqRatchetState)
    (optInner : Option PqRatchetState.Inner) (d : Nat)
    (hlen : (pqi_encodeOptInner optInner).length < 2 ^ 64)
    (hloop : Proto.mergeFieldsLoop PqRatchetState.mergeField
      (pqi_encodeOptInner optInner).length m1 (pqi_encodeOptInner optInner) (d + 1) = .ok st) :
    st.versionNegotiation = m1.versionNegotiation ∧ st.chain = m1.chain := by
  cases optInner with
  | none =>
    dsimp only [pqi_encodeOptInner] at hloop
    rw [pqi_mergeFieldsLoop_nil] at hloop
    injection hloop with hst; subst hst; exact ⟨rfl, rfl⟩
  | some inner =>
    cases inner with
    | v1 v =>
      dsimp only [pqi_encodeOptInner, PqRatchetState.Inner.encode] at hlen hloop
      have hv_len : (V1State.encodeRaw v).length < 2 ^ 64 := by
        unfold Proto.encodeMessage at hlen; simp only [List.length_append] at hlen; omega
      rw [← List.append_nil (Proto.encodeMessage V1State.encodeRaw 3#32 v)] at hloop
      rcases m1 with ⟨vn1, ch1, _ | ⟨⟨v0⟩⟩⟩
      · rw [pqi_mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
              V1State.mergeField V1State.encodeRaw
              (fun m v' => { m with inner := some (.v1 v') })
              ⟨vn1, ch1, none⟩ default v 3#32 [] d
              (by decide) (by decide) hv_len
              (by intro bs; simp [PqRatchetState.mergeField, PqRatchetState.Inner.merge])] at hloop
        rcases hv_loop : Proto.mergeFieldsLoop V1State.mergeField
            (V1State.encodeRaw v).length default (V1State.encodeRaw v) d with e | v'
        · rw [hv_loop] at hloop; nomatch hloop
        · rw [hv_loop] at hloop; dsimp only [Bind.bind, Except.bind] at hloop
          rw [pqi_mergeFieldsLoop_nil] at hloop
          injection hloop with hst; subst hst; exact ⟨rfl, rfl⟩
      · rw [pqi_mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
              V1State.mergeField V1State.encodeRaw
              (fun m v' => { m with inner := some (.v1 v') })
              ⟨vn1, ch1, some (.v1 v0)⟩ v0 v 3#32 [] d
              (by decide) (by decide) hv_len
              (by intro bs; simp [PqRatchetState.mergeField, PqRatchetState.Inner.merge])] at hloop
        rcases hv_loop : Proto.mergeFieldsLoop V1State.mergeField
            (V1State.encodeRaw v).length v0 (V1State.encodeRaw v) d with e | v'
        · rw [hv_loop] at hloop; nomatch hloop
        · rw [hv_loop] at hloop; dsimp only [Bind.bind, Except.bind] at hloop
          rw [pqi_mergeFieldsLoop_nil] at hloop
          injection hloop with hst; subst hst; exact ⟨rfl, rfl⟩

private theorem pqi_decode_chainNone_params {m st : PqRatchetState}
    (hch_none : m.chain = none)
    (hlen : (PqRatchetState.encodeRaw m).length < 2 ^ 64)
    (hdec : PqRatchetState.decode (PqRatchetState.encodeRaw m) = .ok st) :
    st.chain = none ∧ st.versionNegotiation = m.versionNegotiation := by
  have henc : PqRatchetState.encodeRaw m =
      Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 m.versionNegotiation ++
        pqi_encodeOptInner m.inner := by
    unfold PqRatchetState.encodeRaw pqi_encodeOptInner
    rw [hch_none]
    cases m.inner <;> simp [Proto.encodeOptMessage]
  change Proto.mergeFieldsLoop PqRatchetState.mergeField
    (PqRatchetState.encodeRaw m).length default (PqRatchetState.encodeRaw m) (99 + 1) = .ok st at hdec
  rw [henc] at hlen hdec
  rw [pqi_pqRatchetState_step_tag1 default m.versionNegotiation _ 99 rfl hlen (by decide)] at hdec
  have hlen3 : (pqi_encodeOptInner m.inner).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen; omega
  obtain ⟨hvn, hch⟩ := pqi_pqRatchetState_step_tag3
    { (default : PqRatchetState) with versionNegotiation := m.versionNegotiation }
    st m.inner 99 hlen3 hdec
  exact ⟨hch, hvn⟩

/-! ## `SpqrOooBounded` for initial SPQR states -/

theorem spqrOooBounded_is1StateRaw (F : ShaCompress) (d : Direction) (k : Bytes)
    (hk : k.length ≤ 2 ^ 32) :
    SpqrOooBounded (PqRatchetState.encodeRaw (is1StateRaw F d k)) := by
  intro st hdec
  have hlen : (PqRatchetState.encodeRaw (is1StateRaw F d k)).length < 2 ^ 64 := by
    have := is1StateRaw_encodeRaw_length_lt F d k hk
    omega
  obtain ⟨hch, hvn⟩ := pqi_decode_chainNone_params rfl hlen hdec
  refine ⟨fun c hc _ _ => ?_, fun v hv p hp => ?_⟩
  · rw [hch] at hc; cases hc
  · rw [hvn] at hv
    simp only [is1StateRaw, Option.mem_def, Option.some.injEq] at hv
    subst hv
    simp only [Option.mem_def, Option.some.injEq] at hp
    subst hp
    decide

end Symbolic.Swarm.CREF.Grow
