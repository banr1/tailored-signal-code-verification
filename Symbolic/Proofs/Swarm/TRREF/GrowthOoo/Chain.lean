/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX
import VCVio.Prelude.Core

/-!
# Protobuf Roundtrip Lemmas for `ChainParamsPB` and `ChainPB`

Proves that `Proto.mergeFieldsLoop` recovers `p` from `ChainParamsPB.encodeRaw p` and recovers
`ch.params` from `ChainPB.encodeRaw ch` whenever the encoded byte length is `< 2 ^ 64` and
`1 ≤ depth'`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthOoo

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

/-! ## Varint and Key Roundtrip Helpers -/

private theorem toNat_and7F_64 (x : BitVec 64) : (x &&& 0x7f#64).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#64).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem toNat_and7F_8 (x : BitVec 8) : (x &&& 0x7f#8).toNat = x.toNat % 128 := by
  rw [BitVec.toNat_and, show (0x7f#8).toNat = 127 from rfl]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 7

private theorem toNat_contByte (w : BitVec 64) :
    (w.truncate 8 ||| 0x80#8).toNat = w.toNat % 128 + 128 := by
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega) 1
  simp only [Nat.reducePow, Nat.reduceMul] at hor
  have hmod : (w.truncate 8).toNat % 128 = w.toNat % 128 := by rw [BitVec.toNat_setWidth]; omega
  have hlt8 : (w.truncate 8).toNat < 256 := (w.truncate 8).isLt
  rcases (show (w.truncate 8).toNat / 128 = 0 ∨ (w.truncate 8).toNat / 128 = 1 by omega) with h0 | h1
  · have htr : (w.truncate 8).toNat = w.toNat % 128 := by omega
    rw [BitVec.toNat_or, htr, show (0x80#8).toNat = 128 from rfl, Nat.or_comm, ← hor]; omega
  · have htr : (w.truncate 8).toNat = 128 + w.toNat % 128 := by omega
    rw [BitVec.toNat_or, htr, hor, show (0x80#8).toNat = 128 from rfl,
      Nat.or_comm 128 (w.toNat % 128), Nat.or_assoc, Nat.or_self, Nat.or_comm, ← hor]; omega

private theorem low_or_high (w : BitVec 64) : (w &&& 0x7f#64) ||| (w >>> 7) <<< 7 = w := by
  apply BitVec.eq_of_toNat_eq
  have hor := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := w.toNat % 128) (by omega) (w.toNat / 128)
  have hlt := w.isLt; simp only [Nat.reducePow] at hor hlt
  rw [BitVec.toNat_or, toNat_and7F_64, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]
  rw [show w.toNat / 128 * 128 % 18446744073709551616 = 128 * (w.toNat / 128) by omega,
    Nat.or_comm, ← hor]; omega

private theorem varint_split (w : BitVec 64) (idx : Nat) :
    ((w &&& 0x7f#64) <<< (idx * 7)) ||| ((w >>> 7) <<< ((idx + 1) * 7)) = w <<< (idx * 7) := by
  have h : (idx + 1) * 7 = 7 + idx * 7 := by omega
  rw [h, BitVec.shiftLeft_add, ← BitVec.shiftLeft_or_distrib, low_or_high]

private theorem decodeVarintAux_encodeVarintAux (k : Nat) :
    ∀ (idx : Nat) (acc w : BitVec 64) (rest : Bytes),
      idx + k = 10 → 0 < k → w.toNat < 2 ^ (7 * k - 6) →
      Proto.decodeVarintAux k idx acc (Proto.encodeVarintAux k w ++ rest) =
        .ok (acc ||| (w <<< (idx * 7)), rest) := by
  induction k with
  | zero => intro _ _ _ _ _ hk; omega
  | succ k ih =>
    intro idx acc w rest hik _ hw
    by_cases hlt : w < 0x80#64
    · have hlt_nat : w.toNat < 128 := by simpa [BitVec.lt_def] using hlt
      simp only [Proto.encodeVarintAux, hlt, ↓reduceIte, List.cons_append, List.nil_append]
      have h8 : (w.truncate 8).toNat = w.toNat := by rw [BitVec.toNat_setWidth]; omega
      have hbyte : ((w.truncate 8 &&& 0x7f#8).zeroExtend 64) = w := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, toNat_and7F_8, h8]; omega
      by_cases hidx9 : idx == 9
      · have h9 : idx = 9 := beq_iff_eq.mp hidx9; subst h9
        have hk0 : k = 0 := by omega
        subst hk0; have hw2 : w.toNat < 2 := by simpa using hw
        have hge2 : ¬ (w.truncate 8 ≥ 0x02#8) := by
          simp only [ge_iff_le, BitVec.le_def, h8, show (0x02#8).toNat = 2 from rfl]; omega
        simp [Proto.decodeVarintAux, hge2, hbyte]
      · have hlt8 : w.truncate 8 < 0x80#8 := by
          simp only [BitVec.lt_def, h8, show (0x80#8).toNat = 128 from rfl]; omega
        simp [Proto.decodeVarintAux, hidx9, hlt8, hbyte]
    · have hge_nat : 128 ≤ w.toNat := by
        have : ¬ (w.toNat < 128) := by simpa [BitVec.lt_def] using hlt
        omega
      simp only [Proto.encodeVarintAux, hlt, ↓reduceIte, List.cons_append]
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hw; omega
        · exact h
      have hidx9 : (idx == 9) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hcb := toNat_contByte w
      have hlt8 : ¬ ((w.truncate 8 ||| 0x80#8) < 0x80#8) := by
        simp only [BitVec.lt_def, hcb, show (0x80#8).toNat = 128 from rfl]; omega
      have hbyte : (((w.truncate 8 ||| 0x80#8) &&& 0x7f#8).zeroExtend 64) = w &&& 0x7f#64 := by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, toNat_and7F_8, hcb, toNat_and7F_64]; omega
      have hw' : (w >>> 7).toNat < 2 ^ (7 * k - 6) := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
        apply Nat.div_lt_of_lt_mul
        have he : 7 * (k + 1) - 6 = 7 + (7 * k - 6) := by omega
        rw [he, Nat.pow_add] at hw; exact hw
      simp only [Proto.decodeVarintAux, hidx9, Bool.false_eq_true, ↓reduceIte, hlt8, hbyte]
      rw [ih (idx + 1) _ (w >>> 7) rest (by omega) hk hw', BitVec.or_assoc, varint_split]

private theorem decodeVarint_encodeVarint_append (v : BitVec 64) (rest : Bytes) :
    Proto.decodeVarint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  have h := decodeVarintAux_encodeVarintAux 10 0 0#64 v rest (by omega) (by omega) (by simpa using v.isLt)
  simpa [Proto.decodeVarint, Proto.encodeVarint] using h

private theorem truncate_signExtend_32 (v : BitVec 32) : (v.signExtend 64).truncate 32 = v := by
  ext i hi; have hi64 : i < 64 := by omega
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]; simp [hi, hi64]

private theorem mergeUint32_encodeVarint_append (v : BitVec 32) (rest : Bytes) :
    Proto.mergeUint32 .varint (Proto.encodeVarint (v.zeroExtend 64) ++ rest) = .ok (v, rest) := by
  simp [Proto.mergeUint32, Proto.checkWireType, decodeVarint_encodeVarint_append, Bind.bind, Except.bind]

private theorem mergeUint64_encodeVarint_append (v : BitVec 64) (rest : Bytes) :
    Proto.mergeUint64 .varint (Proto.encodeVarint v ++ rest) = .ok (v, rest) := by
  simp [Proto.mergeUint64, Proto.checkWireType, decodeVarint_encodeVarint_append, Bind.bind, Except.bind]

private theorem mergeInt32_encodeVarint_append (v : BitVec 32) (rest : Bytes) :
    Proto.mergeInt32 .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) = .ok (v, rest) := by
  simp [Proto.mergeInt32, Proto.checkWireType, decodeVarint_encodeVarint_append,
    truncate_signExtend_32, Bind.bind, Except.bind]

private theorem mergeBytes_encodeVarint_append (v rest : Bytes) (hlen : v.length < 2 ^ 64) :
    Proto.mergeBytes .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) = .ok (v, rest) := by
  have hl : (BitVec.ofNat 64 v.length).toNat = v.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp [Proto.mergeBytes, Proto.checkWireType, decodeVarint_encodeVarint_append,
    takeExact_eq_take_drop, hl, Bind.bind, Except.bind]

private theorem decodeKey_encodeKey_append (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes)
    (h : Proto.decodeKey (Proto.encodeKey tag wt) = .ok ((tag, wt), [])) :
    Proto.decodeKey (Proto.encodeKey tag wt ++ rest) = .ok ((tag, wt), rest) := by
  simpa using decodeKey_append_of_ok rest h

/-! ## `ChainParamsPB` Field-Merge Roundtrip -/

private theorem chainParamsPB_step_tag1 (m : ChainParamsPB) (v : BitVec 32) (rest : Bytes)
    (depth' : Nat) (hm : m.maxJump = 0#32) :
    Proto.mergeFieldsLoop ChainParamsPB.mergeField
      (Proto.encodeUint32Field 1#32 v ++ rest).length m
      (Proto.encodeUint32Field 1#32 v ++ rest) depth' =
    Proto.mergeFieldsLoop ChainParamsPB.mergeField rest.length { m with maxJump := v } rest depth' := by
  unfold Proto.encodeUint32Field
  by_cases hv : v == 0#32
  · have hv0 : v = 0#32 := beq_iff_eq.mp hv; subst hv0
    have hmeq : { m with maxJump := 0#32 } = m := by cases m; simp at hm; subst hm; rfl
    simp [hmeq]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append 1#32 .varint (Proto.encodeVarint (v.zeroExtend 64) ++ rest) rfl
    have hmf : ChainParamsPB.mergeField m 1#32 .varint
        (Proto.encodeVarint (v.zeroExtend 64) ++ rest) depth' = .ok ({ m with maxJump := v }, rest) := by
      simp [ChainParamsPB.mergeField, mergeUint32_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainParamsPB_mergeField
      m { m with maxJump := v } depth' hdk hmf).2

private theorem chainParamsPB_step_tag2 (m : ChainParamsPB) (v : BitVec 32) (rest : Bytes)
    (depth' : Nat) (hm : m.maxOooKeys = 0#32) :
    Proto.mergeFieldsLoop ChainParamsPB.mergeField
      (Proto.encodeUint32Field 2#32 v ++ rest).length m
      (Proto.encodeUint32Field 2#32 v ++ rest) depth' =
    Proto.mergeFieldsLoop ChainParamsPB.mergeField rest.length { m with maxOooKeys := v } rest depth' := by
  unfold Proto.encodeUint32Field
  by_cases hv : v == 0#32
  · have hv0 : v = 0#32 := beq_iff_eq.mp hv; subst hv0
    have hmeq : { m with maxOooKeys := 0#32 } = m := by cases m; simp at hm; subst hm; rfl
    simp [hmeq]
  · simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append 2#32 .varint (Proto.encodeVarint (v.zeroExtend 64) ++ rest) rfl
    have hmf : ChainParamsPB.mergeField m 2#32 .varint
        (Proto.encodeVarint (v.zeroExtend 64) ++ rest) depth' = .ok ({ m with maxOooKeys := v }, rest) := by
      simp [ChainParamsPB.mergeField, mergeUint32_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainParamsPB_mergeField
      m { m with maxOooKeys := v } depth' hdk hmf).2

/-- `Proto.mergeFieldsLoop` on `ChainParamsPB.encodeRaw p` from `default` returns `.ok p`. -/
theorem chainParamsPB_mergeFieldsLoop_encodeRaw
    (p : ChainParamsPB) (depth' : Nat) :
    Proto.mergeFieldsLoop ChainParamsPB.mergeField
      (ChainParamsPB.encodeRaw p).length default (ChainParamsPB.encodeRaw p) depth' = .ok p := by
  unfold ChainParamsPB.encodeRaw
  rw [← List.append_nil (Proto.encodeUint32Field 2#32 p.maxOooKeys),
    chainParamsPB_step_tag1 default p.maxJump _ depth' rfl,
    chainParamsPB_step_tag2 _ p.maxOooKeys [] depth' rfl]
  cases p; rfl

/-! ## `ChainPB` `params` Roundtrip -/

private theorem chainPB_step_tag1 (m : ChainPB) (v : BitVec 32) (rest : Bytes) (depth' : Nat) :
    ∃ m' : ChainPB, m'.params = m.params ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeInt32Field 1#32 v ++ rest).length m
        (Proto.encodeInt32Field 1#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeInt32Field
  by_cases hv : v == 0#32
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with direction := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append 1#32 .varint (Proto.encodeVarint (v.signExtend 64) ++ rest) rfl
    have hmf : ChainPB.mergeField m 1#32 .varint
        (Proto.encodeVarint (v.signExtend 64) ++ rest) depth' = .ok ({ m with direction := v }, rest) := by
      simp [ChainPB.mergeField, mergeInt32_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with direction := v } depth' hdk hmf).2

private theorem chainPB_step_tag2 (m : ChainPB) (v : BitVec 64) (rest : Bytes) (depth' : Nat) :
    ∃ m' : ChainPB, m'.params = m.params ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeUint64Field 2#32 v ++ rest).length m
        (Proto.encodeUint64Field 2#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeUint64Field
  by_cases hv : v == 0#64
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with currentEpoch := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append 2#32 .varint (Proto.encodeVarint v ++ rest) rfl
    have hmf : ChainPB.mergeField m 2#32 .varint (Proto.encodeVarint v ++ rest) depth' =
        .ok ({ m with currentEpoch := v }, rest) := by
      simp [ChainPB.mergeField, mergeUint64_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with currentEpoch := v } depth' hdk hmf).2

private theorem chainPB_step_tag5 (m : ChainPB) (v : BitVec 64) (rest : Bytes) (depth' : Nat) :
    ∃ m' : ChainPB, m'.params = m.params ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeUint64Field 5#32 v ++ rest).length m
        (Proto.encodeUint64Field 5#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeUint64Field
  by_cases hv : v == 0#64
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with sendEpoch := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    have hdk := decodeKey_encodeKey_append 5#32 .varint (Proto.encodeVarint v ++ rest) rfl
    have hmf : ChainPB.mergeField m 5#32 .varint (Proto.encodeVarint v ++ rest) depth' =
        .ok ({ m with sendEpoch := v }, rest) := by
      simp [ChainPB.mergeField, mergeUint64_encodeVarint_append, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with sendEpoch := v } depth' hdk hmf).2

private theorem chainPB_step_tag4 (m : ChainPB) (v rest : Bytes) (depth' : Nat)
    (hlen : (Proto.encodeBytesField 4#32 v ++ rest).length < 2 ^ 64) :
    ∃ m' : ChainPB, m'.params = m.params ∧
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeBytesField 4#32 v ++ rest).length m
        (Proto.encodeBytesField 4#32 v ++ rest) depth' =
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' := by
  unfold Proto.encodeBytesField at hlen ⊢
  by_cases hv : v.isEmpty
  · exact ⟨m, rfl, by simp [hv]⟩
  · refine ⟨{ m with nextRoot := v }, rfl, ?_⟩
    simp only [hv, Bool.false_eq_true, ↓reduceIte, Proto.encodeBytesUncond, List.append_assoc] at hlen ⊢
    have hv_len : v.length < 2 ^ 64 := by simp only [List.length_append] at hlen; omega
    have hdk := decodeKey_encodeKey_append 4#32 .lengthDelimited
      (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) rfl
    have hmf : ChainPB.mergeField m 4#32 .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 v.length) ++ (v ++ rest)) depth' =
        .ok ({ m with nextRoot := v }, rest) := by
      simp [ChainPB.mergeField, mergeBytes_encodeVarint_append v rest hv_len, Bind.bind, Except.bind]
    exact (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with nextRoot := v } depth' hdk hmf).2

private theorem chainPB_step_tag3_one (m ch' : ChainPB) (ep : ChainEpochPB) (rest : Bytes)
    (depth' : Nat)
    (hlen : (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest).length < 2 ^ 64)
    (hdepth : 1 ≤ depth')
    (hloop : Proto.mergeFieldsLoop ChainPB.mergeField
      (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest).length m
      (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest) depth' = .ok ch') :
    ∃ m' : ChainPB, m'.params = m.params ∧
      Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' = .ok ch' := by
  obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
  have hraw_len : (ChainEpochPB.encodeRaw ep).length < 2 ^ 64 := by
    simp only [Proto.encodeMessage, List.length_append] at hlen; omega
  have hl : (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length).toNat = (ChainEpochPB.encodeRaw ep).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_len]
  have hdk : Proto.decodeKey (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest) =
      .ok ((3#32, .lengthDelimited),
        Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
          (ChainEpochPB.encodeRaw ep ++ rest)) := by
    simp only [Proto.encodeMessage, List.append_assoc]
    exact decodeKey_encodeKey_append 3#32 .lengthDelimited _ rfl
  rcases hsub : Proto.mergeFieldsLoop ChainEpochPB.mergeField
      (ChainEpochPB.encodeRaw ep).length default (ChainEpochPB.encodeRaw ep) d with e | ep'
  · have hmf_err : ChainPB.mergeField m 3#32 .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
          (ChainEpochPB.encodeRaw ep ++ rest)) (d + 1) = .error e := by
      simp [ChainPB.mergeField, Proto.mergeRepeatedMessage, Proto.mergeMessage, Proto.checkWireType,
        decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
    cases hs : Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++ rest with
    | nil => rw [hs] at hdk; nomatch hdk
    | cons b tl =>
      rw [hs] at hloop hdk
      simp only [Proto.mergeFieldsLoop, List.length_cons, hdk, hmf_err, Bind.bind, Except.bind] at hloop
      nomatch hloop
  · have hmf_ok : ChainPB.mergeField m 3#32 .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 (ChainEpochPB.encodeRaw ep).length) ++
          (ChainEpochPB.encodeRaw ep ++ rest)) (d + 1) = .ok ({ m with links := m.links ++ [ep'] }, rest) := by
      simp [ChainPB.mergeField, Proto.mergeRepeatedMessage, Proto.mergeMessage, Proto.checkWireType,
        decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
    have hstep := (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with links := m.links ++ [ep'] } (d + 1) hdk hmf_ok).2
    rw [hstep] at hloop; exact ⟨{ m with links := m.links ++ [ep'] }, rfl, hloop⟩

private theorem chainPB_step_tag3_list :
    ∀ (links : List ChainEpochPB) (m ch' : ChainPB) (rest : Bytes) (depth' : Nat),
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest).length < 2 ^ 64 →
      1 ≤ depth' →
      Proto.mergeFieldsLoop ChainPB.mergeField
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest).length m
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links ++ rest) depth' = .ok ch' →
      ∃ m' : ChainPB, m'.params = m.params ∧
        Proto.mergeFieldsLoop ChainPB.mergeField rest.length m' rest depth' = .ok ch'
  | [], m, ch', rest, depth', _, _, hloop => ⟨m, rfl, hloop⟩
  | ep :: eps, m, ch', rest, depth', hlen, hdepth, hloop => by
    have hcons : Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (ep :: eps) ++ rest =
        Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 ep ++
          (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 eps ++ rest) := by
      simp [Proto.encodeRepeatedMessage, List.append_assoc]
    rw [hcons] at hlen hloop
    obtain ⟨m1, hm1, hloop1⟩ := chainPB_step_tag3_one m ch' ep
      (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 eps ++ rest) depth' hlen hdepth hloop
    have hlen' : (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 eps ++ rest).length < 2 ^ 64 := by
      simp only [List.length_append] at hlen ⊢; omega
    obtain ⟨m2, hm2, hloop2⟩ := chainPB_step_tag3_list eps m1 ch' rest depth' hlen' hdepth hloop1
    exact ⟨m2, hm2.trans hm1, hloop2⟩

private theorem chainPB_step_tag6 (m : ChainPB) (opt : Option ChainParamsPB) (depth' : Nat)
    (hm : m.params = none)
    (hlen : (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt).length < 2 ^ 64)
    (hdepth : 1 ≤ depth') :
    Proto.mergeFieldsLoop ChainPB.mergeField
      (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt).length m
      (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 opt) depth' =
    .ok { m with params := opt } := by
  cases opt with
  | none =>
    have hmeq : { m with params := none } = m := by cases m; simp at hm; subst hm; rfl
    simp [Proto.encodeOptMessage, Proto.mergeFieldsLoop, hmeq]
  | some p =>
    obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
    have hraw_len : (ChainParamsPB.encodeRaw p).length < 2 ^ 64 := by
      simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.length_append] at hlen; omega
    have hl : (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length).toNat = (ChainParamsPB.encodeRaw p).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hraw_len]
    have hdk : Proto.decodeKey (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 (some p)) =
        .ok ((6#32, .lengthDelimited),
          Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
            ChainParamsPB.encodeRaw p) := by
      simp only [Proto.encodeOptMessage, Proto.encodeMessage, List.append_assoc]
      exact decodeKey_encodeKey_append 6#32 .lengthDelimited _ rfl
    have hsub := chainParamsPB_mergeFieldsLoop_encodeRaw p d
    have hmf : ChainPB.mergeField m 6#32 .lengthDelimited
        (Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
          ChainParamsPB.encodeRaw p) (d + 1) = .ok ({ m with params := some p }, []) := by
      have hraw_app : Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
          ChainParamsPB.encodeRaw p = Proto.encodeVarint (BitVec.ofNat 64 (ChainParamsPB.encodeRaw p).length) ++
          (ChainParamsPB.encodeRaw p ++ []) := by simp
      rw [hraw_app]; simp [ChainPB.mergeField, Proto.mergeOptMessage, Proto.mergeMessage, Proto.checkWireType,
        hm, decodeVarint_encodeVarint_append, takeExact_eq_take_drop, hl, hsub, Bind.bind, Except.bind]
    have hstep := (mergeFieldsLoop_step_of_ok protoPrefixStep_chainPB_mergeField
      m { m with params := some p } (d + 1) hdk hmf).2
    rw [hstep]; rfl

/-- If `Proto.mergeFieldsLoop` on `ChainPB.encodeRaw ch` (with byte length `< 2 ^ 64` and
`1 ≤ depth'`) from `default` returns `.ok ch'`, then `ch'.params = ch.params`. -/
theorem chainPB_mergeFieldsLoop_encodeRaw_params
    {ch ch' : ChainPB} {depth' : Nat}
    (hlen : (ChainPB.encodeRaw ch).length < 2 ^ 64)
    (hdepth : 1 ≤ depth')
    (hloop : Proto.mergeFieldsLoop ChainPB.mergeField
      (ChainPB.encodeRaw ch).length default (ChainPB.encodeRaw ch) depth' = .ok ch') :
    ch'.params = ch.params := by
  unfold ChainPB.encodeRaw at hlen hloop; simp only [List.append_assoc] at hlen hloop
  obtain ⟨m1, hm1, h1⟩ := chainPB_step_tag1 default ch.direction _ depth'; rw [h1] at hloop
  obtain ⟨m2, hm2, h2⟩ := chainPB_step_tag2 m1 ch.currentEpoch _ depth'; rw [h2] at hloop
  have hlen3 : (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 ch.links ++
      (Proto.encodeBytesField 4#32 ch.nextRoot ++ (Proto.encodeUint64Field 5#32 ch.sendEpoch ++
        Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params))).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢; omega
  obtain ⟨m3, hm3, hloop3⟩ := chainPB_step_tag3_list ch.links m2 ch' _ depth' hlen3 hdepth hloop
  have hlen4 : (Proto.encodeBytesField 4#32 ch.nextRoot ++ (Proto.encodeUint64Field 5#32 ch.sendEpoch ++
      Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params)).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢; omega
  obtain ⟨m4, hm4, h4⟩ := chainPB_step_tag4 m3 ch.nextRoot _ depth' hlen4; rw [h4] at hloop3
  obtain ⟨m5, hm5, h5⟩ := chainPB_step_tag5 m4 ch.sendEpoch _ depth'; rw [h5] at hloop3
  have hm5_none : m5.params = none := by rw [hm5, hm4, hm3, hm2, hm1]; rfl
  have hlen6 : (Proto.encodeOptMessage ChainParamsPB.encodeRaw 6#32 ch.params).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢; omega
  rw [chainPB_step_tag6 m5 ch.params depth' hm5_none hlen6 hdepth] at hloop3
  injection hloop3 with hch'; subst hch'; rfl

end Symbolic.Swarm.TRREF.GrowthOoo
