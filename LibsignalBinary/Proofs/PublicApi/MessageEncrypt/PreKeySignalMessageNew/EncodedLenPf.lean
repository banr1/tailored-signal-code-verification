/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Stepping Proof for `PreKeySignalMessage::encoded_len`

Hardware `clz` varint-length equivalence, field-layout decomposition, non-overflow bounds, and
per-tag symbolic execution steps for `<wire::PreKeySignalMessage as prost::message::Message>::encoded_len`
(`0x2da84`, block `119`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPf

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Hardware `clz` Varint-Length Formula -/

private theorem hwVarintFormula_fin (c : Fin 64) :
    (((((BitVec.ofNat 64 c.val) ^^^ 0x3f#64) + (((BitVec.ofNat 64 c.val) ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6) =
      BitVec.ofNat 64 ((63 - c.val) / 7 + 1) := by
  revert c
  decide

private theorem hwVarintFormula_bvShift_fin (c : Fin 64) :
    (((((BitVec.ofNat 64 c.val) ^^^ 63#64) + (((BitVec.ofNat 64 c.val) ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64) =
      BitVec.ofNat 64 ((63 - c.val) / 7 + 1) := by
  revert c
  decide

private theorem prost_varint_length_of_pow_bounds :
    ∀ (b y : Nat), 2 ^ b ≤ y → y < 2 ^ (b + 1) → (Prost.varint y).length = b / 7 + 1 := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro y hlo hhi
    rw [Prost.varint]
    by_cases hb : b < 7
    · have hpow : 2 ^ (b + 1) ≤ 128 := by
        have : b + 1 ≤ 7 := by omega
        calc 2 ^ (b + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) this
        _ = 128 := by decide
      have hy : y < 128 := Nat.lt_of_lt_of_le hhi hpow
      simp [hy, Nat.div_eq_of_lt hb]
    · have hb7 : 7 ≤ b := by omega
      have hpow_lo : 128 * 2 ^ (b - 7) = 2 ^ b := by
        conv_rhs => rw [show b = 7 + (b - 7) by omega, Nat.pow_add]
      have hpow_hi : 128 * 2 ^ (b - 7 + 1) = 2 ^ (b + 1) := by
        conv_rhs => rw [show b + 1 = 7 + (b - 7 + 1) by omega, Nat.pow_add]
      have hy128 : ¬ (y < 128) := by
        have : 1 ≤ 2 ^ (b - 7) := Nat.one_le_two_pow
        omega
      simp only [hy128, ↓reduceDIte, List.length_cons]
      have hrec := ih (b - 7) (by omega) (y / 128) (by omega) (by omega)
      rw [hrec]
      have hdiv : b / 7 = (b - 7) / 7 + 1 := by omega
      omega

private theorem or_one_ushiftRight_one (w : BitVec 64) :
    (w ||| 1#64) >>> 1 = w >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or, BitVec.getLsbD_one]
  have : 1 + i ≠ 0 := by omega
  simp [this]

private theorem or_one_toNat_div_two (w : BitVec 64) :
    (w ||| 1#64).toNat / 2 = w.toNat / 2 := by
  have h := congrArg BitVec.toNat (or_one_ushiftRight_one w)
  simpa only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using h

private theorem prost_varint_length_step (n : Nat) :
    (Prost.varint n).length = if n < 128 then 1 else (Prost.varint (n / 128)).length + 1 := by
  rw [Prost.varint]
  split <;> simp

private theorem prost_varint_or_one_length (w : BitVec 64) :
    (Prost.varint (w ||| 1#64).toNat).length = (Prost.varint w.toNat).length := by
  have hdiv2 := or_one_toNat_div_two w
  have hdiv128 : (w ||| 1#64).toNat / 128 = w.toNat / 128 := by omega
  have hlt128 : ((w ||| 1#64).toNat < 128) ↔ (w.toNat < 128) := by omega
  rw [prost_varint_length_step ((w ||| 1#64).toNat), prost_varint_length_step w.toNat, hdiv128]
  by_cases h : w.toNat < 128
  · have h' : (w ||| 1#64).toNat < 128 := hlt128.mpr h
    simp only [h, h', ↓reduceIte]
  · have h' : ¬ ((w ||| 1#64).toNat < 128) := fun hc => h (hlt128.mp hc)
    simp only [h, h', ↓reduceIte]

private theorem or_one_ne_zero (w : BitVec 64) : (w ||| 1#64) ≠ 0#64 := by
  intro h
  have h0 := congrArg (fun x => x.getLsbD 0) h
  simp at h0

theorem prost_varint_length_eq_clz (w : BitVec 64) :
    (Prost.varint w.toNat).length = (63 - (w ||| 1#64).clz.toNat) / 7 + 1 := by
  rw [← prost_varint_or_one_length]
  have hle : (w ||| 1#64).clz.toNat ≤ 63 := ProofLib.clz_or_one_toNat_le w
  have hlo := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero (x := w ||| 1#64) (by decide) (or_one_ne_zero w)
  have hhi := BitVec.toNat_lt_two_pow_sub_clz (x := w ||| 1#64)
  have hsub : 64 - (w ||| 1#64).clz.toNat = (63 - (w ||| 1#64).clz.toNat) + 1 := by omega
  rw [hsub] at hhi
  exact prost_varint_length_of_pow_bounds (63 - (w ||| 1#64).clz.toNat) (w ||| 1#64).toNat hlo hhi

@[local simp, local arm64_norm]
theorem hwVarintLen_eq_prost_varint_length (w : BitVec 64) :
    ((((w ||| 1#64).clz ^^^ 0x3f#64) + (((w ||| 1#64).clz ^^^ 0x3f#64) <<< 3)) + 0x49#64) >>> 6 =
      BitVec.ofNat 64 (Prost.varint w.toNat).length := by
  have hle : (w ||| 1#64).clz.toNat < 64 := Nat.lt_succ_of_le (ProofLib.clz_or_one_toNat_le w)
  have hclz : (w ||| 1#64).clz = BitVec.ofNat 64 (w ||| 1#64).clz.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hclz, hwVarintFormula_fin ⟨(w ||| 1#64).clz.toNat, hle⟩, prost_varint_length_eq_clz]

@[local simp, local arm64_norm]
theorem hwVarintLen_bvShift_eq_prost_varint_length (w : BitVec 64) :
    ((((w ||| 1#64).clz ^^^ 63#64) + (((w ||| 1#64).clz ^^^ 63#64) <<< 3#64)) + 73#64) >>> 6#64 =
      BitVec.ofNat 64 (Prost.varint w.toNat).length := by
  have hle : (w ||| 1#64).clz.toNat < 64 := Nat.lt_succ_of_le (ProofLib.clz_or_one_toNat_le w)
  have hclz : (w ||| 1#64).clz = BitVec.ofNat 64 (w ||| 1#64).clz.toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hclz, hwVarintFormula_bvShift_fin ⟨(w ||| 1#64).clz.toNat, hle⟩, prost_varint_length_eq_clz]

/-! ## Instruction Decode Lemmas -/

gen_decodes libsignalSessionCode_tree preKeyMsgEncLenBin [0x2db68 → 0x2dd6c]

/-! ## Field Layout Decomposition -/

def optVecCap (pin : VecPin) : Option (List (BitVec 8)) → BitVec 64
  | none => noneCap
  | some _ => pin.cap

/-- Heap buffer of a `Vec<u8>` (capacity `cap`, pointer `ptr`, bytes `bs`), detached from its
24-byte `vecHeader`. -/
def vecU8Buf (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_eq_header_sep_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs = vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecU8Buf
  ac_rfl

def optVecPayload (A : RustAlloc) (pin : VecPin) (p : BitVec 64) :
    Option (List (BitVec 8)) → SepProp
  | none => memRegion (p + 8#64) 16
  | some bs =>
    ((p + 8#64) ↦₆₄ pin.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A pin.cap pin.ptr bs

theorem optVecU8At_eq (A : RustAlloc) (pin : VecPin) (p : BitVec 64)
    (opt : Option (List (BitVec 8))) :
    optVecU8At A pin p opt = (p ↦₆₄ optVecCap pin opt) ∗ optVecPayload A pin p opt := by
  cases opt with
  | none => rfl
  | some bs =>
    simp only [optVecU8At, optVecCap, optVecPayload, vecU8At_eq_header_sep_buf, vecHeader, sepConj_assoc]

def optU32Tag : Option (BitVec 32) → BitVec 32
  | none => 0#32
  | some _ => 1#32

def optU32Payload (p : BitVec 64) : Option (BitVec 32) → SepProp
  | none => memRegion (p + 4#64) 4
  | some v => (p + 4#64) ↦₃₂ v

theorem optU32At_eq (p : BitVec 64) (opt : Option (BitVec 32)) :
    LibsignalPublicApiRepr.optU32At p opt = (p ↦₃₂ optU32Tag opt) ∗ optU32Payload p opt := by
  cases opt <;> rfl

theorem vecU8Buf_cap_lt {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {m : Memory} (hm : m ⊨ vecU8Buf A cap ptr bs ∗ R) :
    cap.toNat < 2 ^ 63 := by
  unfold vecU8Buf at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm.1.2.1

theorem cap_add_one_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  omega

theorem cap_add_one_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 != 0#64) = true := by
  simp [bne, cap_add_one_beq_zero_false h]

theorem optVecCap_bounds {A : RustAlloc} {pin : VecPin} {p : BitVec 64}
    {opt : Option (List (BitVec 8))} {R : SepProp} {m : Memory}
    (hm : m ⊨ optVecPayload A pin p opt ∗ R) :
    (optVecCap pin opt + 1#64 == 0#64) = !opt.isSome ∧
      (optVecCap pin opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none =>
    dsimp [optVecCap]
    exact ⟨rfl, rfl⟩
  | some bs =>
    simp only [optVecPayload] at hm
    have hhm : m ⊨ vecU8Buf A pin.cap pin.ptr bs ∗
        (((p + 8#64) ↦₆₄ pin.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ R) := by
      convert hm using 1; ac_rfl
    have hlt := vecU8Buf_cap_lt hhm
    exact ⟨cap_add_one_beq_zero_false hlt, cap_add_one_bne_zero_true hlt⟩

@[local simp, local arm64_norm]
theorem noneCap_add_one_beq_zero : (noneCap + 1#64 == 0#64) = true := rfl

@[local simp, local arm64_norm]
theorem noneCap_add_one_bne_zero : (noneCap + 1#64 != 0#64) = false := rfl

@[local simp, local arm64_norm]
theorem optU32Tag_beq_one (opt : Option (BitVec 32)) :
    (optU32Tag opt == 1#32) = opt.isSome := by
  cases opt <;> rfl

@[local simp, local arm64_norm]
theorem optU32Tag_bne_one (opt : Option (BitVec 32)) :
    (optU32Tag opt != 1#32) = !opt.isSome := by
  cases opt <;> rfl

@[local simp, local arm64_norm]
theorem zext64_optU32Tag_truncate32 (opt : Option (BitVec 32)) :
    (BitVec.zeroExtend 64 (optU32Tag opt)).truncate 32 = optU32Tag opt := by
  cases opt <;> rfl

/-! ## Encoded-Length Arithmetic and Non-Overflow Bounds -/

theorem prost_key_length_eq_one {t wt : Nat} (h : 8 * t + wt < 128 := by omega) :
    (Prost.key t wt).length = 1 := by
  unfold Prost.key
  rw [Prost.varint]
  simp [h]

theorem bv_prost_bytesField_some_length {t : Nat} {bs : List (BitVec 8)}
    (hlen : bs.length < 2 ^ 64) (ht : 8 * t + 2 < 128 := by omega) :
    BitVec.ofNat 64 bs.length +
      BitVec.ofNat 64 (Prost.varint (BitVec.ofNat 64 bs.length).toNat).length + 1#64 =
      BitVec.ofNat 64 (Prost.bytesField t (some bs)).length := by
  have hkey : (Prost.key t 2).length = 1 := prost_key_length_eq_one ht
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  simp only [Prost.bytesField, List.length_append, hkey, htoNat, ← BitVec.ofNat_add]
  congr 1
  omega

theorem bv_prost_uint32Field_some_length {t : Nat} {v : BitVec 32}
    (ht : 8 * t < 128 := by omega) :
    BitVec.ofNat 64 (Prost.varint (BitVec.zeroExtend 64 v).toNat).length + 1#64 =
      BitVec.ofNat 64 (Prost.uint32Field t (some v)).length := by
  have hkey : (Prost.key t 0).length = 1 := prost_key_length_eq_one ht
  have hlt : v.toNat < 2 ^ 64 := by omega
  simp only [Prost.uint32Field, List.length_append, hkey, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hlt, ← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_comm (a b : Nat) :
    BitVec.ofNat 64 b + BitVec.ofNat 64 a = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add, Nat.add_comm]

theorem bv_add_ofNat_eq (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [← BitVec.ofNat_add]

@[local simp, local arm64_norm]
theorem ule_zero_64 (x : BitVec 64) : BitVec.ule 0#64 x = true := by
  simp [BitVec.ule]

@[local simp, local arm64_norm]
theorem ult_zero_64 (x : BitVec 64) : BitVec.ult x 0#64 = false := by
  simp [BitVec.ult]

theorem ule_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ule (BitVec.ofNat 64 b) (BitVec.ofNat 64 (a + b)) = true := by
  rw [BitVec.ule_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem ult_ofNat_add_of_lt {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 (a + b)) (BitVec.ofNat 64 b) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

def EncLenCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x19 = s0.readReg64 .x19 ∧
  s.readReg64 .x20 = s0.readReg64 .x20 ∧
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EncLenCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EncLenCalleeSaved s0 s1) (h2 : EncLenCalleeSaved s1 s2) :
    EncLenCalleeSaved s0 s2 :=
  by reg_chain

def wirePreKeyMsgUnpacked (A : RustAlloc) (g : WirePreKeySignalMessageGhost) (a : BitVec 64)
    (m : ProtoPreKeySignalMessage) : SepProp :=
  (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
    ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
    ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
    ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
    ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
    ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
    ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
    ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId

theorem wirePreKeySignalMessageAt_eq_unpacked (A : RustAlloc) (g : WirePreKeySignalMessageGhost)
    (a : BitVec 64) (m : ProtoPreKeySignalMessage) :
    wirePreKeySignalMessageAt A g a m = wirePreKeyMsgUnpacked A g a m := by
  unfold wirePreKeySignalMessageAt wirePreKeyMsgUnpacked
  rw [optVecU8At_eq A g.kyberCt a, optVecU8At_eq A g.bk (a + 24#64),
      optVecU8At_eq A g.ik (a + 48#64), optVecU8At_eq A g.msg (a + 72#64),
      optU32At_eq (a + 96#64), optU32At_eq (a + 104#64),
      optU32At_eq (a + 112#64), optU32At_eq (a + 120#64)]
  ac_rfl

/-! ## Per-Field Stepping Lemmas -/

theorem step_encLen_f1_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoPreKeySignalMessage)
    (hbk_beq : (optVecCap g.bk m.baseKey + 1#64 == 0#64) = !m.baseKey.isSome)
    (hbk_bne : (optVecCap g.bk m.baseKey + 1#64 != 0#64) = m.baseKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a) (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.baseKey.isSome then (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 64#64
        else (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 172#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (Prost.uint32Field 1 m.preKeyId).length →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        ((wirePreKeyMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 0 64
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 156 16
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hpk : m.preKeyId with
  | none =>
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.baseKey.isSome then entry + 64#64 else entry + 172#64)
    wp_steps
    apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    have henc := bv_prost_uint32Field_some_length (t := 1) (v := v)
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.baseKey.isSome then entry + 64#64 else entry + 172#64)
    wp_steps
    apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f1 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoPreKeySignalMessage)
    (hbk_beq : (optVecCap g.bk m.baseKey + 1#64 == 0#64) = !m.baseKey.isSome)
    (hbk_bne : (optVecCap g.bk m.baseKey + 1#64 != 0#64) = m.baseKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.baseKey.isSome then (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 64#64
        else (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 172#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (Prost.uint32Field 1 m.preKeyId).length →
      EncLenCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((wirePreKeyMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f1_trap b A (tripleRatchetExterns C ctl abs) g a sp v16 v8 m hbk_beq hbk_bne hpc hrun hsp halign hx0 hP hnext

theorem step_encLen_f2_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1 : Nat)
    (hik_beq : (optVecCap g.ik m.identityKey + 1#64 == 0#64) = !m.identityKey.isSome)
    (hik_bne : (optVecCap g.ik m.identityKey + 1#64 != 0#64) = m.identityKey.isSome)
    (hfit : s1 + (Prost.bytesField 2 m.baseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.baseKey.isSome then (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 64#64
      else (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 172#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.identityKey.isSome then (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 112#64
        else (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 188#64) →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (Prost.bytesField 2 m.baseKey).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 64 48
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 172 16
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hbk : m.baseKey with
  | none =>
    simp only [hbk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk none) ∗ optVecPayload A g.bk (a + 24#64) none ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.identityKey.isSome then entry + 112#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hbk, Option.isSome_some, ↓reduceIte] at hpc
    rw [hbk] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 2) (bs := bs) hlen
    have hadd := bv_add_ofNat_comm s1 (Prost.bytesField 2 (some bs)).length
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ g.bk.cap) ∗ ((a + 32#64) ↦₆₄ g.bk.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.bk.cap g.bk.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.identityKey.isSome then entry + 112#64 else entry + 188#64)
    wp_steps
    apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f2 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1 : Nat)
    (hik_beq : (optVecCap g.ik m.identityKey + 1#64 == 0#64) = !m.identityKey.isSome)
    (hik_bne : (optVecCap g.ik m.identityKey + 1#64 != 0#64) = m.identityKey.isSome)
    (hfit : s1 + (Prost.bytesField 2 m.baseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.baseKey.isSome then (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 64#64
      else (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 172#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.identityKey.isSome then (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 112#64
        else (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 188#64) →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (Prost.bytesField 2 m.baseKey).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f2_trap b A (tripleRatchetExterns C ctl abs) g a m s1 hik_beq hik_bne hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f3_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12 : Nat)
    (hfit : s12 + (Prost.bytesField 3 m.identityKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.identityKey.isSome then (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 112#64
      else (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 188#64)) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 196#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (Prost.bytesField 3 m.identityKey).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 112 40
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 188 8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hik : m.identityKey with
  | none =>
    simp only [hik, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := entry + 196#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hik, Option.isSome_some, ↓reduceIte] at hpc
    rw [hik] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 3) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12 (Prost.bytesField 3 (some bs)).length
    have hP3 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ g.ik.cap) ∗ ((a + 56#64) ↦₆₄ g.ik.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ik.cap g.ik.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hik, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := entry + 196#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP3]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f3 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12 : Nat)
    (hfit : s12 + (Prost.bytesField 3 m.identityKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.identityKey.isSome then (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 112#64
      else (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 188#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 196#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (Prost.bytesField 3 m.identityKey).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f3_trap b A (tripleRatchetExterns C ctl abs) g a m s12 hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f4_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123 : Nat)
    (hmsg_beq : (optVecCap g.msg m.message + 1#64 == 0#64) = !m.message.isSome)
    (hfit : s123 + (Prost.bytesField 4 m.message).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 196#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 260#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (Prost.bytesField 4 m.message).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 196 52
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 252 8
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hmsg : m.message with
  | none =>
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.msg (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := entry + 260#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hmsg_beq' : (g.msg.cap + 1#64 == 0#64) = false := by
      rwa [hmsg, Option.isSome_some, Bool.not_true, optVecCap] at hmsg_beq
    rw [hmsg] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 4) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (Prost.bytesField 4 (some bs)).length
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ g.msg.cap) ∗ ((a + 80#64) ↦₆₄ g.msg.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.msg.cap g.msg.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := entry + 260#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f4 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123 : Nat)
    (hmsg_beq : (optVecCap g.msg m.message + 1#64 == 0#64) = !m.message.isSome)
    (hfit : s123 + (Prost.bytesField 4 m.message).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 196#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 260#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (Prost.bytesField 4 m.message).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f4_trap b A (tripleRatchetExterns C ctl abs) g a m s123 hmsg_beq hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f5_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1234 : Nat)
    (hfit : s1234 + (Prost.uint32Field 5 m.registrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 260#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 320#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (Prost.uint32Field 5 m.registrationId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 260 60
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hreg : m.registrationId with
  | none =>
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := entry + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hreg] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 5) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (Prost.uint32Field 5 (some v)).length
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg, optU32Tag, optU32Payload, arm64_norm]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := entry + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f5 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1234 : Nat)
    (hfit : s1234 + (Prost.uint32Field 5 m.registrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 260#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 320#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (Prost.uint32Field 5 m.registrationId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f5_trap b A (tripleRatchetExterns C ctl abs) g a m s1234 hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f6_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12345 : Nat)
    (hfit : s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 320#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 380#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 320 60
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hspk : m.signedPreKeyId with
  | none =>
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 112#64) none ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := entry + 380#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP6]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hspk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 6) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (Prost.uint32Field 6 (some v)).length
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ 1#32) ∗ ((a + 116#64) ↦₃₂ v) ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := entry + 380#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP6]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f6 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12345 : Nat)
    (hfit : s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 320#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 380#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f6_trap b A (tripleRatchetExterns C ctl abs) g a m s12345 hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f7_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123456 : Nat)
    (hfit : s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 380#64) (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123456)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 440#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 380 60
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hkpk : m.kyberPreKeyId with
  | none =>
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 120#64) none := by
      simp only [wirePreKeyMsgUnpacked, hkpk]
    rw [hP7]
    apply SepWPp.of_sepWP (mid := entry + 440#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP7]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hkpk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 7) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123456 (Prost.uint32Field 7 (some v)).length
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ 1#32) ∗ ((a + 124#64) ↦₃₂ v) := by
      simp only [wirePreKeyMsgUnpacked, hkpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP7]
    apply SepWPp.of_sepWP (mid := entry + 440#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP7]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f7 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123456 : Nat)
    (hfit : s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 380#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123456)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 440#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp  := step_encLen_f7_trap b A (tripleRatchetExterns C ctl abs) g a m s123456 hfit hpc hrun hx0 hx8 hP hnext

theorem step_encLen_f8_trap (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a sp fp_val lr_val : BitVec 64)
    (m : ProtoPreKeySignalMessage) (s1234567 : Nat)
    (hkyber_beq : (optVecCap g.kyberCt m.kyberCiphertext + 1#64 == 0#64) = !m.kyberCiphertext.isSome)
    (hfit : s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length < 2 ^ 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName + 440#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234567) (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ fp_val) ∗ ((sp - 8#64) ↦₆₄ lr_val)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = lr_val → sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length) →
      sm.readReg64 .fp = fp_val → sm.readReg64 .lr = lr_val →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAtExt b ext) lr_val sm P Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) lr_val s P Q Qp := by
  code_fetches_range CryptoVerification.libsignalSessionCode preKeyMsgEncLenBin b
    (Rust.withPanics ext) libsignalSessionCode_fnOff_0x2db68 0x2db68 440 68
  generalize_entry (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = entry
  subst hP
  cases hkyber : m.kyberCiphertext with
  | none =>
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.kyberCt a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap]
    rw [hP8]
    apply SepWPp.of_sepWP (mid := lr_val)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP8]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [Prost.bytesField]) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hkyber_beq' : (g.kyberCt.cap + 1#64 == 0#64) = false := by
      rwa [hkyber, Option.isSome_some, Bool.not_true, optVecCap] at hkyber_beq
    rw [hkyber] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 8) (bs := bs) hlen
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234567 (Prost.bytesField 8 (some bs)).length
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ g.kyberCt.cap) ∗ ((a + 8#64) ↦₆₄ g.kyberCt.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.kyberCt.cap g.kyberCt.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP8]
    apply SepWPp.of_sepWP (mid := lr_val)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP8]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f8 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (g : WirePreKeySignalMessageGhost) (a sp fp_val lr_val : BitVec 64)
    (m : ProtoPreKeySignalMessage) (s1234567 : Nat)
    (hkyber_beq : (optVecCap g.kyberCt m.kyberCiphertext + 1#64 == 0#64) = !m.kyberCiphertext.isSome)
    (hfit : s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length < 2 ^ 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234567)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ fp_val) ∗ ((sp - 8#64) ↦₆₄ lr_val)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = lr_val → sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length) →
      sm.readReg64 .fp = fp_val → sm.readReg64 .lr = lr_val →
      EncLenCalleeSaved s sm → SepWPp (tripleRatchetProgAt b C ctl abs) lr_val sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) lr_val s P Q Qp  := step_encLen_f8_trap b A (tripleRatchetExterns C ctl abs) g a sp fp_val lr_val m s1234567 hkyber_beq hfit hpc hrun hsp halign hx0 hx8 hP hnext

/-! ## Top-Level Composition -/

theorem wirePreKeyMsgUnpacked_bounds {A : RustAlloc} {g : WirePreKeySignalMessageGhost}
    {a : BitVec 64} {m : ProtoPreKeySignalMessage} {R : SepProp} {mem : Memory}
    (hm : mem ⊨ wirePreKeyMsgUnpacked A g a m ∗ R) :
    ((optVecCap g.kyberCt m.kyberCiphertext + 1#64 == 0#64) = !m.kyberCiphertext.isSome ∧
     (optVecCap g.kyberCt m.kyberCiphertext + 1#64 != 0#64) = m.kyberCiphertext.isSome) ∧
    ((optVecCap g.bk m.baseKey + 1#64 == 0#64) = !m.baseKey.isSome ∧
     (optVecCap g.bk m.baseKey + 1#64 != 0#64) = m.baseKey.isSome) ∧
    ((optVecCap g.ik m.identityKey + 1#64 == 0#64) = !m.identityKey.isSome ∧
     (optVecCap g.ik m.identityKey + 1#64 != 0#64) = m.identityKey.isSome) ∧
    ((optVecCap g.msg m.message + 1#64 == 0#64) = !m.message.isSome ∧
     (optVecCap g.msg m.message + 1#64 != 0#64) = m.message.isSome) := by
  have h1 : mem ⊨ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
      ((a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗
       optVecPayload A g.bk (a + 24#64) m.baseKey ∗ ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗
       optVecPayload A g.ik (a + 48#64) m.identityKey ∗ ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗
       optVecPayload A g.msg (a + 72#64) m.message ∗ ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗
       optU32Payload (a + 96#64) m.registrationId ∗ ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗
       optU32Payload (a + 104#64) m.preKeyId ∗ ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗
       optU32Payload (a + 112#64) m.signedPreKeyId ∗ ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗
       optU32Payload (a + 120#64) m.kyberPreKeyId ∗ R) := by
    unfold wirePreKeyMsgUnpacked at hm; convert hm using 1; ac_rfl
  have h2 : mem ⊨ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
      ((a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
       ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗
       optVecPayload A g.ik (a + 48#64) m.identityKey ∗ ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗
       optVecPayload A g.msg (a + 72#64) m.message ∗ ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗
       optU32Payload (a + 96#64) m.registrationId ∗ ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗
       optU32Payload (a + 104#64) m.preKeyId ∗ ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗
       optU32Payload (a + 112#64) m.signedPreKeyId ∗ ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗
       optU32Payload (a + 120#64) m.kyberPreKeyId ∗ R) := by
    unfold wirePreKeyMsgUnpacked at hm; convert hm using 1; ac_rfl
  have h3 : mem ⊨ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
      ((a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
       ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
       ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗
       optVecPayload A g.msg (a + 72#64) m.message ∗ ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗
       optU32Payload (a + 96#64) m.registrationId ∗ ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗
       optU32Payload (a + 104#64) m.preKeyId ∗ ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗
       optU32Payload (a + 112#64) m.signedPreKeyId ∗ ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗
       optU32Payload (a + 120#64) m.kyberPreKeyId ∗ R) := by
    unfold wirePreKeyMsgUnpacked at hm; convert hm using 1; ac_rfl
  have h4 : mem ⊨ optVecPayload A g.msg (a + 72#64) m.message ∗
      ((a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
       ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
       ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
       ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗
       optU32Payload (a + 96#64) m.registrationId ∗ ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗
       optU32Payload (a + 104#64) m.preKeyId ∗ ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗
       optU32Payload (a + 112#64) m.signedPreKeyId ∗ ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗
       optU32Payload (a + 120#64) m.kyberPreKeyId ∗ R) := by
    unfold wirePreKeyMsgUnpacked at hm; convert hm using 1; ac_rfl
  exact ⟨optVecCap_bounds h1, optVecCap_bounds h2, optVecCap_bounds h3, optVecCap_bounds h4⟩

theorem preKeyMsg_encode_length_eq (m : ProtoPreKeySignalMessage) :
    m.encode.length =
      (Prost.uint32Field 1 m.preKeyId).length + (Prost.bytesField 2 m.baseKey).length +
      (Prost.bytesField 3 m.identityKey).length + (Prost.bytesField 4 m.message).length +
      (Prost.uint32Field 5 m.registrationId).length + (Prost.uint32Field 6 m.signedPreKeyId).length +
      (Prost.uint32Field 7 m.kyberPreKeyId).length + (Prost.bytesField 8 m.kyberCiphertext).length := by
  simp only [ProtoPreKeySignalMessage.encode, List.length_append]

theorem stackAt_16_eq (sp : BitVec 64) :
    stackAt sp preKeyMsgEncodedLenStack =
      ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64, ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
  change stackAt sp (8 * 2) = _
  rw [stackAt_eq_cells sp 2]
  cells_unfold

theorem progAtExt_fnAddr_preKeyMsgEncodedLen_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr preKeyMsgEncodedLenName = b + 0x2db68#64 := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff preKeyMsgEncodedLenName) = b + 0x2db68#64
  rw [libsignalSessionCode_fnOff_0x2db68]

theorem trTrapProgAt_fnAddr_preKeyMsgEncodedLen_trap (b : BitVec 64) (C : Crypto) (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).fnAddr preKeyMsgEncodedLenName = b + 0x2db68#64 :=
  progAtExt_fnAddr_preKeyMsgEncodedLen_ext b (trTrapExterns C abs)

theorem tripleRatchetProgAt_fnAddr_preKeyMsgEncodedLen (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr preKeyMsgEncodedLenName = b + 0x2db68#64 := by
  change b + BitVec.ofNat 64 (libsignalSessionCode.fnOff preKeyMsgEncodedLenName) = b + 0x2db68#64
  rw [libsignalSessionCode_fnOff_0x2db68]

theorem calleeSavedPreserved_of_encLen {s0 sf : State}
    (hcs : EncLenCalleeSaved s0 sf) (hfp : sf.readReg64 .fp = s0.readReg64 .fp) :
    CalleeSavedPreserved s0 sf :=
  by reg_chain

/-- `PreKeySignalMessage::encoded_len` (`0x2da84`) satisfies `preKeyMsgEncodedLenSpec A` on
`tripleRatchetProgAtExt img.base ext`. -/
theorem preKeyMsgEncodedLen_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (_himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) (img.base + 0x2db68#64)
      (preKeyMsgEncodedLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  simp only [preKeyMsgEncodedLenSpec, wirePreKeySignalMessageAt_eq_unpacked, stackAt_16_eq] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfits⟩, hpre⟩
  have hpre_ex : s0.mem ⊨
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hpre using 1; ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v16, hpre_ex⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v8, hpre_ex⟩
  have hpre' : s0.mem ⊨
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre_ex using 1; ac_rfl
  have hbounds_mem : s0.mem ⊨ wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre' using 1; ac_rfl
  obtain ⟨⟨hkyber_beq, _⟩, ⟨hbk_beq, hbk_bne⟩, ⟨hik_beq, hik_bne⟩, ⟨hmsg_beq, _⟩⟩ :=
    wirePreKeyMsgUnpacked_bounds hbounds_mem
  have hlen_eq := preKeyMsg_encode_length_eq x.m
  have hfits' : x.m.encode.length < 2 ^ 64 := hfits
  rw [hlen_eq] at hfits'
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp_align
  have hpc' : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyMsgEncodedLenName := by
    rw [progAtExt_fnAddr_preKeyMsgEncodedLen_ext, hpc]
  refine ⟨(wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ emp, R,
      by simpa [sepConj_emp] using hpre', ?_⟩
  apply step_encLen_f1_trap img.base A ext x.g x.a s0.sp v16 v8 x.m
    hbk_beq hbk_bne hpc' hrun rfl halign hx0 rfl
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  apply SepWPp.congr_pre (show (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ emp =
      wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) by
    simp [sepConj_emp, sepConj_assoc])
  apply step_encLen_f2_trap img.base A ext x.g x.a x.m
    (Prost.uint32Field 1 x.m.preKeyId).length hik_beq hik_bne (by omega)
    hpc1 hrun1 hx0_1 hx8_1 rfl
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  apply step_encLen_f3_trap img.base A ext x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length)
    (by omega) hpc2 hrun2 hx0_2 hx8_2 rfl
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  apply step_encLen_f4_trap img.base A ext x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length)
    hmsg_beq (by omega) hpc3 hrun3 hx0_3 hx8_3 rfl
  intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  apply step_encLen_f5_trap img.base A ext x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length)
    (by omega) hpc4 hrun4 hx0_4 hx8_4 rfl
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  apply step_encLen_f6_trap img.base A ext x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length)
    (by omega) hpc5 hrun5 hx0_5 hx8_5 rfl
  intro s6 hpc6 hrun6 hsp6 htr6 hx0_6 hx8_6 hcs6
  apply step_encLen_f7_trap img.base A ext x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length +
      (Prost.uint32Field 6 x.m.signedPreKeyId).length)
    (by omega) hpc6 hrun6 hx0_6 hx8_6 rfl
  intro s7 hpc7 hrun7 hsp7 htr7 hx0_7 hx8_7 hcs7
  apply step_encLen_f8_trap img.base A ext x.g x.a s0.sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length +
      (Prost.uint32Field 6 x.m.signedPreKeyId).length +
      (Prost.uint32Field 7 x.m.kyberPreKeyId).length)
    hkyber_beq (by omega) hpc7 hrun7 (by reg_chain)
    halign hx0_7 hx8_7 (F := emp) (by simp [sepConj_emp, sepConj_assoc])
  intro sf hpcf hrunf hspf htrf hx0_f hfpf hlrf hcs8
  apply SepWPp.done hpcf hrunf
  refine ⟨?_, hspf, by reg_chain⟩
  intro hmf
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by rw [hx0_f, ← hlen_eq], by reg_chain⟩, ?_⟩
  have hmf' : sf.mem ⊨
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hmf using 1; ac_rfl
  have hent : (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ⊢
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) :=
    Entails.sepExists_right (s0.readReg64 .fp)
      (Entails.sepExists_right (s0.readReg64 .lr) (Entails.refl _))
  have hmf'' := Satisfies.mono (sepConj_mono_left hent) hmf'
  convert hmf'' using 1; ac_rfl

theorem preKeyMsgEncodedLen_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)} (_himg : Obj.Loads libsignalSessionImage img) :
    PreKeyMsgEncodedLenOk_trap img C A abs :=
  preKeyMsgEncodedLen_ok_ext _himg

theorem preKeyMsgEncodedLen_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (_himg : Obj.Loads libsignalSessionImage img) :
    PreKeyMsgEncodedLenOk img C A ctl abs :=
  subroutine_ok_kit_of_trTrap (preKeyMsgEncodedLen_ok_trap _himg)

/-! ## Relocatable Placement Proofs -/

open CryptoVerification.LibsignalPublicApi.Placed

theorem step_encLen_f1_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a sp v16 v8 : BitVec 64) (m : ProtoPreKeySignalMessage)
    (hbk_beq : (optVecCap g.bk m.baseKey + 1#64 == 0#64) = !m.baseKey.isSome)
    (hbk_bne : (optVecCap g.bk m.baseKey + 1#64 != 0#64) = m.baseKey.isSome)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64) (hx0 : s.readReg64 .x0 = a)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64) →
      sm.status = .Running → sm.sp = sp - 16#64 → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (Prost.uint32Field 1 m.preKeyId).length →
      EncLenCalleeSaved s sm →
      SepWPp (lsProg_119 H) ret sm
        ((wirePreKeyMsgUnpacked A g a m ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .lr)) ∗ F) Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hpk : m.preKeyId with
  | none =>
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 104#64) none ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64)
    wp_steps
    apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    have henc := bv_prost_uint32Field_some_length (t := 1) (v := v)
    have hP1 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ 1#32) ∗ ((a + 108#64) ↦₃₂ v) ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP1]
    apply SepWPp.of_sepWP (mid := if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64)
    wp_steps
    apply SepWP.done (by cases m.baseKey <;> simp_all) (by simp_all)
    rw [← hP1]
    exact hnext _ (by cases m.baseKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f2_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1 : Nat)
    (hik_beq : (optVecCap g.ik m.identityKey + 1#64 == 0#64) = !m.identityKey.isSome)
    (hik_bne : (optVecCap g.ik m.identityKey + 1#64 != 0#64) = m.identityKey.isSome)
    (hfit : s1 + (Prost.bytesField 2 m.baseKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.baseKey.isSome then (blkPl_119).base + 64#64 else (blkPl_119).base + 172#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64) →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1 + (Prost.bytesField 2 m.baseKey).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hbk : m.baseKey with
  | none =>
    simp only [hbk, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk none) ∗ optVecPayload A g.bk (a + 24#64) none ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64)
    wp_steps
    apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hbk, Option.isSome_some, ↓reduceIte] at hpc
    rw [hbk] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 2) (bs := bs) hlen
    have hadd := bv_add_ofNat_comm s1 (Prost.bytesField 2 (some bs)).length
    have hP2 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ g.bk.cap) ∗ ((a + 32#64) ↦₆₄ g.bk.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.bk.cap g.bk.ptr bs ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hbk, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP2]
    apply SepWPp.of_sepWP (mid := if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64)
    wp_steps
    apply SepWP.done (by cases m.identityKey <;> simp_all) (by simp_all)
    rw [← hP2]
    exact hnext _ (by cases m.identityKey <;> simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f3_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12 : Nat)
    (hfit : s12 + (Prost.bytesField 3 m.identityKey).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (if m.identityKey.isSome then (blkPl_119).base + 112#64 else (blkPl_119).base + 188#64))
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_119).base + 196#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12 + (Prost.bytesField 3 m.identityKey).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hik : m.identityKey with
  | none =>
    simp only [hik, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hpc
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 196#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    simp only [hik, Option.isSome_some, ↓reduceIte] at hpc
    rw [hik] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 3) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12 (Prost.bytesField 3 (some bs)).length
    have hP3 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ g.ik.cap) ∗ ((a + 56#64) ↦₆₄ g.ik.ptr) ∗
        ((a + 64#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.ik.cap g.ik.ptr bs ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hik, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP3]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 196#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP3]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f4_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123 : Nat)
    (hmsg_beq : (optVecCap g.msg m.message + 1#64 == 0#64) = !m.message.isSome)
    (hfit : s123 + (Prost.bytesField 4 m.message).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 196#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_119).base + 260#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123 + (Prost.bytesField 4 m.message).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hmsg : m.message with
  | none =>
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ noneCap) ∗ optVecPayload A g.msg (a + 72#64) none ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 260#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.bytesField]) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hmsg_beq' : (g.msg.cap + 1#64 == 0#64) = false := by
      rwa [hmsg, Option.isSome_some, Bool.not_true, optVecCap] at hmsg_beq
    rw [hmsg] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 4) (bs := bs) hlen
    have hcc := ule_ofNat_add_of_lt hfit
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123 (Prost.bytesField 4 (some bs)).length
    have hP4 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ g.msg.cap) ∗ ((a + 80#64) ↦₆₄ g.msg.ptr) ∗
        ((a + 88#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.msg.cap g.msg.ptr bs ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hmsg, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP4]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 260#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP4]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f5_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s1234 : Nat)
    (hfit : s1234 + (Prost.uint32Field 5 m.registrationId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 260#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_119).base + 320#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s1234 + (Prost.uint32Field 5 m.registrationId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hreg : m.registrationId with
  | none =>
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 96#64) none ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hreg] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 5) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234 (Prost.uint32Field 5 (some v)).length
    have hP5 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ 1#32) ∗ ((a + 100#64) ↦₃₂ v) ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hreg, optU32Tag, optU32Payload, arm64_norm]
    rw [hP5]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 320#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP5]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f6_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s12345 : Nat)
    (hfit : s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 320#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s12345)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_119).base + 380#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s12345 + (Prost.uint32Field 6 m.signedPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hspk : m.signedPreKeyId with
  | none =>
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 112#64) none ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 380#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP6]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hspk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 6) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s12345 (Prost.uint32Field 6 (some v)).length
    have hP6 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ 1#32) ∗ ((a + 116#64) ↦₃₂ v) ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hspk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP6]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 380#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP6]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f7_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a : BitVec 64) (m : ProtoPreKeySignalMessage) (s123456 : Nat)
    (hfit : s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 380#64)
    (hrun : s.status = .Running) (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s123456)
    (hP : P = wirePreKeyMsgUnpacked A g a m ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (blkPl_119).base + 440#64 →
      sm.status = .Running → sm.sp = s.sp → sm.trace = s.trace → sm.readReg64 .x0 = a →
      sm.readReg64 .x8 = BitVec.ofNat 64 (s123456 + (Prost.uint32Field 7 m.kyberPreKeyId).length) →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) ret sm P Q Qp) :
    SepWPp (lsProg_119 H) ret s P Q Qp := by
  subst hP
  cases hkpk : m.kyberPreKeyId with
  | none =>
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag none) ∗ optU32Payload (a + 120#64) none := by
      simp only [wirePreKeyMsgUnpacked, hkpk]
    rw [hP7]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 440#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP7]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all [Prost.uint32Field]) (by simp_all [EncLenCalleeSaved])
  | some v =>
    rw [hkpk] at hfit
    have henc := bv_prost_uint32Field_some_length (t := 7) (v := v)
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s123456 (Prost.uint32Field 7 (some v)).length
    have hP7 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ optVecCap g.kyberCt m.kyberCiphertext) ∗ optVecPayload A g.kyberCt a m.kyberCiphertext ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ 1#32) ∗ ((a + 124#64) ↦₃₂ v) := by
      simp only [wirePreKeyMsgUnpacked, hkpk, optU32Tag, optU32Payload, arm64_norm]
    rw [hP7]
    apply SepWPp.of_sepWP (mid := (blkPl_119).base + 440#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP7]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

theorem step_encLen_f8_placed [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (g : WirePreKeySignalMessageGhost) (a sp fp_val lr_val : BitVec 64)
    (m : ProtoPreKeySignalMessage) (s1234567 : Nat)
    (hkyber_beq : (optVecCap g.kyberCt m.kyberCiphertext + 1#64 == 0#64) = !m.kyberCiphertext.isSome)
    (hfit : s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length < 2 ^ 64)
    {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_119).base + 440#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 16#64) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 s1234567)
    (hP : P = (wirePreKeyMsgUnpacked A g a m ∗ ((sp - 16#64) ↦₆₄ fp_val) ∗ ((sp - 8#64) ↦₆₄ lr_val)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = lr_val → sm.status = .Running → sm.sp = sp → sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (s1234567 + (Prost.bytesField 8 m.kyberCiphertext).length) →
      sm.readReg64 .fp = fp_val → sm.readReg64 .lr = lr_val →
      EncLenCalleeSaved s sm → SepWPp (lsProg_119 H) lr_val sm P Q Qp) :
    SepWPp (lsProg_119 H) lr_val s P Q Qp := by
  subst hP
  cases hkyber : m.kyberCiphertext with
  | none =>
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ noneCap) ∗ optVecPayload A g.kyberCt a none ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap]
    rw [hP8]
    apply SepWPp.of_sepWP (mid := lr_val)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP8]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all [Prost.bytesField]) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])
  | some bs =>
    have hkyber_beq' : (g.kyberCt.cap + 1#64 == 0#64) = false := by
      rwa [hkyber, Option.isSome_some, Bool.not_true, optVecCap] at hkyber_beq
    rw [hkyber] at hfit
    have hlen : bs.length < 2 ^ 64 := by simp only [Prost.bytesField, List.length_append] at hfit; omega
    have henc := bv_prost_bytesField_some_length (t := 8) (bs := bs) hlen
    have hcs_ovf := ult_ofNat_add_of_lt hfit
    have hadd := bv_add_ofNat_comm s1234567 (Prost.bytesField 8 (some bs)).length
    have hP8 : wirePreKeyMsgUnpacked A g a m =
        (a ↦₆₄ g.kyberCt.cap) ∗ ((a + 8#64) ↦₆₄ g.kyberCt.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A g.kyberCt.cap g.kyberCt.ptr bs ∗
        ((a + 24#64) ↦₆₄ optVecCap g.bk m.baseKey) ∗ optVecPayload A g.bk (a + 24#64) m.baseKey ∗
        ((a + 48#64) ↦₆₄ optVecCap g.ik m.identityKey) ∗ optVecPayload A g.ik (a + 48#64) m.identityKey ∗
        ((a + 72#64) ↦₆₄ optVecCap g.msg m.message) ∗ optVecPayload A g.msg (a + 72#64) m.message ∗
        ((a + 96#64) ↦₃₂ optU32Tag m.registrationId) ∗ optU32Payload (a + 96#64) m.registrationId ∗
        ((a + 104#64) ↦₃₂ optU32Tag m.preKeyId) ∗ optU32Payload (a + 104#64) m.preKeyId ∗
        ((a + 112#64) ↦₃₂ optU32Tag m.signedPreKeyId) ∗ optU32Payload (a + 112#64) m.signedPreKeyId ∗
        ((a + 120#64) ↦₃₂ optU32Tag m.kyberPreKeyId) ∗ optU32Payload (a + 120#64) m.kyberPreKeyId := by
      simp only [wirePreKeyMsgUnpacked, hkyber, optVecCap, optVecPayload, sepConj_assoc, arm64_norm]
    rw [hP8]
    apply SepWPp.of_sepWP (mid := lr_val)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all); rw [← hP8]
    exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
      (by simp_all) (by simp_all) (by simp_all) (by simp_all [EncLenCalleeSaved])

/-- Relocatable `PreKeySignalMessage::encoded_len` (block `119`) satisfies
`preKeyMsgEncodedLenSpec A`. -/
theorem preKeyMsgEncodedLen_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_119 H) (blkPl_119).base (preKeyMsgEncodedLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  simp only [preKeyMsgEncodedLenSpec, wirePreKeySignalMessageAt_eq_unpacked, stackAt_16_eq] at hpre ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfits⟩, hpre⟩
  have hpre_ex : s0.mem ⊨
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hpre using 1; ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v16, hpre_ex⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpre_ex
  rcases hpre_ex with ⟨v8, hpre_ex⟩
  have hpre' : s0.mem ⊨
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
        ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ R := by
    convert hpre_ex using 1; ac_rfl
  have hbounds_mem : s0.mem ⊨ wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗ R) := by
    convert hpre' using 1; ac_rfl
  obtain ⟨⟨hkyber_beq, _⟩, ⟨hbk_beq, hbk_bne⟩, ⟨hik_beq, hik_bne⟩, ⟨hmsg_beq, _⟩⟩ :=
    wirePreKeyMsgUnpacked_bounds hbounds_mem
  have hlen_eq := preKeyMsg_encode_length_eq x.m
  have hfits' : x.m.encode.length < 2 ^ 64 := hfits
  rw [hlen_eq] at hfits'
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using hsp_align
  refine ⟨(wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) ∗ emp, R,
      by simpa [sepConj_emp] using hpre', ?_⟩
  apply step_encLen_f1_placed A H x.g x.a s0.sp v16 v8 x.m
    hbk_beq hbk_bne hpc hrun rfl halign hx0 rfl
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hx8_1 hcs1
  apply SepWPp.congr_pre (show (wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗ emp =
      wirePreKeyMsgUnpacked A x.g x.a x.m ∗
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) by
    simp [sepConj_emp, sepConj_assoc])
  apply step_encLen_f2_placed A H x.g x.a x.m
    (Prost.uint32Field 1 x.m.preKeyId).length hik_beq hik_bne (by omega)
    hpc1 hrun1 hx0_1 hx8_1 rfl
  intro s2 hpc2 hrun2 hsp2 htr2 hx0_2 hx8_2 hcs2
  apply step_encLen_f3_placed A H x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length)
    (by omega) hpc2 hrun2 hx0_2 hx8_2 rfl
  intro s3 hpc3 hrun3 hsp3 htr3 hx0_3 hx8_3 hcs3
  apply step_encLen_f4_placed A H x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length)
    hmsg_beq (by omega) hpc3 hrun3 hx0_3 hx8_3 rfl
  intro s4 hpc4 hrun4 hsp4 htr4 hx0_4 hx8_4 hcs4
  apply step_encLen_f5_placed A H x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length)
    (by omega) hpc4 hrun4 hx0_4 hx8_4 rfl
  intro s5 hpc5 hrun5 hsp5 htr5 hx0_5 hx8_5 hcs5
  apply step_encLen_f6_placed A H x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length)
    (by omega) hpc5 hrun5 hx0_5 hx8_5 rfl
  intro s6 hpc6 hrun6 hsp6 htr6 hx0_6 hx8_6 hcs6
  apply step_encLen_f7_placed A H x.g x.a x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length +
      (Prost.uint32Field 6 x.m.signedPreKeyId).length)
    (by omega) hpc6 hrun6 hx0_6 hx8_6 rfl
  intro s7 hpc7 hrun7 hsp7 htr7 hx0_7 hx8_7 hcs7
  apply step_encLen_f8_placed A H x.g x.a s0.sp
    (s0.readReg64 .fp) (s0.readReg64 .lr) x.m
    ((Prost.uint32Field 1 x.m.preKeyId).length + (Prost.bytesField 2 x.m.baseKey).length +
      (Prost.bytesField 3 x.m.identityKey).length + (Prost.bytesField 4 x.m.message).length +
      (Prost.uint32Field 5 x.m.registrationId).length +
      (Prost.uint32Field 6 x.m.signedPreKeyId).length +
      (Prost.uint32Field 7 x.m.kyberPreKeyId).length)
    hkyber_beq (by omega) hpc7 hrun7 (by reg_chain)
    halign hx0_7 hx8_7 (F := emp) (by simp [sepConj_emp, sepConj_assoc])
  intro sf hpcf hrunf hspf htrf hx0_f hfpf hlrf hcs8
  apply SepWPp.done hpcf hrunf
  refine ⟨?_, hspf, by reg_chain⟩
  intro hmf
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨by rw [hx0_f, ← hlen_eq], by reg_chain⟩, ?_⟩
  have hmf' : sf.mem ⊨
      (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ∗
      (wirePreKeyMsgUnpacked A x.g x.a x.m ∗ R) := by
    convert hmf using 1; ac_rfl
  have hent : (((s0.sp - 16#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .lr)) ⊢
      (∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64, ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8)) :=
    Entails.sepExists_right (s0.readReg64 .fp)
      (Entails.sepExists_right (s0.readReg64 .lr) (Entails.refl _))
  have hmf'' := Satisfies.mono (sepConj_mono_left hent) hmf'
  convert hmf'' using 1; ac_rfl

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.EncodedLenPf
