/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodeVarintDecodes
import ProofLib.SepLogic.WPp

/-!
# Base Lemmas and Initial Stages for No-Grow `encode_varint`

Callee-saved register invariants, `BitVec` continuation-byte lemmas, and stepping lemmas for the
prologue, final byte write, and stages 1–3 of `encode_varint` (`0x30a0`) on the spare-capacity path.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace EncodeVarintNorm

@[scoped simp, scoped arm64_norm]
theorem false_eq_true' : (false = true) = False := Bool.false_eq_true

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[scoped arm64_norm ↓, scoped wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

theorem zext64_trunc32_orr_mask (x : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 18446743528248704896#64)) =
      BitVec.zeroExtend 64 (BitVec.truncate 32 x) ||| 4294967168#64 := by
  simp

theorem ushr_ushr_7 (v : BitVec 64) (k n : Nat) (h : k + 7 = n := by rfl) :
    (v >>> k) >>> 7 = v >>> n := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

end EncodeVarintNorm
open EncodeVarintNorm

/-! ## Callee-Saved Register Invariants -/

def EncVarintCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem EncVarintCalleeSaved.refl (s : State) : EncVarintCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem EncVarintCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : EncVarintCalleeSaved s0 s1) (h2 : EncVarintCalleeSaved s1 s2) :
    EncVarintCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1, h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2.2.2⟩

theorem cap_beq_len_false {cap : BitVec 64} {n : Nat} (hlt : n < cap.toNat) :
    (cap == BitVec.ofNat 64 n) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  have hn : n < 2 ^ 64 := Nat.lt_trans hlt cap.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h1
  omega

theorem bv_len_add_one (bs : List (BitVec 8)) (byte : BitVec 8) :
    BitVec.ofNat 64 bs.length + 1#64 = BitVec.ofNat 64 (bs ++ [byte]).length := by
  simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]

/-! ## `BitVec` and `encodeVarint` Byte Lemmas -/

def varintContByte (v : BitVec 64) : BitVec 8 :=
  ((v &&& 0x7F#64) ||| 0x80#64).setWidth 8

private theorem bv8_and_7f_or_80 :
    ∀ b : BitVec 8, (b &&& 0x7F#8) ||| 0x80#8 = b ||| 0x80#8 := by
  decide

private theorem varintContByte_eq_or_80 (v : BitVec 64) :
    varintContByte v = v.setWidth 8 ||| 0x80#8 := by
  unfold varintContByte
  rw [BitVec.setWidth_or, BitVec.setWidth_and]
  exact bv8_and_7f_or_80 (v.setWidth 8)

@[scoped simp, scoped arm64_norm]
theorem zext8_zext64_trunc32 (x : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) = BitVec.zeroExtend 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w64 (w : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 w) ||| 18446743528248704896#64) =
      varintContByte w := by
  rw [varintContByte_eq_or_80]
  have h1 := zext8_zext64_trunc32 w
  simp only [BitVec.zeroExtend, BitVec.setWidth_or] at h1 ⊢
  rw [h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_7 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 7) ||| 18446743528248704896#64) =
      varintContByte (v >>> 7) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 7)).setWidth 8 =
      (v >>> 7).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_14 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 14) ||| 18446743528248704896#64) =
      varintContByte (v >>> 14) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 14)).setWidth 8 =
      (v >>> 14).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem hw_contByte_w32_21 (v : BitVec 64) :
    BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 21) ||| 18446743528248704896#64) =
      varintContByte (v >>> 21) := by
  rw [varintContByte_eq_or_80]
  have h1 : (BitVec.zeroExtend 64 (BitVec.truncate 32 v >>> 21)).setWidth 8 =
      (v >>> 21).setWidth 8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  simp only [BitVec.zeroExtend, BitVec.setWidth_or, h1]
  rfl

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_7 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 7) =
      varintContByte (v >>> 7) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_14 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 14) =
      varintContByte (v >>> 14) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem varintContByte_w32_21 (v : BitVec 64) :
    varintContByte (BitVec.zeroExtend 64 (BitVec.truncate 32 v) >>> 21) =
      varintContByte (v >>> 21) := by
  rw [varintContByte_eq_or_80, varintContByte_eq_or_80]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

@[scoped simp, scoped arm64_norm]
theorem ult_0x4000_eq (v : BitVec 64) :
    v.ult 16384#64 = (v >>> 7).ult 128#64 := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ule_0x4000_eq (v : BitVec 64) :
    (16384#64 : BitVec 64).ule v = !(v >>> 7).ult 128#64 := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    ← decide_not]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ult_0x200000_eq (v : BitVec 64) :
    v.ult 2097152#64 = (v >>> 14).ult 128#64 := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem ule_0x200000_eq (v : BitVec 64) :
    (2097152#64 : BitVec 64).ule v = !(v >>> 14).ult 128#64 := by
  simp only [BitVec.ule_eq_decide, BitVec.ult_eq_decide, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    ← decide_not]
  exact decide_eq_decide.mpr (by omega)

private theorem beq_zero64_eq_decide (x : BitVec 64) :
    (x == 0#64) = decide (x.toNat = 0) := by
  rcases hx : (x == 0#64) with _ | _
  · rw [beq_eq_false_iff_ne] at hx
    exact (decide_eq_false (fun heq => hx (BitVec.eq_of_toNat_eq heq))).symm
  · rw [beq_iff_eq] at hx
    exact (decide_eq_true (congrArg BitVec.toNat hx)).symm

@[scoped simp, scoped arm64_norm]
theorem shr28_beq_zero (v : BitVec 64) :
    (v >>> 28 == 0#64) = (v >>> 21).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr28_bne_zero (v : BitVec 64) :
    (v >>> 28 != 0#64) = !(v >>> 21).ult 128#64 := by
  simp only [bne, shr28_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr35_beq_zero (v : BitVec 64) :
    (v >>> 35 == 0#64) = (v >>> 28).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr35_bne_zero (v : BitVec 64) :
    (v >>> 35 != 0#64) = !(v >>> 28).ult 128#64 := by
  simp only [bne, shr35_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr42_beq_zero (v : BitVec 64) :
    (v >>> 42 == 0#64) = (v >>> 35).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr42_bne_zero (v : BitVec 64) :
    (v >>> 42 != 0#64) = !(v >>> 35).ult 128#64 := by
  simp only [bne, shr42_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr49_beq_zero (v : BitVec 64) :
    (v >>> 49 == 0#64) = (v >>> 42).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr49_bne_zero (v : BitVec 64) :
    (v >>> 49 != 0#64) = !(v >>> 42).ult 128#64 := by
  simp only [bne, shr49_beq_zero]

@[scoped simp, scoped arm64_norm]
theorem shr56_beq_zero (v : BitVec 64) :
    (v >>> 56 == 0#64) = (v >>> 49).ult 128#64 := by
  rw [beq_zero64_eq_decide]
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  exact decide_eq_decide.mpr (by omega)

@[scoped simp, scoped arm64_norm]
theorem shr56_bne_zero (v : BitVec 64) :
    (v >>> 56 != 0#64) = !(v >>> 49).ult 128#64 := by
  simp only [bne, shr56_beq_zero]

private theorem bv8_getLsbD_7 :
    ∀ b : BitVec 8, b.getLsbD 7 = !decide (b.toNat < 128) := by
  decide

private theorem bv8_eq_or_80_of_not_lt :
    ∀ b : BitVec 8, decide (b.toNat < 128) = false → b = b ||| 0x80#8 := by
  decide

@[scoped simp, scoped arm64_norm]
theorem getLsbD_63_eq (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  have hv := v.isLt
  have h1 : ((v >>> 56).setWidth 8).getLsbD 7 = v.getLsbD 63 := by
    simp
  have h2 : ((v >>> 56).setWidth 8).toNat = (v >>> 56).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [← h1, bv8_getLsbD_7, h2, BitVec.ult_eq_decide]
  rfl

theorem contByte9_contByte_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    BitVec.zeroExtend 8 (val >>> 56) = varintContByte (val >>> 56) := by
  have hv := val.isLt
  have h2 : ((val >>> 56).setWidth 8).toNat = (val >>> 56).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [varintContByte_eq_or_80]
  apply bv8_eq_or_80_of_not_lt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  rw [h2]
  exact h

theorem contByte9_shr63_eq (val : BitVec 64) (h : (val >>> 56).ult 128#64 = false) :
    (1#64 : BitVec 64) = val >>> 63 := by
  have hv := val.isLt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not] at h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem shr63_ult_128 (val : BitVec 64) :
    (val >>> 63).ult 128#64 = true := by
  have hv := val.isLt
  simp only [BitVec.ult_eq_decide, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, decide_eq_true_eq]
  omega

/-! ## `encodeVarint` Unfolding and Spare-Capacity Helpers -/

theorem encodeVarintAux_of_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = true) :
    encodeVarintAux (fuel + 1) v = [v.setWidth 8] := by
  have hlt : v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; exact h
  simp [encodeVarintAux, hlt]

theorem encodeVarintAux_of_not_ult {fuel : Nat} {v : BitVec 64} (h : v.ult 128#64 = false) :
    encodeVarintAux (fuel + 1) v = varintContByte v :: encodeVarintAux fuel (v >>> 7) := by
  have hlt : ¬ v.toNat < 128 := by simp [BitVec.ult_eq_decide] at h; omega
  simp [encodeVarintAux, varintContByte, hlt]

theorem encodeVarint_exit_bs {fuel : Nat} {v : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = true) :
    bs ++ [v.setWidth 8] = rhs := by
  rw [← encodeVarintAux_of_ult h, hcur]

theorem encodeVarint_step_bs {fuel : Nat} {v nextV : BitVec 64}
    {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux (fuel + 1) v = rhs)
    (h : v.ult 128#64 = false)
    (hshift : v >>> 7 = nextV) :
    (bs ++ [varintContByte v]) ++ encodeVarintAux fuel nextV = rhs := by
  rw [List.append_assoc, List.singleton_append, ← hshift,
    ← encodeVarintAux_of_not_ult h, hcur]

theorem encodeVarint_exit_bs_s9 {v : BitVec 64} {bs rhs : List (BitVec 8)}
    (hcur : bs ++ encodeVarintAux 1 (v >>> 63) = rhs)
    (h : (v >>> 56).ult 128#64 = false) :
    bs ++ [(1#64 : BitVec 64).setWidth 8] = rhs := by
  have h1 : (1#64 : BitVec 64) = v >>> 63 := contByte9_shr63_eq v h
  rw [h1, ← encodeVarintAux_of_ult (shr63_ult_128 v), hcur]

theorem curBs_length_lt_cap {curBs bs : List (BitVec 8)} {k : Nat} {v cap val : BitVec 64}
    (hcur : curBs ++ encodeVarintAux (k + 1) v = bs ++ encodeVarint val)
    (hcap : bs.length + (encodeVarint val).length ≤ cap.toNat) :
    curBs.length < cap.toNat := by
  have h1 := congrArg List.length hcur
  simp only [List.length_append] at h1
  have h2 : 1 ≤ (encodeVarintAux (k + 1) v).length := by
    unfold encodeVarintAux; split <;> simp
  omega

theorem stackAt_encodeVarint_eq (sp : BitVec 64) :
    stackAt sp encodeVarintStack =
      stackAt (sp - 48#64) doReserveStack ∗
      (∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64,
       ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (doReserveStack + 8 * 6) = _
  rw [LibsignalTripleRatchet.stackAt_split_cells sp doReserveStack 6 (by decide)]
  congr 1
  cells_unfold

/-! ## Prologue, Final-Byte, and Stage 1–3 Stepping Lemmas -/

theorem step_encVarint_prologue_trap (b : BitVec 64)
    (ext : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 32#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length →
      sm.readReg64 .x9 = cap →
      EncVarintCalleeSaved s sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry (b := b)
    (H := Rust.withPanics (ext))
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30a0
  have hf4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 4)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30a4
  have hf8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 8)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30a8
  have hf12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 12)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30ac
  have hf16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 16)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30b0
  have hf20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 20)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30b4
  have hf24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 24)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30b8
  have hf28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 28)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30bc
  revert hpc hnext hf0 hf4 hf8 hf12 hf16 hf20 hf24 hf28
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf0 hf4 hf8 hf12 hf16 hf20 hf24 hf28
  examples_hide_fetches
  subst hP
  apply SepWPp.of_sepWP (mid := if val.ult 128#64 then entry + 512#64 else entry + 32#64)
  wp_steps
  apply SepWP.done (by cases val.ult 128#64 <;> simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by cases val.ult 128#64 <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *, and_self])

theorem step_encVarint_prologue (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v cap ptr sp v48 v40 v32 v24 v16 v8 : BitVec 64) (bs : List (BitVec 8))
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hP : P = ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if val.ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 32#64) →
      sm.status = .Running →
      sm.sp = sp - 48#64 →
      sm.trace = s.trace →
      sm.readReg64 .x0 = val →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 bs.length →
      sm.readReg64 .x9 = cap →
      EncVarintCalleeSaved s sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
          ((sp - 32#64) ↦₆₄ s.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s.readReg64 .x19)) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_prologue_trap b (tripleRatchetExterns C ctl abs) val v cap ptr sp v48 v40 v32 v24 v16 v8 bs hpc hrun hsp halign hx0 hx1 hP hnext
theorem step_encVarint_final_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      Q sf (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A curCap curPtr (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q Qp := by
  have hf512 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 512)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32a0
  have hf516 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 516)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32a4
  have hf520 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 520)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32a8
  have hf524 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 524)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32ac
  have hf528 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 528)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32b0
  have hf532 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 532)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32b4
  have hf536 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 536)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32b8
  have hf540 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 540)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32bc
  have hf544 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 544)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32c0
  have hf548 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 548)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32c4
  have hf552 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 552)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32c8
  have hf556 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 556)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32cc
  have hf560 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 560)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32d0
  have hf564 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 564)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x32d4
  revert hpc hf512 hf516 hf520 hf524 hf528 hf532 hf536 hf540 hf544 hf548 hf552 hf556 hf560 hf564
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hf512 hf516 hf520 hf524 hf528 hf532 hf536 hf540 hf544 hf548 hf552 hf556 hf560 hf564
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (lastVal.setWidth 8)
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  rw [vecU8Buf_snoc_eq A curCap curPtr curBs (BitVec.zeroExtend 8 lastVal) hlt]
  refine hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) ?_
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]

theorem step_encVarint_final (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (lastVal v curCap curPtr sp v48 v40 : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 48#64)
    (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = lastVal)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
      ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
      A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf →
      Q sf (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [lastVal.setWidth 8]).length) ∗
        vecU8Buf A curCap curPtr (curBs ++ [lastVal.setWidth 8]) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗
        ((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp - 8#64) ↦₆₄ s0.readReg64 .x19) ∗
        A.pool ∗ stackAt (sp - 48#64) doReserveStack) ∗ F)) :
    SepWPp (tripleRatchetProgAt b C ctl abs) (s0.readReg64 .lr) s P Q Qp :=
  step_encVarint_final_trap b A (tripleRatchetExterns C ctl abs) lastVal v curCap curPtr sp v48 v40 curBs hlt hpc hrun hsp halign htr hx0 hx1 hx8 hx9 hcs hP hnext
theorem step_encVarint_s1_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 32#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 7).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 136#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte val])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 32)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30c0
  have hf36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 36)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30c4
  have hf40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 40)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30c8
  have hf44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 44)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30cc
  have hf48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 48)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30d0
  have hf52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 52)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30d4
  have hf56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 56)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30d8
  have hf60 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 60)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30dc
  have hf64 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 64)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30e0
  have hf68 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 68)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30e4
  have hf72 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 72)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x30e8
  revert hpc hnext hf32 hf36 hf40 hf44 hf48 hf52 hf56 hf60 hf64 hf68 hf72
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf32 hf36 hf40 hf44 hf48 hf52 hf56 hf60 hf64 hf68 hf72
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte val)
  have hcond := ult_0x4000_eq val
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 7).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 136#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte val) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s1 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 32#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 7).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 136#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 7).ult 128#64 then val >>> 7 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte val]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte val]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte val])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s1_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hcs hP hnext
theorem step_encVarint_s2_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 136#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 14).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 252#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 7)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf136 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 136)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3128
  have hf140 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 140)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x312c
  have hf144 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 144)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3130
  have hf148 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 148)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3134
  have hf152 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 152)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3138
  have hf156 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 156)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x313c
  have hf160 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 160)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3140
  have hf164 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 164)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3144
  have hf168 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 168)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3148
  have hf172 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 172)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x314c
  have hf176 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 176)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x3150
  revert hpc hnext hf136 hf140 hf144 hf148 hf152 hf156 hf160 hf164 hf168 hf172 hf176
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf136 hf140 hf144 hf148 hf152 hf156 hf160 hf164 hf168 hf172 hf176
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 7))
  have hcond := ult_0x200000_eq val
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 14).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 252#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 7)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s2 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 136#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 14).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 252#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 14).ult 128#64 then val >>> 14 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x10 = curPtr →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 7)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 7)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s2_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx10 hcs hP hnext
theorem step_encVarint_s3_trap (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 252#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 21).ult 128#64 then
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName + 360#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 14)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q Qp := by
  have hf252 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 252)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x319c
  have hf256 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 256)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31a0
  have hf260 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 260)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31a4
  have hf264 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 264)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31a8
  have hf268 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 268)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31ac
  have hf272 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 272)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31b0
  have hf276 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 276)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31b4
  have hf280 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 280)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31b8
  have hf284 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 284)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31bc
  have hf288 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 288)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31c0
  have hf292 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 292)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31c4
  have hf296 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := b)
    (H := Rust.withPanics (ext)) (k := 296)
    libsignalSessionCode_fnOff_0x30a0 (by decide) encodeVarintBin_decode_0x31c8
  revert hpc hnext hf252 hf256 hf260 hf264 hf268 hf272 hf276 hf280 hf284 hf288 hf292 hf296
  generalize (tripleRatchetProgAtExt b ext).fnAddr encodeVarintName = entry
  intro hpc hnext hf252 hf256 hf260 hf264 hf268 hf272 hf276 hf280 hf284 hf288 hf292 hf296
  examples_hide_fetches
  subst hP
  rcases hcs with ⟨h21, h22, h23, h24, h25, h26, h27, h28, hvregs⟩
  have hbeq := cap_beq_len_false hlt
  have hlen1 := bv_len_add_one curBs (varintContByte (val >>> 14))
  rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  cases hbr : (val >>> 21).ult 128#64
  · apply SepWPp.of_sepWP (mid := entry + 360#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])
  · apply SepWPp.of_sepWP (mid := entry + 512#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs (varintContByte (val >>> 14)) hlt]
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [EncVarintCalleeSaved, arm64_norm, *])

theorem step_encVarint_s3 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (val v curCap curPtr : BitVec 64) (curBs : List (BitVec 8))
    (hlt : curBs.length < curCap.toNat)
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 252#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = val)
    (hx1 : s.readReg64 .x1 = v)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 curBs.length)
    (hx9 : s.readReg64 .x9 = curCap)
    (hx10 : s.readReg64 .x10 = curPtr)
    (hcs : EncVarintCalleeSaved s0 s)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (if (val >>> 21).ult 128#64 then
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 512#64
      else
        (tripleRatchetProgAt b C ctl abs).fnAddr encodeVarintName + 360#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = (if (val >>> 21).ult 128#64 then val >>> 21 else val) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x8 = BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length →
      sm.readReg64 .x9 = curCap →
      sm.readReg64 .x12 = val >>> 28 →
      EncVarintCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (curBs ++ [varintContByte (val >>> 14)]).length) ∗
          vecU8Buf A curCap curPtr (curBs ++ [varintContByte (val >>> 14)])) ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp :=
  step_encVarint_s3_trap b A (tripleRatchetExterns C ctl abs) val v curCap curPtr curBs hlt hpc hrun hx0 hx1 hx8 hx9 hx10 hcs hP hnext

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
