/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.BV.ReflectROBDD
public meta import ProofLib.BV.ReflectROBDD
public import Arm64.Trusted.ISA.Decode
public import Arm64.Testing.Harness.Encode

/-!
# Shared Encoder/Decoder Round-Trip Lemmas

Finite bitvector enumeration helpers, `[simp]` round-trip identities for registers, widths,
conditions, shifts, and extensions, and immediate extraction identities shared across the
encoder/decoder proofs.
-/

@[expose] public section

namespace Arm64

/-! ## Option Splitting and Finite BitVec Enumeration -/

theorem ite_some_imp {α : Type} {c : Bool} {t e : Option α} {p : α} {P : Prop}
    (ht : c = true → t = some p → P)
    (he : c = false → e = some p → P)
    (h : (if c then t else e) = some p) : P := by
  cases hc : c
  · simp [hc] at h
    exact he hc h
  · simp [hc] at h
    exact ht hc h

theorem forall_bitvec {n : Nat} {P : BitVec n → Prop} [DecidablePred P]
    (h : (List.finRange (2 ^ n)).all (fun i => decide (P (BitVec.ofFin i))) = true) :
    ∀ b : BitVec n, P b := by
  intro ⟨i⟩
  have hmem : i ∈ List.finRange (2 ^ n) := List.mem_finRange i
  have hp := List.all_eq_true.mp h i hmem
  exact of_decide_eq_true hp

theorem forall_bitvec6_2 {P : BitVec 6 → BitVec 6 → Prop} [∀ x y, Decidable (P x y)]
    (h : (List.finRange 64).all (fun i => (List.finRange 64).all (fun j => decide (P (BitVec.ofFin i) (BitVec.ofFin j)))) = true) :
    ∀ x y : BitVec 6, P x y := by
  intro ⟨i⟩ ⟨j⟩
  have h1 := List.all_eq_true.mp h i (List.mem_finRange i)
  have h2 := List.all_eq_true.mp h1 j (List.mem_finRange j)
  exact of_decide_eq_true h2

/-! ## Register, Width, Condition, Shift, and Extend Round-Trips -/

@[simp]
theorem Reg.isValidZR_fromZRBits : ∀ b : BitVec 5, (Reg.fromZRBits b).isValidZR = true := by
  apply forall_bitvec; decide

@[simp]
theorem Reg.toBits_fromZRBits : ∀ b : BitVec 5, (Reg.fromZRBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem Reg.isValidSP_fromSPBits : ∀ b : BitVec 5, (Reg.fromSPBits b).isValidSP = true := by
  apply forall_bitvec; decide

@[simp]
theorem Reg.toBits_fromSPBits : ∀ b : BitVec 5, (Reg.fromSPBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem Reg.isValid_cond_ZR_SP (c : Bool) (b : BitVec 5) :
    (if c then (if c then Reg.fromZRBits b else Reg.fromSPBits b).isValidZR
          else (if c then Reg.fromZRBits b else Reg.fromSPBits b).isValidSP) = true := by
  cases c <;> simp

@[simp]
theorem Reg.toBits_cond_ZR_SP (c : Bool) (b : BitVec 5) :
    (if c then Reg.fromZRBits b else Reg.fromSPBits b).toBits = b := by
  cases c <;> simp

@[simp]
theorem AddSubOp.toBits_ofBits (isSub setFlags : Bool) :
    (AddSubOp.ofBits isSub setFlags).toBits = (isSub, setFlags) := by
  cases isSub <;> cases setFlags <;> rfl

@[simp]
theorem CondSelectOp.toBits_ofBits (op o2 : Bool) :
    (CondSelectOp.ofBits op o2).toBits = (op, o2) := by
  cases op <;> cases o2 <;> rfl

@[simp]
theorem LogicalOp.toBits_ofBits (opc : BitVec 2) (nBit : Bool) :
    (LogicalOp.ofBits opc nBit).toBits = (opc, nBit) := by
  revert opc; cases nBit <;> (apply forall_bitvec; decide)

@[simp]
theorem RegWidth.toBool_ofBool (b : Bool) :
    (RegWidth.ofBool b).toBool = b := by
  cases b <;> rfl

@[simp]
theorem RegWidth.toBool_ite (b : Bool) :
    (if b then RegWidth.W64 else RegWidth.W32).toBool = b := by
  cases b <;> rfl

@[simp]
theorem RegWidth.beq_W64_ite (b : Bool) :
    ((if b then RegWidth.W64 else RegWidth.W32) == RegWidth.W64) = b := by
  cases b <;> rfl

@[simp]
theorem RegWidth.beq_W32_ite (b : Bool) :
    ((if b then RegWidth.W64 else RegWidth.W32) == RegWidth.W32) = !b := by
  cases b <;> rfl

@[simp]
theorem RegWidth.beq_self (w : RegWidth) : (w == w) = true := by
  cases w <;> rfl

@[simp]
theorem bitvec_ofNat_mod_16_eq_extractLsb (w : BitVec 32) :
    BitVec.ofNat 4 (w.toNat % 16) = w.extractLsb' 0 4 := by
  apply BitVec.eq_of_toNat_eq
  simp

@[simp]
theorem CondCode.toBits_ofBits : ∀ b : BitVec 4, (CondCode.ofBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem ShiftType.toBits_ofBits : ∀ b : BitVec 2, (ShiftType.ofBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem ExtendType.toBits_ofBits : ∀ b : BitVec 3, (ExtendType.ofBits b).toBits = b := by
  apply forall_bitvec; decide

theorem bitvec2_cases (b : BitVec 2) : b = 0#2 ∨ b = 1#2 ∨ b = 2#2 ∨ b = 3#2 := by
  revert b; apply forall_bitvec; decide

theorem bitvec3_cases (b : BitVec 3) :
    b = 0#3 ∨ b = 1#3 ∨ b = 2#3 ∨ b = 3#3 ∨ b = 4#3 ∨ b = 5#3 ∨ b = 6#3 ∨ b = 7#3 := by
  revert b; apply forall_bitvec; decide

@[simp]
theorem tbz_bitPos_lt_64 (b5 : Bool) (b40 : BitVec 5) :
    ((if b5 then 32 else 0) + b40.toNat < 64) = true := by
  revert b40; cases b5 <;> (apply forall_bitvec; decide)

@[simp]
theorem tbz_bitPos_ge_32 (b5 : Bool) (b40 : BitVec 5) :
    decide ((if b5 then 32 else 0) + b40.toNat ≥ 32) = b5 := by
  revert b40; cases b5 <;> (apply forall_bitvec; decide)

@[simp]
theorem tbz_bitPos_mod_32 (b5 : Bool) (b40 : BitVec 5) :
    BitVec.ofNat 5 (((if b5 then 32 else 0) + b40.toNat) % 32) = b40 := by
  revert b40; cases b5 <;> (apply forall_bitvec; decide)

@[simp]
theorem MemWidth.toBits_ofBits : ∀ b : BitVec 2, (MemWidth.ofBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem AesOp.toBits_ofBits : ∀ b : BitVec 2, (AesOp.ofBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem RegWidth.beq_simps :
    (RegWidth.W64 == RegWidth.W64) = true ∧
    (RegWidth.W64 == RegWidth.W32) = false ∧
    (RegWidth.W32 == RegWidth.W64) = false ∧
    (RegWidth.W32 == RegWidth.W32) = true ∧
    RegWidth.W64.toBool = true ∧
    RegWidth.W32.toBool = false := by
  decide

@[simp]
theorem ShiftType.beq_ROR :
    (ShiftType.LSL == ShiftType.ROR) = false ∧
    (ShiftType.LSR == ShiftType.ROR) = false ∧
    (ShiftType.ASR == ShiftType.ROR) = false ∧
    (ShiftType.ROR == ShiftType.ROR) = true ∧
    (ShiftType.LSL != ShiftType.ROR) = true ∧
    (ShiftType.LSR != ShiftType.ROR) = true ∧
    (ShiftType.ASR != ShiftType.ROR) = true := by
  decide

@[simp]
theorem bitvec4_ofNat_shift_mod (k : Nat) (w : BitVec 32) :
    BitVec.ofNat 4 (w.toNat >>> k % 16) = w.extractLsb' k 4 := by
  have h : (w.extractLsb' k 4).toNat = w.toNat >>> k % 16 := by simp
  rw [← h, BitVec.ofNat_toNat]
  rfl

@[simp]
theorem bitvec5_ofNat_shift_mod (k : Nat) (w : BitVec 32) :
    BitVec.ofNat 5 (w.toNat >>> k % 32) = w.extractLsb' k 5 := by
  have h : (w.extractLsb' k 5).toNat = w.toNat >>> k % 32 := by simp
  rw [← h, BitVec.ofNat_toNat]
  rfl

@[simp]
theorem bitvec6_ofNat_shift_mod (k : Nat) (w : BitVec 32) :
    BitVec.ofNat 6 (w.toNat >>> k % 64) = w.extractLsb' k 6 := by
  have h : (w.extractLsb' k 6).toNat = w.toNat >>> k % 64 := by simp
  rw [← h, BitVec.ofNat_toNat]
  rfl

/-! ## Immediate Extraction and Extension Identities -/

@[simp]
theorem adr_offset_page_true (imm21 : BitVec 21) :
    (((imm21.signExtend 64) <<< 12).extractLsb' 12 21) = imm21 := by bv_slice

@[simp]
theorem adr_offset_page_false (imm21 : BitVec 21) :
    ((imm21.signExtend 64).extractLsb' 0 21) = imm21 := by bv_slice

@[simp]
theorem adr_immhi_immlo_low (immhi : BitVec 19) (immlo : BitVec 2) :
    (immhi ++ immlo).extractLsb' 0 2 = immlo := by bv_slice

@[simp]
theorem adr_immhi_immlo_high (immhi : BitVec 19) (immlo : BitVec 2) :
    (immhi ++ immlo).extractLsb' 2 19 = immhi := by bv_slice

@[simp]
theorem addSubImm_sh_false (imm12 : BitVec 12) :
    ((imm12.zeroExtend 64).extractLsb' 0 12) = imm12 := by bv_slice

theorem addSubImm_sh_true_lo_ne (imm12 : BitVec 12) (h : (imm12 == 0#12) = false) :
    (((((imm12.zeroExtend 64) <<< 12).extractLsb' 0 12).zeroExtend 64) == ((imm12.zeroExtend 64) <<< 12)) = false := by
  bv_robdd

@[simp]
theorem addSubImm_sh_true_hi (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 12).extractLsb' 12 12) = imm12 := by bv_slice

@[simp]
theorem b_offset_extract (imm26 : BitVec 26) :
    (((imm26.signExtend 64) <<< 2).extractLsb' 2 26) = imm26 := by bv_slice

@[simp]
theorem imm19_offset_extract (imm19 : BitVec 19) :
    (((imm19.signExtend 64) <<< 2).extractLsb' 2 19) = imm19 := by bv_slice

@[simp]
theorem imm14_offset_extract (imm14 : BitVec 14) :
    (((imm14.signExtend 64) <<< 2).extractLsb' 2 14) = imm14 := by bv_slice

@[simp]
theorem imm5_zeroExtend_extract (imm5 : BitVec 5) :
    ((imm5.zeroExtend 64).extractLsb' 0 5) = imm5 := by bv_slice

@[simp]
theorem imm6_zeroExtend_extract (imm6 : BitVec 6) :
    ((imm6.zeroExtend 64).extractLsb' 0 6) = imm6 := by bv_slice

@[simp]
theorem imm16_zeroExtend_extract (imm16 : BitVec 16) :
    ((imm16.zeroExtend 64).extractLsb' 0 16) = imm16 := by bv_slice

@[simp]
theorem imm7_offset_extract_2 (imm7 : BitVec 7) :
    (((imm7.signExtend 64) <<< 2).extractLsb' 2 7) = imm7 := by bv_slice

@[simp]
theorem imm7_offset_extract_3 (imm7 : BitVec 7) :
    (((imm7.signExtend 64) <<< 3).extractLsb' 3 7) = imm7 := by bv_slice

@[simp]
theorem imm7_offset_extract_4 (imm7 : BitVec 7) :
    (((imm7.signExtend 64) <<< 4).extractLsb' 4 7) = imm7 := by bv_slice

@[simp]
theorem uimm12_offset_extract_0 (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 0).extractLsb' 0 12) = imm12 := by bv_slice

@[simp]
theorem uimm12_offset_extract_1 (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 1).extractLsb' 1 12) = imm12 := by bv_slice

@[simp]
theorem uimm12_offset_extract_2 (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 2).extractLsb' 2 12) = imm12 := by bv_slice

@[simp]
theorem uimm12_offset_extract_3 (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 3).extractLsb' 3 12) = imm12 := by bv_slice

@[simp]
theorem imm12_offset_extract_4 (imm12 : BitVec 12) :
    (((imm12.zeroExtend 64) <<< 4).extractLsb' 4 12) = imm12 := by bv_slice

@[simp]
theorem simm9_offset_extract (imm9 : BitVec 9) :
    ((imm9.signExtend 64).extractLsb' 0 9) = imm9 := by bv_slice

attribute [-simp] BitVec.getLsbD_eq_getElem

end Arm64
