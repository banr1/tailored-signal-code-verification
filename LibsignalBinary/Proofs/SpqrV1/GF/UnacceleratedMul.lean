/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.SpqrV1.GF.GfCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `spqr::encoding::gf::unaccelerated::mul`

Proves fixed-offset (`0x63ca4`) and relocatable `[LibsignalPlacement]` (Block `384`) subroutine
contracts for `spqr::encoding::gf::unaccelerated::mul` against `unaccelerated.mul`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.GF.UnacceleratedMul

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

abbrev unacceleratedMulName : String := "spqr::encoding::gf::unaccelerated::mul"

theorem unacceleratedMul_fnOff : libsignalSessionCode.fnOff unacceleratedMulName = 0x5e8ac :=
  ls_lemma% fnOff "spqr::encoding::gf::unaccelerated::mul"

gen_decodes libsignalSessionCode_tree unacceleratedMulBin [0x5e8ac → 0x5e994]

/-- Image offset of `spqr::encoding::gf::reduce::REDUCE_BYTES` (`0x85ae0`, 512 bytes = 256 × `u16`). -/
abbrev reduceBytesOff : Nat := num% (ls_xref% 0x5e970 0x5e974)

/-- The 512 little-endian bytes of `spqr::encoding::gf::reduce::REDUCE_BYTES`. -/
def reduceTableBytes : List (BitVec 8) :=
  (List.range 256).flatMap fun i =>
    let w := reduce.reduceByteEntry (BitVec.ofNat 8 i)
    [w.extractLsb' 0 8, w.extractLsb' 8 8]

theorem reduceTableBytes_length : reduceTableBytes.length = 512 := by
  decide +kernel

theorem reduceTableBytes_pack16 (idx : BitVec 8) :
    pack16 (reduceTableBytes.getD (2 * idx.toNat) 0#8)
      (reduceTableBytes.getD (2 * idx.toNat + 1) 0#8) =
    reduce.reduceByteEntry idx := by
  revert idx
  decide +kernel

/-- Read-only separation-logic assertion for `REDUCE_BYTES` at `b + 0xa4ae0`. -/
def reduceTableAt (b : BitVec 64) : SepProp :=
  (b + bv% (ls_xref% 0x5e970 0x5e974)) ↦ᵣ reduceTableBytes

/-- `.rodata` slice at `0x85ae0` (`ls_xref% 0x63d68 0x63d6c`, 512 bytes): `REDUCE_BYTES`. -/
theorem rodata_reduceTable {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ reduceTableAt img.base ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := reduceBytesOff) (n := 512) (bs := reduceTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) reduceTableBytes_length (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by rw [reduceTableBytes_length]; decide) hP

def reduceTableFrame (b : BitVec 64) (off : Nat) : SepProp :=
  let base := b + bv% (ls_xref% 0x5e970 0x5e974)
  (base ↦ᵣ reduceTableBytes.take off) ∗
    ((base + BitVec.ofNat 64 (off + 2)) ↦ᵣ reduceTableBytes.drop (off + 2))

theorem reduceTableAt_focus16 (b : BitVec 64) (idx : BitVec 8) :
    reduceTableAt b =
      ((b + bv% (ls_xref% 0x5e970 0x5e974) + BitVec.ofNat 64 (2 * idx.toNat)) ↦₁₆ᵣ
        reduce.reduceByteEntry idx) ∗
      reduceTableFrame b (2 * idx.toNat) := by
  have hlt := idx.isLt
  have hlen : 2 * idx.toNat + 2 ≤ reduceTableBytes.length := by
    rw [reduceTableBytes_length]; omega
  unfold reduceTableAt reduceTableFrame
  rw [pointsToBytesRO_split3 _ reduceTableBytes (2 * idx.toNat) 2 hlen,
      pointsToBytesRO_take2_eq_pointsTo16RO _ reduceTableBytes (2 * idx.toNat) hlen,
      reduceTableBytes_pack16 idx]

theorem reduceTableAt_unfocus16 (b : BitVec 64) (idx : BitVec 8) :
    ((b + bv% (ls_xref% 0x5e970 0x5e974) + BitVec.ofNat 64 (2 * idx.toNat)) ↦₁₆ᵣ
      reduce.reduceByteEntry idx) ∗
    reduceTableFrame b (2 * idx.toNat) ⊢
      reduceTableAt b := by
  rw [reduceTableAt_focus16 b idx]
  exact Entails.refl _

theorem fnAddr_adrp_63d68 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr unacceleratedMulName + 196#64) &&&
      0xfffffffffffff000#64) = b + 0x5e000#64 := by
  rw [Program.fnAddr_rebase, unacceleratedMul_fnOff]
  revert hb; bv_bits

private theorem sbfx64_helper (w : BitVec 64) :
    (w &&& 1#64 |||
      (if w.getLsbD 0 = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if w.getLsbD 0 then 18446744073709551615#64 else 0#64 := by
  bv_bits

private theorem sbfx64_one_eq (v : BitVec 64) (i : Nat) :
    (v >>> i &&& 1#64 |||
      (if v.getLsbD i = true then 18446744073709551615#64 else 0#64) &&&
        18446744073709551614#64) =
      if v.getLsbD i then 18446744073709551615#64 else 0#64 := by
  have h0 : (v >>> i).getLsbD 0 = v.getLsbD i := by simp
  rw [← h0, sbfx64_helper]

private theorem truncate32_if_all_ones (b : Bool) :
    BitVec.truncate 32 (if b then 18446744073709551615#64 else 0#64) =
      if b then 0xffffffff#32 else 0#32 := by
  cases b <;> rfl

private theorem x0_mask16 (x0 : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64 =
      BitVec.zeroExtend 64 (BitVec.truncate 16 x0) := by
  bv_bits

private theorem truncate32_zext64_16 (v : BitVec 16) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 v) = BitVec.zeroExtend 32 v := by
  bv_bits

private theorem x1_getLsbD (x1 : BitVec 64) (i : Nat) (hi : i < 16) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD i =
      (BitVec.truncate 16 x1).getLsbD i := by
  have hi32 : i < 32 := by omega
  have hi64 : i < 64 := by omega
  simp [hi, hi32, hi64]

private theorem sxth32_x1_eq (x1 : BitVec 64) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 0 &&& 65535#64 |||
        (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 15 = true then
            18446744073709551615#64
          else 0#64) &&&
          18446744073709486080#64) =
      BitVec.signExtend 32 (BitVec.truncate 16 x1) := by
  bv_bits

private theorem sxth32_trunc16 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 32 yv) = yv := by
  bv_bits

private theorem sxth32_shr16 (yv : BitVec 16) :
    (BitVec.signExtend 32 yv) >>> 16 = if yv.getLsbD 15 then 0xffff#32 else 0#32 := by
  bv_bits

private theorem sxth33_trunc16 (yv : BitVec 16) :
    BitVec.truncate 16 (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) = yv := by
  bv_bits

private theorem sxth33_shr16 (yv : BitVec 16) :
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)) >>> 16 =
      if yv.getLsbD 15 then 0x1ffff#33 else 0#33 := by
  bv_bits

private theorem yv_shr15 (yv : BitVec 16) :
    yv >>> 15 = if yv.getLsbD 15 then 1#16 else 0#16 := by
  bv_bits

private theorem beq_bne_self (a b : Bool) : (b == (a != b)) = !a := by
  cases a <;> cases b <;> rfl

private theorem adds_sxth_one_gt (yv : BitVec 16) :
    ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = !yv.getLsbD 15 := by
  have hlo32 := congrArg BitVec.toNat (sxth32_trunc16 yv)
  have hhi32 := congrArg BitVec.toNat (sxth32_shr16 yv)
  have hlo33 := congrArg BitVec.toNat (sxth33_trunc16 yv)
  have hhi33 := congrArg BitVec.toNat (sxth33_shr16 yv)
  have hb15 := congrArg BitVec.toNat (yv_shr15 yv)
  rw [BitVec.toNat_setWidth] at hlo32 hlo33
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hhi32 hhi33 hb15
  have hlt16 : yv.toNat < 2 ^ 16 := yv.isLt
  have hlt32 : (BitVec.signExtend 32 yv).toNat < 2 ^ 32 := (BitVec.signExtend 32 yv).isLt
  have hlt33 : (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat < 2 ^ 33 :=
    (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).isLt
  unfold ConditionHolds addsPState32 AddWithCarry32
  dsimp only
  rw [beq_bne_self]
  cases hb : yv.getLsbD 15 <;>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true] at hhi32 hhi33 hb15 ⊢
  · rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', beq_eq_false_iff_ne]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 0 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 0 at hhi33
    change yv.toNat / 32768 = 0 at hb15
    refine ⟨?_, ?_⟩
    · intro h
      have ht := congrArg BitVec.toNat h
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat] at ht
      omega
    · rw [BitVec.msb_eq_false_iff_two_mul_lt]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]
      omega
  · rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', beq_iff_eq]
    change (BitVec.signExtend 32 yv).toNat / 65536 = 65535 at hhi32
    change (BitVec.signExtend 33 (BitVec.signExtend 32 yv)).toNat / 65536 = 131071 at hhi33
    change yv.toNat / 32768 = 1 at hb15
    by_cases hy : yv.toNat = 65535
    · left
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    · right
      rw [BitVec.msb_eq_true_iff_two_mul_ge]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      have hs1 : (BitVec.signExtend 33 1#32).toNat = 1 := rfl
      rw [hs1]
      omega

private def pmTerm (cv yv : BitVec 16) (i : Nat) : BitVec 32 :=
  (BitVec.zeroExtend 32 cv <<< i) &&& (if yv.getLsbD i = true then 0xffff_ffff#32 else 0#32)

private theorem ite_xor_eq_xor_and_mask (b : Bool) (acc x : BitVec 32) :
    (if b = true then acc ^^^ x else acc) =
      acc ^^^ (x &&& (if b = true then 0xffff_ffff#32 else 0#32)) := by
  cases b <;> bv_slice

private theorem test_bit16_eq_getLsbD (yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (0#16 != yv &&& (1#16 <<< i)) = yv.getLsbD i := by
  match i, hi with
  | 0, _ => bv_slice
  | 1, _ => bv_slice
  | 2, _ => bv_slice
  | 3, _ => bv_slice
  | 4, _ => bv_slice
  | 5, _ => bv_slice
  | 6, _ => bv_slice
  | 7, _ => bv_slice
  | 8, _ => bv_slice
  | 9, _ => bv_slice
  | 10, _ => bv_slice
  | 11, _ => bv_slice
  | 12, _ => bv_slice
  | 13, _ => bv_slice
  | 14, _ => bv_slice
  | 15, _ => bv_slice
  | n + 16, hi => omega

private theorem pmTerm_rhs_0 (cv yv : BitVec 16) :
    (if (0#16 != yv &&& (1#16 <<< 0)) = true then BitVec.zeroExtend 32 cv <<< 0 else 0#32) =
      pmTerm cv yv 0 := by
  dsimp only [pmTerm]
  rw [test_bit16_eq_getLsbD yv 0 (by decide)]
  generalize yv.getLsbD 0 = b
  cases b <;> bv_slice

private theorem pmTerm_rhs (cv yv : BitVec 16) (i : Nat) (hi : i < 16) :
    (BitVec.zeroExtend 32 cv <<< i) &&&
      (if (0#16 != yv &&& (1#16 <<< i)) = true then 0xffff_ffff#32 else 0#32) =
      pmTerm cv yv i := by
  dsimp only [pmTerm]
  rw [test_bit16_eq_getLsbD yv i hi]

private theorem truncate32_xor (a b : BitVec 64) :
    BitVec.truncate 32 (a ^^^ b) = BitVec.truncate 32 a ^^^ BitVec.truncate 32 b := by
  bv_slice

private theorem polyMul_term_0 (cv yv : BitVec 16) :
    BitVec.truncate 32
      (BitVec.zeroExtend 64 (if yv.getLsbD 0 = true then 0xffffffff#32 else 0#32) &&&
        BitVec.zeroExtend 64 cv) =
    pmTerm cv yv 0 := by
  dsimp only [pmTerm]
  generalize yv.getLsbD 0 = b
  cases b <;> bv_slice

private theorem polyMul_term_mid (cv yv : BitVec 16) (i : Nat) :
    (if yv.getLsbD i = true then 0xffffffff#32 else 0#32) &&&
      (BitVec.zeroExtend 32 cv <<< i) =
    pmTerm cv yv i := by
  dsimp only [pmTerm]
  rw [BitVec.and_comm]

private theorem polyMul_term_15 (cv yv : BitVec 16) :
    BitVec.truncate 32
      (if ConditionHolds CondCode.GT (addsPState32 (BitVec.signExtend 32 yv) 1#32) = true then 0#64
       else BitVec.truncate 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 cv <<< 15))) =
    pmTerm cv yv 15 := by
  dsimp only [pmTerm]
  rw [adds_sxth_one_gt]
  generalize yv.getLsbD 15 = b
  cases b <;> bv_slice

attribute [local irreducible] pmTerm in
private theorem unaccelerated_polyMul_eq_pmTerms (cv yv : BitVec 16) :
    unaccelerated.polyMul cv yv =
      pmTerm cv yv 0 ^^^ pmTerm cv yv 1 ^^^ pmTerm cv yv 2 ^^^ pmTerm cv yv 3 ^^^
      pmTerm cv yv 4 ^^^ pmTerm cv yv 5 ^^^ pmTerm cv yv 6 ^^^ pmTerm cv yv 7 ^^^
      pmTerm cv yv 8 ^^^ pmTerm cv yv 9 ^^^ pmTerm cv yv 10 ^^^ pmTerm cv yv 11 ^^^
      pmTerm cv yv 12 ^^^ pmTerm cv yv 13 ^^^ pmTerm cv yv 14 ^^^ pmTerm cv yv 15 := by
  simp only [unaccelerated.polyMul, unaccelerated.polyMulLoop,
    ite_xor_eq_xor_and_mask, Nat.reduceAdd, BitVec.zero_xor,
    pmTerm_rhs_0 cv yv, pmTerm_rhs cv yv 1 (by decide),
    pmTerm_rhs cv yv 2 (by decide), pmTerm_rhs cv yv 3 (by decide),
    pmTerm_rhs cv yv 4 (by decide), pmTerm_rhs cv yv 5 (by decide),
    pmTerm_rhs cv yv 6 (by decide), pmTerm_rhs cv yv 7 (by decide),
    pmTerm_rhs cv yv 8 (by decide), pmTerm_rhs cv yv 9 (by decide),
    pmTerm_rhs cv yv 10 (by decide), pmTerm_rhs cv yv 11 (by decide),
    pmTerm_rhs cv yv 12 (by decide), pmTerm_rhs cv yv 13 (by decide),
    pmTerm_rhs cv yv 14 (by decide), pmTerm_rhs cv yv 15 (by decide)]

attribute [local irreducible] pmTerm in
theorem polyMul_asm_eq (x0 x1 : BitVec 64) :
    BitVec.zeroExtend 64
      (BitVec.truncate 32
        (BitVec.zeroExtend 64
            (BitVec.truncate 32
              (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 0 &&& 1#64 |||
                (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 0 = true then
                    18446744073709551615#64
                  else 0#64) &&&
                  18446744073709551614#64)) &&&
          (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) ^^^
        if
            ConditionHolds CondCode.GT
                (addsPState32
                  (BitVec.truncate 32
                    (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 0 &&& 65535#64 |||
                      (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 15 = true then
                          18446744073709551615#64
                        else 0#64) &&&
                        18446744073709486080#64))
                  1#32) =
              true then
          0#64
        else
          BitVec.truncate 64
            (BitVec.truncate 32
              ((BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 15))) ^^^
      (BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 1 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 1 = true then
                   18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 1 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 2 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 2 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 2) ^^^
      (BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 3 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 3 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 3 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 4 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 4 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 4 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 5 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 5 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 5) ^^^
      (BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 6 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 6 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 6 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 7 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 7 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 7 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 8 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 8 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 8 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 9 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 9 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 9) ^^^
      (BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 10 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 10 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 10 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 11 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 11 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 11 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 12 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 12 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 12 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 13 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 13 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 13 ^^^
        BitVec.truncate 32
            (BitVec.zeroExtend 64 (BitVec.truncate 32 x1) >>> 14 &&& 1#64 |||
              (if (BitVec.zeroExtend 64 (BitVec.truncate 32 x1)).getLsbD 14 = true then
                  18446744073709551615#64
                else 0#64) &&&
                18446744073709551614#64) &&&
          BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x0) &&& 65535#64) <<< 14)) =
    BitVec.zeroExtend 64 (unaccelerated.polyMul (BitVec.truncate 16 x0) (BitVec.truncate 16 x1)) := by
  rw [sxth32_x1_eq x1]
  simp only [sbfx64_one_eq, truncate32_if_all_ones]
  simp only [x1_getLsbD x1 0 (by decide), x1_getLsbD x1 1 (by decide),
    x1_getLsbD x1 2 (by decide), x1_getLsbD x1 3 (by decide),
    x1_getLsbD x1 4 (by decide), x1_getLsbD x1 5 (by decide),
    x1_getLsbD x1 6 (by decide), x1_getLsbD x1 7 (by decide),
    x1_getLsbD x1 8 (by decide), x1_getLsbD x1 9 (by decide),
    x1_getLsbD x1 10 (by decide), x1_getLsbD x1 11 (by decide),
    x1_getLsbD x1 12 (by decide), x1_getLsbD x1 13 (by decide),
    x1_getLsbD x1 14 (by decide),
    x0_mask16, truncate32_zext64_16,
    truncate32_xor, polyMul_term_0, polyMul_term_15, polyMul_term_mid,
    unaccelerated_polyMul_eq_pmTerms]
  congr 1
  ac_rfl

theorem ofNat_mul2_eq_shl1 (idx : BitVec 8) :
    BitVec.ofNat 64 (2 * idx.toNat) = (BitVec.zeroExtend 64 idx) <<< 1 := by
  revert idx
  decide +kernel

theorem uxtw1_idx1_eq (p : BitVec 32) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (p >>> 24)).toNat) =
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 p >>> 24)) <<< 1 := by
  rw [ofNat_mul2_eq_shl1]
  bv_bits

theorem uxtw1_idx2_eq (v1 : BitVec 32) :
    BitVec.ofNat 64 (2 * (BitVec.truncate 8 (v1 >>> 16)).toNat) =
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 v1 >>> 16 &&& 255#64)) <<< 1 := by
  rw [ofNat_mul2_eq_shl1]
  bv_bits

private theorem polyReduce_asm_helper (r2 : BitVec 16) (v1 : BitVec 32) :
    BitVec.zeroExtend 16
      (BitVec.truncate 32 (BitVec.zeroExtend 64 r2 ^^^ BitVec.zeroExtend 64 v1)) =
      BitVec.truncate 16 (v1 ^^^ BitVec.zeroExtend 32 r2) := by
  bv_slice

@[local arm64_norm, local wp_norm]
theorem polyReduce_asm_eq (a b_arg : BitVec 16) :
    BitVec.zeroExtend 16
      (BitVec.truncate 32
        (BitVec.zeroExtend 64
            (reduce.reduceByteEntry
              (BitVec.truncate 8
                ((unaccelerated.polyMul a b_arg ^^^
                    BitVec.zeroExtend 32
                        (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
                      8) >>>
                  16))) ^^^
          BitVec.zeroExtend 64
            (unaccelerated.polyMul a b_arg ^^^
              BitVec.zeroExtend 32
                  (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul a b_arg >>> 24))) <<<
                8))) =
    unaccelerated.mul a b_arg := by
  dsimp only [unaccelerated.mul, reduce.polyReduce]
  exact polyReduce_asm_helper _ _

/-- Specification of `spqr::encoding::gf::unaccelerated::mul` (`0x63ca4`).
Takes two 16-bit field elements `a` and `b_arg` in the low 16 bits of `.x0` and `.x1`,
reads the precomputed table `reduceTableAt b`, and returns `unaccelerated.mul a b_arg`
in the low 16 bits of `.x0` without touching the stack. -/
def unacceleratedMulSpec (b : BitVec 64) : Spec (BitVec 16 × BitVec 16) where
  pre := fun (a, b_arg) s =>
    ⌜b &&& 0xfff#64 = 0#64 ∧
      BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b_arg⌝ ∗
      reduceTableAt b
  post := fun (a, b_arg) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = unaccelerated.mul a b_arg ∧
      sf.trace = s0.trace⌝ ∗
      reduceTableAt b

theorem unacceleratedMul_ok (b : BitVec 64) (ext : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unacceleratedMulName)
      (unacceleratedMulSpec b) := by
  have hfn : libsignalSessionCode.fnOff unacceleratedMulName = 0x5e8ac := unacceleratedMul_fnOff
  code_fetches CryptoVerification.libsignalSessionCode unacceleratedMulBin b
    (Rust.withPanics ext) hfn 0x5e8ac 236
  dsimp only [tripleRatchetProgAtExt] at ⊢
  clear hfn
  simp only [unacceleratedMulSpec]
  wp_init ab s0
  have hpc' : s0.pc = (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr unacceleratedMulName := by
    rw [Program.fnAddr_rebase, unacceleratedMul_fnOff]; exact hpc
  clear hpc
  have hadrp := fnAddr_adrp_63d68 (H := Rust.withPanics ext) h_1
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr unacceleratedMulName = entry
  examples_hide_fetches
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2),
        ← reduceTableAt_focus16 b (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTableAt_focus16 b
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_done

/-! ## Relocatable `[LibsignalPlacement]` Contract (Block `384`) -/

abbrev reduceTableSym : String := "spqr:.rodata..Lanon.234"

/-- Relocatable read-only separation-logic assertion for `REDUCE_BYTES` at `lsρ reduceTableSym`. -/
def reduceTablePlacedAt [LibsignalPlacement] : SepProp :=
  (lsρ reduceTableSym) ↦ᵣ reduceTableBytes

theorem rodata_reduceTable_placed [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) {P : SepProp} (hP : m ⊨ P) :
    m ⊨ reduceTablePlacedAt ∗ P :=
  lsro_intro_chk hro (by decide +kernel) hP

def reduceTablePlacedFrame [LibsignalPlacement] (off : Nat) : SepProp :=
  let base := lsρ reduceTableSym
  (base ↦ᵣ reduceTableBytes.take off) ∗
    ((base + BitVec.ofNat 64 (off + 2)) ↦ᵣ reduceTableBytes.drop (off + 2))

theorem reduceTablePlacedAt_focus16 [LibsignalPlacement] (idx : BitVec 8) :
    reduceTablePlacedAt =
      ((lsρ reduceTableSym + BitVec.ofNat 64 (2 * idx.toNat)) ↦₁₆ᵣ
        reduce.reduceByteEntry idx) ∗
      reduceTablePlacedFrame (2 * idx.toNat) := by
  have hlt := idx.isLt
  have hlen : 2 * idx.toNat + 2 ≤ reduceTableBytes.length := by
    rw [reduceTableBytes_length]; omega
  unfold reduceTablePlacedAt reduceTablePlacedFrame
  rw [pointsToBytesRO_split3 _ reduceTableBytes (2 * idx.toNat) 2 hlen,
      pointsToBytesRO_take2_eq_pointsTo16RO _ reduceTableBytes (2 * idx.toNat) hlen,
      reduceTableBytes_pack16 idx]

theorem reduceTablePlacedAt_unfocus16 [LibsignalPlacement] (idx : BitVec 8) :
    ((lsρ reduceTableSym + BitVec.ofNat 64 (2 * idx.toNat)) ↦₁₆ᵣ
      reduce.reduceByteEntry idx) ∗
    reduceTablePlacedFrame (2 * idx.toNat) ⊢
      reduceTablePlacedAt := by
  rw [reduceTablePlacedAt_focus16 idx]
  exact Entails.refl _

/-- Relocatable specification of `spqr::encoding::gf::unaccelerated::mul` (Block `384`). -/
def unacceleratedMulPlacedSpec [LibsignalPlacement] : Spec (BitVec 16 × BitVec 16) where
  pre := fun (a, b_arg) s =>
    ⌜BitVec.truncate 16 (s.readReg64 .x0) = a ∧
      BitVec.truncate 16 (s.readReg64 .x1) = b_arg⌝ ∗
      reduceTablePlacedAt
  post := fun (a, b_arg) s0 sf =>
    ⌜BitVec.truncate 16 (sf.readReg64 .x0) = unaccelerated.mul a b_arg ∧
      sf.trace = s0.trace⌝ ∗
      reduceTablePlacedAt

/-- Relocatable `spqr::encoding::gf::unaccelerated::mul` (Block `384`) meets
`unacceleratedMulPlacedSpec` under `[LibsignalPlacement]`. -/
theorem unacceleratedMul_placed_ok [LibsignalPlacement] (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_384).rebase (blkPl_384).base H) (blkPl_384).base
      unacceleratedMulPlacedSpec := by
  simp only [unacceleratedMulPlacedSpec]
  wp_init ab s0
  wp_steps 52
  rw [polyMul_asm_eq]
  wp_steps 1
  wp_conv_pre =>
    rw [reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2)]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx1_eq (unaccelerated.polyMul ab.1 ab.2),
        ← reduceTablePlacedAt_focus16 (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24)),
        reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16)),
        uxtw1_idx2_eq]
  wp_steps 3
  wp_conv_pre =>
    rw [← uxtw1_idx2_eq,
        ← reduceTablePlacedAt_focus16
          (BitVec.truncate 8
            ((unaccelerated.polyMul ab.1 ab.2 ^^^
                BitVec.zeroExtend 32
                    (reduce.reduceByteEntry (BitVec.truncate 8 (unaccelerated.polyMul ab.1 ab.2 >>> 24))) <<<
                  8) >>>
              16))]
  wp_done

end CryptoVerification.SpqrV1.GF.UnacceleratedMul
