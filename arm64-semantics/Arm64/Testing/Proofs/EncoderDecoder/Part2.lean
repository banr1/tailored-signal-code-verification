/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common

/-!
# ARM64 Decoder-Encoder Round-Trip, Part 2

Packing identities (`pack*_eq`) and per-branch decoder soundness lemmas (`branch_*_sound`) for
branch (`b`, `cbz`, `tbz`, `bCond`, `br`) and register or conditional data-processing
(`logicalReg`, `addSubReg`, `addSubExt`, `addSubCarry`, `condCompare`, `condSelect`) encodings.
-/

@[expose] public section

namespace Arm64

theorem packB_eq (w : BitVec 32) (h : ((w &&& 0x7c000000#32) == 0x14000000#32) = true) :
    packB (w.getLsbD 31) (w.extractLsb' 0 26) = w := by
  dsimp [packB]; bv_robdd

theorem packCbz_eq (w : BitVec 32) (h : ((w &&& 0x7e000000#32) == 0x34000000#32) = true) :
    packCbz (w.getLsbD 31) (w.getLsbD 24) (w.extractLsb' 5 19) (w.extractLsb' 0 5) = w := by
  dsimp [packCbz]; bv_robdd

theorem packTbz_eq (w : BitVec 32) (h : ((w &&& 0x7e000000#32) == 0x36000000#32) = true) :
    packTbz (w.getLsbD 31) (w.getLsbD 24) (w.extractLsb' 19 5) (w.extractLsb' 5 14) (w.extractLsb' 0 5) = w := by
  dsimp [packTbz]; bv_robdd

theorem packBCond_eq (w : BitVec 32) (h : ((w &&& 0xff000010#32) == 0x54000000#32) = true) :
    packBCond (w.extractLsb' 5 19) (w.extractLsb' 0 4) = w := by
  dsimp [packBCond]; bv_robdd

theorem packBr_eq (w : BitVec 32) (h : ((w &&& 0xff9ffc1f#32) == 0xd61f0000#32) = true) :
    packBr (w.extractLsb' 21 2) (w.extractLsb' 5 5) = w := by
  dsimp [packBr]; bv_robdd

theorem packLogicalReg_eq (w : BitVec 32) (h : ((w &&& 0x1f000000#32) == 0x0a000000#32) = true) :
    packLogicalReg (w.getLsbD 31) (w.extractLsb' 29 2) (w.extractLsb' 22 2) (w.getLsbD 21)
      (w.extractLsb' 16 5) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLogicalReg]; bv_robdd

theorem packAddSubReg_eq (w : BitVec 32) (h : ((w &&& 0x1f200000#32) == 0x0b000000#32) = true) :
    packAddSubReg (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
      (w.extractLsb' 16 5) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packAddSubReg]; bv_robdd

theorem packAddSubExt_eq (w : BitVec 32) (h : ((w &&& 0x1fe00000#32) == 0x0b200000#32) = true) :
    packAddSubExt (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 16 5)
      (w.extractLsb' 13 3) (w.extractLsb' 10 3) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packAddSubExt]; bv_robdd

theorem packAddSubCarry_eq (w : BitVec 32) (h : ((w &&& 0x1fe0fc00#32) == 0x1a000000#32) = true) :
    packAddSubCarry (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 29)
      (w.extractLsb' 16 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packAddSubCarry]; bv_robdd

theorem packCondCompare_eq (w : BitVec 32) (h : ((w &&& 0x3fe00410#32) == 0x3a400000#32) = true) :
    packCondCompare (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 11) (w.extractLsb' 16 5)
      (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.extractLsb' 0 4) = w := by
  dsimp [packCondCompare]; bv_robdd

theorem packCondSelect_eq (w : BitVec 32) (h : ((w &&& 0x3fe00800#32) == 0x1a800000#32) = true) :
    packCondSelect (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 10) (w.extractLsb' 16 5)
      (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packCondSelect]; bv_robdd

attribute [-simp] BitVec.getLsbD_eq_getElem

theorem branch_b_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7c000000#32) == 0x14000000#32) = true)
    (hb : (let isBl := w.getLsbD 31
           let imm26 : BitVec 26 := w.extractLsb' 0 26
           let offset : BitVec 64 := (imm26.signExtend 64) <<< 2
           if isBl then
             some (.bl offset)
           else
             some (.b offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packB_eq w hc
  cases hl : w.getLsbD 31 <;> (rw [hl] at hb hpack; cases hb; dsimp [encode]; simp [hpack])

theorem branch_cbz_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7e000000#32) == 0x34000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let isNonZero := w.getLsbD 24
           let imm19 : BitVec 19 := w.extractLsb' 5 19
           let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.cbz width isNonZero rt offset)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packCbz_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_tbz_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7e000000#32) == 0x36000000#32) = true)
    (hb : (let b5 := w.getLsbD 31
           let isNonZero := w.getLsbD 24
           let b40 := (w.extractLsb' 19 5).toNat
           let bitPos := (if b5 then 32 else 0) + b40
           let imm14 : BitVec 14 := w.extractLsb' 5 14
           let offset : BitVec 64 := (imm14.signExtend 64) <<< 2
           let tbzW : RegWidth := if b5 then .W64 else .W32
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.tbz tbzW isNonZero rt bitPos offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packTbz_eq w hc
  have hlt := tbz_bitPos_lt_64 (w.getLsbD 31) (w.extractLsb' 19 5)
  have hge := tbz_bitPos_ge_32 (w.getLsbD 31) (w.extractLsb' 19 5)
  have hmod := tbz_bitPos_mod_32 (w.getLsbD 31) (w.extractLsb' 19 5)
  simp at hlt hge hmod
  cases hb
  dsimp [encode]
  simp [hlt, hge, hmod, hpack]

theorem branch_bCond_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff000010#32) == 0x54000000#32) = true)
    (hb : (let imm19 : BitVec 19 := w.extractLsb' 5 19
           let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
           let cond := CondCode.ofBits (w.extractLsb' 0 4)
           some (.bCond cond offset)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packBCond_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_br_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff9ffc1f#32) == 0xd61f0000#32) = true)
    (hb : (let opc := (w.extractLsb' 21 2).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           match opc with
           | 0 => some (.br rn)
           | 1 => some (.blr rn)
           | 2 => some (.ret rn)
           | _ => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packBr_eq w hc
  rcases bitvec2_cases (w.extractLsb' 21 2) with hopc | hopc | hopc | hopc <;>
    (rw [hopc] at hb hpack;
     cases hb <;> (dsimp [encode]; simp [hpack]))

theorem branch_logicalReg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f000000#32) == 0x0a000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let opc := w.extractLsb' 29 2
           let shift := ShiftType.ofBits (w.extractLsb' 22 2)
           let nBit := w.getLsbD 21
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let imm6 := (w.extractLsb' 10 6).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           if !sf && imm6 >= 32 then
             none
           else
             some (.logicalShift width (LogicalOp.ofBits opc nBit) rd rn rm shift imm6)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLogicalReg_eq w hc
  have h_lt64 : (w.extractLsb' 10 6).toNat < 64 := (w.extractLsb' 10 6).isLt
  simp at h_lt64
  cases hsf : w.getLsbD 31
  · cases h32 : decide ((w.extractLsb' 10 6).toNat ≥ 32) <;>
      (rw [hsf, h32] at hb;
       cases hb <;>
         (rw [hsf] at hpack;
          rw [decide_eq_false_iff_not, Nat.not_le] at h32;
          simp at h32;
          dsimp [encode, RegWidth.ofBool];
          simp [h32, hpack]))
  · rw [hsf] at hb hpack
    cases hb
    dsimp [encode, RegWidth.ofBool]
    simp [h_lt64, hpack]

theorem branch_addSubReg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f200000#32) == 0x0b000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
           let shiftBits := w.extractLsb' 22 2
           if shiftBits == 3#2 then
             none
           else
             let shift := ShiftType.ofBits shiftBits
             let rm := Reg.fromZRBits (w.extractLsb' 16 5)
             let imm6 := (w.extractLsb' 10 6).toNat
             let rn := Reg.fromZRBits (w.extractLsb' 5 5)
             let rd := Reg.fromZRBits (w.extractLsb' 0 5)
             if !sf && imm6 >= 32 then
               none
             else
               some (.addSubShift width op rd rn rm shift imm6)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packAddSubReg_eq w hc
  have h_lt64 : (w.extractLsb' 10 6).toNat < 64 := (w.extractLsb' 10 6).isLt
  simp at h_lt64
  cases hsf : w.getLsbD 31
  · rcases bitvec2_cases (w.extractLsb' 22 2) with hsh | hsh | hsh | hsh <;>
      cases h32 : decide ((w.extractLsb' 10 6).toNat ≥ 32) <;>
      (rw [hsh, hsf, h32] at hb;
       cases hb <;>
         (rw [hsh, hsf] at hpack;
          rw [decide_eq_false_iff_not, Nat.not_le] at h32;
          simp at h32;
          dsimp [encode, RegWidth.ofBool, ShiftType.ofBits, ShiftType.toBits];
          simp [h32, hpack]))
  · rcases bitvec2_cases (w.extractLsb' 22 2) with hsh | hsh | hsh | hsh <;>
      (rw [hsh, hsf] at hb hpack;
       cases hb <;>
         (dsimp [encode, RegWidth.ofBool, ShiftType.ofBits, ShiftType.toBits];
          simp [h_lt64, hpack]))

theorem branch_addSubExt_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1fe00000#32) == 0x0b200000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let optBits := w.extractLsb' 13 3
           let imm3 := (w.extractLsb' 10 3).toNat
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rdBits := w.extractLsb' 0 5
           if imm3 > 4 then
             none
           else
             let ext := ExtendType.ofBits optBits
             let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
             some (.addSubExt width op rd rn rm ext imm3)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packAddSubExt_eq w hc
  rcases bitvec3_cases (w.extractLsb' 10 3) with himm3 | himm3 | himm3 | himm3 | himm3 | himm3 | himm3 | himm3 <;>
    (rw [himm3] at hb;
     cases hb <;>
       (rw [himm3] at hpack;
        cases h30 : w.getLsbD 30 <;> cases h29 : w.getLsbD 29 <;>
          (rw [h30, h29] at hpack;
           dsimp [encode, AddSubOp.ofBits, AddSubOp.setsFlags, AddSubOp.toBits];
           simp [hpack])))

theorem branch_addSubCarry_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1fe0fc00#32) == 0x1a000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.addSubCarry width op rd rn rm)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packAddSubCarry_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_condCompare_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fe00410#32) == 0x3a400000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let isSub := w.getLsbD 30
           let isImm := w.getLsbD 11
           let rmOrImm := w.extractLsb' 16 5
           let cond := CondCode.ofBits (w.extractLsb' 12 4)
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let nzcv := w.extractLsb' 0 4
           if isImm then
             some (.condCompareImm width isSub rn rmOrImm nzcv cond)
           else
             some (.condCompareReg width isSub rn (Reg.fromZRBits rmOrImm) nzcv cond)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packCondCompare_eq w hc
  cases hi : w.getLsbD 11 <;>
    (rw [hi] at hb hpack;
     cases hb;
     dsimp [encode];
     simp [hpack])

theorem branch_condSelect_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fe00800#32) == 0x1a800000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op := CondSelectOp.ofBits (w.getLsbD 30) (w.getLsbD 10)
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let cond := CondCode.ofBits (w.extractLsb' 12 4)
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.condSelect width op rd rn rm cond)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packCondSelect_eq w hc
  dsimp [encode]
  simp [hpack]

end Arm64
