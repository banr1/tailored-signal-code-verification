/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common

/-!
# AArch64 Decoder-Encoder Round-Trip: Part 3

Proves per-branch decoder soundness (`branch_*_sound`) for 1-, 2-, and 3-source data processing
(`dataProc1`, `dataProc2`, `dataProc3`), scalar loads and stores (`loadStorePair`,
`loadStoreUImm`, `loadStore24`, `ldrLit`, `ldarStlr`, `ldxr`, `stxr`), and system and barrier
instructions (`sysReg`, `barrier`).
-/

@[expose] public section

namespace Arm64

theorem packDataProc1_eq (w : BitVec 32) (h : ((w &&& 0x7fff0000#32) == 0x5ac00000#32) = true) :
    packDataProc1 (w.getLsbD 31) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packDataProc1]; bv_robdd

theorem packDataProc2_eq (w : BitVec 32) (h : ((w &&& 0x7fe00000#32) == 0x1ac00000#32) = true) :
    packDataProc2 (w.getLsbD 31) (w.extractLsb' 16 5) (w.extractLsb' 10 6)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packDataProc2]; bv_robdd

theorem packDataProc3_eq (w : BitVec 32) (h : ((w &&& 0x7f000000#32) == 0x1b000000#32) = true) :
    packDataProc3 (w.getLsbD 31) (w.extractLsb' 21 3) (w.extractLsb' 16 5) (w.getLsbD 15)
      (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packDataProc3]; bv_robdd

theorem packLoadStorePair_eq (w : BitVec 32) (h : ((w &&& 0x3e000000#32) == 0x28000000#32) = true) :
    packLoadStorePair (w.extractLsb' 30 2) (w.extractLsb' 23 2) (w.getLsbD 22)
      (w.extractLsb' 15 7) (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLoadStorePair]; bv_robdd

theorem packLoadStoreUImm_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x39000000#32) = true) :
    packLoadStoreUImm (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 10 12)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLoadStoreUImm]; bv_robdd

theorem packLoadStoreSimm9_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x38000000#32) = true)
    (h21 : w.getLsbD 21 = false) :
    packLoadStoreSimm9 (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 10 2)
      (w.extractLsb' 12 9) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLoadStoreSimm9]; bv_robdd

theorem packLoadStoreRegOff_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x38000000#32) = true)
    (h21 : w.getLsbD 21 = true) (h10 : w.extractLsb' 10 2 = 2#2) :
    packLoadStoreRegOff (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 13 3) (w.getLsbD 12) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLoadStoreRegOff]; bv_robdd

theorem packLdrLit_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x18000000#32) = true) :
    packLdrLit (w.extractLsb' 30 2) (w.extractLsb' 5 19) (w.extractLsb' 0 5) = w := by
  dsimp [packLdrLit]; bv_robdd

theorem packLdarStlr_eq (w : BitVec 32) (h : ((w &&& 0x3fbffc00#32) == 0x089ffc00#32) = true) :
    packLdarStlr (w.extractLsb' 30 2) (w.getLsbD 22) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLdarStlr]; bv_robdd

theorem packLdxr_eq (w : BitVec 32) (h : ((w &&& 0x3fff7c00#32) == 0x085f7c00#32) = true) :
    packLdxr (w.extractLsb' 30 2) (w.getLsbD 15) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLdxr]; bv_robdd

theorem packStxr_eq (w : BitVec 32) (h : ((w &&& 0x3fe07c00#32) == 0x08007c00#32) = true) :
    packStxr (w.extractLsb' 30 2) (w.getLsbD 15) (w.extractLsb' 16 5) (w.extractLsb' 5 5)
      (w.extractLsb' 0 5) = w := by
  dsimp [packStxr]; bv_robdd

theorem packSysReg_eq (w : BitVec 32) (h : ((w &&& 0xffd00000#32) == 0xd5100000#32) = true) :
    packSysReg (w.getLsbD 21) (w.extractLsb' 5 15) (w.extractLsb' 0 5) = w := by
  dsimp [packSysReg]; bv_robdd

theorem packBarrier_eq (w : BitVec 32) (h : ((w &&& 0xfffff01f#32) == 0xd503301f#32) = true) :
    packBarrier (w.extractLsb' 8 4) (w.extractLsb' 5 3) = w := by
  dsimp [packBarrier]; bv_robdd

attribute [-simp] BitVec.getLsbD_eq_getElem

theorem dataProc1_cases (b : BitVec 6) :
    b = 0#6 ∨ b = 1#6 ∨ b = 2#6 ∨ b = 3#6 ∨ b = 4#6 ∨ b = 5#6 ∨
    (b.toNat ≠ 0 ∧ b.toNat ≠ 1 ∧ b.toNat ≠ 2 ∧ b.toNat ≠ 3 ∧ b.toNat ≠ 4 ∧ b.toNat ≠ 5) := by
  revert b; apply forall_bitvec; decide

theorem branch_dataProc1_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7fff0000#32) == 0x5ac00000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let opcode := (w.extractLsb' 10 6).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           match opcode with
           | 0 => some (.dataProc1 width .RBIT rd rn)
           | 1 => some (.dataProc1 width .REV16 rd rn)
           | 2 =>
             if sf then some (.dataProc1 .W64 .REV32 rd rn)
             else some (.dataProc1 .W32 .REV rd rn)
           | 3 =>
             if sf then some (.dataProc1 .W64 .REV rd rn)
             else none
           | 4 => some (.dataProc1 width .CLZ rd rn)
           | 5 => some (.dataProc1 width .CLS rd rn)
           | _ => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packDataProc1_eq w hc
  rcases dataProc1_cases (w.extractLsb' 10 6) with
    h | h | h | h | h | h | ⟨h0, h1, h2, h3, h4, h5⟩
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc1Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc1Op.toBits]; simp [hpack]
  · rw [h] at hb hpack
    cases hsf : w.getLsbD 31 <;> (rw [hsf] at hb hpack; cases hb; dsimp [encode, DataProc1Op.toBits]; simp [hpack])
  · rw [h] at hb hpack
    cases hsf : w.getLsbD 31 <;> (rw [hsf] at hb hpack; cases hb <;> (dsimp [encode, DataProc1Op.toBits]; simp [hpack]))
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc1Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc1Op.toBits]; simp [hpack]
  · split at hb <;> simp_all

theorem dataProc2_cases (b : BitVec 6) :
    b = 2#6 ∨ b = 3#6 ∨ b = 8#6 ∨ b = 9#6 ∨ b = 10#6 ∨ b = 11#6 ∨
    (b.toNat ≠ 2 ∧ b.toNat ≠ 3 ∧ b.toNat ≠ 8 ∧ b.toNat ≠ 9 ∧ b.toNat ≠ 10 ∧ b.toNat ≠ 11) := by
  revert b; apply forall_bitvec; decide

theorem branch_dataProc2_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7fe00000#32) == 0x1ac00000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let opcode := (w.extractLsb' 10 6).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           match opcode with
           | 2  => some (.dataProc2 width .UDIV rd rn rm)
           | 3  => some (.dataProc2 width .SDIV rd rn rm)
           | 8  => some (.dataProc2 width .LSLV rd rn rm)
           | 9  => some (.dataProc2 width .LSRV rd rn rm)
           | 10 => some (.dataProc2 width .ASRV rd rn rm)
           | 11 => some (.dataProc2 width .RORV rd rn rm)
           | _  => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packDataProc2_eq w hc
  rcases dataProc2_cases (w.extractLsb' 10 6) with
    h | h | h | h | h | h | ⟨h2, h3, h8, h9, h10, h11⟩
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · rw [h] at hb hpack; cases hb; dsimp [encode, DataProc2Op.toBits]; simp [hpack]
  · split at hb <;> simp_all

set_option maxHeartbeats 1200000 in
theorem branch_dataProc3_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7f000000#32) == 0x1b000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op31 := (w.extractLsb' 21 3).toNat
           let o0 := w.getLsbD 15
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let raBits := w.extractLsb' 10 5
           let ra := Reg.fromZRBits raBits
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           match sf, op31, o0 with
           | _, 0, false    => some (.dataProc3 width .MADD rd rn rm ra)
           | _, 0, true     => some (.dataProc3 width .MSUB rd rn rm ra)
           | true, 1, false => some (.dataProc3 .W64 .SMADDL rd rn rm ra)
           | true, 1, true  => some (.dataProc3 .W64 .SMSUBL rd rn rm ra)
           | true, 2, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .SMULH rd rn rm .xzr) else none
           | true, 5, false => some (.dataProc3 .W64 .UMADDL rd rn rm ra)
           | true, 5, true  => some (.dataProc3 .W64 .UMSUBL rd rn rm ra)
           | true, 6, false => if raBits == 0b11111#5 then some (.dataProc3 .W64 .UMULH rd rn rm .xzr) else none
           | _, _, _        => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packDataProc3_eq w hc
  cases hsf : w.getLsbD 31 <;>
    rcases bitvec3_cases (w.extractLsb' 21 3) with hop31 | hop31 | hop31 | hop31 | hop31 | hop31 | hop31 | hop31 <;>
    cases ho0 : w.getLsbD 15 <;>
    cases hra : (w.extractLsb' 10 5 == 31#5) <;>
    (rw [hsf, hop31, ho0] at hb hpack;
     try rw [hra] at hb;
     cases hb <;>
     (dsimp [encode];
      first | (simp +decide [hpack]; done) | (try (rw [eq_of_beq hra] at hpack); simp +decide [hpack])))

set_option maxHeartbeats 800000 in
theorem branch_loadStorePair_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3e000000#32) == 0x28000000#32) = true)
    (hb : (let opc := (w.extractLsb' 30 2).toNat
           let modeBits := (w.extractLsb' 23 2).toNat
           let isLoad := w.getLsbD 22
           let imm7 : BitVec 7 := w.extractLsb' 15 7
           let rt2Bits := w.extractLsb' 10 5
           let rnBits := w.extractLsb' 5 5
           let rt1Bits := w.extractLsb' 0 5
           let scale : Nat := if opc == 2 then 3 else 2
           let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
           let rn := Reg.fromSPBits rnBits
           let rt1 := Reg.fromZRBits rt1Bits
           let rt2 := Reg.fromZRBits rt2Bits
           let addr? : Option AddrMode :=
             match modeBits with
             | 1 => some (.PostIndex rn offset)
             | 2 => some (.Offset rn offset)
             | 3 => some (.PreIndex rn offset)
             | _ => none
           let wbOverlap := (modeBits == 1 || modeBits == 3) && rnBits != 31#5 && (rt1Bits == rnBits || rt2Bits == rnBits)
           let loadPairOverlap := isLoad && rt1Bits == rt2Bits
           match addr? with
           | none => none
           | some addr =>
             if wbOverlap || loadPairOverlap then
               none
             else
               match opc, isLoad with
               | 0, true  => some (.ldp .W32 false rt1 rt2 addr)
               | 0, false => some (.stp .W32 rt1 rt2 addr)
               | 1, true  => some (.ldp .W64 true  rt1 rt2 addr)
               | 2, true  => some (.ldp .W64 false rt1 rt2 addr)
               | 2, false => some (.stp .W64 rt1 rt2 addr)
               | _, _     => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLoadStorePair_eq w hc
  rcases bitvec2_cases (w.extractLsb' 23 2) with hmode | hmode | hmode | hmode
  · rw [hmode] at hb; cases hb
  all_goals
    cases hover : (((w.extractLsb' 23 2).toNat == 1 || (w.extractLsb' 23 2).toNat == 3) &&
        w.extractLsb' 5 5 != 31#5 &&
        (w.extractLsb' 0 5 == w.extractLsb' 5 5 || w.extractLsb' 10 5 == w.extractLsb' 5 5) ||
      (w.getLsbD 22 && w.extractLsb' 0 5 == w.extractLsb' 10 5)) <;>
    rcases bitvec2_cases (w.extractLsb' 30 2) with hopc | hopc | hopc | hopc <;>
    cases hload : w.getLsbD 22 <;>
    (rw [hover] at hb;
     rw [hopc, hmode, hload] at hb hpack;
     rw [hmode, hload] at hover;
     cases hb <;>
     (dsimp [encode, encodeLoadStorePair]; simp_all; try grind))

set_option maxHeartbeats 800000 in
theorem branch_loadStoreUImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x39000000#32) = true)
    (hb : (let sizeBits := (w.extractLsb' 30 2).toNat
           let opc := (w.extractLsb' 22 2).toNat
           let imm12 : BitVec 12 := w.extractLsb' 10 12
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           let offset : BitVec 64 := (imm12.zeroExtend 64) <<< sizeBits
           mkLoadStoreInst sizeBits opc rt (.Offset rn offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLoadStoreUImm_eq w hc
  rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
    rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
    (rw [hsz, hopc] at hb hpack;
     dsimp [mkLoadStoreInst] at hb;
     cases hb <;>
     (dsimp [encode, encodeLoadStore, MemWidth.toBits]; simp [hpack]))

set_option maxHeartbeats 2000000 in
theorem branch_loadStore24_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x38000000#32) = true)
    (hb : (let sizeBits := (w.extractLsb' 30 2).toNat
           let opc := (w.extractLsb' 22 2).toNat
           let rnBits := w.extractLsb' 5 5
           let rtBits := w.extractLsb' 0 5
           let rn := Reg.fromSPBits rnBits
           let rt := Reg.fromZRBits rtBits
           if !(w.getLsbD 21) then
             let imm9 : BitVec 9 := w.extractLsb' 12 9
             let offset : BitVec 64 := imm9.signExtend 64
             let mode2 := (w.extractLsb' 10 2).toNat
             let wbOverlap := (mode2 == 1 || mode2 == 3) && rnBits != 31#5 && rtBits == rnBits
             if wbOverlap then
               none
             else
               match mode2 with
               | 0 => mkLoadStoreInst sizeBits opc rt (.UnscaledOffset rn offset)
               | 1 => mkLoadStoreInst sizeBits opc rt (.PostIndex rn offset)
               | 3 => mkLoadStoreInst sizeBits opc rt (.PreIndex rn offset)
               | _ => none
           else if (w.extractLsb' 10 2) == 2#2 then
             let rm := Reg.fromZRBits (w.extractLsb' 16 5)
             let extBits := w.extractLsb' 13 3
             let ext := ExtendType.ofBits extBits
             let sBit := w.getLsbD 12
             if !extBits.getLsbD 1 || (sizeBits == 0 && sBit) then
               none
             else
               let amount := if sBit then sizeBits else 0
               mkLoadStoreInst sizeBits opc rt (.RegOffset rn rm ext amount)
           else
             none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  cases h21 : w.getLsbD 21
  · have hpack := packLoadStoreSimm9_eq w hc h21
    rcases bitvec2_cases (w.extractLsb' 10 2) with hmode | hmode | hmode | hmode
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        (rw [h21, hmode, hsz, hopc] at hb;
         dsimp [mkLoadStoreInst] at hb;
         cases hb <;>
         (rw [hmode, hsz, hopc] at hpack; dsimp [encode, encodeLoadStore, MemWidth.toBits]; simp [hpack]))
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        cases hwb : (((w.extractLsb' 10 2).toNat == 1 || (w.extractLsb' 10 2).toNat == 3) &&
          w.extractLsb' 5 5 != 31#5 && w.extractLsb' 0 5 == w.extractLsb' 5 5) <;>
        (rw [hwb, h21, hmode, hsz, hopc] at hb;
         rw [hmode] at hwb;
         dsimp [mkLoadStoreInst] at hb;
         cases hb <;>
         (rw [hmode, hsz, hopc] at hpack; dsimp [encode, encodeLoadStore, MemWidth.toBits]; simp_all; try grind))
    · simp [h21, hmode] at hb
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        cases hwb : (((w.extractLsb' 10 2).toNat == 1 || (w.extractLsb' 10 2).toNat == 3) &&
          w.extractLsb' 5 5 != 31#5 && w.extractLsb' 0 5 == w.extractLsb' 5 5) <;>
        (rw [hwb, h21, hmode, hsz, hopc] at hb;
         rw [hmode] at hwb;
         dsimp [mkLoadStoreInst] at hb;
         cases hb <;>
         (rw [hmode, hsz, hopc] at hpack; dsimp [encode, encodeLoadStore, MemWidth.toBits]; simp_all; try grind))
  · rcases bitvec2_cases (w.extractLsb' 10 2) with hmode | hmode | hmode | hmode
    · rw [h21, hmode] at hb; cases hb
    · rw [h21, hmode] at hb; cases hb
    · have hpack := packLoadStoreRegOff_eq w hc h21 hmode
      rcases bitvec3_cases (w.extractLsb' 13 3) with hext | hext | hext | hext | hext | hext | hext | hext <;>
        rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        cases hs : w.getLsbD 12 <;>
        (rw [h21, hmode, hext, hsz, hopc, hs] at hb;
         dsimp [mkLoadStoreInst] at hb;
         cases hb <;>
         (rw [hext, hsz, hopc, hs] at hpack;
          dsimp [encode, encodeLoadStore, MemWidth.toBits, ExtendType.ofBits, ExtendType.toBits];
          simp [hpack]))
    · rw [h21, hmode] at hb; cases hb

theorem branch_ldrLit_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x18000000#32) = true)
    (hb : (let opc := (w.extractLsb' 30 2).toNat
           let imm19 : BitVec 19 := w.extractLsb' 5 19
           let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           match opc with
           | 0 => some (.ldrLit .W32 false rt offset)
           | 1 => some (.ldrLit .W64 false rt offset)
           | 2 => some (.ldrLit .W64 true  rt offset)
           | _ => some (.prfmLit (w.extractLsb' 0 5) offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLdrLit_eq w hc
  rcases bitvec2_cases (w.extractLsb' 30 2) with hopc | hopc | hopc | hopc <;>
    (rw [hopc] at hb hpack;
     cases hb <;> (dsimp [encode, encodeLdrLit]; simp [hpack]))

theorem branch_ldarStlr_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fbffc00#32) == 0x089ffc00#32) = true)
    (hb : (let sz := MemWidth.ofBits (w.extractLsb' 30 2)
           let isLoad := w.getLsbD 22
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.ldarStlr sz isLoad rn rt)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packLdarStlr_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_ldxr_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fff7c00#32) == 0x085f7c00#32) = true)
    (hb : (let sz := MemWidth.ofBits (w.extractLsb' 30 2)
           let acq := w.getLsbD 15
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.ldxr sz acq rn rt)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packLdxr_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_stxr_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fe07c00#32) == 0x08007c00#32) = true)
    (hb : (let rsBits := w.extractLsb' 16 5
           let rnBits := w.extractLsb' 5 5
           let rtBits := w.extractLsb' 0 5
           if rsBits == rtBits || (rsBits == rnBits && rnBits != 31#5) then
             none
           else
             let sz := MemWidth.ofBits (w.extractLsb' 30 2)
             let rel := w.getLsbD 15
             let rs := Reg.fromZRBits rsBits
             let rn := Reg.fromSPBits rnBits
             let rt := Reg.fromZRBits rtBits
             some (.stxr sz rel rs rn rt)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · cases hb
  · cases hb
    have hpack := packStxr_eq w hc
    dsimp [encode]
    simp [hpack]

theorem branch_sysReg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffd00000#32) == 0xd5100000#32) = true)
    (hb : (let isRead := w.getLsbD 21
           let sysreg : BitVec 15 := w.extractLsb' 5 15
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.sysReg isRead sysreg rt)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packSysReg_eq w hc
  dsimp [encode]
  simp [hpack]

theorem branch_barrier_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xfffff01f#32) == 0xd503301f#32) = true)
    (hb : (let crm : BitVec 4 := w.extractLsb' 8 4
           let op2 : BitVec 3 := w.extractLsb' 5 3
           if op2 == 2#3 || op2 == 4#3 || op2 == 5#3 || op2 == 6#3 then
             some (.barrier crm op2)
           else
             none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb <;> cases hb
  dsimp [encode]
  simp_all [packBarrier_eq w hc]

end Arm64
