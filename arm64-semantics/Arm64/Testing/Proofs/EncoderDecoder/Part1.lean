/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common

/-!
# ARM64 Decoder-Encoder Round-Trip: Bitmask and Immediate Classes

Proves `encodeBitMasks_of_decodeBitMasks` and per-branch decoder soundness (`branch_*_sound`)
for system (`nop`, `svc`, `brk`), PC-relative (`adr`), and immediate data-processing
(`addSubImm`, `logicalImm`, `moveWide`, `bitfield`, `extr`) instruction classes.
-/

@[expose] public section

namespace Arm64

/-! ## Bitmask Immediate Round-Trip -/

def decodeBitMasksElem (immN : Bool) (imms immr : BitVec 6) : BitVec 64 :=
  let levels := decodeBitMasksLevels immN imms
  let s : BitVec 6 := imms &&& levels
  let r : BitVec 6 := immr &&& levels
  let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
  let elemMask : BitVec 64 := (2#64 <<< levels.zeroExtend 64) - 1#64
  if r == 0#6 then elemOnes
  else
    let shlAmt : BitVec 6 := (levels - r) + 1#6
    ((elemOnes >>> r.zeroExtend 64) ||| (elemOnes <<< shlAmt.zeroExtend 64)) &&& elemMask

theorem encodeBitMasksLevels_val_false (imms immr : BitVec 6)
    (h : decodeBitMasksValid false imms immr = true) :
    encodeBitMasksLevels (decodeBitMasksVal false imms immr) = decodeBitMasksLevels false imms := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem encodeBitMasksLevels_val_true (imms immr : BitVec 6)
    (h : decodeBitMasksValid true imms immr = true) :
    encodeBitMasksLevels (decodeBitMasksVal true imms immr) = decodeBitMasksLevels true imms := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem encodeBitMasksLevels_val (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    encodeBitMasksLevels (decodeBitMasksVal immN imms immr) = decodeBitMasksLevels immN imms := by
  cases immN
  · exact encodeBitMasksLevels_val_false imms immr h
  · exact encodeBitMasksLevels_val_true imms immr h

theorem decodeBitMasksVal_and_elemMask (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    (decodeBitMasksVal immN imms immr) &&& ((2#64 <<< (decodeBitMasksLevels immN imms).zeroExtend 64) - 1#64) =
      decodeBitMasksElem immN imms immr := by
  cases immN <;> (revert h imms immr; apply forall_bitvec6_2; decide)

theorem popcount64_decodeBitMasksElem_false (imms immr : BitVec 6)
    (h : decodeBitMasksValid false imms immr = true) :
    popcount64 (decodeBitMasksElem false imms immr) = (imms &&& decodeBitMasksLevels false imms) + 1#6 := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem popcount64_decodeBitMasksElem_true (imms immr : BitVec 6)
    (h : decodeBitMasksValid true imms immr = true) :
    popcount64 (decodeBitMasksElem true imms immr) = (imms &&& decodeBitMasksLevels true imms) + 1#6 := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem popcount64_decodeBitMasksElem (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    popcount64 (decodeBitMasksElem immN imms immr) = (imms &&& decodeBitMasksLevels immN imms) + 1#6 := by
  cases immN
  · exact popcount64_decodeBitMasksElem_false imms immr h
  · exact popcount64_decodeBitMasksElem_true imms immr h

theorem ctz64_decodeBitMasksElem_false (imms immr : BitVec 6)
    (h : decodeBitMasksValid false imms immr = true) :
    (let levels := decodeBitMasksLevels false imms
     let elem := decodeBitMasksElem false imms immr
     let onesCount : BitVec 6 := (imms &&& levels) + 1#6
     let s : BitVec 6 := onesCount - 1#6
     let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
     let r : BitVec 6 :=
       if elem == elemOnes then 0#6
       else if !(elem.getLsbD 0) then (levels + 1#6) - ctz64 elem
       else onesCount - ctz64 (~~~elem)
     r &&& levels) = immr := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem ctz64_decodeBitMasksElem_true (imms immr : BitVec 6)
    (h : decodeBitMasksValid true imms immr = true) :
    (let levels := decodeBitMasksLevels true imms
     let elem := decodeBitMasksElem true imms immr
     let onesCount : BitVec 6 := (imms &&& levels) + 1#6
     let s : BitVec 6 := onesCount - 1#6
     let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
     let r : BitVec 6 :=
       if elem == elemOnes then 0#6
       else if !(elem.getLsbD 0) then (levels + 1#6) - ctz64 elem
       else onesCount - ctz64 (~~~elem)
     r &&& levels) = immr := by
  revert h imms immr; apply forall_bitvec6_2; decide

theorem ctz64_decodeBitMasksElem (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    (let levels := decodeBitMasksLevels immN imms
     let elem := decodeBitMasksElem immN imms immr
     let onesCount : BitVec 6 := (imms &&& levels) + 1#6
     let s : BitVec 6 := onesCount - 1#6
     let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
     let r : BitVec 6 :=
       if elem == elemOnes then 0#6
       else if !(elem.getLsbD 0) then (levels + 1#6) - ctz64 elem
       else onesCount - ctz64 (~~~elem)
     r &&& levels) = immr := by
  cases immN
  · exact ctz64_decodeBitMasksElem_false imms immr h
  · exact ctz64_decodeBitMasksElem_true imms immr h

theorem encodeBitMasksImmN_val (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    encodeBitMasksImmN (decodeBitMasksVal immN imms immr) = immN := by
  unfold encodeBitMasksImmN
  rw [encodeBitMasksLevels_val immN imms immr h]
  cases immN
  · clear h; revert imms; apply forall_bitvec; decide
  · rfl

theorem encodeBitMasksImms_val (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    encodeBitMasksImms (decodeBitMasksVal immN imms immr) = imms := by
  unfold encodeBitMasksImms
  dsimp only []
  rw [encodeBitMasksLevels_val immN imms immr h, decodeBitMasksVal_and_elemMask immN imms immr h,
      popcount64_decodeBitMasksElem immN imms immr h]
  cases immN <;> (revert h imms immr; apply forall_bitvec6_2; decide)

theorem encodeBitMasksImmr_val (immN : Bool) (imms immr : BitVec 6)
    (h : decodeBitMasksValid immN imms immr = true) :
    encodeBitMasksImmr (decodeBitMasksVal immN imms immr) = immr := by
  unfold encodeBitMasksImmr
  dsimp only []
  rw [encodeBitMasksLevels_val immN imms immr h, decodeBitMasksVal_and_elemMask immN imms immr h,
      popcount64_decodeBitMasksElem immN imms immr h]
  exact ctz64_decodeBitMasksElem immN imms immr h

theorem encodeBitMasks_of_decodeBitMasks (sfBit immN : Bool) (imms immr : BitVec 6) (mask : BitVec 64)
    (h_sf : ((if sfBit then RegWidth.W64 else RegWidth.W32) == RegWidth.W32 && immN) = false)
    (h_dec : decodeBitMasks immN imms immr = some mask) :
    encodeBitMasks (if sfBit then RegWidth.W64 else RegWidth.W32) mask = some (immN, imms, immr) := by
  have h_dec' := h_dec
  dsimp [decodeBitMasks] at h_dec'
  cases hv : decodeBitMasksValid immN imms immr
  · simp [hv] at h_dec'
  · simp [hv] at h_dec'
    subst h_dec'
    have hN := encodeBitMasksImmN_val immN imms immr hv
    have hS := encodeBitMasksImms_val immN imms immr hv
    have hR := encodeBitMasksImmr_val immN imms immr hv
    simp [encodeBitMasks, hN, hS, hR, h_dec]
    intro h_sfBit
    subst h_sfBit
    exact Bool.and_eq_false_imp.mp h_sf rfl

/-! ## Bit-Packing and Per-Branch Soundness -/

theorem packSystem_false_eq (w : BitVec 32) (h : ((w &&& 0xffe0001f#32) == 0xd4000001#32) = true) :
    packSystem false (w.extractLsb' 5 16) = w := by
  dsimp [packSystem]; bv_robdd

theorem packSystem_true_eq (w : BitVec 32) (h : ((w &&& 0xffe0001f#32) == 0xd4200000#32) = true) :
    packSystem true (w.extractLsb' 5 16) = w := by
  dsimp [packSystem]; bv_robdd

theorem packAdr_eq (w : BitVec 32) (h : ((w &&& 0x1f000000#32) == 0x10000000#32) = true) :
    packAdr (w.getLsbD 31) (w.extractLsb' 29 2) (w.extractLsb' 5 19) (w.extractLsb' 0 5) = w := by
  dsimp [packAdr]; bv_robdd

theorem packAddSubImm_eq (w : BitVec 32) (h : ((w &&& 0x1f800000#32) == 0x11000000#32) = true) :
    packAddSubImm (w.getLsbD 31) (w.getLsbD 30) (w.getLsbD 29) (w.getLsbD 22)
      (w.extractLsb' 10 12) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packAddSubImm]; bv_robdd

theorem packLogicalImm_eq (w : BitVec 32) (h : ((w &&& 0x1f800000#32) == 0x12000000#32) = true) :
    packLogicalImm (w.getLsbD 31) (w.extractLsb' 29 2) (w.getLsbD 22)
      (w.extractLsb' 16 6) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLogicalImm]; bv_robdd

theorem packMoveWide_eq (w : BitVec 32) (h : ((w &&& 0x1f800000#32) == 0x12800000#32) = true) :
    packMoveWide (w.getLsbD 31) (w.extractLsb' 29 2) (w.extractLsb' 21 2)
      (w.extractLsb' 5 16) (w.extractLsb' 0 5) = w := by
  dsimp [packMoveWide]; bv_robdd

theorem packBitfield_eq (w : BitVec 32) (h : ((w &&& 0x1f800000#32) == 0x13000000#32) = true)
    (hn : w.getLsbD 22 = w.getLsbD 31) :
    packBitfield (w.getLsbD 31) (w.extractLsb' 29 2)
      (w.extractLsb' 16 6) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packBitfield]; bv_robdd

theorem packExtr_eq (w : BitVec 32) (h : ((w &&& 0x7f800000#32) == 0x13800000#32) = true)
    (hn : w.getLsbD 22 = w.getLsbD 31) (ho0 : w.getLsbD 21 = false) :
    packExtr (w.getLsbD 31) (w.extractLsb' 16 5) (w.extractLsb' 10 6)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packExtr]; bv_robdd

attribute [-simp] BitVec.getLsbD_eq_getElem

theorem branch_nop_sound (w : BitVec 32) (p : Instr)
    (hc : (w == 0xd503201f#32) = true)
    (hb : (some .nop : Option Instr) = some p) :
    encode p = some w := by
  cases hb
  rw [eq_of_beq hc]
  rfl

theorem branch_svc_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe0001f#32) == 0xd4000001#32) = true)
    (hb : (some (.system false (w.extractLsb' 5 16)) : Option Instr) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSystem_false_eq w hc]

theorem branch_brk_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe0001f#32) == 0xd4200000#32) = true)
    (hb : (some (.system true (w.extractLsb' 5 16)) : Option Instr) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSystem_true_eq w hc]

theorem branch_adr_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f000000#32) == 0x10000000#32) = true)
    (hb : (let page := w.getLsbD 31
           let immlo : BitVec 2 := w.extractLsb' 29 2
           let immhi : BitVec 19 := w.extractLsb' 5 19
           let imm21 : BitVec 21 := immhi ++ immlo
           let offset : BitVec 64 :=
             if page then (imm21.signExtend 64) <<< 12
             else imm21.signExtend 64
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           some (.adr page rd offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packAdr_eq w hc
  cases hp : w.getLsbD 31 <;> (rw [hp] at hb hpack; cases hb; dsimp [encode]; simp [hpack])

theorem branch_addSubImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f800000#32) == 0x11000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
           let sh := w.getLsbD 22
           let imm12 : BitVec 12 := w.extractLsb' 10 12
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rdBits := w.extractLsb' 0 5
           let rd := if op.setsFlags then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
           some (.addSubImm width op rd rn imm12 sh)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packAddSubImm_eq w hc
  cases h30 : w.getLsbD 30 <;>
    cases h29 : w.getLsbD 29 <;>
    (rw [h30, h29] at hb hpack;
     cases hb;
     dsimp [encode, AddSubOp.ofBits, AddSubOp.setsFlags, AddSubOp.toBits];
     simp [hpack])

theorem branch_logicalImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f800000#32) == 0x12000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let opc := w.extractLsb' 29 2
           let immN := w.getLsbD 22
           let immr : BitVec 6 := w.extractLsb' 16 6
           let imms : BitVec 6 := w.extractLsb' 10 6
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rdBits := w.extractLsb' 0 5
           if !sf && immN then
             none
           else
             match decodeBitMasks immN imms immr with
             | none => none
             | some mask =>
               let op := LogicalOp.ofBits opc false
               let rd := if opc == 3#2 then Reg.fromZRBits rdBits else Reg.fromSPBits rdBits
               some (.logicalImm width op rd rn mask)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  cases hsf : (!w.getLsbD 31 && w.getLsbD 22)
  · rw [hsf] at hb
    cases hmask : decodeBitMasks (w.getLsbD 22) (w.extractLsb' 10 6) (w.extractLsb' 16 6)
    · rw [hmask] at hb; cases hb
    · rename_i mask
      rw [hmask] at hb
      have h_sf : ((if w.getLsbD 31 then RegWidth.W64 else RegWidth.W32) == .W32 && w.getLsbD 22) = false := by
        cases h31 : w.getLsbD 31 <;> simp_all
      have henc := encodeBitMasks_of_decodeBitMasks (w.getLsbD 31) (w.getLsbD 22)
        (w.extractLsb' 10 6) (w.extractLsb' 16 6) mask h_sf hmask
      have hpack := packLogicalImm_eq w hc
      rcases bitvec2_cases (w.extractLsb' 29 2) with hopc | hopc | hopc | hopc <;>
        (rw [hopc] at hb hpack; cases hb;
         dsimp [encode, RegWidth.ofBool, LogicalOp.ofBits, LogicalOp.toBits]; simp [henc, hpack])
  · rw [hsf] at hb; cases hb

set_option maxHeartbeats 800000 in
theorem branch_moveWide_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f800000#32) == 0x12800000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let opc := (w.extractLsb' 29 2).toNat
           let hwBits := (w.extractLsb' 21 2).toNat
           let imm16 : BitVec 16 := w.extractLsb' 5 16
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           if !sf && hwBits >= 2 then
             none
           else
             let hw := hwBits * 16
             match opc with
             | 0 => some (.moveWide width .MOVN rd imm16 hw)
             | 2 => some (.moveWide width .MOVZ rd imm16 hw)
             | 3 => some (.moveWide width .MOVK rd imm16 hw)
             | _ => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packMoveWide_eq w hc
  rcases bitvec2_cases (w.extractLsb' 29 2) with hopc | hopc | hopc | hopc <;>
    rcases bitvec2_cases (w.extractLsb' 21 2) with hhw | hhw | hhw | hhw <;>
    cases hsf : w.getLsbD 31 <;>
    (rw [hopc, hhw, hsf] at hb hpack;
     cases hb <;>
     (dsimp [encode, RegWidth.ofBool, RegWidth.toBool, MoveWideOp.toBits]; simp [hpack]))

set_option maxHeartbeats 1200000 in
theorem branch_bitfield_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x1f800000#32) == 0x13000000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let opc := (w.extractLsb' 29 2).toNat
           let nBit := w.getLsbD 22
           let immr := (w.extractLsb' 16 6).toNat
           let imms := (w.extractLsb' 10 6).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           if sf != nBit then
             none
           else if !sf && (immr >= 32 || imms >= 32) then
             none
           else
             match opc with
             | 0 => some (.bitfield width .SBFM rd rn immr imms)
             | 1 => some (.bitfield width .BFM  rd rn immr imms)
             | 2 => some (.bitfield width .UBFM rd rn immr imms)
             | _ => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hr_lt64 : (w.extractLsb' 16 6).toNat < 64 := (w.extractLsb' 16 6).isLt
  have hs_lt64 : (w.extractLsb' 10 6).toNat < 64 := (w.extractLsb' 10 6).isLt
  simp at hr_lt64 hs_lt64
  cases hsf : w.getLsbD 31
  · rcases bitvec2_cases (w.extractLsb' 29 2) with hopc | hopc | hopc | hopc <;>
      cases hn : w.getLsbD 22 <;>
      cases hr32 : decide ((w.extractLsb' 16 6).toNat ≥ 32) <;>
      cases hs32 : decide ((w.extractLsb' 10 6).toNat ≥ 32) <;>
      (rw [hopc, hsf, hn, hr32, hs32] at hb;
       cases hb <;>
       (rw [decide_eq_false_iff_not, Nat.not_le] at hr32 hs32;
        simp at hr32 hs32;
        have hpack := packBitfield_eq w hc (by rw [hn, hsf]);
        rw [hopc, hsf] at hpack;
        dsimp [encode, RegWidth.ofBool, RegWidth.toBool, BitfieldOp.toBits];
        simp [hr32, hs32, hpack]))
  · rcases bitvec2_cases (w.extractLsb' 29 2) with hopc | hopc | hopc | hopc <;>
      cases hn : w.getLsbD 22 <;>
      (rw [hopc, hsf, hn] at hb;
       cases hb <;>
       (have hpack := packBitfield_eq w hc (by rw [hn, hsf]);
        rw [hopc, hsf] at hpack;
        dsimp [encode, RegWidth.ofBool, RegWidth.toBool, BitfieldOp.toBits];
        simp [hr_lt64, hs_lt64, hpack]))

set_option maxHeartbeats 800000 in
theorem branch_extr_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7f800000#32) == 0x13800000#32) = true)
    (hb : (let sf := w.getLsbD 31
           let width : RegWidth := RegWidth.ofBool sf
           let nBit := w.getLsbD 22
           let o0 := w.getLsbD 21
           let rm := Reg.fromZRBits (w.extractLsb' 16 5)
           let imms := (w.extractLsb' 10 6).toNat
           let rn := Reg.fromZRBits (w.extractLsb' 5 5)
           let rd := Reg.fromZRBits (w.extractLsb' 0 5)
           if sf != nBit || o0 || (!sf && imms >= 32) then
             none
           else
             some (.extr width rd rn rm imms)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have h_lt64 : (w.extractLsb' 10 6).toNat < 64 := (w.extractLsb' 10 6).isLt
  simp at h_lt64
  cases hsf : w.getLsbD 31
  · cases hn : w.getLsbD 22 <;>
      cases ho0 : w.getLsbD 21 <;>
      cases h32 : decide ((w.extractLsb' 10 6).toNat ≥ 32) <;>
      (rw [hsf, hn, ho0, h32] at hb;
       cases hb <;>
       (rw [decide_eq_false_iff_not, Nat.not_le] at h32;
        simp at h32;
        have hpack := packExtr_eq w hc (by rw [hn, hsf]) ho0;
        rw [hsf] at hpack;
        dsimp [encode, RegWidth.ofBool, RegWidth.toBool];
        simp [h32, hpack]))
  · cases hn : w.getLsbD 22 <;>
      cases ho0 : w.getLsbD 21 <;>
      (rw [hsf, hn, ho0] at hb;
       cases hb <;>
       (have hpack := packExtr_eq w hc (by rw [hn, hsf]) ho0;
        rw [hsf] at hpack;
        dsimp [encode, RegWidth.ofBool, RegWidth.toBool];
        simp [h_lt64, hpack]))

end Arm64
