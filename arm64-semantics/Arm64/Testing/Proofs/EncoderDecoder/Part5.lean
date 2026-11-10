/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common
public import Arm64.Testing.Proofs.EncoderDecoder.Part3
public import Arm64.Testing.Proofs.EncoderDecoder.Part4

/-!
# ARM64 Decoder-Encoder Round-Trip: Part 5

Proves per-branch decoder soundness (`branch_*_sound`) for hints, `udf`, `dcZva`, `crc32`,
non-temporal GPR and SIMD load/store pairs (`ldnp`, `stnp`), `prfm` (immediate, unscaled, and
register modes; literal mode is in `Part3.branch_ldrLit_sound`), LSE (`atomicRmw`, `ldapr`) and
RCpc (`ldapurStlur`) atomics, exclusives and compare-and-swap (`ldxp`, `stxp`, `cas`, `casp`), and
SIMD literal/structure instructions (`ldrSimdLit`, `simdLdSt1Multi`, `simdLd1r`, `simdTbl`,
`simdAddpScalar`).
-/

@[expose] public section

namespace Arm64

attribute [-simp] BitVec.getLsbD_eq_getElem

/-! ## Field round-trip helpers -/

@[simp]
theorem AtomicOp.toBits_ofBits : ∀ b : BitVec 3, (AtomicOp.ofBits b).toBits = b := by
  apply forall_bitvec; decide

@[simp]
theorem AtomicOp.isSwp_ofBits : ∀ b : BitVec 3, (AtomicOp.ofBits b).isSwp = false := by
  apply forall_bitvec; decide

theorem bitvec4_cases (b : BitVec 4) :
    b = 0#4 ∨ b = 1#4 ∨ b = 2#4 ∨ b = 3#4 ∨ b = 4#4 ∨ b = 5#4 ∨ b = 6#4 ∨ b = 7#4 ∨
    b = 8#4 ∨ b = 9#4 ∨ b = 10#4 ∨ b = 11#4 ∨ b = 12#4 ∨ b = 13#4 ∨ b = 14#4 ∨ b = 15#4 := by
  revert b; apply forall_bitvec; decide

/-! ## Hint / UDF / DC ZVA -/

theorem branch_hint_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xfffff01f#32) == 0xd503201f#32) = true)
    (hb : some (.hint (w.extractLsb' 5 7)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packHint (w.extractLsb' 5 7) = w := by dsimp [packHint]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_udf_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffff0000#32) == 0x00000000#32 && w != 0#32) = true)
    (hb : some (.udf (w.extractLsb' 0 16)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packUdf (w.extractLsb' 0 16) = w := by dsimp [packUdf]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_dcZva_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffffffe0#32) == 0xd50b7420#32) = true)
    (hb : some (.dcZva (Reg.fromZRBits (w.extractLsb' 0 5))) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packDcZva (w.extractLsb' 0 5) = w := by dsimp [packDcZva]; bv_robdd
  dsimp [encode]; simp [hpack]

/-! ## CRC32 -/

theorem branch_crc32_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7fe0e000#32) == 0x1ac04000#32) = true)
    (hb : (let szBits := w.extractLsb' 10 2
           if w.getLsbD 31 != (szBits == 3#2) then none
           else
             some (.crc32 (w.getLsbD 12) (MemWidth.ofBits szBits)
               (Reg.fromZRBits (w.extractLsb' 0 5)) (Reg.fromZRBits (w.extractLsb' 5 5))
               (Reg.fromZRBits (w.extractLsb' 16 5)))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · cases hb
  · rename_i hsf
    cases hb
    have hsf' : (w.extractLsb' 10 2 == 3#2) = w.getLsbD 31 := by
      revert hsf; cases w.getLsbD 31 <;> cases (w.extractLsb' 10 2 == 3#2) <;> decide
    have hpack : packCrc32 (w.extractLsb' 10 2 == 3#2) (w.getLsbD 12) (w.extractLsb' 10 2)
        (w.extractLsb' 16 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      rw [hsf']; dsimp [packCrc32]; bv_robdd
    dsimp [encode]; simp only [MemWidth.toBits_ofBits, Reg.toBits_fromZRBits,
      Reg.isValidZR_fromZRBits, Bool.and_self, ite_true, hpack]

/-! ## TBL / ADDP scalar -/

theorem branch_simdTbl_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfe08c00#32) == 0x0e000000#32) = true)
    (hb : some (.simdTbl (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 13 2) (w.getLsbD 12)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packSimdTbl (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 13 2) (w.getLsbD 12)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by dsimp [packSimdTbl]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_simdAddpScalar_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xfffffc00#32) == 0x5ef1b800#32) = true)
    (hb : some (.simdAddpScalar (w.extractLsb' 5 5) (w.extractLsb' 0 5)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packSimdAddpScalar (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packSimdAddpScalar]; bv_robdd
  dsimp [encode]; simp [hpack]

/-! ## Exclusive pair / CAS / CASP -/

theorem packExclPair_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x08000000#32) = true) :
    packExclPair (w.extractLsb' 30 2) (w.getLsbD 23) (w.getLsbD 22) (w.getLsbD 21) (w.extractLsb' 16 5)
      (w.getLsbD 15) (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packExclPair]; bv_robdd

theorem branch_ldxp_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfff0000#32) == 0x887f0000#32) = true)
    (hb : (let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
           let acq := w.getLsbD 15
           let t2Bits := w.extractLsb' 10 5
           let tBits := w.extractLsb' 0 5
           if tBits == t2Bits then none
           else some (.ldxp sz acq (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits tBits)
             (Reg.fromZRBits t2Bits))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packExclPair_eq w (by bv_robdd)
  have h23 : w.getLsbD 23 = false := by bv_robdd
  have h22 : w.getLsbD 22 = true := by bv_robdd
  have h21 : w.getLsbD 21 = true := by bv_robdd
  have h16 : w.extractLsb' 16 5 = 31#5 := by bv_robdd
  have h31 : w.getLsbD 31 = true := by bv_robdd
  rw [h23, h22, h21, h16] at hpack
  cases h30 : w.getLsbD 30 <;> cases ht : (w.extractLsb' 0 5 == w.extractLsb' 10 5) <;>
    (rw [h30, ht] at hb; cases hb)
  · have hsz : w.extractLsb' 30 2 = 2#2 := by bv_robdd
    rw [hsz] at hpack
    dsimp [encode, pairSf?]; simp [hpack, ht]
  · have hsz : w.extractLsb' 30 2 = 3#2 := by bv_robdd
    rw [hsz] at hpack
    dsimp [encode, pairSf?]; simp [hpack, ht]

theorem branch_stxp_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfe00000#32) == 0x88200000#32) = true)
    (hb : (let sBits := w.extractLsb' 16 5
           let t2Bits := w.extractLsb' 10 5
           let nBits := w.extractLsb' 5 5
           let tBits := w.extractLsb' 0 5
           if sBits == tBits || sBits == t2Bits || (sBits == nBits && nBits != 31#5) then none
           else
             let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
             some (.stxp sz (w.getLsbD 15) (Reg.fromZRBits sBits) (Reg.fromSPBits nBits)
               (Reg.fromZRBits tBits) (Reg.fromZRBits t2Bits))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packExclPair_eq w (by bv_robdd)
  have h23 : w.getLsbD 23 = false := by bv_robdd
  have h22 : w.getLsbD 22 = false := by bv_robdd
  have h21 : w.getLsbD 21 = true := by bv_robdd
  rw [h23, h22, h21] at hpack
  split at hb
  · cases hb
  · cases h30 : w.getLsbD 30 <;> (rw [h30] at hb; cases hb)
    · have hsz : w.extractLsb' 30 2 = 2#2 := by bv_robdd
      rw [hsz] at hpack
      dsimp [encode, pairSf?]; simp [hpack]
    · have hsz : w.extractLsb' 30 2 = 3#2 := by bv_robdd
      rw [hsz] at hpack
      dsimp [encode, pairSf?]; simp [hpack]

theorem branch_cas_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3fa07c00#32) == 0x08a07c00#32) = true)
    (hb : (let sz := MemWidth.ofBits (w.extractLsb' 30 2)
           some (.cas sz (w.getLsbD 22) (w.getLsbD 15) (Reg.fromZRBits (w.extractLsb' 16 5))
             (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits (w.extractLsb' 0 5)))) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packExclPair_eq w (by bv_robdd)
  have h23 : w.getLsbD 23 = true := by bv_robdd
  have h21 : w.getLsbD 21 = true := by bv_robdd
  have h10 : w.extractLsb' 10 5 = 31#5 := by bv_robdd
  rw [h23, h21, h10] at hpack
  dsimp [encode]; simp [hpack]

set_option linter.unusedSimpArgs false in
theorem branch_casp_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfa07c00#32) == 0x08207c00#32) = true)
    (hb : (let sBits := w.extractLsb' 16 5
           let tBits := w.extractLsb' 0 5
           if sBits.getLsbD 0 || tBits.getLsbD 0 then none
           else
             let sz : MemWidth := if w.getLsbD 30 then .X64 else .W32
             some (.casp sz (w.getLsbD 22) (w.getLsbD 15) (Reg.fromZRBits sBits)
               (Reg.fromZRBits (sBits + 1#5)) (Reg.fromSPBits (w.extractLsb' 5 5)) (Reg.fromZRBits tBits)
               (Reg.fromZRBits (tBits + 1#5)))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packExclPair_eq w (by bv_robdd)
  have h23 : w.getLsbD 23 = false := by bv_robdd
  have h21 : w.getLsbD 21 = true := by bv_robdd
  have h10 : w.extractLsb' 10 5 = 31#5 := by bv_robdd
  rw [h23, h21, h10] at hpack
  cases hs : (w.extractLsb' 16 5).getLsbD 0 <;> cases ht : (w.extractLsb' 0 5).getLsbD 0 <;>
    cases h30 : w.getLsbD 30 <;> (rw [hs, ht, h30] at hb; try simp only [Bool.or_self, Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or] at hb; cases hb)
  · have hsz : w.extractLsb' 30 2 = 0#2 := by bv_robdd
    rw [hsz] at hpack
    dsimp [encode, pairSf?]; simp [hpack, hs, ht]
  · have hsz : w.extractLsb' 30 2 = 1#2 := by bv_robdd
    rw [hsz] at hpack
    dsimp [encode, pairSf?]; simp [hpack, hs, ht]

/-! ## LDNP / STNP (GPR and SIMD) -/

set_option maxHeartbeats 800000 in
theorem branch_ldnp_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7f800000#32) == 0x28000000#32) = true)
    (hb : (let is64 := w.getLsbD 31
           let isLoad := w.getLsbD 22
           let imm7 : BitVec 7 := w.extractLsb' 15 7
           let offset : BitVec 64 := (imm7.signExtend 64) <<< (if is64 then 3 else 2)
           let rt2Bits := w.extractLsb' 10 5
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rtBits := w.extractLsb' 0 5
           let sz : MemWidth := if is64 then .X64 else .W32
           if isLoad then
             if rtBits == rt2Bits then none
             else some (.ldnp sz rn (Reg.fromZRBits rtBits) (Reg.fromZRBits rt2Bits) offset)
           else some (.stnp sz rn (Reg.fromZRBits rtBits) (Reg.fromZRBits rt2Bits) offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLoadStorePair_eq w (by bv_robdd)
  have hmode : w.extractLsb' 23 2 = 0#2 := by bv_robdd
  rw [hmode] at hpack
  cases h31 : w.getLsbD 31 <;> cases hL : w.getLsbD 22 <;>
    cases ht : (w.extractLsb' 0 5 == w.extractLsb' 10 5) <;>
    (rw [h31, hL] at hb; try rw [ht] at hb; cases hb)
  all_goals first
    | (have hopc : w.extractLsb' 30 2 = 0#2 := by bv_robdd
       rw [hopc, hL] at hpack
       dsimp [encode, encodeLdStNp, pairSf?]; simp [hpack, ht])
    | (have hopc : w.extractLsb' 30 2 = 2#2 := by bv_robdd
       rw [hopc, hL] at hpack
       dsimp [encode, encodeLdStNp, pairSf?]; simp [hpack, ht])

set_option maxHeartbeats 800000 in
theorem branch_simdNp_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f800000#32) == 0x2c000000#32) = true)
    (hb : (let sz? : Option (SimdMemSize × Nat) :=
             match (w.extractLsb' 30 2).toNat with
             | 0 => some (.S32, 2)
             | 1 => some (.D64, 3)
             | 2 => some (.Q128, 4)
             | _ => none
           match sz? with
           | none => none
           | some (sz, scale) =>
             let imm7 : BitVec 7 := w.extractLsb' 15 7
             let offset : BitVec 64 := (imm7.signExtend 64) <<< scale
             let vt2 : BitVec 5 := w.extractLsb' 10 5
             let rn := Reg.fromSPBits (w.extractLsb' 5 5)
             let vt1 : BitVec 5 := w.extractLsb' 0 5
             if w.getLsbD 22 then
               if vt1 == vt2 then none else some (.ldnpSimd sz vt1 vt2 rn offset)
             else some (.stnpSimd sz vt1 vt2 rn offset)) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packSimdLoadStorePair_eq w (by bv_robdd)
  have hmode : w.extractLsb' 23 2 = 0#2 := by bv_robdd
  rw [hmode] at hpack
  rcases bitvec2_cases (w.extractLsb' 30 2) with hopc | hopc | hopc | hopc <;>
    cases hL : w.getLsbD 22 <;>
    cases hvt : (w.extractLsb' 0 5 == w.extractLsb' 10 5) <;>
    (rw [hopc, hL, hvt] at hb;
     cases hb <;>
     (rw [hopc, hL] at hpack; dsimp [encode, encodeSimdNp]; simp [hpack, hvt]))

/-! ## PRFM (immediate / unscaled / register) -/

theorem branch_prfmImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffc00000#32) == 0xf9800000#32) = true)
    (hb : (let imm12 : BitVec 12 := w.extractLsb' 10 12
           let offset : BitVec 64 := (imm12.zeroExtend 64) <<< 3
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           some (.prfm (w.extractLsb' 0 5) (.Offset rn offset))) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packLoadStoreUImm_eq w (by bv_robdd)
  have hsz : w.extractLsb' 30 2 = 3#2 := by bv_robdd
  have hopc : w.extractLsb' 22 2 = 2#2 := by bv_robdd
  rw [hsz, hopc] at hpack
  dsimp [encode, encodePrfm]; simp [hpack]

theorem branch_prfum_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe00c00#32) == 0xf8800000#32) = true)
    (hb : (let imm9 : BitVec 9 := w.extractLsb' 12 9
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           some (.prfm (w.extractLsb' 0 5) (.UnscaledOffset rn (imm9.signExtend 64)))) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packLoadStoreSimm9_eq w (by bv_robdd) (by bv_robdd)
  have hsz : w.extractLsb' 30 2 = 3#2 := by bv_robdd
  have hopc : w.extractLsb' 22 2 = 2#2 := by bv_robdd
  have hmode : w.extractLsb' 10 2 = 0#2 := by bv_robdd
  rw [hsz, hopc, hmode] at hpack
  dsimp [encode, encodePrfm]; simp [hpack]

theorem branch_prfmReg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe00c00#32) == 0xf8a00800#32) = true)
    (hb : (let extBits := w.extractLsb' 13 3
           if !extBits.getLsbD 1 then none
           else
             let rn := Reg.fromSPBits (w.extractLsb' 5 5)
             let rm := Reg.fromZRBits (w.extractLsb' 16 5)
             let amount := if w.getLsbD 12 then 3 else 0
             some (.prfm (w.extractLsb' 0 5) (.RegOffset rn rm (ExtendType.ofBits extBits) amount))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLoadStoreRegOff_eq w (by bv_robdd) (by bv_robdd) (by bv_robdd)
  have hsz : w.extractLsb' 30 2 = 3#2 := by bv_robdd
  have hopc : w.extractLsb' 22 2 = 2#2 := by bv_robdd
  rw [hsz, hopc] at hpack
  cases hext : (w.extractLsb' 13 3).getLsbD 1 <;> cases hs : w.getLsbD 12 <;>
    (rw [hext] at hb; try rw [hs] at hb; cases hb)
  all_goals (rw [hs] at hpack; dsimp [encode, encodePrfm]; simp [hpack, hext])

/-! ## LSE atomics / LDAPR -/

theorem packLse_eq (w : BitVec 32) (h : ((w &&& 0x3f200c00#32) == 0x38200000#32) = true) :
    packLse (w.extractLsb' 30 2) (w.getLsbD 23) (w.getLsbD 22) (w.extractLsb' 16 5) (w.getLsbD 15)
      (w.extractLsb' 12 3) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packLse]; bv_robdd

set_option maxHeartbeats 800000 in
theorem branch_lse_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f200c00#32) == 0x38200000#32) = true)
    (hb : (let sz := MemWidth.ofBits (w.extractLsb' 30 2)
           let acq := w.getLsbD 23
           let rel := w.getLsbD 22
           let sBits := w.extractLsb' 16 5
           let o3 := w.getLsbD 15
           let opc : BitVec 3 := w.extractLsb' 12 3
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let rt := Reg.fromZRBits (w.extractLsb' 0 5)
           if !o3 then
             some (.atomicRmw (AtomicOp.ofBits opc) sz acq rel (Reg.fromZRBits sBits) rn rt)
           else if opc == 0#3 then
             some (.atomicRmw .SWP sz acq rel (Reg.fromZRBits sBits) rn rt)
           else if opc == 4#3 && acq && !rel && sBits == 31#5 then
             some (.ldapr sz rn rt)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packLse_eq w hc
  cases ho3 : w.getLsbD 15
  · rw [ho3] at hb hpack
    cases hb
    dsimp [encode]; simp [hpack, AtomicOp.isSwp_ofBits]
  · rw [ho3] at hb hpack
    cases hop0 : (w.extractLsb' 12 3 == 0#3)
    · rw [hop0] at hb
      cases hl : (w.extractLsb' 12 3 == 4#3 && w.getLsbD 23 && !w.getLsbD 22 && w.extractLsb' 16 5 == 31#5)
      · rw [hl] at hb; cases hb
      · rw [hl] at hb; cases hb
        have h1 : w.extractLsb' 12 3 = 4#3 := by simp_all
        have h2 : w.getLsbD 23 = true := by simp_all
        have h3 : w.getLsbD 22 = false := by simp_all
        have h4 : w.extractLsb' 16 5 = 31#5 := by simp_all
        rw [h1, h2, h3, h4] at hpack
        dsimp [encode]; simp [hpack]
    · rw [hop0] at hb; cases hb
      have h1 : w.extractLsb' 12 3 = 0#3 := by simpa using hop0
      rw [h1] at hpack
      dsimp [encode, AtomicOp.isSwp, AtomicOp.toBits]; simp [hpack]

/-! ## RCpc unscaled (`STLUR`, `LDAPUR*`) -/

set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
theorem branch_rcpc_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f200c00#32) == 0x19000000#32) = true)
    (hb : (let sizeBits := w.extractLsb' 30 2
           let opc : BitVec 2 := w.extractLsb' 22 2
           if (sizeBits == 3#2 && opc.getLsbD 1) || (sizeBits == 2#2 && opc == 3#2) then none
           else
             let imm9 : BitVec 9 := w.extractLsb' 12 9
             let rn := Reg.fromSPBits (w.extractLsb' 5 5)
             let rt := Reg.fromZRBits (w.extractLsb' 0 5)
             some (.ldapurStlur (MemWidth.ofBits sizeBits) opc rn rt (imm9.signExtend 64))) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack : packRcpcUnscaled (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 12 9)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by dsimp [packRcpcUnscaled]; bv_robdd
  rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
    rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
    (rw [hsz, hopc] at hb hpack;
     cases hb <;> (dsimp [encode]; simp [hpack, hopc]))

/-! ## SIMD literal -/

theorem branch_ldrSimdLit_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x1c000000#32) = true)
    (hb : (let imm19 : BitVec 19 := w.extractLsb' 5 19
           let offset : BitVec 64 := (imm19.signExtend 64) <<< 2
           let vt : BitVec 5 := w.extractLsb' 0 5
           match (w.extractLsb' 30 2).toNat with
           | 0 => some (.ldrSimdLit .S32 vt offset)
           | 1 => some (.ldrSimdLit .D64 vt offset)
           | 2 => some (.ldrSimdLit .Q128 vt offset)
           | _ => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack : packSimdLdrLit (w.extractLsb' 30 2) (w.extractLsb' 5 19) (w.extractLsb' 0 5) = w := by
    dsimp [packSimdLdrLit]; bv_robdd
  rcases bitvec2_cases (w.extractLsb' 30 2) with hopc | hopc | hopc | hopc <;>
    (rw [hopc] at hb hpack;
     cases hb <;> (dsimp [encode]; simp [hpack]))

/-! ## SIMD LD1/ST1 (multiple) / LD1R -/

set_option maxHeartbeats 1600000 in
theorem branch_ld1Multi_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfbf0000#32) == 0x0c000000#32 || (w &&& 0xbfa00000#32) == 0x0c800000#32) = true)
    (hb : (let isLoad := w.getLsbD 22
           let q := w.getLsbD 30
           let size := w.extractLsb' 10 2
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let postIdx := w.getLsbD 23
           let rm := w.extractLsb' 16 5
           let vt := w.extractLsb' 0 5
           match (w.extractLsb' 12 4).toNat with
           | 7  => some (.simdLdSt1Multi isLoad q size 1 rn postIdx rm vt)
           | 10 => some (.simdLdSt1Multi isLoad q size 2 rn postIdx rm vt)
           | 6  => some (.simdLdSt1Multi isLoad q size 3 rn postIdx rm vt)
           | 2  => some (.simdLdSt1Multi isLoad q size 4 rn postIdx rm vt)
           | 8  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 2 rn postIdx rm vt)
           | 4  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 3 rn postIdx rm vt)
           | 0  => if size == 3#2 && !q then none else some (.simdLdStMulti isLoad q size 4 rn postIdx rm vt)
           | _  => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hrm : (w.getLsbD 23 || w.extractLsb' 16 5 == 0#5) = true := by bv_robdd
  cases hsz : (w.extractLsb' 10 2 == 3#2 && !w.getLsbD 30) <;>
    simp only [hsz, ↓reduceIte, Bool.false_eq_true] at hb <;>
    rcases bitvec4_cases (w.extractLsb' 12 4) with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] at hb <;>
    cases hb <;>
    (have hpack : packSimdLdStStruct 0x0c000000#32 (w.getLsbD 30) (w.getLsbD 23) (w.getLsbD 22)
        (w.extractLsb' 16 5) (w.extractLsb' 12 4) (w.extractLsb' 10 2) (w.extractLsb' 5 5)
        (w.extractLsb' 0 5) = w := by dsimp [packSimdLdStStruct]; bv_robdd
     rw [h] at hpack
     dsimp [encode, ld1MultiOpcode?, ldMultiOpcode?]; simp [hpack, hrm])

theorem branch_ld1r_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbffff000#32) == 0x0d40c000#32 || (w &&& 0xbfe0f000#32) == 0x0dc0c000#32) = true)
    (hb : some (.simdLd1r (w.getLsbD 30) (w.extractLsb' 10 2) (Reg.fromSPBits (w.extractLsb' 5 5))
      (w.getLsbD 23) (w.extractLsb' 16 5) (w.extractLsb' 0 5)) = some p) :
    encode p = some w := by
  cases hb
  have hrm : (w.getLsbD 23 || w.extractLsb' 16 5 == 0#5) = true := by bv_robdd
  have hpack : packSimdLdStStruct 0x0d000000#32 (w.getLsbD 30) (w.getLsbD 23) true
      (w.extractLsb' 16 5) 12#4 (w.extractLsb' 10 2) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packSimdLdStStruct]; bv_robdd
  dsimp [encode]; simp [hpack, hrm]

theorem branch_simdPmull_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbf20fc00#32) == 0x0e20e000#32) = true)
    (hb : (let size : BitVec 2 := w.extractLsb' 22 2
           if size == 0#2 || size == 3#2 then
             let q := w.getLsbD 30
             let rm : BitVec 5 := w.extractLsb' 16 5
             let rn : BitVec 5 := w.extractLsb' 5 5
             let rd : BitVec 5 := w.extractLsb' 0 5
             some (.simdPmull q (size == 3#2) rm rn rd)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · rename_i hsz
    cases hb
    have hpack : packSimdPmull (w.getLsbD 30) (w.extractLsb' 22 2 == 3#2)
        (w.extractLsb' 16 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packSimdPmull]; bv_robdd
    dsimp [encode]; simp [hpack]
  · cases hb

theorem branch_cryptoSha2Reg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xfffe0c00#32) == 0x5e280800#32) = true)
    (hb : (let opcode : BitVec 5 := w.extractLsb' 12 5
           if opcode == 0#5 || opcode == 1#5 || opcode == 2#5 then
             let rn : BitVec 5 := w.extractLsb' 5 5
             let rd : BitVec 5 := w.extractLsb' 0 5
             some (.cryptoSha2Reg opcode rn rd)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · rename_i hop
    cases hb
    have hpack : packCryptoSha2Reg (w.extractLsb' 12 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packCryptoSha2Reg]; bv_robdd
    dsimp [encode]; simp [hop, hpack]
  · cases hb

theorem branch_cryptoSha3Reg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe08c00#32) == 0x5e000000#32) = true)
    (hb : (let opcode : BitVec 3 := w.extractLsb' 12 3
           if opcode != 7#3 then
             let rm : BitVec 5 := w.extractLsb' 16 5
             let rn : BitVec 5 := w.extractLsb' 5 5
             let rd : BitVec 5 := w.extractLsb' 0 5
             some (.cryptoSha3Reg opcode rm rn rd)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · rename_i hop
    cases hb
    have hpack : packCryptoSha3Reg (w.extractLsb' 12 3) (w.extractLsb' 16 5)
        (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packCryptoSha3Reg]; bv_robdd
    dsimp [encode]; simp [hop, hpack]
  · cases hb

theorem branch_cryptoSha512Reg2_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xfffffc00#32) == 0xcec08000#32) = true)
    (hb : (let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.cryptoSha512Reg2 rn rd)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packCryptoSha512Reg2 (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packCryptoSha512Reg2]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_cryptoSha512Reg3_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe0f000#32) == 0xce608000#32) = true)
    (hb : (let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 2 := w.extractLsb' 10 2
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.cryptoSha512Reg3 opcode rm rn rd)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packCryptoSha512Reg3 (w.extractLsb' 10 2) (w.extractLsb' 16 5)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packCryptoSha512Reg3]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_cryptoSha3FourReg_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffc08000#32) == 0xce000000#32) = true)
    (hb : (let isBcax := w.getLsbD 21
           let rm : BitVec 5 := w.extractLsb' 16 5
           let ra : BitVec 5 := w.extractLsb' 10 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.cryptoSha3FourReg isBcax rm ra rn rd)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packCryptoSha3FourReg (w.getLsbD 21) (w.extractLsb' 16 5)
      (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packCryptoSha3FourReg]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_cryptoXar_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe00000#32) == 0xce800000#32) = true)
    (hb : (let rm : BitVec 5 := w.extractLsb' 16 5
           let imm6 : BitVec 6 := w.extractLsb' 10 6
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.cryptoXar rm imm6 rn rd)) = some p) :
    encode p = some w := by
  cases hb
  have hpack : packCryptoXar (w.extractLsb' 16 5) (w.extractLsb' 10 6)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
    dsimp [packCryptoXar]; bv_robdd
  dsimp [encode]; simp [hpack]

theorem branch_simdLdSt1Single_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfbf0000#32) == 0x0d000000#32 || (w &&& 0xbfe00000#32) == 0x0dc00000#32) = true)
    (hb : (let q := w.getLsbD 30
           let postIdx := w.getLsbD 23
           let isLoad := w.getLsbD 22
           let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 3 := w.extractLsb' 13 3
           let sBit := w.getLsbD 12
           let size : BitVec 2 := w.extractLsb' 10 2
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let vt : BitVec 5 := w.extractLsb' 0 5
           if validSimdLdSt1Single opcode sBit size then
             some (.simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · cases hb
    have hpack : packSimdLdSt1Single (w.getLsbD 22) (w.getLsbD 30) (w.getLsbD 23)
        (w.extractLsb' 16 5) (w.extractLsb' 13 3) (w.getLsbD 12) (w.extractLsb' 10 2)
        (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packSimdLdSt1Single]; bv_robdd
    dsimp [encode]; simp [hpack]
  · cases hb

theorem branch_simdDupScalar_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffe0fc00#32) == 0x5e000400#32) = true)
    (hb : (let imm5 : BitVec 5 := w.extractLsb' 16 5
           if imm5.extractLsb' 0 4 != 0#4 then
             some (.simdDupScalar imm5 (w.extractLsb' 5 5) (w.extractLsb' 0 5))
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · cases hb
    have hpack : packSimdDupScalar (w.extractLsb' 16 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packSimdDupScalar]; bv_robdd
    dsimp [encode]; simp [hpack]
  · cases hb

theorem branch_simdThreeDiff_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9f200c00#32) == 0x0e200000#32) = true)
    (hb : (let size : BitVec 2 := w.extractLsb' 22 2
           let opcode : BitVec 4 := w.extractLsb' 12 4
           if validSimdThreeDiff size opcode then
             let q := w.getLsbD 30
             let u := w.getLsbD 29
             let rm : BitVec 5 := w.extractLsb' 16 5
             let rn : BitVec 5 := w.extractLsb' 5 5
             let rd : BitVec 5 := w.extractLsb' 0 5
             some (.simdThreeDiff q u size rm opcode rn rd)
           else none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  split at hb
  · cases hb
    have hpack : packSimdThreeDiff (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
        (w.extractLsb' 16 5) (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
      dsimp [packSimdThreeDiff]; bv_robdd
    dsimp [encode]; simp [hpack]
  · cases hb
end Arm64
