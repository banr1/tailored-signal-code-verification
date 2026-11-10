/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Proofs.EncoderDecoder.Common

/-!
# ARM64 Decoder-Encoder Round-Trip, Part 4: SIMD, Crypto, and Floating-Point

Bit-packing identities (`pack*_eq`) and per-branch decoder soundness (`branch_*_sound`) for SIMD
load/store (`simdLoadStorePair`, `simdLoadStoreUImm`, `simdLoadStore24`, `st1SinglePost`), AES,
GPR/vector move (`fmovGprVec`), SIMD data-processing (`simdImmShift`, `simdInsDup`,
`simdThreeSame`, `simdTwoRegMisc`, `simdAcrossLanes`, `simdPermute`, `simdExt`), and scalar
floating-point (`fpDataProc1..3`, `fpCompare`, `fpImm`, `fpCondCompare`, `fpCondSelect`,
`fpFixedConv`) encodings.
-/

@[expose] public section

namespace Arm64

theorem packSimdLoadStorePair_eq (w : BitVec 32) (h : ((w &&& 0x3e000000#32) == 0x2c000000#32) = true) :
    packSimdLoadStorePair (w.extractLsb' 30 2) (w.extractLsb' 23 2) (w.getLsbD 22)
      (w.extractLsb' 15 7) (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdLoadStorePair]; bv_robdd

theorem packSimdLoadStoreUImm_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x3d000000#32) = true) :
    packSimdLoadStoreUImm (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 10 12)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdLoadStoreUImm]; bv_robdd

theorem packSimdLoadStoreSimm9_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x3c000000#32) = true)
    (h21 : w.getLsbD 21 = false) :
    packSimdLoadStoreSimm9 (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 10 2)
      (w.extractLsb' 12 9) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdLoadStoreSimm9]; bv_robdd

theorem packSimdLoadStoreRegOff_eq (w : BitVec 32) (h : ((w &&& 0x3f000000#32) == 0x3c000000#32) = true)
    (h21 : w.getLsbD 21 = true) (h10 : w.extractLsb' 10 2 = 2#2) :
    packSimdLoadStoreRegOff (w.extractLsb' 30 2) (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 13 3) (w.getLsbD 12) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdLoadStoreRegOff]; bv_robdd

theorem packSt1SinglePost_eq (w : BitVec 32) (h : ((w &&& 0xbfe00000#32) == 0x0d800000#32) = true) :
    packSt1SinglePost (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 13 3)
      (w.getLsbD 12) (w.extractLsb' 10 2) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSt1SinglePost]; bv_robdd

theorem packAes_eq (w : BitVec 32) (h : ((w &&& 0xffffcc00#32) == 0x4e284800#32) = true) :
    packAes (w.extractLsb' 12 2) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packAes]; bv_robdd

theorem packFmovGprVec_eq (w : BitVec 32) (h : ((w &&& 0x7f20fc00#32) == 0x1e200000#32) = true) :
    packFmovGprVec (w.getLsbD 31) (w.extractLsb' 22 2) (w.extractLsb' 19 2)
      (w.extractLsb' 16 3) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFmovGprVec]; bv_robdd

theorem packSimdImmShift_eq (w : BitVec 32) (h : ((w &&& 0x9f800400#32) == 0x0f000400#32) = true) :
    packSimdImmShift (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 19 4)
      (w.extractLsb' 16 3) (w.extractLsb' 11 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdImmShift]; bv_robdd

theorem packSimdInsDup_eq (w : BitVec 32) (h : ((w &&& 0x9fe08400#32) == 0x0e000400#32) = true) :
    packSimdInsDup (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 16 5)
      (w.extractLsb' 11 4) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdInsDup]; bv_robdd

theorem packSimdThreeSame_eq (w : BitVec 32) (h : ((w &&& 0x9f200400#32) == 0x0e200400#32) = true) :
    packSimdThreeSame (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
      (w.extractLsb' 16 5) (w.extractLsb' 11 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdThreeSame]; bv_robdd

theorem packSimdTwoRegMisc_eq (w : BitVec 32) (h : ((w &&& 0x9f3e0c00#32) == 0x0e200800#32) = true) :
    packSimdTwoRegMisc (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
      (w.extractLsb' 12 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdTwoRegMisc]; bv_robdd

theorem packSimdAcrossLanes_eq (w : BitVec 32) (h : ((w &&& 0x9f3e0c00#32) == 0x0e300800#32) = true) :
    packSimdAcrossLanes (w.getLsbD 30) (w.getLsbD 29) (w.extractLsb' 22 2)
      (w.extractLsb' 12 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdAcrossLanes]; bv_robdd

theorem packSimdPermute_eq (w : BitVec 32) (h : ((w &&& 0xbf208c00#32) == 0x0e000800#32) = true) :
    packSimdPermute (w.getLsbD 30) (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 12 3) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdPermute]; bv_robdd

theorem packSimdExt_eq (w : BitVec 32) (h : ((w &&& 0xbfe08400#32) == 0x2e000000#32) = true) :
    packSimdExt (w.getLsbD 30) (w.extractLsb' 16 5) (w.extractLsb' 11 4)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packSimdExt]; bv_robdd

attribute [-simp] BitVec.getLsbD_eq_getElem

set_option maxHeartbeats 800000 in
theorem branch_simdLoadStorePair_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3e000000#32) == 0x2c000000#32) = true)
    (hb : (let opc := (w.extractLsb' 30 2).toNat
           let modeBits := (w.extractLsb' 23 2).toNat
           let isLoad := w.getLsbD 22
           let sz? : Option (SimdMemSize × Nat) :=
             match opc with
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
             let addr? : Option AddrMode :=
               match modeBits with
               | 1 => some (.PostIndex rn offset)
               | 2 => some (.Offset rn offset)
               | 3 => some (.PreIndex rn offset)
               | _ => none
             match addr? with
             | some addr =>
               if isLoad then
                 if vt1 == vt2 then none else some (.ldpSimd sz vt1 vt2 addr)
               else some (.stpSimd sz vt1 vt2 addr)
             | none => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packSimdLoadStorePair_eq w hc
  rcases bitvec2_cases (w.extractLsb' 30 2) with hopc | hopc | hopc | hopc <;>
    rcases bitvec2_cases (w.extractLsb' 23 2) with hmode | hmode | hmode | hmode <;>
    cases hL : w.getLsbD 22 <;>
    cases hvt : (w.extractLsb' 0 5 == w.extractLsb' 10 5) <;>
    (rw [hopc, hmode, hL, hvt] at hb;
     cases hb <;>
     (rw [hopc, hmode, hL] at hpack; dsimp [encode, encodeSimdLoadStorePair]; simp [hpack, hvt]))

set_option maxHeartbeats 800000 in
theorem branch_simdLoadStoreUImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x3d000000#32) = true)
    (hb : (let sizeBits := (w.extractLsb' 30 2).toNat
           let opc := (w.extractLsb' 22 2).toNat
           match decodeSimdLoadStoreType sizeBits opc with
           | some (isLoad, sz, scale) =>
             let imm12 : BitVec 12 := w.extractLsb' 10 12
             let offset : BitVec 64 := (imm12.zeroExtend 64) <<< scale
             let rn := Reg.fromSPBits (w.extractLsb' 5 5)
             let vt : BitVec 5 := w.extractLsb' 0 5
             let addr := AddrMode.Offset rn offset
             if isLoad then some (.ldrSimd sz vt addr)
             else some (.strSimd sz vt addr)
           | none => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  have hpack := packSimdLoadStoreUImm_eq w hc
  rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
    rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
    (rw [hsz, hopc] at hb hpack;
     cases hb <;>
     (dsimp [encode, encodeSimdLoadStoreAddr, encodeSimdLoadStoreType]; simp [hpack]))

set_option maxHeartbeats 2000000 in
theorem branch_simdLoadStore24_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x3f000000#32) == 0x3c000000#32) = true)
    (hb : (let sizeBits := (w.extractLsb' 30 2).toNat
           let opc := (w.extractLsb' 22 2).toNat
           match decodeSimdLoadStoreType sizeBits opc with
           | some (isLoad, sz, scale) =>
             let rn := Reg.fromSPBits (w.extractLsb' 5 5)
             let vt : BitVec 5 := w.extractLsb' 0 5
             let addr? : Option AddrMode :=
               if !(w.getLsbD 21) then
                 let imm9 : BitVec 9 := w.extractLsb' 12 9
                 let offset : BitVec 64 := imm9.signExtend 64
                 match (w.extractLsb' 10 2).toNat with
                 | 0 => some (.UnscaledOffset rn offset)
                 | 1 => some (.PostIndex rn offset)
                 | 3 => some (.PreIndex rn offset)
                 | _ => none
               else if (w.extractLsb' 10 2) == 2#2 then
                 let rm := Reg.fromZRBits (w.extractLsb' 16 5)
                 let extBits := w.extractLsb' 13 3
                 let ext := ExtendType.ofBits extBits
                 let sBit := w.getLsbD 12
                 if !extBits.getLsbD 1 || (scale == 0 && sBit) then
                   none
                 else
                   let amount := if sBit then scale else 0
                   some (.RegOffset rn rm ext amount)
               else
                 none
             match addr? with
             | some addr =>
               if isLoad then some (.ldrSimd sz vt addr)
               else some (.strSimd sz vt addr)
             | none => none
           | none => none) = some p) :
    encode p = some w := by
  dsimp only [] at hb
  cases h21 : w.getLsbD 21
  · have hpack := packSimdLoadStoreSimm9_eq w hc h21
    rcases bitvec2_cases (w.extractLsb' 10 2) with hmode | hmode | hmode | hmode <;>
      rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
      rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
      (rw [h21, hmode, hsz, hopc] at hb;
       cases hb <;>
       (rw [hmode, hsz, hopc] at hpack; dsimp [encode, encodeSimdLoadStoreAddr, encodeSimdLoadStoreType]; simp [hpack]))
  · rcases bitvec2_cases (w.extractLsb' 10 2) with hmode | hmode | hmode | hmode
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        (rw [h21, hmode, hsz, hopc] at hb; cases hb)
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        (rw [h21, hmode, hsz, hopc] at hb; cases hb)
    · have hpack := packSimdLoadStoreRegOff_eq w hc h21 hmode
      rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        cases hs : w.getLsbD 12 <;>
        cases hext1 : (w.extractLsb' 13 3).getLsbD 1 <;>
        (rw [h21, hmode, hsz, hopc, hs, hext1] at hb;
         cases hb <;>
         (rw [hsz, hopc, hs] at hpack; dsimp [encode, encodeSimdLoadStoreAddr, encodeSimdLoadStoreType]; simp [hpack, hext1]))
    · rcases bitvec2_cases (w.extractLsb' 30 2) with hsz | hsz | hsz | hsz <;>
        rcases bitvec2_cases (w.extractLsb' 22 2) with hopc | hopc | hopc | hopc <;>
        (rw [h21, hmode, hsz, hopc] at hb; cases hb)

theorem branch_st1SinglePost_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfe00000#32) == 0x0d800000#32) = true)
    (hb : (let q := w.getLsbD 30
           let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 3 := w.extractLsb' 13 3
           let sBit := w.getLsbD 12
           let size : BitVec 2 := w.extractLsb' 10 2
           let rn := Reg.fromSPBits (w.extractLsb' 5 5)
           let vt : BitVec 5 := w.extractLsb' 0 5
           some (.st1SinglePost q rm opcode sBit size rn vt)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packSt1SinglePost_eq w hc
  dsimp [encode]
  simp at hpack ⊢
  exact hpack

theorem branch_aes_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xffffcc00#32) == 0x4e284800#32) = true)
    (hb : (let op := AesOp.ofBits (w.extractLsb' 12 2)
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.aes op rd rn)) = some p) :
    encode p = some w := by
  cases hb
  have hpack := packAes_eq w hc
  dsimp [encode]
  simp at hpack ⊢
  exact hpack

theorem branch_fmovGprVec_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7f20fc00#32) == 0x1e200000#32) = true)
    (hb : (let sfBit := w.getLsbD 31
           let ftype : BitVec 2 := w.extractLsb' 22 2
           let rmode : BitVec 2 := w.extractLsb' 19 2
           let opcode : BitVec 3 := w.extractLsb' 16 3
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fmovGprVec sfBit ftype rmode opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFmovGprVec_eq w hc]

theorem branch_simdImmShift_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9f800400#32) == 0x0f000400#32) = true)
    (hb : (let q := w.getLsbD 30
           let op := w.getLsbD 29
           let immh : BitVec 4 := w.extractLsb' 19 4
           let immb : BitVec 3 := w.extractLsb' 16 3
           let opcode : BitVec 5 := w.extractLsb' 11 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdImmShift q op immh immb opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdImmShift_eq w hc]

theorem branch_simdInsDup_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9fe08400#32) == 0x0e000400#32) = true)
    (hb : (let q := w.getLsbD 30
           let op := w.getLsbD 29
           let imm5 : BitVec 5 := w.extractLsb' 16 5
           let imm4 : BitVec 4 := w.extractLsb' 11 4
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdInsDup q op imm5 imm4 rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdInsDup_eq w hc]

theorem branch_simdThreeSame_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9f200400#32) == 0x0e200400#32) = true)
    (hb : (let q := w.getLsbD 30
           let u := w.getLsbD 29
           let size : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 5 := w.extractLsb' 11 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdThreeSame q u size rm opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdThreeSame_eq w hc]

theorem branch_simdTwoRegMisc_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9f3e0c00#32) == 0x0e200800#32) = true)
    (hb : (let q := w.getLsbD 30
           let u := w.getLsbD 29
           let size : BitVec 2 := w.extractLsb' 22 2
           let opcode : BitVec 5 := w.extractLsb' 12 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdTwoRegMisc q u size opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdTwoRegMisc_eq w hc]

theorem branch_simdAcrossLanes_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x9f3e0c00#32) == 0x0e300800#32) = true)
    (hb : (let q := w.getLsbD 30
           let u := w.getLsbD 29
           let size : BitVec 2 := w.extractLsb' 22 2
           let opcode : BitVec 5 := w.extractLsb' 12 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdAcrossLanes q u size opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdAcrossLanes_eq w hc]

theorem branch_simdPermute_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbf208c00#32) == 0x0e000800#32) = true)
    (hb : (let q := w.getLsbD 30
           let size : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 3 := w.extractLsb' 12 3
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdPermute q size rm opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdPermute_eq w hc]

theorem branch_simdExt_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xbfe08400#32) == 0x2e000000#32) = true)
    (hb : (let q := w.getLsbD 30
           let rm : BitVec 5 := w.extractLsb' 16 5
           let imm4 : BitVec 4 := w.extractLsb' 11 4
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.simdExt q rm imm4 rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packSimdExt_eq w hc]

theorem packFpDataProc1_eq (w : BitVec 32) (h : ((w &&& 0xff207c00#32) == 0x1e204000#32) = true) :
    packFpDataProc1 (w.extractLsb' 22 2) (w.extractLsb' 15 6)
      (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpDataProc1]; bv_robdd

theorem packFpDataProc2_eq (w : BitVec 32) (h : ((w &&& 0xff200c00#32) == 0x1e200800#32) = true) :
    packFpDataProc2 (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpDataProc2]; bv_robdd

theorem branch_fpDataProc1_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff207c00#32) == 0x1e204000#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let opcode : BitVec 6 := w.extractLsb' 15 6
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpDataProc1 ftype opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpDataProc1_eq w hc]

theorem branch_fpDataProc2_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff200c00#32) == 0x1e200800#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let opcode : BitVec 4 := w.extractLsb' 12 4
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpDataProc2 ftype rm opcode rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpDataProc2_eq w hc]

theorem packFpCompare_eq (w : BitVec 32) (h : ((w &&& 0xff203c00#32) == 0x1e202000#32) = true) :
    packFpCompare (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 14 2) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpCompare]; bv_robdd

theorem packFpImm_eq (w : BitVec 32) (h : ((w &&& 0xff201fe0#32) == 0x1e201000#32) = true) :
    packFpImm (w.extractLsb' 22 2) (w.extractLsb' 13 8) (w.extractLsb' 0 5) = w := by
  dsimp [packFpImm]; bv_robdd

theorem packFpCondCompare_eq (w : BitVec 32) (h : ((w &&& 0xff200c00#32) == 0x1e200400#32) = true) :
    packFpCondCompare (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.getLsbD 4) (w.extractLsb' 0 4) = w := by
  dsimp [packFpCondCompare]; bv_robdd

theorem packFpCondSelect_eq (w : BitVec 32) (h : ((w &&& 0xff200c00#32) == 0x1e200c00#32) = true) :
    packFpCondSelect (w.extractLsb' 22 2) (w.extractLsb' 16 5)
      (w.extractLsb' 12 4) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpCondSelect]; bv_robdd

theorem packFpDataProc3_eq (w : BitVec 32) (h : ((w &&& 0xff000000#32) == 0x1f000000#32) = true) :
    packFpDataProc3 (w.extractLsb' 22 2) (w.getLsbD 21) (w.extractLsb' 16 5)
      (w.getLsbD 15) (w.extractLsb' 10 5) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpDataProc3]; bv_robdd

theorem packFpFixedConv_eq (w : BitVec 32) (h : ((w &&& 0x7f200000#32) == 0x1e000000#32) = true) :
    packFpFixedConv (w.getLsbD 31) (w.extractLsb' 22 2) (w.extractLsb' 19 2)
      (w.extractLsb' 16 3) (w.extractLsb' 10 6) (w.extractLsb' 5 5) (w.extractLsb' 0 5) = w := by
  dsimp [packFpFixedConv]; bv_robdd

theorem branch_fpCompare_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff203c00#32) == 0x1e202000#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let op : BitVec 2 := w.extractLsb' 14 2
           let rn : BitVec 5 := w.extractLsb' 5 5
           let opcode2 : BitVec 5 := w.extractLsb' 0 5
           some (.fpCompare ftype rm op rn opcode2)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpCompare_eq w hc]

theorem branch_fpImm_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff201fe0#32) == 0x1e201000#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let imm8 : BitVec 8 := w.extractLsb' 13 8
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpImm ftype imm8 rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpImm_eq w hc]

theorem branch_fpCondCompare_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff200c00#32) == 0x1e200400#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let cond : BitVec 4 := w.extractLsb' 12 4
           let rn : BitVec 5 := w.extractLsb' 5 5
           let op := w.getLsbD 4
           let nzcv : BitVec 4 := w.extractLsb' 0 4
           some (.fpCondCompare ftype rm cond rn op nzcv)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpCondCompare_eq w hc]

theorem branch_fpCondSelect_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff200c00#32) == 0x1e200c00#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let rm : BitVec 5 := w.extractLsb' 16 5
           let cond : BitVec 4 := w.extractLsb' 12 4
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpCondSelect ftype rm cond rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpCondSelect_eq w hc]

theorem branch_fpDataProc3_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0xff000000#32) == 0x1f000000#32) = true)
    (hb : (let ftype : BitVec 2 := w.extractLsb' 22 2
           let o1 := w.getLsbD 21
           let rm : BitVec 5 := w.extractLsb' 16 5
           let o0 := w.getLsbD 15
           let ra : BitVec 5 := w.extractLsb' 10 5
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpDataProc3 ftype o1 rm o0 ra rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpDataProc3_eq w hc]

theorem branch_fpFixedConv_sound (w : BitVec 32) (p : Instr)
    (hc : ((w &&& 0x7f200000#32) == 0x1e000000#32) = true)
    (hb : (let sfBit := w.getLsbD 31
           let ftype : BitVec 2 := w.extractLsb' 22 2
           let rmode : BitVec 2 := w.extractLsb' 19 2
           let opcode : BitVec 3 := w.extractLsb' 16 3
           let scale : BitVec 6 := w.extractLsb' 10 6
           let rn : BitVec 5 := w.extractLsb' 5 5
           let rd : BitVec 5 := w.extractLsb' 0 5
           some (.fpFixedConv sfBit ftype rmode opcode scale rn rd)) = some p) :
    encode p = some w := by
  cases hb
  dsimp [encode]
  rw [packFpFixedConv_eq w hc]

end Arm64
