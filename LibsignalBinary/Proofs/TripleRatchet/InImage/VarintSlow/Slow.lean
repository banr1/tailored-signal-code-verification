/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.TrapRng
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.Defs
import LibsignalBinary.Proofs.TripleRatchet.InImage.VarintSlow.From
import ProofLib.SepLogic.WPp

/-!
# Verification of `prost::encoding::varint::decode_varint_slow`

Verifies the 10-byte slow-path LEB128 varint decoder `decode_varint_slow::<&mut &[u8]>` against
`decodeVarintSlowSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre' (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre' (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre' (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre' (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre' (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := rfl

theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

theorem memRegion_48_split (a : BitVec 64) :
    memRegion a 48 = (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ memRegion (a + 8#64) 40 := by
  rw [← memRegion_eight, ← memRegion_split a 8 40 (by decide)]

theorem stackAt_varintSlow (sp : BitVec 64) :
    stackAt sp varintSlowStack =
      stackAt (sp - 64#64) decodeErrorHookStack ∗
        memRegion (sp - 56#64) 40 ∗
        (∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v8 : BitVec 64,
          ((sp - 64#64) ↦₆₄ v8) ∗ ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  have h0 := stackAt_split_cells sp decodeErrorHookStack 8 (by decide)
  rw [← memRegion_cells (sp - BitVec.ofNat 64 (8 * 8)) 8 (by decide)] at h0
  change stackAt sp varintSlowStack =
    stackAt (sp - 64#64) decodeErrorHookStack ∗ memRegion (sp - 64#64) 64 at h0
  have s1 := memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s1
  have s2 := memRegion_split (sp - 56#64) 40 16 (by decide)
  rw [bv_sub_add_lit sp 56 40] at s2
  have s3 := memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s3
  rw [h0, s1, s2, s3,
    memRegion_eight (sp - 64#64), memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem toNat_le_0x7f_iff (b : BitVec 8) : b.toNat ≤ 0x7f ↔ b ≤ 0x7f#8 := Iff.rfl

theorem two_le_toNat_iff (b : BitVec 8) : 2 ≤ b.toNat ↔ 2#8 ≤ b := Iff.rfl

theorem getLsbD_7_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    b.getLsbD 7 = false := by revert h; revert b; decide +kernel

theorem getLsbD_7_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    b.getLsbD 7 = true := by revert h; revert b; decide +kernel

theorem getLsbD_7_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = false := by
  rw [getLsbD_7_of_le h]; rfl

theorem getLsbD_7_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.getLsbD 7 == true) = true := by
  rw [getLsbD_7_of_gt h]; rfl

theorem signExtend32_getLsbD_31_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.signExtend 32).getLsbD 31 = false := by revert h; revert b; decide +kernel

theorem signExtend32_getLsbD_31_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.signExtend 32).getLsbD 31 = true := by revert h; revert b; decide +kernel

theorem signExtend32_getLsbD_31_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    ((b.signExtend 32).getLsbD 31 == true) = false := by
  rw [signExtend32_getLsbD_31_of_le h]; rfl

theorem signExtend32_getLsbD_31_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    ((b.signExtend 32).getLsbD 31 == true) = true := by
  rw [signExtend32_getLsbD_31_of_gt h]; rfl

theorem signExtend64_getLsbD_63_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = false := by revert h; revert b; decide +kernel

theorem signExtend64_getLsbD_63_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    (b.signExtend 64).getLsbD 63 = true := by revert h; revert b; decide +kernel

theorem signExtend64_getLsbD_63_beq_of_le {b : BitVec 8} (h : b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = false := by
  rw [signExtend64_getLsbD_63_of_le h]; rfl

theorem signExtend64_getLsbD_63_beq_of_gt {b : BitVec 8} (h : ¬ b ≤ 0x7f#8) :
    ((b.signExtend 64).getLsbD 63 == true) = true := by
  rw [signExtend64_getLsbD_63_of_gt h]; rfl

theorem byte9_hi_of_ge {b9 : BitVec 8} (hb9 : 2#8 ≤ b9) :
    (1#32).ult (BitVec.truncate 32 (BitVec.signExtend 64 b9)) = true := by
  revert hb9; revert b9; decide +kernel

theorem byte9_hi_of_lt {b9 : BitVec 8} (_hb9 : b9 ≤ 0x7f#8) (hb9_lt : ¬ 2#8 ≤ b9) :
    (1#32).ult (BitVec.truncate 32 (BitVec.signExtend 64 b9)) = false := by
  revert hb9_lt _hb9; revert b9; decide +kernel

theorem ofNat_ne_ofNat {n k : Nat} (hne : n ≠ k) (hn : n < 2 ^ 64) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 n ≠ BitVec.ofNat 64 k := by
  rw [ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  change n % 2 ^ 64 ≠ k % 2 ^ 64
  omega

abbrev vAcc1 (b0 : BitVec 8) : BitVec 64 :=
  0#64 ||| ((b0 &&& 0x7f#8).zeroExtend 64 <<< 0)
abbrev vAcc2 (b0 b1 : BitVec 8) : BitVec 64 :=
  vAcc1 b0 ||| ((b1 &&& 0x7f#8).zeroExtend 64 <<< 7)
abbrev vAcc3 (b0 b1 b2 : BitVec 8) : BitVec 64 :=
  vAcc2 b0 b1 ||| ((b2 &&& 0x7f#8).zeroExtend 64 <<< 14)
abbrev vAcc4 (b0 b1 b2 b3 : BitVec 8) : BitVec 64 :=
  vAcc3 b0 b1 b2 ||| ((b3 &&& 0x7f#8).zeroExtend 64 <<< 21)
abbrev vAcc5 (b0 b1 b2 b3 b4 : BitVec 8) : BitVec 64 :=
  vAcc4 b0 b1 b2 b3 ||| ((b4 &&& 0x7f#8).zeroExtend 64 <<< 28)
abbrev vAcc6 (b0 b1 b2 b3 b4 b5 : BitVec 8) : BitVec 64 :=
  vAcc5 b0 b1 b2 b3 b4 ||| ((b5 &&& 0x7f#8).zeroExtend 64 <<< 35)
abbrev vAcc7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) : BitVec 64 :=
  vAcc6 b0 b1 b2 b3 b4 b5 ||| ((b6 &&& 0x7f#8).zeroExtend 64 <<< 42)
abbrev vAcc8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  vAcc7 b0 b1 b2 b3 b4 b5 b6 ||| ((b7 &&& 0x7f#8).zeroExtend 64 <<< 49)
abbrev vAcc9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) : BitVec 64 :=
  vAcc8 b0 b1 b2 b3 b4 b5 b6 b7 ||| ((b8 &&& 0x7f#8).zeroExtend 64 <<< 56)
abbrev vAcc10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) : BitVec 64 :=
  vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8 ||| ((b9 &&& 0x7f#8).zeroExtend 64 <<< 63)

theorem zeroExtend64_and_127 (b : BitVec 8) :
    (b &&& 0x7f#8).zeroExtend 64 = b.zeroExtend 64 &&& 127#64 := by revert b; decide +kernel

theorem vAcc1_eq (b0 : BitVec 8) :
    b0.zeroExtend 64 &&& 127#64 = vAcc1 b0 := by revert b0; decide +kernel

theorem signExtend64_shiftLeft_63 (b9 : BitVec 8) :
    b9.signExtend 64 <<< 63 = (b9.zeroExtend 64 &&& 127#64) <<< 63 := by revert b9; decide +kernel

theorem varintSlow_1 (b0 : BitVec 8) (rest : List (BitVec 8)) (hb0 : b0 ≤ 0x7f#8) :
    varintSlow (b0 :: rest) = some (vAcc1 b0, 1) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, vAcc1]

theorem varintSlow_2 (b0 b1 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : b1 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: rest) = some (vAcc2 b0 b1, 2) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, vAcc2, vAcc1]

theorem varintSlow_3 (b0 b1 b2 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : b2 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: rest) = some (vAcc3 b0 b1 b2, 3) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, vAcc3, vAcc2, vAcc1]

theorem varintSlow_4 (b0 b1 b2 b3 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : b3 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: rest) = some (vAcc4 b0 b1 b2 b3, 4) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_5 (b0 b1 b2 b3 b4 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : b4 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: rest) = some (vAcc5 b0 b1 b2 b3 b4, 5) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4,
    vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_6 (b0 b1 b2 b3 b4 b5 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : b5 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: rest) = some (vAcc6 b0 b1 b2 b3 b4 b5, 6) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5,
    vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : b6 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: rest) =
      some (vAcc7 b0 b1 b2 b3 b4 b5 b6, 7) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : b7 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest) =
      some (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7, 8) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : b8 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest) =
      some (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8, 9) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8,
    vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, vAcc1]

theorem varintSlow_10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : b9 ≤ 0x7f#8) (hb9_lt : ¬ 2#8 ≤ b9) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) =
      some (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9, 10) := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4,
    hb5, hb6, hb7, hb8, hb9, hb9_lt, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3,
    vAcc2, vAcc1]

theorem varintSlow_none_1 (b0 : BitVec 8) (hb0 : ¬ b0 ≤ 0x7f#8) :
    varintSlow [b0] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0]

theorem varintSlow_none_2 (b0 b1 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) :
    varintSlow [b0, b1] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1]

theorem varintSlow_none_3 (b0 b1 b2 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2]

theorem varintSlow_none_4 (b0 b1 b2 b3 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8) (hb3 : ¬ b3 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3]

theorem varintSlow_none_5 (b0 b1 b2 b3 b4 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4]

theorem varintSlow_none_6 (b0 b1 b2 b3 b4 b5 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5]

theorem varintSlow_none_7 (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8) (hb6 : ¬ b6 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6]

theorem varintSlow_none_8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6, b7] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

theorem varintSlow_none_9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 : BitVec 8)
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8) :
    varintSlow [b0, b1, b2, b3, b4, b5, b6, b7, b8] = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]

theorem varintSlow_none_10_gt (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : ¬ b9 ≤ 0x7f#8) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7,
    hb8, hb9]

theorem varintSlow_none_10_ovf (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : BitVec 8) (rest : List (BitVec 8))
    (hb0 : ¬ b0 ≤ 0x7f#8) (hb1 : ¬ b1 ≤ 0x7f#8) (hb2 : ¬ b2 ≤ 0x7f#8)
    (hb3 : ¬ b3 ≤ 0x7f#8) (hb4 : ¬ b4 ≤ 0x7f#8) (hb5 : ¬ b5 ≤ 0x7f#8)
    (hb6 : ¬ b6 ≤ 0x7f#8) (hb7 : ¬ b7 ≤ 0x7f#8) (hb8 : ¬ b8 ≤ 0x7f#8)
    (hb9 : b9 ≤ 0x7f#8) (hb9_ge : 2#8 ≤ b9) :
    varintSlow (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: b9 :: rest) = none := by
  simp [varintSlow, varintSlowAux, toNat_le_0x7f_iff, two_le_toNat_iff, hb0, hb1, hb2, hb3, hb4,
    hb5, hb6, hb7, hb8, hb9, hb9_ge]

def CalleeSaved19_28 (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 19#5) ∧
  s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
  s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

def StateAt (s0 s : State) (pc : BitVec 64) : Prop :=
  s.pc = pc ∧ s.status = .Running ∧ s.sp = s0.sp - 64#64 ∧
    s.trace = s0.trace ∧ CalleeSaved19_28 s0 s

theorem ofNat_sub_ofNat_of_le {n k : Nat} (h : k ≤ n) (hlt : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : n % 2 ^ 64 = n := Nat.mod_eq_of_lt hlt
  have : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  have : (n - k) % 2 ^ 64 = n - k := Nat.mod_eq_of_lt (by omega)
  omega

theorem pointsToBytes_extract_at (ptr : BitVec 64) (bs pre rest : List (BitVec 8)) (b : BitVec 8)
    (k : Nat) (h : pre ++ b :: rest = bs) (hk : pre.length = k) :
    (ptr ↦ₛ bs) =
      (ptr ↦ₛ pre) ∗ ((ptr + BitVec.ofNat 64 k) ↦₈ b) ∗
        ((ptr + BitVec.ofNat 64 k + 1#64) ↦ₛ rest) := by
  subst h hk
  rw [pointsToBytes_append, pointsToBytes_cons]

attribute [local irreducible] Program.fnOff

/-- `decode_varint_slow::<&mut &[u8]>` satisfies `decodeVarintSlowSpec A` for any hook table `F`
given `subroutine_ok` for `DecodeError::from`. -/
theorem decodeVarintSlow_ok_F (b : BitVec 64) (A : RustAlloc) (F : String → Option (State → State))
    (hFrom : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics F))
      ((libsignalSessionCode.rebase b (Rust.withPanics F)).fnAddr decodeErrorFromName)
      (decodeErrorFromSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics F))
      ((libsignalSessionCode.rebase b (Rust.withPanics F)).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) := by
  unfold decodeVarintSlowSpec
  simp only [stackAt_varintSlow, sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff varintSlowName = num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>") := varintSlow_fnOff
  have hFromCall : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics F))
      ((libsignalSessionCode.rebase b (Rust.withPanics F)).fnAddr varintSlowName - 11672#64)
      (decodeErrorFromSpec A) := by
    have heq : (libsignalSessionCode.rebase b (Rust.withPanics F)).fnAddr varintSlowName - 11672#64 =
        (libsignalSessionCode.rebase b (Rust.withPanics F)).fnAddr decodeErrorFromName := by
      simp only [Program.fnAddr_rebase, varintSlow_fnOff, decodeErrorFrom_fnOff]
      bv_lin
    rw [heq]
    exact hFrom
  code_fetches CryptoVerification.libsignalSessionCode
    varintSlowBin b
    (Rust.withPanics F) hfn (num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) 448
  clear hfn hFrom
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics F)).fnAddr varintSlowName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics F)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨slotA, slot, ptr, bs⟩ := x
  dsimp only at *
  rw [show entry - 11672#64 = entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") - (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")) by bv_lin] at hFromCall
  have herr : ∀ {s : State} (k : Nat),
      varintSlow bs = none →
      min 10 bs.length = k →
      StateAt s0 s (entry + bv% (76)) →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s k hnone hk ⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩
    subst hk
    simp only [hnone]
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "<prost::error::DecodeError as core::convert::From<prost::error::DecodeErrorKind>>::from") - (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
    refine SepWPp.call_frame (x := (s0.sp - 64#64, 0x8000000000000001#64))
      (ret_pc := entry + bv% (92)) hFromCall
      (by simp only [arm64_norm]) (by simp only [arm64_norm, hruns])
      (by simp only [State.spAligned, arm64_norm, hsps]; exact hsp_align)
      (by simp only [arm64_norm])
      (by simp only [arm64_norm, hsps]; rfl)
      (⟨rfl, by decide⟩ : s0.sp - 64#64 = s0.sp - 64#64 ∧ KindNoHeap 0x8000000000000001#64)
      (by sep_focus)
      (fun _ _ _ _ hex => allowPanic_not_exited hex)
      (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm, htrs])) hpan) ?_
    intro sm hpcm hrunm hspm hcsm
    apply SepWPp.of_sepWP_ret
    simp only [memRegion_48_split, sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm, hsps]
    apply SepWP.exists_elim; intro v_err
    wp_steps
    wp_done
  have hok : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s (entry + bv% (52)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  have hok9 : ∀ {s : State} (v : BitVec 64) (k : Nat),
      varintSlow bs = some (v, k) →
      StateAt s0 s (entry + bv% (432)) ∧ s.readReg64 (Reg.gpr 1#5) = v →
      SepWPp prog (s0.readReg64 Reg.lr) s
        (slotA ↦₆₄ slot ∗
          slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
          (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k) ∗
          ptr ↦ₛ bs ∗ A.pool ∗
          stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
          memRegion (s0.sp - 56#64) 40 ∗
          (s0.sp - 64#64) ↦₆₄ v_stk_2 ∗
          (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
          (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5))
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R →
              sf.mem ⊨
                (∃∗ x, ∃∗ x_1, ∃∗ x_2,
                  ⌜sf.trace = s0.trace⌝ ∗
                    slotA ↦₆₄ slot ∗ ptr ↦ₛ bs ∗ A.pool ∗
                    (stackAt (s0.sp - 64#64) decodeErrorHookStack ∗
                      memRegion (s0.sp - 56#64) 40 ∗
                      (s0.sp - 64#64) ↦₆₄ x_2 ∗
                      (s0.sp - 16#64) ↦₆₄ x_1 ∗
                      (s0.sp - 8#64) ↦₆₄ x) ∗
                    match varintSlow bs with
                    | some (v, k) =>
                      ⌜sf.readReg64 Reg.x0 = 0#64 ∧ sf.readReg64 Reg.x1 = v⌝ ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 k) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k)
                    | none =>
                      ⌜sf.readReg64 Reg.x0 = 1#64 ∧ sf.readReg64 Reg.x1 ≠ 0#64⌝ ∗
                        decodeErrorAtStackLen A (sf.readReg64 Reg.x1) 0 ∗
                        slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length)) ∗
                        (slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length)) ∗ R) ∧
            sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          sf.mem ⊨ P_f ∗ R →
            sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) := by
    intro s v k hsome ⟨⟨hpcs, hruns, hsps, htrs, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hvregs⟩, hx1⟩
    simp only [hsome]
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done
  apply SepWPp.of_sepWP (mid := entry + bv% (20))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
  by_cases hbs0 : bs = []
  · have hlen0 : BitVec.ofNat 64 bs.length = 0#64 := by simp [hbs0]
    apply SepWPp.of_sepWP (mid := entry + bv% (76))
    wp_steps
    conv => arg 4; rw [show (slot ↦₆₄ ptr) = (slot ↦₆₄ (ptr + BitVec.ofNat 64 0)) by simp,
      show ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) =
        ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - 0)) by simp]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    apply herr 0 (by simp [hbs0, varintSlow, varintSlowAux]) (by simp [hbs0])
    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
      by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [CalleeSaved19_28, arm64_norm]⟩
  · obtain ⟨b0, bs1, hcons0'⟩ := List.exists_cons_of_ne_nil hbs0
    have hcons0 : ([] : List (BitVec 8)) ++ b0 :: bs1 = bs := hcons0'.symm
    clear hcons0' hbs0
    have hlen_ne0 : BitVec.ofNat 64 bs.length ≠ 0#64 :=
      ofNat_ne_ofNat (by rw [← hcons0]; simp) h (by decide)
    have hpts0 : (ptr ↦ₛ bs) = (ptr ↦₈ b0) ∗ ((ptr + 1#64) ↦ₛ bs1) := by
      rw [← hcons0, List.nil_append, pointsToBytes_cons]
    apply SepWPp.of_sepWP (mid := entry + bv% (48))
    conv => arg 4; rw [hpts0]
    wp_steps
    conv => arg 4; rw [← hpts0, ofNat_sub_ofNat_of_le (k := 1) (by rw [← hcons0]; simp) h]
    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    by_cases hb0 : b0 ≤ 0x7f#8
    · have hbit0 := getLsbD_7_of_le hb0
      apply SepWPp.of_sepWP (mid := entry + bv% (52))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      apply hok (vAcc1 b0) 1 (by rw [← hcons0]; exact varintSlow_1 b0 bs1 hb0)
      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [CalleeSaved19_28, arm64_norm]⟩,
        by simp only [arm64_norm, ← vAcc1_eq]⟩
    · have hbit0 := getLsbD_7_of_gt hb0
      apply SepWPp.of_sepWP (mid := entry + bv% (68))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
      by_cases hbs1 : bs1 = []
      · have hlen1 : BitVec.ofNat 64 bs.length = 1#64 := by
          rw [← hcons0, hbs1]; rfl
        apply SepWPp.of_sepWP (mid := entry + bv% (76))
        wp_steps
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        apply herr 1
          (by rw [← hcons0, hbs1]; exact varintSlow_none_1 b0 hb0)
          (by rw [← hcons0, hbs1]; rfl)
        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
          by simp only [arm64_norm], by simp only [arm64_norm],
          by simp only [CalleeSaved19_28, arm64_norm]⟩
      · obtain ⟨b1, bs2, hcons1'⟩ := List.exists_cons_of_ne_nil hbs1
        have hcons1 : [b0] ++ b1 :: bs2 = bs := by rw [← hcons0, hcons1']; rfl
        clear hcons1' hbs1 hcons0
        have hlen_ne1 : BitVec.ofNat 64 bs.length ≠ 1#64 :=
          ofNat_ne_ofNat (by rw [← hcons1]; simp) h (by decide)
        have hpts1 := pointsToBytes_extract_at ptr bs [b0] bs2 b1 1 hcons1 rfl
        apply SepWPp.of_sepWP (mid := entry + bv% (136))
        conv => arg 4; rw [hpts1]
        wp_steps
        conv => arg 4; rw [← hpts1, ofNat_sub_ofNat_of_le (k := 2) (by rw [← hcons1]; simp) h]
        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
        by_cases hb1 : b1 ≤ 0x7f#8
        · have hbit1 := getLsbD_7_of_le hb1
          apply SepWPp.of_sepWP (mid := entry + bv% (52))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          apply hok (vAcc2 b0 b1) 2 (by rw [← hcons1]; exact varintSlow_2 b0 b1 bs2 hb0 hb1)
          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
            by simp only [arm64_norm], by simp only [arm64_norm],
            by simp only [CalleeSaved19_28, arm64_norm]⟩,
            by simp only [arm64_norm, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
        · have hbit1 := getLsbD_7_of_gt hb1
          apply SepWPp.of_sepWP (mid := entry + bv% (140))
          wp_steps
          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
          by_cases hbs2 : bs2 = []
          · have hlen2 : BitVec.ofNat 64 bs.length = 2#64 := by
              rw [← hcons1, hbs2]; rfl
            apply SepWPp.of_sepWP (mid := entry + bv% (76))
            wp_steps
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            apply herr 2
              (by rw [← hcons1, hbs2]; exact varintSlow_none_2 b0 b1 hb0 hb1)
              (by rw [← hcons1, hbs2]; rfl)
            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
              by simp only [arm64_norm], by simp only [arm64_norm],
              by simp only [CalleeSaved19_28, arm64_norm]⟩
          · obtain ⟨b2, bs3, hcons2'⟩ := List.exists_cons_of_ne_nil hbs2
            have hcons2 : [b0, b1] ++ b2 :: bs3 = bs := by rw [← hcons1, hcons2']; rfl
            clear hcons2' hbs2 hcons1
            have hlen_ne2 : BitVec.ofNat 64 bs.length ≠ 2#64 :=
              ofNat_ne_ofNat (by rw [← hcons2]; simp) h (by decide)
            have hpts2 := pointsToBytes_extract_at ptr bs [b0, b1] bs3 b2 2 hcons2 rfl
            apply SepWPp.of_sepWP (mid := entry + bv% (172))
            conv => arg 4; rw [hpts2]
            wp_steps
            conv => arg 4; rw [← hpts2, ofNat_sub_ofNat_of_le (k := 3) (by rw [← hcons2]; simp) h]
            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
            by_cases hb2 : b2 ≤ 0x7f#8
            · have hbit2 := getLsbD_7_of_le hb2
              apply SepWPp.of_sepWP (mid := entry + bv% (52))
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              apply hok (vAcc3 b0 b1 b2) 3 (by rw [← hcons2]; exact varintSlow_3 b0 b1 b2 bs3 hb0 hb1 hb2)
              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                by simp only [arm64_norm], by simp only [arm64_norm],
                by simp only [CalleeSaved19_28, arm64_norm]⟩,
                by simp only [arm64_norm, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
            · have hbit2 := getLsbD_7_of_gt hb2
              apply SepWPp.of_sepWP (mid := entry + bv% (176))
              wp_steps
              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
              by_cases hbs3 : bs3 = []
              · have hlen3 : BitVec.ofNat 64 bs.length = 3#64 := by
                  rw [← hcons2, hbs3]; rfl
                apply SepWPp.of_sepWP (mid := entry + bv% (76))
                wp_steps
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                apply herr 3
                  (by rw [← hcons2, hbs3]; exact varintSlow_none_3 b0 b1 b2 hb0 hb1 hb2)
                  (by rw [← hcons2, hbs3]; rfl)
                exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                  by simp only [arm64_norm], by simp only [arm64_norm],
                  by simp only [CalleeSaved19_28, arm64_norm]⟩
              · obtain ⟨b3, bs4, hcons3'⟩ := List.exists_cons_of_ne_nil hbs3
                have hcons3 : [b0, b1, b2] ++ b3 :: bs4 = bs := by rw [← hcons2, hcons3']; rfl
                clear hcons3' hbs3 hcons2
                have hlen_ne3 : BitVec.ofNat 64 bs.length ≠ 3#64 :=
                  ofNat_ne_ofNat (by rw [← hcons3]; simp) h (by decide)
                have hpts3 := pointsToBytes_extract_at ptr bs [b0, b1, b2] bs4 b3 3 hcons3 rfl
                apply SepWPp.of_sepWP (mid := entry + bv% (208))
                conv => arg 4; rw [hpts3]
                wp_steps
                conv => arg 4; rw [← hpts3, ofNat_sub_ofNat_of_le (k := 4) (by rw [← hcons3]; simp) h]
                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                by_cases hb3 : b3 ≤ 0x7f#8
                · have hbit3 := getLsbD_7_of_le hb3
                  apply SepWPp.of_sepWP (mid := entry + bv% (52))
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  apply hok (vAcc4 b0 b1 b2 b3) 4 (by rw [← hcons3]; exact varintSlow_4 b0 b1 b2 b3 bs4 hb0 hb1 hb2 hb3)
                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                    by simp only [arm64_norm], by simp only [arm64_norm],
                    by simp only [CalleeSaved19_28, arm64_norm]⟩,
                    by simp only [arm64_norm, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                · have hbit3 := getLsbD_7_of_gt hb3
                  apply SepWPp.of_sepWP (mid := entry + bv% (212))
                  wp_steps
                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                  by_cases hbs4 : bs4 = []
                  · have hlen4 : BitVec.ofNat 64 bs.length = 4#64 := by
                      rw [← hcons3, hbs4]; rfl
                    apply SepWPp.of_sepWP (mid := entry + bv% (76))
                    wp_steps
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    apply herr 4
                      (by rw [← hcons3, hbs4]; exact varintSlow_none_4 b0 b1 b2 b3 hb0 hb1 hb2 hb3)
                      (by rw [← hcons3, hbs4]; rfl)
                    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                      by simp only [arm64_norm], by simp only [arm64_norm],
                      by simp only [CalleeSaved19_28, arm64_norm]⟩
                  · obtain ⟨b4, bs5, hcons4'⟩ := List.exists_cons_of_ne_nil hbs4
                    have hcons4 : [b0, b1, b2, b3] ++ b4 :: bs5 = bs := by rw [← hcons3, hcons4']; rfl
                    clear hcons4' hbs4 hcons3
                    have hlen_ne4 : BitVec.ofNat 64 bs.length ≠ 4#64 :=
                      ofNat_ne_ofNat (by rw [← hcons4]; simp) h (by decide)
                    have hpts4 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3] bs5 b4 4 hcons4 rfl
                    apply SepWPp.of_sepWP (mid := entry + bv% (244))
                    conv => arg 4; rw [hpts4]
                    wp_steps
                    conv => arg 4; rw [← hpts4, ofNat_sub_ofNat_of_le (k := 5) (by rw [← hcons4]; simp) h]
                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                    by_cases hb4 : b4 ≤ 0x7f#8
                    · have hbit4 := getLsbD_7_of_le hb4
                      apply SepWPp.of_sepWP (mid := entry + bv% (52))
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      apply hok (vAcc5 b0 b1 b2 b3 b4) 5 (by rw [← hcons4]; exact varintSlow_5 b0 b1 b2 b3 b4 bs5 hb0 hb1 hb2 hb3 hb4)
                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                        by simp only [arm64_norm], by simp only [arm64_norm],
                        by simp only [CalleeSaved19_28, arm64_norm]⟩,
                        by simp only [arm64_norm, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                    · have hbit4 := getLsbD_7_of_gt hb4
                      apply SepWPp.of_sepWP (mid := entry + bv% (248))
                      wp_steps
                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                      by_cases hbs5 : bs5 = []
                      · have hlen5 : BitVec.ofNat 64 bs.length = 5#64 := by
                          rw [← hcons4, hbs5]; rfl
                        apply SepWPp.of_sepWP (mid := entry + bv% (76))
                        wp_steps
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        apply herr 5
                          (by rw [← hcons4, hbs5]; exact varintSlow_none_5 b0 b1 b2 b3 b4 hb0 hb1 hb2 hb3 hb4)
                          (by rw [← hcons4, hbs5]; rfl)
                        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                          by simp only [arm64_norm], by simp only [arm64_norm],
                          by simp only [CalleeSaved19_28, arm64_norm]⟩
                      · obtain ⟨b5, bs6, hcons5'⟩ := List.exists_cons_of_ne_nil hbs5
                        have hcons5 : [b0, b1, b2, b3, b4] ++ b5 :: bs6 = bs := by rw [← hcons4, hcons5']; rfl
                        clear hcons5' hbs5 hcons4
                        have hlen_ne5 : BitVec.ofNat 64 bs.length ≠ 5#64 :=
                          ofNat_ne_ofNat (by rw [← hcons5]; simp) h (by decide)
                        have hpts5 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4] bs6 b5 5 hcons5 rfl
                        apply SepWPp.of_sepWP (mid := entry + bv% (280))
                        conv => arg 4; rw [hpts5]
                        wp_steps
                        conv => arg 4; rw [← hpts5, ofNat_sub_ofNat_of_le (k := 6) (by rw [← hcons5]; simp) h]
                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                        by_cases hb5 : b5 ≤ 0x7f#8
                        · have hbit5 := getLsbD_7_of_le hb5
                          apply SepWPp.of_sepWP (mid := entry + bv% (52))
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          apply hok (vAcc6 b0 b1 b2 b3 b4 b5) 6 (by rw [← hcons5]; exact varintSlow_6 b0 b1 b2 b3 b4 b5 bs6 hb0 hb1 hb2 hb3 hb4 hb5)
                          exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                            by simp only [arm64_norm], by simp only [arm64_norm],
                            by simp only [CalleeSaved19_28, arm64_norm]⟩,
                            by simp only [arm64_norm, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                        · have hbit5 := getLsbD_7_of_gt hb5
                          apply SepWPp.of_sepWP (mid := entry + bv% (284))
                          wp_steps
                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                          by_cases hbs6 : bs6 = []
                          · have hlen6 : BitVec.ofNat 64 bs.length = 6#64 := by
                              rw [← hcons5, hbs6]; rfl
                            apply SepWPp.of_sepWP (mid := entry + bv% (76))
                            wp_steps
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            apply herr 6
                              (by rw [← hcons5, hbs6]; exact varintSlow_none_6 b0 b1 b2 b3 b4 b5 hb0 hb1 hb2 hb3 hb4 hb5)
                              (by rw [← hcons5, hbs6]; rfl)
                            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                              by simp only [arm64_norm], by simp only [arm64_norm],
                              by simp only [CalleeSaved19_28, arm64_norm]⟩
                          · obtain ⟨b6, bs7, hcons6'⟩ := List.exists_cons_of_ne_nil hbs6
                            have hcons6 : [b0, b1, b2, b3, b4, b5] ++ b6 :: bs7 = bs := by rw [← hcons5, hcons6']; rfl
                            clear hcons6' hbs6 hcons5
                            have hlen_ne6 : BitVec.ofNat 64 bs.length ≠ 6#64 :=
                              ofNat_ne_ofNat (by rw [← hcons6]; simp) h (by decide)
                            have hpts6 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5] bs7 b6 6 hcons6 rfl
                            apply SepWPp.of_sepWP (mid := entry + bv% (316))
                            conv => arg 4; rw [hpts6]
                            wp_steps
                            conv => arg 4; rw [← hpts6, ofNat_sub_ofNat_of_le (k := 7) (by rw [← hcons6]; simp) h]
                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                            by_cases hb6 : b6 ≤ 0x7f#8
                            · have hbit6 := getLsbD_7_of_le hb6
                              apply SepWPp.of_sepWP (mid := entry + bv% (52))
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              apply hok (vAcc7 b0 b1 b2 b3 b4 b5 b6) 7 (by rw [← hcons6]; exact varintSlow_7 b0 b1 b2 b3 b4 b5 b6 bs7 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                              exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                by simp only [arm64_norm], by simp only [arm64_norm],
                                by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                by simp only [arm64_norm, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                            · have hbit6 := getLsbD_7_of_gt hb6
                              apply SepWPp.of_sepWP (mid := entry + bv% (320))
                              wp_steps
                              apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                              by_cases hbs7 : bs7 = []
                              · have hlen7 : BitVec.ofNat 64 bs.length = 7#64 := by
                                  rw [← hcons6, hbs7]; rfl
                                apply SepWPp.of_sepWP (mid := entry + bv% (76))
                                wp_steps
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                apply herr 7
                                  (by rw [← hcons6, hbs7]; exact varintSlow_none_7 b0 b1 b2 b3 b4 b5 b6 hb0 hb1 hb2 hb3 hb4 hb5 hb6)
                                  (by rw [← hcons6, hbs7]; rfl)
                                exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                  by simp only [arm64_norm], by simp only [arm64_norm],
                                  by simp only [CalleeSaved19_28, arm64_norm]⟩
                              · obtain ⟨b7, bs8, hcons7'⟩ := List.exists_cons_of_ne_nil hbs7
                                have hcons7 : [b0, b1, b2, b3, b4, b5, b6] ++ b7 :: bs8 = bs := by rw [← hcons6, hcons7']; rfl
                                clear hcons7' hbs7 hcons6
                                have hlen_ne7 : BitVec.ofNat 64 bs.length ≠ 7#64 :=
                                  ofNat_ne_ofNat (by rw [← hcons7]; simp) h (by decide)
                                have hpts7 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6] bs8 b7 7 hcons7 rfl
                                apply SepWPp.of_sepWP (mid := entry + bv% (352))
                                conv => arg 4; rw [hpts7]
                                wp_steps
                                conv => arg 4; rw [← hpts7, ofNat_sub_ofNat_of_le (k := 8) (by rw [← hcons7]; simp) h]
                                apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                by_cases hb7 : b7 ≤ 0x7f#8
                                · have hbit7 := getLsbD_7_of_le hb7
                                  apply SepWPp.of_sepWP (mid := entry + bv% (52))
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  apply hok (vAcc8 b0 b1 b2 b3 b4 b5 b6 b7) 8 (by rw [← hcons7]; exact varintSlow_8 b0 b1 b2 b3 b4 b5 b6 b7 bs8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                  exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                    by simp only [arm64_norm], by simp only [arm64_norm],
                                    by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                    by simp only [arm64_norm, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                                · have hbit7 := getLsbD_7_of_gt hb7
                                  apply SepWPp.of_sepWP (mid := entry + bv% (356))
                                  wp_steps
                                  apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                  by_cases hbs8 : bs8 = []
                                  · have hlen8 : BitVec.ofNat 64 bs.length = 8#64 := by
                                      rw [← hcons7, hbs8]; rfl
                                    apply SepWPp.of_sepWP (mid := entry + bv% (76))
                                    wp_steps
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    apply herr 8
                                      (by rw [← hcons7, hbs8]; exact varintSlow_none_8 b0 b1 b2 b3 b4 b5 b6 b7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7)
                                      (by rw [← hcons7, hbs8]; rfl)
                                    exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                      by simp only [arm64_norm], by simp only [arm64_norm],
                                      by simp only [CalleeSaved19_28, arm64_norm]⟩
                                  · obtain ⟨b8, bs9, hcons8'⟩ := List.exists_cons_of_ne_nil hbs8
                                    have hcons8 : [b0, b1, b2, b3, b4, b5, b6, b7] ++ b8 :: bs9 = bs := by rw [← hcons7, hcons8']; rfl
                                    clear hcons8' hbs8 hcons7
                                    have hlen_ne8 : BitVec.ofNat 64 bs.length ≠ 8#64 :=
                                      ofNat_ne_ofNat (by rw [← hcons8]; simp) h (by decide)
                                    have hpts8 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7] bs9 b8 8 hcons8 rfl
                                    apply SepWPp.of_sepWP (mid := entry + bv% (388))
                                    conv => arg 4; rw [hpts8]
                                    wp_steps
                                    conv => arg 4; rw [← hpts8, ofNat_sub_ofNat_of_le (k := 9) (by rw [← hcons8]; simp) h]
                                    apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                    by_cases hb8 : b8 ≤ 0x7f#8
                                    · have hbit8 := getLsbD_7_of_le hb8
                                      apply SepWPp.of_sepWP (mid := entry + bv% (52))
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      apply hok (vAcc9 b0 b1 b2 b3 b4 b5 b6 b7 b8) 9 (by rw [← hcons8]; exact varintSlow_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 bs9 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                      exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                        by simp only [arm64_norm], by simp only [arm64_norm],
                                        by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                        by simp only [arm64_norm, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127]⟩
                                    · have hbit8 := getLsbD_7_of_gt hb8
                                      apply SepWPp.of_sepWP (mid := entry + bv% (392))
                                      wp_steps
                                      apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                      by_cases hbs9 : bs9 = []
                                      · have hlen9 : BitVec.ofNat 64 bs.length = 9#64 := by
                                          rw [← hcons8, hbs9]; rfl
                                        apply SepWPp.of_sepWP (mid := entry + bv% (76))
                                        wp_steps
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        apply herr 9
                                          (by rw [← hcons8, hbs9]; exact varintSlow_none_9 b0 b1 b2 b3 b4 b5 b6 b7 b8 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8)
                                          (by rw [← hcons8, hbs9]; rfl)
                                        exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                          by simp only [arm64_norm], by simp only [arm64_norm],
                                          by simp only [CalleeSaved19_28, arm64_norm]⟩
                                      · obtain ⟨b9, bs10, hcons9'⟩ := List.exists_cons_of_ne_nil hbs9
                                        have hcons9 : [b0, b1, b2, b3, b4, b5, b6, b7, b8] ++ b9 :: bs10 = bs := by rw [← hcons8, hcons9']; rfl
                                        clear hcons9' hbs9 hcons8
                                        have hlen_ne9 : BitVec.ofNat 64 bs.length ≠ 9#64 :=
                                          ofNat_ne_ofNat (by rw [← hcons9]; simp) h (by decide)
                                        have hpts9 := pointsToBytes_extract_at ptr bs [b0, b1, b2, b3, b4, b5, b6, b7, b8] bs10 b9 9 hcons9 rfl
                                        apply SepWPp.of_sepWP (mid := entry + bv% (416))
                                        conv => arg 4; rw [hpts9]
                                        wp_steps
                                        conv => arg 4; rw [← hpts9, ofNat_sub_ofNat_of_le (k := 10) (by rw [← hcons9]; simp) h]
                                        apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                        by_cases hb9 : b9 ≤ 0x7f#8
                                        · have hbit9 := signExtend64_getLsbD_63_of_le hb9
                                          apply SepWPp.of_sepWP (mid := entry + bv% (424))
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          by_cases hb9_ovf : 2#8 ≤ b9
                                          · have hovf := byte9_hi_of_ge hb9_ovf
                                            apply SepWPp.of_sepWP (mid := entry + bv% (76))
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            apply herr 10
                                              (by rw [← hcons9]; exact varintSlow_none_10_ovf b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                              (by rw [← hcons9]; simp)
                                            exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                              by simp only [arm64_norm], by simp only [arm64_norm],
                                              by simp only [CalleeSaved19_28, arm64_norm]⟩
                                          · have hovf := byte9_hi_of_lt hb9 hb9_ovf
                                            apply SepWPp.of_sepWP (mid := entry + bv% (432))
                                            wp_steps
                                            apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                            apply hok9 (vAcc10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) 10
                                              (by rw [← hcons9]; exact varintSlow_10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb9_ovf)
                                            exact ⟨⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                              by simp only [arm64_norm], by simp only [arm64_norm],
                                              by simp only [CalleeSaved19_28, arm64_norm]⟩,
                                              by simp only [arm64_norm, vAcc10, vAcc9, vAcc8, vAcc7, vAcc6, vAcc5, vAcc4, vAcc3, vAcc2, ← vAcc1_eq, zeroExtend64_and_127, signExtend64_shiftLeft_63]⟩
                                        · have hbit9 := signExtend64_getLsbD_63_of_gt hb9
                                          apply SepWPp.of_sepWP (mid := entry + bv% (76))
                                          wp_steps
                                          apply SepWP.done (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
                                          apply herr 10
                                            (by rw [← hcons9]; exact varintSlow_none_10_gt b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 bs10 hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9)
                                            (by rw [← hcons9]; simp)
                                          exact ⟨by simp only [arm64_norm], by simp only [arm64_norm, hrun],
                                            by simp only [arm64_norm], by simp only [arm64_norm],
                                            by simp only [CalleeSaved19_28, arm64_norm]⟩


theorem decodeVarintSlow_ok_aux_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) :=
  decodeVarintSlow_ok_F b A _ (decodeErrorFrom_ok_aux_trap b C A abs hA)

theorem decodeVarintSlow_ok_aux (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (hA : AllocHooks A abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr varintSlowName)
      (decodeVarintSlowSpec A) := by
  rw [← (trapsOnly_trTrap_kit b C ctl abs).fnAddr varintSlowName]
  exact subroutine_ok_kit_of_trTrap (decodeVarintSlow_ok_aux_trap b C A abs hA)

end CryptoVerification.LibsignalTripleRatchet.InImage.VarintSlow
