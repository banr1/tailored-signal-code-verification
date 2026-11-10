/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopSegs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.ConstsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Previous-Session Loop Head (`+0x1e78 → +0x1ee8`)

Relocatable (`[LibsignalPlacement]`) statement and proof for the `previous_sessions` loop head
(`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x1ee8`) on `lsProg_518` when `len = 1#64`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches SepProp
open CryptoVerification
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CliHandshake.RespClosurePlaced

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalPlacement]` statement for the loop head
(`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x1ee8`) on `lsProg_518 ext` when `len = 1#64`. -/
def OverPrevLoopHeadCliPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ (ext : String → Option (State → State))
    (s : State) (coroPtr prevCap prevPtr u3e0 wd0 : BitVec 64),
    s.pc = (blkPl_518).base + 0x1e78#64 →
    s.status = .Running →
    (s.sp &&& 15#64 == 0#64) = true →
    s.readReg64 .x19 = coroPtr →
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ee8#64) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64))) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = prevPtr ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)

set_option maxHeartbeats 800000 in
/-- Loop head (`(blkPl_518).base + 0x1e78 → (blkPl_518).base + 0x1ee8`) on `lsProg_518 ext` when `len = 1#64`. -/
theorem overPrevLoop_head_cli_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (coroPtr prevCap prevPtr u3e0 wd0 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x1e78#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1ee8#64) s
      (((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
       ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u3e0) ∗ ((s.sp + 0xd0#64) ↦₆₄ wd0))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0xe0#64) ↦₆₄ prevCap) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevPtr) ∗
          ((coroPtr + 0xf0#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
          ((s.sp + 0xd0#64) ↦₆₄ (prevPtr + 24#64))) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧ s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = s.sp + 0x930#64 ∧ s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧ s1.readReg64 .x26 = 0#64 ∧
        s1.readReg64 .x27 = prevPtr ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨Entails.refl _, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem overPrevLoopHead_cli_placed_ok [LibsignalPlacement] : OverPrevLoopHeadCliPlacedStmt :=
  overPrevLoop_head_cli_placed_wp

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
