/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Outer
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# `<PolyEncoder>::into_pb`: Budget-Threaded Placed Dispatch

Placed `.points` and `.polys` branch dispatch lemmas for Block `375` preserving `VmPreserved` and
`AllocCallPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.OuterBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement blkPC_375 blkPl_375)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb (
  pointsTo64_off48_split32 pointsTo64_split32_tag
)
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)

section PlacedDispatch

variable [LibsignalPlacement]

/-- Branch dispatch for `.points` (`+88 -> +452`) in `[LibsignalPlacement]`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem into_pb_dispatch_points_placed
    {ext : String → Option (State → State)}
    (s0 : State) (fsp out encA ptr_points ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (idx : BitVec 32)
    (v0 v1 v2 v3 v4 v5 v6 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = encA)
    (hx20 : s.readReg64 .x20 = out)
    (hx21 : s.readReg64 .x21 = ptr_points)
    (hx0 : s.readReg64 .x0 = ptr_polys)
    (hx22 : s.readReg64 .x22 = idx.zeroExtend 64)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 452#64) s
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
        ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
        ((fsp + 48#64) ↦₆₄ v6) ∗ (encA ↦₆₄ 0#64) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ((Pm ⊢ (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          memRegion encA 8 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = encA ∧ sm.readReg64 .x20 = out ∧
        sm.readReg64 .x22 = encA + 8#64 ∧ sm.readReg64 .x23 = 0#64 ∧
        sm.readReg64 .x24 = 24#64 ∧ sm.readReg64 .x25 = 1#64 ∧
        sm.trace = s0.trace ∧ AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)) := by
  rcases hacp with ⟨hfs, _, hsig, htp, hbrk0, horacle, hsymtab⟩
  by_vm_steps (
    conv => arg 4; rw [pointsTo64_off48_split32 fsp v6, CryptoVerification.SpqrV1.Poly.EncoderIntoPb.pointsTo64_split32 encA 0#64]
    wp_steps
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans
          (pointsTo64_split32_tag encA 0#64
            ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
              ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗ Frame))
          (Entails.of_eq (by sep_ac_rfl)))) ?_
    dsimp only [AllocCallPreserved]
    wp_done
  )

/-- Branch dispatch for `.polys` (`+88 -> +188`) in `[LibsignalPlacement]`, preserving `VmPreserved` and `AllocCallPreserved`. -/
theorem into_pb_dispatch_polys_placed
    {ext : String → Option (State → State)}
    (s0 : State) (fsp out encA ptr_points ptr_polys : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (idx : BitVec 32)
    (v0 v1 v2 v3 v4 v5 v6 : BitVec 64)
    (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_375).base + 88#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx29 : s.readReg64 .x29 = fsp + 128#64)
    (hx19 : s.readReg64 .x19 = encA)
    (hx20 : s.readReg64 .x20 = out)
    (hx21 : s.readReg64 .x21 = ptr_points)
    (hx0 : s.readReg64 .x0 = ptr_polys)
    (hx22 : s.readReg64 .x22 = idx.zeroExtend 64)
    (htrace : s.trace = s0.trace)
    (hacp : AllocCallPreserved s0 s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      ((blkPl_375).base + 188#64) s
      ((fsp ↦₆₄ v0) ∗ ((fsp + 8#64) ↦₆₄ v1) ∗ ((fsp + 16#64) ↦₆₄ v2) ∗
        ((fsp + 24#64) ↦₆₄ v3) ∗ ((fsp + 32#64) ↦₆₄ v4) ∗ ((fsp + 40#64) ↦₆₄ v5) ∗
        ((fsp + 48#64) ↦₆₄ v6) ∗ (encA ↦₆₄ 1#64) ∗ Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        ((Pm ⊢
          (fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
          ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
          ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗
          memRegion encA 8 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x29 = fsp + 128#64 ∧
        sm.readReg64 .x19 = encA ∧
        sm.readReg64 .x20 = out ∧
        sm.readReg64 .x22 = encA + 8#64 ∧
        sm.readReg64 .x23 = 0#64 ∧
        sm.readReg64 .x28 = 0#64 ∧
        sm.readReg64 .x24 = fsp ∧
        sm.readReg64 .x25 = 24#64 ∧
        sm.readReg64 .x26 = 1#64 ∧
        sm.trace = s0.trace ∧
        AllocCallPreserved s0 sm ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)) := by
  rcases hacp with ⟨hfs, _, hsig, htp, hbrk0, horacle, hsymtab⟩
  by_vm_steps (
    conv => arg 4; rw [pointsTo64_off48_split32 fsp v6, CryptoVerification.SpqrV1.Poly.EncoderIntoPb.pointsTo64_split32 encA 1#64]
    wp_steps
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (by sep_ac_rfl))
        (Entails.trans
          (pointsTo64_split32_tag encA 1#64
            ((fsp ↦₆₄ 16#64) ∗ ((fsp + 8#64) ↦₆₄ ptr_points) ∗ ((fsp + 16#64) ↦₆₄ 0#64) ∗
              ((fsp + 24#64) ↦₆₄ 16#64) ∗ ((fsp + 32#64) ↦₆₄ ptr_polys) ∗ ((fsp + 40#64) ↦₆₄ 0#64) ∗
              ((fsp + 48#64) ↦₃₂ idx) ∗ ((fsp + 52#64) ↦₃₂ v6.extractLsb' 32 32) ∗ Frame))
          (Entails.of_eq (by sep_ac_rfl)))) ?_
    dsimp only [AllocCallPreserved]
    wp_done
  )

end PlacedDispatch

end LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.OuterBudget
