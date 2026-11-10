/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply

/-!
# `HookSat`-backed Read-Only Second-Slice `ct_eq` (`CtEqROSat`, Block `213`)

Relocatable `[LibsignalPlacement]` contracts for `<[u8] as subtle::ConstantTimeEq>::ct_eq`
(Block `213`) with read-only second slice (`p2 ↦ᵣ k2`) under
`HookSat H lsBlackBoxU8Sym blackBoxSpecSat`:
- tight `+16 B` (`64` B) contracts (`ctEqSliceRO{,Budget}Spec16`, `ctEqSliceROMem{,Budget}Spec16`),
- `extHookStack32 = 16384` B contracts (`ctEqSliceROSpecExt`, `withVmPreserved ctEqSliceROSpecExt`).
-/

public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat

open Arm64 ProofLib
open CryptoVerification
  (LibsignalPlacement blkLib_eq_213 blkPC_213 blkPl_213 libsignalSessionImage lsBlackBoxU8Sym
   ls_externAt?_of_mem lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open LibsignalBinary.Heap (VmPreserved VmPreserved.refl VmPreserved.trans)
open LibsignalBinary.Heap.SpecBudget (subroutine_ok_of_withVmPreserved withVmPreserved)
open CryptoVerification.LibsignalSession.FindReceiverChainIndex
  (ctEq_pre_rearrange_ext32 ct_eq_bool_32_u8_ext32 extHookStack32 fnFrameBytes_ctEqName_ext32
   ite_one_zero_and_8_ext32 ite_one_zero_and_one_8_ext32 pointsToBytes32
   pointsToBytes_eq_pointsToBytes32 setWidth32_and_4294967297_ext32 setWidth8_and32_ext32
   setWidth8_and64_ext32 setWidth8_ite_1_0_32_ext32 setWidth8_ite_prop_1_0_ext32
   setWidth8_setWidth32_ext32 setWidth8_zext64_32_ext32 sp_sub48_aligned_ext32)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
  (ctEqName ctEqSliceROSpecExt pointsToBytesRO32 pointsToBytesRO_eq_pointsToBytesRO32)
open LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.CtEqSat
  (blackBoxSpecSat memRegion_64_eq_ctEqFrame_16 step_blackBox_sat step_blackBox_tail_sat)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)

/-! ## 1. Tight `+16 B` (`64` B) Read-Only Second-Slice Specs -/

/-- Read-only second-slice `ct_eq` contract extended with `16` B below `ct_eq`'s 48-byte frame. -/
@[expose] noncomputable def ctEqSliceROSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
      stackAt (sp - 48#64) 16
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗
      stackFrameFor libsignalSessionImage "<[u8] as subtle::ConstantTimeEq>::ct_eq" sp ∗
      stackAt (sp - 48#64) 16

/-- `VmPreserved`-strengthened `ctEqSliceROSpec16`. -/
@[expose] noncomputable def ctEqSliceROBudgetSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceROSpec16

/-- Image-free read-only second-slice `ct_eq` contract with `memRegion (sp - 64#64) 64` (`48 + 16` B). -/
@[expose] def ctEqSliceROMemSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (p1, k1, p2, k2, sp) s =>
    ⌜s.readReg64 .x0 = p1 ∧ s.readReg64 .x1 = p2 ∧ s.sp = sp ∧ k1.length = 32 ∧ k2.length = 32⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 64#64) 64
  post := fun (p1, k1, p2, k2, sp) s0 sf =>
    ⌜sf.readReg64 .x0 = (if k1 = k2 then 1#64 else 0#64) ∧ sf.trace = s0.trace⌝ ∗
      (p1 ↦ₛ k1) ∗ (p2 ↦ᵣ k2) ∗ memRegion (sp - 64#64) 64

/-- `VmPreserved`-strengthened `ctEqSliceROMemSpec16`. -/
@[expose] def ctEqSliceROMemBudgetSpec16 :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8) × BitVec 64) :=
  withVmPreserved ctEqSliceROMemSpec16

/-! ## 2. Block `213` Read-Only Second-Slice Proofs under `blackBoxSpecSat` -/

private theorem zeroExtend64_ite_prop_1_0_8 (P : Prop) [Decidable P] :
    BitVec.zeroExtend 64 (if P then 1#8 else 0#8) = if P then 1#64 else 0#64 := by
  split <;> rfl

private theorem setWidth32_ite_1_0_64 (P : Prop) [Decidable P] :
    BitVec.setWidth 32 (if P then 1#64 else 0#64) = if P then 1#32 else 0#32 := by
  split <;> rfl

section VmStepping

attribute [local irreducible] Program.fnOff VmPreserved

attribute [local simp, local wp_norm, local arm64_norm]
  setWidth8_ite_prop_1_0_ext32 setWidth8_ite_1_0_32_ext32 setWidth8_zext64_32_ext32
  setWidth8_setWidth32_ext32 setWidth8_and64_ext32 setWidth8_and32_ext32
  ite_one_zero_and_8_ext32 setWidth32_and_4294967297_ext32 ite_one_zero_and_one_8_ext32
  fnFrameBytes_ctEqName_ext32

set_option hygiene false in
local macro "wp_seg_bb_213 " : tactic =>
  `(tactic| (
    apply sepWP_seg_ls_vm (Q := (blkPC_213).rebase (blkPl_213).base (hooksException H))
      blkLib_eq_213 (mid := lsρ lsBlackBoxU8Sym)
    intro _m_strip
    wp_steps
    refine SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
    have hvm_seg : VmPreserved _ _ := _hnsp.toVmPreserved (by wp_norm_lhs)
    simp only [State.setMem_setMem] at hvm_seg ⊢
    have hvm_cur : VmPreserved s0 _ := hvm_bb.trans hvm_seg
    clear hvm_seg _hnsp _m_strip
  ))

set_option hygiene false in
local macro "wp_black_box_sat " hbb:ident hal:ident : tactic =>
  `(tactic| (
    refine step_blackBox_sat $hbb $hal hvm_cur
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) ?_
    clear hvm_cur
    try clear _m_real
    try clear hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb hvm_bb s_bb
    intro s_bb hpc_bb hrun_bb hsp_bb hx0_bb hx19_bb hx19_8_bb hx20_bb hx21_8_bb hx22_8_bb hx23_bb hx24_bb hx25_bb hx26_bb hx27_bb hx28_bb hx29_bb hvregs_bb htr_bb hvm_bb
  ))

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1600000 in
/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for `<[u8] as ConstantTimeEq>::ct_eq`
(Block `213`) with read-only second operand and `16` B below `ct_eq`'s frame
(`ctEqSliceROBudgetSpec16`). -/
theorem ct_eq_ro_placed_vm_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceROBudgetSpec16 := by
  rcases h_bb with ⟨f_bb, hfH, hfOk⟩
  have hbb : subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (lsρ lsBlackBoxU8Sym)
      blackBoxSpecSat :=
    subroutine_ok_of_hookOk ((ls_externAt?_of_mem).trans hfH) hfOk
  simp only [ctEqSliceROBudgetSpec16, withVmPreserved, ctEqSliceROSpec16]
  wp_init x s0
  obtain ⟨p1, k1, p2, k2, sp⟩ := x
  dsimp only at *
  subst h_1 h_2 h_3
  have hal_sub48 : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    sp_sub48_aligned_ext32 hsp_align
  have h_slices :
      pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) k1 ∗
        pointsToBytesRO32 (s0.readReg64 (Reg.gpr 1#5)) k2 =
      ((s0.readReg64 (Reg.gpr 0#5)) ↦ₛ k1) ∗ ((s0.readReg64 (Reg.gpr 1#5)) ↦ᵣ k2) := by
    rw [pointsToBytes_eq_pointsToBytes32 (s0.readReg64 (Reg.gpr 0#5)) h_4,
        pointsToBytesRO_eq_pointsToBytesRO32 (s0.readReg64 (Reg.gpr 1#5)) h]
  rw [ctEq_pre_rearrange_ext32]
  conv =>
    arg 4
    rw [← h_slices]
    unfold pointsToBytes32 pointsToBytesRO32
    simp only [sepConj_assoc]
  have hvm_bb : VmPreserved s0 s0 := VmPreserved.refl s0
  iterate 32 (wp_seg_bb_213; wp_black_box_sat hbb hal_sub48)
  clear hx19_bb
  wp_seg_bb_213
  conv =>
    arg 5; ext sf P_f
    rw [← zeroExtend64_ite_prop_1_0_8 (k1 = k2)]
  refine step_blackBox_tail_sat hbb hsp_align hvm_cur
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    (by wp_norm_lhs) (by wp_norm_lhs) (ct_eq_bool_32_u8_ext32 h_4 h) ?_
  rw [← h_slices]
  unfold pointsToBytes32 pointsToBytesRO32
  simp only [sepConj_assoc]

end VmStepping

/-- Relocatable `[LibsignalPlacement]` contract for `<[u8] as ConstantTimeEq>::ct_eq` (Block `213`)
with read-only second operand on `ctEqSliceROSpec16`. -/
theorem ct_eq_ro_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceROSpec16 :=
  subroutine_ok_of_withVmPreserved (ct_eq_ro_placed_vm_ok_16_sat h_bb)

/-- `withLsCodeLoaded` corollary of `ct_eq_ro_placed_vm_ok_16_sat`. -/
theorem ct_eq_ro_placed_vm_ok_16_withLsCodeLoaded_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROBudgetSpec16) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_placed_vm_ok_16_sat h_bb)

/-- `withLsCodeLoaded` corollary of `ct_eq_ro_placed_ok_16_sat`. -/
theorem ct_eq_ro_placed_ok_16_withLsCodeLoaded_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROSpec16) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_placed_ok_16_sat h_bb)

/-- Image-free `VmPreserved` contract for read-only second-slice `ct_eq` (Block `213`) on
`ctEqSliceROMemBudgetSpec16` (`64` B). -/
theorem ct_eq_ro_mem_placed_vm_ok_16_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      ctEqSliceROMemBudgetSpec16 := by
  refine subroutine_ok_map (ct_eq_ro_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  refine ⟨(p1, k1, p2, k2, sp), R, ?_, ?_⟩
  · simpa only [ctEqSliceROMemBudgetSpec16, ctEqSliceROBudgetSpec16, withVmPreserved,
      ctEqSliceROMemSpec16, ctEqSliceROSpec16, memRegion_64_eq_ctEqFrame_16 sp, sepConj_assoc]
      using hpre
  · intro sf hpost
    simpa only [ctEqSliceROMemBudgetSpec16, ctEqSliceROBudgetSpec16, withVmPreserved,
      ctEqSliceROMemSpec16, ctEqSliceROSpec16, memRegion_64_eq_ctEqFrame_16 sp, sepConj_assoc]
      using hpost

/-- Image-free contract for read-only second-slice `ct_eq` (Block `213`) on `ctEqSliceROMemSpec16`. -/
theorem ct_eq_ro_mem_placed_ok_16_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceROMemSpec16 :=
  subroutine_ok_of_withVmPreserved (ct_eq_ro_mem_placed_vm_ok_16_sat h_bb)

/-- `withLsCodeLoaded` corollary of `ct_eq_ro_mem_placed_vm_ok_16_sat`. -/
theorem ct_eq_ro_mem_placed_vm_ok_16_withLsCodeLoaded_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROMemBudgetSpec16) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_mem_placed_vm_ok_16_sat h_bb)

/-- `withLsCodeLoaded` corollary of `ct_eq_ro_mem_placed_ok_16_sat`. -/
theorem ct_eq_ro_mem_placed_ok_16_withLsCodeLoaded_sat [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withLsCodeLoaded lsmpl ctEqSliceROMemSpec16) :=
  subroutine_ok_withLsCodeLoaded_of_plain (ct_eq_ro_mem_placed_ok_16_sat h_bb)

/-- Relocatable `[LibsignalPlacement]` `VmPreserved` contract for read-only second-slice `ct_eq`
(Block `213`) on `withVmPreserved ctEqSliceROSpecExt` (`48 + 16384` B). -/
theorem ct_eq_ro_placed_vm_ok_ext_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base
      (withVmPreserved ctEqSliceROSpecExt) := by
  refine subroutine_ok_map (ct_eq_ro_placed_vm_ok_16_sat h_bb) ?_
    (fun _ _ _ _ _ hp => not_satisfies_false_sepConj hp)
    (fun _ _ _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => False.elim (not_satisfies_false_sepConj ho))
  rintro ⟨p1, k1, p2, k2, sp⟩ R s0 hpre
  have hstk : stackAt (sp - 48#64) extHookStack32 =
      memRegion ((sp - 48#64) - 16384#64) 16368 ∗ stackAt (sp - 48#64) 16 :=
    ProofLib.stackAt_split_bottom (sp - 48#64) 16 16368 (by decide)
  refine ⟨(p1, k1, p2, k2, sp), memRegion ((sp - 48#64) - 16384#64) 16368 ∗ R, ?_, ?_⟩
  · dsimp only [withVmPreserved, ctEqSliceROSpecExt, ctEqName, ctEqSliceROBudgetSpec16,
      ctEqSliceROSpec16] at hpre ⊢
    rw [hstk] at hpre
    convert hpre using 1; sep_ac_rfl
  · intro sf hpost
    dsimp only [withVmPreserved, ctEqSliceROSpecExt, ctEqName, ctEqSliceROBudgetSpec16,
      ctEqSliceROSpec16] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨hvm, ⟨hx0, htr⟩, hmem⟩
    refine ⟨hvm, ⟨by rw [hx0, setWidth32_ite_1_0_64], htr⟩, ?_⟩
    rw [hstk]
    convert hmem using 1; sep_ac_rfl

/-- Relocatable `[LibsignalPlacement]` contract for read-only second-slice `ct_eq` (Block `213`)
on `ctEqSliceROSpecExt` (`48 + 16384` B). -/
theorem ct_eq_ro_placed_ok_ext_sat [LibsignalPlacement] {H : String → Option (State → State)}
    (h_bb : HookSat H lsBlackBoxU8Sym blackBoxSpecSat) :
    subroutine_ok ((blkPC_213).rebase (blkPl_213).base H) (blkPl_213).base ctEqSliceROSpecExt :=
  subroutine_ok_of_withVmPreserved (ct_eq_ro_placed_vm_ok_ext_sat h_bb)

end LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqROSat
