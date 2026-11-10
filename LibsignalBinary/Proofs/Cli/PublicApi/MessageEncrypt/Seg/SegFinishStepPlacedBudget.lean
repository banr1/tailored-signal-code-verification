/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegFinish` Steppers (`+0xe88..+0xf9c`)

`VmPreserved`-carrying `SepWP` stepping lemmas on `lsProg_464 Hk` (`blkPl_464`) for
`segFinish_placed_okV` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishStepPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap (VmPreserved)
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem finish_stage_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp cap w0 w1 w2 w3 : BitVec 64} {b469 : BitVec 8}
    {bws dws : List (BitVec 64)}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hcap : cap.toNat < 2 ^ 63)
    (hpc : s.pc = encEntryPlaced + 0xe88#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xef0#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x469#64) ↦₈ b469) ∗
        words64At (sp + 0x9d0#64) dws)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w2 ∧
        sf.readReg64 .x22 = w0 ∧
        sf.readReg64 .x23 = w3 ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x27 = w1 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ 0#8) ∗
          words64At (sp + 0x9d0#64) bws)) := by
  subst hsp
  have hne : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap
  have hne' : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rw [words64At_27 (s.sp + 0x390#64) hbws,
        words64At_27 (s.sp + 0x9d0#64) hdws]
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    refine ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, hx26, rfl,
      rfl, rfl, rfl, rfl, ?_⟩
    rw [words64At_27 (s.sp + 0x9d0#64) hbws]
    simp only [BitVec.add_assoc, BitVec.reduceAdd])

/-- Step `+0xef0..+0xef4` (`ldr x0, [sp, #0x50]; bl drop_glue<SessionStructure>[local#2]`) up to
`lsmpl.base 442`, preserving `VmPreserved`. -/
theorem finish_dropSs_placed_step_pre [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xef0#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (lsmpl.base 442) s
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x128#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xef8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) := by
  subst hsp
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩)

theorem finish_prev_zero_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp prevPtr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xef8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xf58#64) s
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩)

set_option maxHeartbeats 800000 in
/-- Step `+0xef8..+0xf24` when `prevCap ≠ 0#64` (`previous_sessions` empty `Vec` buffer deallocation
setup) up to `lsρ lsRustDeallocSym`, preserving `VmPreserved`. -/
theorem finish_prev_nz_placed_step_pre [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp prevCap prevPtr : BitVec 64}
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = encEntryPlaced + 0xef8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (lsρ lsRustDeallocSym) s
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = prevPtr ∧
        (sf.readReg64 .x1).toNat = prevCap.toNat * 24 ∧
        (sf.readReg64 .x2).toNat = 8 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xf58#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hmul24 := mul24_shift_toNat hcap_lt
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, hmul24, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 800000 in
theorem finish_copyAtF58_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks} {sp w0 : BitVec 64}
    {bws dws : List (BitVec 64)} {s : State}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hpc : s.pc = encEntryPlaced + 0xf58#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx22 : s.readReg64 .x22 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5f8#64) s
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        sf.readReg64 .x22 = w0 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) bws)) := by
  subst hsp
  have hw0_ne' : w0 + 2#64 ≠ 0#64 := beq_eq_false_iff_ne.mp hw0_ne
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rw [words64At_27 (s.sp + 0x9d0#64) hbws,
        words64At_27 (s.sp + 0x4a0#64) hdws]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    refine ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, hx28, hx22, rfl, rfl,
      rfl, rfl, ?_⟩
    rw [words64At_27 (s.sp + 0x4a0#64) hbws]
    simp only [BitVec.add_assoc, BitVec.reduceAdd])

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishStepPlacedBudget
