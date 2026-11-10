/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable Basic-Block Step Lemmas for `segTrust` (`+0xa70..+0xd40`)
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem getLsbD0_of_setWidth8_placed {w : BitVec 64} {d : BitVec 8} (h : w.setWidth 8 = d) :
    w.getLsbD 0 = d.getLsbD 0 := by
  subst h; simp

/-- E7 part 1 (`+0xa70..+0xa84`) on `lsProg_464 Hk`: load arguments from frame spills and call `shimAddr`. -/
theorem step_a70_to_a84_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {remA idA id_vt shimAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xa70#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (lsProg_464 Hk) shimAddr s
      (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
       ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
       ((id_vt + 0x30#64) ↦₆₄ᵣ shimAddr))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
          ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
          ((id_vt + 0x30#64) ↦₆₄ᵣ shimAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = idA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x350#64 ∧ sf.readReg64 .x3 = 0#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xa88#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7 part 2 (`+0xa88..+0xa9c`) on `lsProg_464 Hk`: store future box/vtable and call `pollAddr`. -/
theorem step_a88_to_a9c_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box u470 u478 futVtAddr pollAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xa88#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = box)
    (hx1 : s.readReg64 .x1 = futVtAddr) :
    SepWP (lsProg_464 Hk) pollAddr s
      (((s.sp + 0x470#64) ↦₆₄ u470) ∗
       ((s.sp + 0x478#64) ↦₆₄ u478) ∗
       ((futVtAddr + 0x18#64) ↦₆₄ᵣ pollAddr))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ futVtAddr) ∗
          ((futVtAddr + 0x18#64) ↦₆₄ᵣ pollAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = s.sp + 0x480#64 ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xaa0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7 + E7r part 1 (`+0xaa0..+0xaa8`, `+0xb7c..+0xbac`) on `lsProg_464 Hk`. -/
theorem step_aa0_to_bac_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box w0 w1 w2 w3 w4 w5 u970 u978 u980 futVtAddr futDropAddr : BitVec 64}
    (hdrop : futDropAddr ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xaa0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hw0 : w0 = 0xFFFFFFFFFFFFFFFE#64 ∨ w0 = 0x800000000000001A#64) :
    SepWP (lsProg_464 Hk) futDropAddr s
      (((s.sp + 0x470#64) ↦₆₄ box) ∗
       ((s.sp + 0x478#64) ↦₆₄ futVtAddr) ∗
       ((s.sp + 0x580#64) ↦₆₄ w0) ∗
       ((s.sp + 0x588#64) ↦₆₄ w1) ∗
       ((s.sp + 0x590#64) ↦₆₄ w2) ∗
       ((s.sp + 0x598#64) ↦₆₄ w3) ∗
       ((s.sp + 0x5a0#64) ↦₆₄ w4) ∗
       ((s.sp + 0x5a8#64) ↦₆₄ w5) ∗
       ((s.sp + 0x970#64) ↦₆₄ u970) ∗
       ((s.sp + 0x978#64) ↦₆₄ u978) ∗
       ((s.sp + 0x980#64) ↦₆₄ u980) ∗
       (futVtAddr ↦₆₄ᵣ futDropAddr))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x470#64) ↦₆₄ box) ∗
          ((s.sp + 0x478#64) ↦₆₄ futVtAddr) ∗
          ((s.sp + 0x580#64) ↦₆₄ w0) ∗
          ((s.sp + 0x588#64) ↦₆₄ w1) ∗
          ((s.sp + 0x590#64) ↦₆₄ w2) ∗
          ((s.sp + 0x598#64) ↦₆₄ w3) ∗
          ((s.sp + 0x5a0#64) ↦₆₄ w4) ∗
          ((s.sp + 0x5a8#64) ↦₆₄ w5) ∗
          ((s.sp + 0x970#64) ↦₆₄ w3) ∗
          ((s.sp + 0x978#64) ↦₆₄ w4) ∗
          ((s.sp + 0x980#64) ↦₆₄ w5) ∗
          (futVtAddr ↦₆₄ᵣ futDropAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = futVtAddr ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x24 = box ∧ sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xbb0#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (futDropAddr == 0#64) = false := by simp [hdrop]
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (rcases hw0 with rfl | rfl <;> wp_steps <;>
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7r part 2 (`+0xbb0..+0xbc0`) on `lsProg_464 Hk`: read size/align from vtable and call `__rust_dealloc`. -/
theorem step_bb0_to_bc0_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box futVtAddr boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xbb0#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = futVtAddr)
    (hx24 : s.readReg64 .x24 = box) :
    SepWP (lsProg_464 Hk) (lsρ lsRustDeallocSym) s
      (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xbc4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7r `Err` branch (`+0xbc4..+0xbc8`) on `lsProg_464 Hk`: jump to T5 store `+0xc20`. -/
theorem step_bc4_err_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    (hpc : s.pc = encEntryPlaced + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xc20#64) s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7r `Ok(true)` branch (`+0xbc4..+0xbd0`) on `lsProg_464 Hk`: fall through to `+0xbd4` (`SaveStateVPlaced`). -/
theorem step_bc4_ok_true_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {w1 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xbc4#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 1#8) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xbd4#64) s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.sp + 0x8b8#64 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8_placed hw1
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E7r `Ok(false)` + E9 part 1 (`+0xbc4..+0xbd0`, `+0xc78..+0xc84`, `+0xd0c..+0xd18`) on `lsProg_464 Hk`:
branch on `tbz`, skip log block via `FromRecordCallees.lsLogOff`, and call `String::clone`. -/
theorem step_bc4_ok_false_to_d18_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {w1 remA : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xbc4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64)
    (hx21 : s.readReg64 .x21 = w1)
    (hw1 : w1.setWidth 8 = 0#8) :
    SepWP (lsProg_464 Hk) (lsmpl.base 623) s
      (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ FromRecordCallees.lsLogOff)
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0xc0#64) ↦₆₄ remA) ∗ FromRecordCallees.lsLogOff) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧ sf.readReg64 .x8 = s.sp + 0x580#64 ∧
        sf.readReg64 .x21 = remA ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xd1c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hb0 := getLsbD0_of_setWidth8_placed hw1
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true, FromRecordCallees.lsLogOff, lsLogFilterAddr]
  wp_steps
  exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all)

/-- E9 part 2a (`+0xd1c..+0xd28`) on `lsProg_464 Hk`. -/
theorem step_d1c_to_d2c_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {remA cap ptr : BitVec 64} {dev b598 : BitVec 8}
    (hpc : s.pc = encEntryPlaced + 0xd1c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx21 : s.readReg64 .x21 = remA) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xd2c#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
       ((s.sp + 0x580#64) ↦₆₄ cap) ∗
       ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x598#64) ↦₈ b598))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((remA + 0x18#64) ↦₈ dev) ∗
          ((s.sp + 0x580#64) ↦₆₄ cap) ∗
          ((s.sp + 0x588#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x598#64) ↦₈ dev)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x21 = cap ∧ sf.readReg64 .x23 = ptr ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E9 part 2b (`+0xd2c..+0xd3c`) on `lsProg_464 Hk`: set `x27 = speWord 12` and copy `[len, devWord]`
from `sp + 0x590` to `sp + 0x9d0`, reaching `+0xd40` (`tailCmDrop_placed_ok`). -/
theorem step_d2c_to_d40_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {len devWord u9d0 u9d8 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xd2c#64)
    (hrun : s.status = .Running)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = s.sp + 0x9d0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xd40#64) s
      (((s.sp + 0x590#64) ↦₆₄ len) ∗
       ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
       ((s.sp + 0x9d0#64) ↦₆₄ u9d0) ∗
       ((s.sp + 0x9d8#64) ↦₆₄ u9d8))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x590#64) ↦₆₄ len) ∗
          ((s.sp + 0x598#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9d0#64) ↦₆₄ len) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x27 = speWord 12 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true, speWord]
  by_vm_steps (wp_steps; exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustStepsPlacedBudget
