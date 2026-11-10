/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStoreSteps
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable CLI `SegApplyStore` Basic-Block Steppers

`VmPreserved`-carrying `SepWP` basic-block stepping lemmas (`+0xd9c..+0xe88`) on `lsProg_464 Hk`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreStepsPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
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
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust hiding
  alloc_onPanic_entails_placed dealloc_placed_ok_at_enc stringClone_placed_ok_at_enc
  trustVtablesAt_placed_intro saveVtablesAt_placed_intro storeVtablesAt_placed_intro
  speStaged_storeErr_placed call_nopanic_placed call_alloc_placed call_rocl_alloc_placed
  call_rocl_nopanic_placed

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 1600000 in
/-- E10b apply (`+0xd9c..+0xde4`) on `lsProg_464 Hk`: clear drop flag `[sp+0x469]`, copy 200-byte OTR
from `sp+0x288` to `sp+0x580`, and call `OTR::apply_to_session_state` (`lsmpl.base 20`). -/
theorem step_d9c_to_de4_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u469 : BitVec 8}
    (hpc : s.pc = encEntryPlaced + 0xd9c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 20) s
      (((s.sp + 0x38#64) ↦₆₄ (s.sp + 0x288#64)) ∗
       ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
       ((s.sp + 0x469#64) ↦₈ u469) ∗
       otrWords25 (s.sp + 0x288#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
         w18 w19 w20 w21 w22 w23 w24 ∗
       otrWords25 (s.sp + 0x580#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
         d18 d19 d20 d21 d22 d23 d24)
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x38#64) ↦₆₄ (s.sp + 0x288#64)) ∗
          ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
          ((s.sp + 0x469#64) ↦₈ 0#8) ∗
          otrWords25 (s.sp + 0x288#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
            w18 w19 w20 w21 w22 w23 w24 ∗
          otrWords25 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
            w18 w19 w20 w21 w22 w23 w24) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = s.sp + 0x580#64 ∧ sf.readReg64 .x1 = s.sp + 0x128#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xde8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true, otrWords25]
  by_vm_steps (
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store part 1 (`+0xde8..+0xdf8`) on `lsProg_464 Hk`: load arguments from frame spills and call `shimAddr`. -/
theorem step_de8_to_df8_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {remA ssA ss_vt shimAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64) :
    SepWP (lsProg_464 Hk) shimAddr s
      (((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xd0#64) ↦₆₄ ssA) ∗
       ((s.sp + 0xd8#64) ↦₆₄ ss_vt) ∗
       ((ss_vt + 0x20#64) ↦₆₄ᵣ shimAddr))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xd0#64) ↦₆₄ ssA) ∗
          ((s.sp + 0xd8#64) ↦₆₄ ss_vt) ∗
          ((ss_vt + 0x20#64) ↦₆₄ᵣ shimAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = ssA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x110#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xdfc#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store part 2 (`+0xdfc..+0xe10`) on `lsProg_464 Hk`: store future box/vtable and call `pollAddr`. -/
theorem step_dfc_to_e10_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box u470 u478 futVtAddr pollAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xdfc#64)
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
        sf.readReg64 .x30 = encEntryPlaced + 0xe14#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store part 3 (`+0xe14..+0xe1c`, `+0xe38..+0xe68`) on `lsProg_464 Hk`: check `Ready`, copy SPE tail
to `sp + 0x9b0`, and call `futDropAddr`. -/
theorem step_e14_to_e68_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box w0 w1 w2 w3 w4 w5 u9b0 u9b8 u9c0 futVtAddr futDropAddr : BitVec 64}
    (hdrop : futDropAddr ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xe14#64)
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
       ((s.sp + 0x9b0#64) ↦₆₄ u9b0) ∗
       ((s.sp + 0x9b8#64) ↦₆₄ u9b8) ∗
       ((s.sp + 0x9c0#64) ↦₆₄ u9c0) ∗
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
          ((s.sp + 0x9b0#64) ↦₆₄ w3) ∗
          ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9c0#64) ↦₆₄ w5) ∗
          (futVtAddr ↦₆₄ᵣ futDropAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x20 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = futVtAddr ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xe6c#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (futDropAddr == 0#64) = false := by simp [hdrop]
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rcases hw0 with rfl | rfl <;> wp_steps <;>
      exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store part 4 (`+0xe6c..+0xe7c`) on `lsProg_464 Hk`: read size/align from vtable and call `__rust_dealloc`. -/
theorem step_e6c_to_e7c_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box futVtAddr boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xe6c#64)
    (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = box)
    (hx22 : s.readReg64 .x22 = futVtAddr) :
    SepWP (lsProg_464 Hk) (lsρ lsRustDeallocSym) s
      (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xe80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hsz' : (boxSizeBv == 0#64) = false := by simp [hsz]
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store `Err` branch (`+0xe80..+0xe84` when `x27 = 0x800000000000001A`) on `lsProg_464 Hk`: jump to `+0xf2c`. -/
theorem step_e80_err_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    (hpc : s.pc = encEntryPlaced + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xf2c#64) s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10b store `Ok(())` branch (`+0xe80..+0xe84` when `x27 = 0xFFFFFFFFFFFFFFFE`) on `lsProg_464 Hk`: fall through to `+0xe88`. -/
theorem step_e80_ok_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    (hpc : s.pc = encEntryPlaced + 0xe80#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xe88#64) s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreStepsPlacedBudget
