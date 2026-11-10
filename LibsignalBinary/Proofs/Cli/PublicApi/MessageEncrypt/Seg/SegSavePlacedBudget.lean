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
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFramePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSave
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `segSave`: `SaveStateVBudget` → `ApplyStateVBudget` (`+0xbd4..+0xd9c`)
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust (
  cliEncCommonRest cliTrustPassive encCommonPlaced_eq trustBaseActivePlaced
  seam_mem_split_placed seam_mem_to_tail_placed trustActivePlaced
  trustBaseActive_join_extra_placed trustActive_split_extra_placed trustPollPlacedOut_words
)

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSave
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust hiding
  alloc_onPanic_entails_placed dealloc_placed_ok_at_enc stringClone_placed_ok_at_enc
  trustVtablesAt_placed_intro saveVtablesAt_placed_intro storeVtablesAt_placed_intro
  speStaged_storeErr_placed call_nopanic_placed call_alloc_placed call_rocl_alloc_placed
  call_rocl_nopanic_placed
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Basic-Block `SepWP` Stepping Lemmas (`+0xbd4..+0xd9c`) -/

/-- E8 part 1 (`+0xbd4..+0xbe4`) on `lsProg_464 Hk`: load arguments from frame spills and call `shimAddr`. -/
theorem step_bd4_to_be4_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {remA idA id_vt shimAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xbd4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (lsProg_464 Hk) shimAddr s
      (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
       ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
       ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
       ((id_vt + 0x28#64) ↦₆₄ᵣ shimAddr))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
          ((s.sp + 0xc0#64) ↦₆₄ remA) ∗
          ((s.sp + 0xe0#64) ↦₆₄ idA) ∗
          ((s.sp + 0xe8#64) ↦₆₄ id_vt) ∗
          ((id_vt + 0x28#64) ↦₆₄ᵣ shimAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = idA ∧ sf.readReg64 .x1 = remA ∧
        sf.readReg64 .x2 = s.sp + 0x350#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xbe8#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E8 part 2 (`+0xbe8..+0xbfc`) on `lsProg_464 Hk`: store future box/vtable and call `pollAddr`. -/
theorem step_be8_to_bfc_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box u470 u478 futVtAddr pollAddr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0xbe8#64)
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
        sf.readReg64 .x30 = encEntryPlaced + 0xc00#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E8 + E10a part 1 (`+0xc00..+0xc08`, `+0xd50..+0xd7c`) on `lsProg_464 Hk`:
check `Ready`, copy SPE tail to `sp + 0x990`, and call `futDropAddr`. -/
theorem step_c00_to_d7c_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box w0 w1 w2 w3 w4 w5 u990 u998 u9a0 futVtAddr futDropAddr : BitVec 64}
    (hdrop : futDropAddr ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xc00#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx22 : s.readReg64 .x22 = s.sp + 0x8b8#64)
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
       ((s.sp + 0x990#64) ↦₆₄ u990) ∗
       ((s.sp + 0x998#64) ↦₆₄ u998) ∗
       ((s.sp + 0x9a0#64) ↦₆₄ u9a0) ∗
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
          ((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x998#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9a0#64) ↦₆₄ w5) ∗
          (futVtAddr ↦₆₄ᵣ futDropAddr)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x22 = box ∧ sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x24 = futVtAddr ∧ sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xd80#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdz' : (futDropAddr == 0#64) = false := by simp [hdrop]
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rcases hw0 with rfl | rfl <;> wp_steps <;>
      exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-- E10a part 2 (`+0xd80..+0xd90`) on `lsProg_464 Hk`: read size/align from vtable and call `__rust_dealloc`. -/
theorem step_d80_to_d90_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {box futVtAddr boxSizeBv : BitVec 64}
    (hsz : boxSizeBv ≠ 0#64)
    (hpc : s.pc = encEntryPlaced + 0xd80#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = box)
    (hx24 : s.readReg64 .x24 = futVtAddr) :
    SepWP (lsProg_464 Hk) (lsρ lsRustDeallocSym) s
      (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((futVtAddr + 8#64) ↦₆₄ᵣ boxSizeBv) ∗ ((futVtAddr + 0x10#64) ↦₆₄ᵣ 8#64)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = box ∧ sf.readReg64 .x1 = boxSizeBv ∧ sf.readReg64 .x2 = 8#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0xd94#64 ∧
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

/-- E10a `Err` branch (`+0xd94..+0xd98`) on `lsProg_464 Hk`: jump to T5 store `+0xe28`. -/
theorem step_d94_err_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    (hpc : s.pc = encEntryPlaced + 0xd94#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0x800000000000001A#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xe28#64) s emp
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

/-- E10a `Ok(c)` branch (`+0xd94..+0xd98`) on `lsProg_464 Hk`: fall through to `+0xd9c` (`ApplyStateVPlaced`). -/
theorem step_d94_ok_placed [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State}
    (hpc : s.pc = encEntryPlaced + 0xd94#64)
    (hrun : s.status = .Running)
    (hx27 : s.readReg64 .x27 = 0xFFFFFFFFFFFFFFFE#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xd9c#64) s emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧ sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    exact SepWP.done (by simp_all) (by simp_all) (by refine ⟨?_, rfl, ?_⟩ <;> simp_all))

/-! ## 2. Placed Seam Frame Split & Poll Output Helpers (from `SegSavePlaced`) -/

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave (
  cliSavePassive save_seam_mem_split_placed
  save_seam_mem_to_tail_placed savePollPlacedOut_words
)

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    {addr} (addrA : BitVec 64) :
    protocolAddressAt (A.atState lim st s) addr addrA = protocolAddressAt A.repAlloc addr addrA := rfl

private theorem savePassive_atState [LibsignalPlacement] {M : AllocCostModel}
    (ss_vt id_vt : BitVec 64) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (m : CiphertextMessage) (draws : Nat) (s0 : State) :
    cliSavePassive ss_vt id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' m draws s0 =
      cliSavePassive ss_vt id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0 := rfl

private theorem dropRecordSlots_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (om : Option CiphertextMessage) (poll : SepProp) :
    dropRecordSlots (A.atState lim st s) sp scratch g rec ot om poll =
      dropRecordSlots A.repAlloc sp scratch g rec ot om poll := rfl

private theorem encStoreExtraPlaced_retag {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (kit : SessionStoreSpec A.repAlloc 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
        (retagIdentityStore (A' := A.atState lim st s) ikit) ist x s0 =
      encStoreExtraPlaced kit st0 ikit ist x s0 := rfl

/-! ## 3. E8 + E10a Path (`+0xbd4..+0xd94`) -/

theorem save_to_d94_placed [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 ist1 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    {x : WithStoresEncGhost} {st_init st : M.σ} {k : IdentityKey} {F R R0 : SepProp} {s0 s : State}
    {next : State → Prop}
    (hfit : FitsEnv M lim st (SaveStepEnv ikit ikitEnv ist1 x.rem.val k))
    (haddr : ikit.addrOk x.rem.val)
    (henv : ∀ s', Steps (lsProg_464 Hk) s s' → s'.trace = s.trace → ikit.envOk s'.fs.files)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = encEntryPlaced + 0xbd4#64) (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true) (hx22 : s.readReg64 .x22 = s.sp + 0x8b8#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64) (hpref0 : s0.trace <+: s.trace)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hm : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist1
        s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (evs : List AllocEvent) (ans : Except Unit IdentityChange)
      (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      Steps (lsProg_464 Hk) s sm → sm.pc = encEntryPlaced + 0xd94#64 →
      sm.status = .Running → sm.sp = s.sp → sm.spAligned = true →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      ikit.saveRel ist1 x.rem.val k ans → sm.trace = s.trace ++ ikit.saveEvs x.rem.val k ans →
      SaveStepEnv ikit ikitEnv ist1 x.rem.val k evs →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x25 = s.readReg64 .x25 → sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 → sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 → sm.readReg64 .x21 = w1 → sm.readReg64 .x23 = w2 →
      (match ans with
       | .ok c => w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
           w1.setWidth 32 = (if c == .replacedExisting then 1#32 else 0#32) ∧ H = emp
       | .error () => w0 = 0x800000000000001A#64 ∧ w2 = 10#64 ∧ w3 = 1#64 ∧ H = (w1 ↦ᵣ storeHookStr)) →
      (sm.mem ⊨ (trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs st) sm) ikit)
          (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗ ((s.sp + 0x998#64) ↦₆₄ w4) ∗ ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R)) →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64)) ∗
      ((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((s.sp + 0xe0#64) ↦₆₄ x.idA) ∗
      ((s.sp + 0xe8#64) ↦₆₄ ikit.id_vt) ∗ ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff))) ∗
      (((((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist1 ∗
        stackAt s.sp (encSubStackV kit ikit) ∗ A.pool lim st s ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [saveVtablesAt, trustActivePlaced, retagIdentityStore, RustCliAllocBudget.atState_pool] at hm
    rw [protocolAddressAt_atState] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine SegExitBudget.of_sepWP hm1 (step_bd4_to_be4_placed hpc hrun hsp_align) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨hvm1, rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx30_1, hx19_1, hx20_1, hx22_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  rw [← A.pool_transport lim st s s1 hvm1] at hm2
  have hsp1_al : s1.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
  have hm3 : s1.mem ⊨ (kitSaveShimBudgetSpec M A lim ikit).pre (⟨x.idA, x.remA, s.sp + 0x350#64⟩, st) s1 ∗
      ((((s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ ikit.identityAt x.idA ist1 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - ikit.saveShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitSaveShimBudgetSpec]; rw [hsp1]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.saveShimStack
          (saveShimStack_le_encSubStackV kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1, hfit.seq_left⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine call_rocl_alloc_placed (env.ikitOk.saveShim (by decide))
    (⟨x.idA, x.remA, s.sp + 0x350#64⟩, st) hpc1 hrun1 hsp1_al hx30_1 hpref1 hcrl1 hm3 ?_
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hcrl2 hm4
  dsimp only [kitSaveShimBudgetSpec] at hm4
  rw [hsp1] at hsp2 hm4
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨evs₁, ⟨hx1_2, _, _, htr2, hevs1⟩, hm4⟩ := hm4
  set st1 := M.stepEvents evs₁ st
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 ∗
        ikit.identityAt x.idA ist1 ∗ A.pool lim st1 s2 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.saveShimStack
          (saveShimStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗ ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff))) ∗
      (((A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 0#8 ∗
        ikit.identityAt x.idA ist1 ∗ A.pool lim st1 s2 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        FromRecordCallees.lsLogOff ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    rw [hsp2]; exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine SegExitBudget.of_sepWP hm6 (step_be8_to_bfc_placed hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨hvm3, rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx22_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  rw [← A.pool_transport lim st1 s2 s3 hvm3] at hm7
  have hsp3_al : s3.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2]; exact hpref1
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps3.keepsFrozen
  let pollCall : IdentityPollCall := ⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x350#64, k⟩⟩
  have hm8 : s3.mem ⊨ (kitSavePollBudgetSpecI M A lim ikit ikitEnv).pre (pollCall, x.idA, ist1, st1) s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - ikit.savePollStack) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitSavePollBudgetSpecI, StoreKit.withLsLogOff, kitSavePollBudgetSpecE,
      kitSavePollBudgetSpec, withEnvPre, pollCall]
    rw [hsp3]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.savePollStack
          (savePollStack_le_encSubStackV kit ikit)] at hm7
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨henv s3 (hsteps1.trans (hsteps2.trans hsteps3)) (by rw [htr3, htr2, htr1]),
      ⟨hx0_3, hx8_3, haddr, (hfit.seq_right hevs1).seq_left⟩,
      Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  refine call_rocl_alloc_placed (env.ikitOk.savePoll (by decide)) (pollCall, x.idA, ist1, st1)
    hpc3 hrun3 hsp3_al hx30_3 hpref3 hcrl3 hm8 ?_
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hcrl4 hm9
  dsimp only [kitSavePollBudgetSpecI, StoreKit.withLsLogOff, kitSavePollBudgetSpecE,
    kitSavePollBudgetSpec, withEnvPre, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm9
  obtain ⟨ans, evs₂, ⟨hsaveRel, htr4, hevs2⟩, hm9⟩ := hm9
  set st2 := M.stepEvents evs₂ st1
  have hm9_poll : s4.mem ⊨ savePollPlacedOutAt (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x990#64) 24 ∗
      (((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp ikit.savePollStack
          (savePollStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left (savePollPlacedOut_words (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans⟩, hm10⟩ := hm10
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x990#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗ H ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u990, u998, u9a0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x990#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗ ((s4.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗ ((s4.sp + 0x588#64) ↦₆₄ w1) ∗ ((s4.sp + 0x590#64) ↦₆₄ w2) ∗
      ((s4.sp + 0x598#64) ↦₆₄ w3) ∗ ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗ ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x990#64) ↦₆₄ u990) ∗ ((s4.sp + 0x998#64) ↦₆₄ u998) ∗ ((s4.sp + 0x9a0#64) ↦₆₄ u9a0) ∗
      ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff))) ∗
      (((A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s4 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff ∗ H) ∗ F) ∗ R) := by
    rw [hsp4]; exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx22_4 : s4.readReg64 .x22 = s4.sp + 0x8b8#64 := by
    rw [hsp4, cs_x22 hcs4, hx22_3, cs_x22 hcs2, hx22_1, hx22]
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1, hx25]
  refine SegExitBudget.of_sepWP hm12
    (step_c00_to_d7c_placed (ikit.saveFutDrop_ne_zero (by decide)) hpc4 hrun4 hsp4_align hx22_4 hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨hvm5, rfl, hsp5, htr5, hx0_5, hx21_5, hx22_5, hx23_5, hx24_5, hx27_5, hx30_5,
      hx19_5, hx20_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  rw [← A.pool_transport lim st2 s4 s5 hvm5] at hm13
  have hsp5_al : s5.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropBudgetSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗ (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff))) ∗
      ((A.live box ikit.saveBoxSize 8 ∗ ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s5 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff ∗ H) ∗ F)) ∗ R) := by
    dsimp only [futDropBudgetSpec]; rw [emp_sepConj]; exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine call_rocl_nopanic_placed (env.ikitOk.saveFutDrop (by decide)) ()
    hpc5 hrun5 hsp5_al hx30_5 (hcrl4.of_keepsFrozen hsteps5.keepsFrozen) hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropBudgetSpec] at hm15; rw [hsp5] at hsp6; rw [satisfies_pure_sepConj] at hm15
  obtain ⟨⟨htr6, hvm6⟩, hm15⟩ := hm15
  rw [← A.pool_transport lim st2 s5 s6 hvm6] at hm15
  have hm15_box : s6.mem ⊨
      ikit.saveBoxAt box x.idA x.remA (s.sp + 0x350#64) 1#8 ∗
      ((((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗ (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        A.live box ikit.saveBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s6 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff ∗ H) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15' := Satisfies.mono (sepConj_mono_left
    (ikit.saveBoxAt_memRegion box x.idA x.remA (s.sp + 0x350#64) 1#8)) hm15_box
  have hm16 : s6.mem ⊨ (((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
      ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
        (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x990#64) ↦₆₄ w3 ∗ (s.sp + 0x998#64) ↦₆₄ w4 ∗ (s.sp + 0x9a0#64) ↦₆₄ w5 ∗
        ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗
        memRegion box ikit.saveBoxSize ∗ A.live box ikit.saveBoxSize 8 ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        A.pool lim st2 s6 ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗
        ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗
        FromRecordCallees.lsLogOff ∗ H) ∗ F) ∗ R) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15'
  have hx22_6 : s6.readReg64 .x22 = box := (cs_x22 hcs6).trans hx22_5
  have hx24_6 : s6.readReg64 .x24 = 0#64 + ikit.saveFutVtOff := (cs_x24 hcs6).trans hx24_5
  refine SegExitBudget.of_sepWP hm16
    (step_d80_to_d90_placed ikit.saveBoxSize_ne_zero hpc6 hrun6 hx22_6 hx24_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨hvm7, rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  rw [← A.pool_transport lim st2 s6 s7 hvm7] at hm17
  have hsp7_al : s7.spAligned = true := CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hsp_al hsp7
  have hm18 : s7.mem ⊨ (rustCliDeallocBudgetSpec M A lim).pre (box, ikit.saveBoxSize, 8, st2) s7 ∗
      (((saveVtablesAt ikit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (0#64 + ikit.saveFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗ (s.sp + 0x590#64) ↦₆₄ w2 ∗
          (s.sp + 0x598#64) ↦₆₄ w3 ∗ (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗ ((s.sp + 0x998#64) ↦₆₄ w4) ∗ ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
        ikit.identityAt x.idA (ikit.saveUpdate ist1 x.rem.val k ans) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗ (s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList ∗
        (s.sp + 0x40#64) ↦₆₄ (s.sp + 0x350#64) ∗ (s.sp + 0xc0#64) ↦₆₄ x.remA ∗
        (s.sp + 0xe0#64) ↦₆₄ x.idA ∗ (s.sp + 0xe8#64) ↦₆₄ ikit.id_vt ∗
        FromRecordCallees.lsLogOff ∗ H) ∗ F) ∗ R) := by
    dsimp only [rustCliDeallocBudgetSpec, saveVtablesAt]; rw [hsp7]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ikit.saveBoxSize_lt],
      by rw [hx2_7]; rfl,
      by rw [hx30_7]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0xd94#64 (by decide) (by decide)⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  refine call_nopanic_placed (dealloc_placed_ok_at_enc env) (box, ikit.saveBoxSize, 8, st2)
    hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  dsimp only [rustCliDeallocBudgetSpec] at hm19; rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨⟨hpres8, _⟩, hm19⟩ := hm19
  have htr8 : s8.trace = s7.trace := hpres8.2.1
  let evs_all := evs₁ ++ (evs₂ ++ rustDeallocEvents ikit.saveBoxSize 8)
  have hevs_all : SaveStepEnv ikit ikitEnv ist1 x.rem.val k evs_all :=
    Or.inr ⟨evs₁, evs₂ ++ rustDeallocEvents ikit.saveBoxSize 8, rfl, hevs1,
      Or.inr ⟨evs₂, rustDeallocEvents ikit.saveBoxSize 8, rfl, hevs2, rfl⟩⟩
  have hst_all : M.stepEvents (rustDeallocEvents ikit.saveBoxSize 8) st2 = M.stepEvents evs_all st := by
    simp only [evs_all, M.stepEvents_append, st1, st2]
  rw [hst_all] at hm19
  have hm20 : s8.mem ⊨ saveVtablesAt ikit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (0#64 + ikit.saveFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗ ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((trustActivePlaced (retagIdentityStore (A' := A.atState lim (M.stepEvents evs_all st) s8) ikit)
          (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗ ((s.sp + 0x998#64) ↦₆₄ w4) ∗ ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R))) := by
    dsimp only [trustActivePlaced, retagIdentityStore, RustCliAllocBudget.atState_pool]
    rw [protocolAddressAt_atState]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
          (allocHookStack_le_encSubStackV kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (0#64 + ikit.saveFutVtOff))
    (sepConj_mono_left (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_tail := hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))
  have hcrl8 : StoreKit.LibsignalCodeRoLoaded lsmpl s8.mem := hcrl4.of_keepsFrozen hsteps_tail.keepsFrozen
  have hsteps_all := hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans hsteps_tail)))
  refine hcont s8 evs_all ans w0 w1 w2 w3 w4 w5 H hsteps_all hpc8 hrun8 hsp8 hsp8_al hcrl8 hsaveRel
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2, htr1])
    hevs_all
    (by rw [cs_x19 hcs8, hx19_7, cs_x19 hcs6, hx19_5, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1])
    (by rw [cs_x20 hcs8, hx20_7, cs_x20 hcs6, hx20_5, cs_x20 hcs4, hx20_3, cs_x20 hcs2, hx20_1])
    (by rw [cs_x25 hcs8, hx25_7, cs_x25 hcs6, hx25_5, cs_x25 hcs4, hx25_3, cs_x25 hcs2, hx25_1])
    (by rw [cs_x26 hcs8, hx26_7, cs_x26 hcs6, hx26_5, cs_x26 hcs4, hx26_3, cs_x26 hcs2, hx26_1])
    (by rw [cs_x28 hcs8, hx28_7, cs_x28 hcs6, hx28_5, cs_x28 hcs4, hx28_3, cs_x28 hcs2, hx28_1])
    (by rw [cs_x29 hcs8, hx29_7, cs_x29 hcs6, hx29_5, cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1])
    (by rw [cs_vregs hcs8, hvregs_7, cs_vregs hcs6, hvregs_5, cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1])
    (by rw [cs_x27 hcs8, hx27_7, cs_x27 hcs6, hx27_5])
    (by rw [cs_x21 hcs8, hx21_7, cs_x21 hcs6, hx21_5])
    (by rw [cs_x23 hcs8, hx23_7, cs_x23 hcs6, hx23_5])
    hans (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

/-! ## 4. Main Theorem: `segSave_placed_okV` -/

theorem segSave_placed_okV [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegSaveSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init st r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s haddr hfs hsave
  obtain ⟨hbud, hsave⟩ := hsave
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨⟨h15, htrustRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx22, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hsave
  have h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' := h15
  have htrustRel : ikit.trustRel ist0 x.rem.val k .sending (.ok true) := htrustRel
  dsimp only [retagSessionStore, retagIdentityStore] at htr hm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set ist1 := ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)
  set F := cliSavePassive kit.ss_vt ikit.id_vt A.repAlloc ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActivePlaced ikit.id_vt (A.atState lim st s) s.sp x k ∗
        encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x990#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots (A.atState lim st s) s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x draws s0) ∗
        (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st s) kit) st0
          (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x s0 ∗ R0) := by
      rw [hsp, encStoreExtraPlaced_retag]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [save_seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st s) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp,
        savePassive_atState] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra_placed (retagSessionStore (A' := A.atState lim st s) kit) st0
      (retagIdentityStore (A' := A.atState lim st s) ikit) ist1 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  dsimp only [retagSessionStore] at hbound hm_join
  have hm_split : s.mem ⊨ (saveVtablesAt ikit ∗
      trustActivePlaced (retagIdentityStore (A' := A.atState lim st s) ikit) ist1
        s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x990#64) 24) ∗ (F ∗ R) := by
    have hm' := saveVtablesAt_placed_intro env.idVtables hcrl.2 hm_join
    dsimp only [R]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx22' : s.readReg64 .x22 = s.sp + 0x8b8#64 := by rw [hsp]; exact hx22
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  refine save_to_d94_placed env hbud.1.seq_left haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
        simp only [NoFsEv.append_iff, hl, ht, and_self]).2)
    hbound hpc hrun hsp_al hx22' hx25' hpref0 hcrl hm_split ?_
  intro sm evs_save ans w0 w1 w2 w3 w4 w5 H _hsteps_d94 hpcm hrunm hspm hspm_al hcrlm hsaveRel htrm
    hsaveEnv hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  set st_m := M.stepEvents evs_save st
  have hbud_m := hbud.advance hsaveEnv
  let R' : SepProp := encStoreExtraPlaced kit st0 ikit (ikit.saveUpdate ist1 x.rem.val k ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x990#64) ↦₆₄ w3) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActivePlaced (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
            (ikit.saveUpdate ist1 x.rem.val k ans) s.sp (encSubStackV kit ikit) x k ∗
          (retagSessionStore (A' := A.atState lim st_m sm) kit).storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗ H) ∗ F ∗ R0) := by
      dsimp only [R] at hmm_act
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra_placed (retagSessionStore (A' := A.atState lim st_m sm) kit) st0
        (retagIdentityStore (A' := A.atState lim st_m sm) ikit)
        (ikit.saveUpdate ist1 x.rem.val k ans) x k s0 s.sp hsp hbound)) hmm1
    rw [encStoreExtraPlaced_retag] at hmm2
    dsimp only [R']
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k ans)) := by
    rw [htrm, htr, List.append_assoc, List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | c
  ·
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_d94_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨hvm_err, rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_err] at hm_err
    have hcrl_err : StoreKit.LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_err) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5)) ∗
          (w1 ↦ᵣ storeHookStr)) ∗
          cliSavePassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_err
      rw [savePassive_atState]
      exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent := save_seam_mem_to_tail_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_err) ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x990#64) ↦₆₄ 1#64) ∗
        ((s.sp + 0x998#64) ↦₆₄ w4) ∗
        ((s.sp + 0x9a0#64) ↦₆₄ w5))
      (pollWith s.sp 0x990 [1#64, w4, w5])
      (w1 ↦ᵣ storeHookStr)
      (savePoll_merge_990 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists, dropRecordSlots_atState] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm :=
      StepsThroughEncrypt.tailModel_save_err (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrustRel hsaveRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfSaveErr r) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfSaveErr r) rfl
    refine SegExitBudget.of_false
      (env.tailStoreHookErr x st_init st_m R0 s0 s_err (answersOfSaveErr r) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xe28 0x990 (Or.inr (Or.inl rfl))
        htm (speStaged_storeErr_placed A.repAlloc x.ret w1 w4 w5) ?_)
    refine ⟨hbud_m.narrow (fun _ h => Or.inl h), hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hcrl_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_save_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, ist1, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal,
      answersOfSaveErr, R', retagSessionStore, retagIdentityStore] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  ·
    obtain ⟨rfl, _, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m sm) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x990#64) ↦₆₄ w3) ∗
            ((s.sp + 0x998#64) ↦₆₄ w4) ∗
            ((s.sp + 0x9a0#64) ↦₆₄ w5))) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitBudget.of_sepWP hmm_emp (step_d94_ok_placed hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨hvm_ok, rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj, ← A.atState_eq_of_vmPreserved lim st_m hvm_ok] at hm_ok
    have hcrl_ok : StoreKit.LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_990 : s_ok.mem ⊨
        (((s.sp + 0x990#64) ↦₆₄ w3) ∗
          ((s.sp + 0x990#64 + 8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x990#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x990#64) w3 w4 w5)) hm_ok_990
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt (A.atState lim st_m s_ok) s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x990#64) 24) ∗
          cliSavePassive kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      rw [savePassive_atState]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← save_seam_mem_split_placed kit.ss_vt ikit.id_vt (A.atState lim st_m s_ok) ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    refine SegExitBudget.next ⟨st_m, c, hbud_m.narrow (fun _ h => Or.inr h),
      ⟨h15, htrustRel, hsaveRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc]; rfl,
      ⟨by rw [hx20_ok, hx20m, hx20],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [sp, draws, ist1, R', retagSessionStore, retagIdentityStore] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlacedBudget
