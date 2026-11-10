/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs -- shake: keep

/-!
# Budget-Threaded Relocatable CLI `SegLoad` Dispatch: `.ok (some r)` & `segLoad_placed_okV`

Proves `segLoad_dispatch_some_budget` and assembles the budget-threaded `segLoad_placed_okV`
on `lsProg_464 Hk` (`blkPl_464`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad hiding segLoad_placed_okV

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
open CryptoVerification.LibsignalTripleRatchet hiding
  LibsignalCodeRoLoaded withLsCodeRoLoaded sepWP_seq_lscro sepWPp_seq_lscro
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Pf.RecordMove
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadShimPollPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchPlacedBudget
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem cs_x19 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x19 = s0.readReg64 .x19 := h.1
private theorem cs_x20 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x20 = s0.readReg64 .x20 := h.2.1
private theorem cs_x22 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x22 = s0.readReg64 .x22 := h.2.2.2.1
private theorem cs_x23 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x23 = s0.readReg64 .x23 := h.2.2.2.2.1
private theorem cs_x25 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x25 = s0.readReg64 .x25 := h.2.2.2.2.2.2.1
private theorem cs_x26 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x26 = s0.readReg64 .x26 := h.2.2.2.2.2.2.2.1
private theorem cs_x28 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x28 = s0.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
private theorem cs_x29 {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : sf.readReg64 .x29 = s0.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
private theorem cs_vregs {s0 sf : State} (h : CalleeSavedPreserved s0 sf) : calleeSavedVRegs sf = calleeSavedVRegs s0 := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## 1. Straight-Line `by_vm_steps` Blocks for `ans = .ok (some r)` -/

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_some_to_memcpy_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp remA v50 w0 w1 w2 w3 w4 w5 w6 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hw0_ne1 : w0 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hw0_ne2 : w0 ≠ 0xFFFFFFFFFFFFFFFE#64)
    (hx24 : s.readReg64 .x24 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64) :
    SepWP (lsProg_464 Hk) (lsmpl.ρ "memcpy") s
      (((sp + 0x50#64) ↦₆₄ v50) ∗
        ((sp + 0x108#64) ↦₆₄ remA) ∗
        memRegion (sp + 0x110#64) 0x358 ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6))
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = (((sp + 0x110#64) ↦₆₄ w0) ∗ ((sp + 0x118#64) ↦₆₄ w1) ∗
          ((sp + 0x120#64) ↦₆₄ w2) ∗ ((sp + 0x128#64) ↦₆₄ w3) ∗
          ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
          ((sp + 0x140#64) ↦₆₄ w6) ∗
          memRegion (sp + 0x148#64) 312 ∗
          memRegion (sp + 0x280#64) 0x1e8 ∗
          ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
          ((sp + 0x108#64) ↦₆₄ remA) ∗
          ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
          ((sp + 0x840#64) ↦₆₄ w6)) ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = sp + 0x148#64 ∧
        sf.readReg64 .x1 = sp + 0x6f8#64 ∧
        sf.readReg64 .x2 = 0x138#64 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x1bc#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x20 = sp + 0x58#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x23 = w3 ∧
        sf.readReg64 .x25 = sp + 0x580#64 ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hw0_b2 : (w0 + 2#64 == 0#64) = false := ne_neg2_add2_ne_zero hw0_ne2
  have hw0_b1 : (w0 + 1#64 == 0#64) = false := ne_neg1_add1_ne_zero hw0_ne1
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx24 hx27 hx21 hx23 hx25 hx26 hx28
  by_vm_steps (
    wp_conv_pre => rw [memRegion_0x110_split_record s.sp]
    wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro _)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, ?_, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · sep_ac_rfl
    · simp only [wp_norm, arm64_norm, hx23, hx25, hx26, hx28, hal_norm, true_and])

theorem segLoad_dispatch_some_cur_tail_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp w3 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x1bc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hw3_ne : w3 ≠ 0xFFFFFFFFFFFFFFFF#64)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx23 : s.readReg64 .x23 = w3) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x20c#64) s
      emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x20 = sp + 0x58#64 ∧
        sf.readReg64 .x21 = sp + 0x128#64 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hw3_b1 : (w3 + 1#64 != 0#64) = true := ne_neg1_add1_bne_zero hw3_ne
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx20 hx23
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, rfl, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx20, hal_norm, true_and])

theorem segLoad_dispatch_some_nocur_to_clone_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp remA : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x1bc#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx22 : s.readReg64 .x22 = remA)
    (hx23 : s.readReg64 .x23 = 0xFFFFFFFFFFFFFFFF#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 623) s
      emp
      (fun sf P_f =>
        VmPreserved s sf ∧
        P_f = emp ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = remA ∧
        sf.readReg64 .x8 = sp + 0x580#64 ∧
        sf.readReg64 .x22 = remA ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x1d4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x28 = s.readReg64 .x28) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx20 hx22 hx23
  by_vm_steps (
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, rfl, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx22, hal_norm, true_and])

set_option maxHeartbeats 800000 in
theorem segLoad_dispatch_some_nocur_post_budget_wp_vm [LibsignalPlacement] {Hk : LibsignalHooks}
    {s : State} {sp remA cap ptr len w0 w1 w2 w4 w5 w6 : BitVec 64}
    {dev : BitVec 8} {F : SepProp}
    (hpc : s.pc = encEntryPlaced + 0x1d4#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hcap_ne2 : cap ≠ 0xFFFFFFFFFFFFFFFE#64)
    (hx22 : s.readReg64 .x22 = remA)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x564#64) s
      (((remA + 0x18#64) ↦₈ dev) ∗
        ((sp + 0x110#64) ↦₆₄ w0) ∗ ((sp + 0x118#64) ↦₆₄ w1) ∗
        ((sp + 0x120#64) ↦₆₄ w2) ∗ ((sp + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
        ((sp + 0x140#64) ↦₆₄ w6) ∗
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ len) ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp + 0x848#64) 0x338 ∗ F)
      (fun sf P_f =>
        VmPreserved s sf ∧
        ∃ w3 : BitVec 64, DevWord dev w3 ∧
          sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x29 = sp + 0xb80#64 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s ∧
          sf.readReg64 .x26 = sp + 0x9d0#64 ∧
          sf.readReg64 .x28 = sp + 0x4a0#64 ∧
          sf.readReg64 .x27 = cap ∧
          sf.readReg64 .x21 = ptr ∧
          sf.readReg64 .x23 = len ∧
          P_f = (((remA + 0x18#64) ↦₈ dev) ∗
            recordWords56At (sp + 0x110#64) w0 w1 w2 0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
            memRegion (sp + 0x580#64) 368 ∗
            memRegion (sp + 0x848#64) 0x188 ∗
            ((sp + 0x9d0#64) ↦₆₄ w3) ∗
            ((sp + 0x9d8#64) ↦₆₄ (lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122")) ∗
            ((sp + 0x9e0#64) ↦₆₄ 15#64) ∗
            memRegion (sp + 0x9e8#64) 0x198 ∗ F)) := by
  subst hsp
  have hal_norm : (s.sp &&& 15#64 == 0#64) = true := hal
  have hcap_b2 : (cap + 2#64 == 0#64) = false := ne_neg2_add2_ne_zero hcap_ne2
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true] at hpc ⊢
  simp only [wp_norm, arm64_norm] at hx22 hx26 hx28 hx29
  wp_step
  wp_step
  apply sepWP_shift_vmPreserved (by simp only [wp_norm, arm64_norm])
  by_vm_steps (
    wp_conv_pre =>
      rw [memRegion_0x598_split s.sp, memRegion_0x848_split_0x9d0_0xb00 s.sp]
    wp_simp_pre [cells_succ, cells_zero, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc]
    repeat (apply SepWP.exists_elim; intro _)
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.fold (devWord_of_pointsTo8_memRegion7_1432 s.sp dev) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepConj_assoc]
    apply SepWP.exists_elim; intro w3
    apply SepWP.pure_elim; intro hdev
    wp_steps
    apply SepWP.fold (recordWords56At_fold_sp110 s.sp w0 w1 w2 0xFFFFFFFFFFFFFFFF#64 w4 w5 w6) (by sep_focus)
    apply SepWP.fold (memRegion_0x580_368_fold s.sp cap ptr len w3 _) (by sep_focus)
    apply SepWP.fold (memRegion_0x9e8_0x198_fold s.sp w3 _ 15#64) (by sep_focus)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine ⟨?_, w3, hdev, ?_⟩
    · simp only [wp_norm, arm64_norm]
    · simp only [wp_norm, arm64_norm, hx26, hx28, hx29, hal_norm, true_and]
      sep_ac_rfl)

/-! ## 2. `segLoad_dispatch_some_budget` & Top-Level `segLoad_placed_okV` -/

set_option maxHeartbeats 1600000 in
theorem segLoad_dispatch_some_budget [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st3 : M.σ) (R : SepProp) (s0 s : State)
    (r : SessionRecord (List (BitVec 8)))
    (sp w0 w1 w2 w3 w4 w5 w6 v50 : BitVec 64) (tail : List (BitVec 8))
    (hbud3 : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
      st_init st3 (LoadRemEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x))
    (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hpc : s.pc = encEntryPlaced + 0x160#64)
    (hmeta : encMidMetaPlaced x s0 s)
    (hbnds : x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
      x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (htail : tail.length = 312)
    (hl : kit.loadRel st0 x.rem.val (.ok (some r)))
    (htr : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hx24 : s.readReg64 .x24 = w0) (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2) (hx23 : s.readReg64 .x23 = w3)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hps : s.pstate = addsPState64 w0 2#64)
    (hm : s.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      ((sp + 0x6f8#64) ↦ₛ tail) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6) ∗
      LoadOutResPlaced Scope A.repAlloc (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st3 s ∗ stackAt sp encSubStack ∗ loadVtablesAt kit ∗
      dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s
      (fun s' => ∃ st' r g sess,
        CurStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st' r g sess R s0 s') := by
  subst hsp_eq
  rcases hmeta with ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩
  rcases hbnds with ⟨hpt_lt, hrest_lt, hloc_ne, hnsec, hsp_le⟩
  have hm_drop : s.mem ⊨
      LoadOutResPlaced Scope A.repAlloc (.ok (some r)) w0 w1 w2 w3 w4 w5 w6 tail ∗
      ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
        memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
        ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
        ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗ ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
        ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
        protocolAddressAt A.repAlloc x.rem x.remA ∗
        A.pool lim st3 s ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
        dispatchFramePlaced kit st0 ikit ist0 ctl x s0 v50) ∗ R) := by
    refine Satisfies.drop_left (P := loadVtablesAt kit) ?_
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  clear hm
  rw [loadOutResPlaced_some_eq] at hm_drop
  obtain ⟨g, hm_drop1⟩ := satisfies_sepExists_left hm_drop
  clear hm_drop
  rw [sepConj_assoc] at hm_drop1
  obtain ⟨⟨hscope, hcap_lt, hw0_eq, hw1_eq, hw2_eq, hw3_eq_init, htail_inl⟩, hm_drop2⟩ :=
    satisfies_pure_left hm_drop1
  clear hm_drop1
  subst hw0_eq hw1_eq hw2_eq hw3_eq_init
  obtain ⟨hw0_ne1, hw0_ne2, _⟩ := ne_neg_tags_of_lt_two_pow_63 hcap_lt
  let sp := s0.sp - 0xbe0#64
  let F_1 : SepProp :=
    ((sp + 0x6f8#64) ↦ₛ tail) ∗
      recordHeap A.repAlloc g r ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st3 s ∗ stackAt sp encSubStack ∗
      memRegion (sp + 0x848#64) 0x338 ∗
      dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0
  have hm_1 : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ v50) ∗
        ((sp + 0x108#64) ↦₆₄ x.remA) ∗
        memRegion (sp + 0x110#64) 0x358 ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6)) ∗ (F_1 ∗ R) := by
    dsimp only [F_1, sp]
    refine Satisfies.mono ?_ hm_drop2
    rw [dispatchFramePlaced_eq_rec_sep kit st0 ikit ist0 ctl x s0 v50]
    exact Entails.of_eq (by sep_ac_rfl)
  clear hm_drop2
  refine SegExitBudget.of_sepWP (R0 := R) hm_1
    (segLoad_dispatch_some_to_memcpy_wp_vm hpc hrun hsp hal hw0_ne1 hw0_ne2
      hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps) ?_
  rintro sm1 P1 _ hsteps_1 hpc1 hrun1 hm1
    ⟨hvm_1, rfl, hsp1, hal1, htr1, hx0_1, hx1_1, hx2_1, hx30_1,
      hx19_1, hx29_1, hvregs_1, hx20_1, hx22_1, hx23_1, hx25_1, hx26_1, hx28_1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl sm1.mem := hcrl.of_keepsFrozen hsteps_1.keepsFrozen
  let F_2 : SepProp :=
    (((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
      ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
      ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
      ((sp + 0x140#64) ↦₆₄ w6) ∗
      memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x108#64) ↦₆₄ x.remA) ∗
      ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
      ((sp + 0x840#64) ↦₆₄ w6)) ∗
    (recordHeap A.repAlloc g r ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 368 ∗
      protocolAddressAt A.repAlloc x.rem x.remA ∗
      A.pool lim st3 s ∗ stackAt sp encSubStack ∗
      memRegion (sp + 0x848#64) 0x338 ∗
      dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)
  have hm_2 : sm1.mem ⊨
      sessionMemcpyRegionBudgetSpec.pre (sp + 0x148#64, sp + 0x6f8#64, tail) sm1 ∗ (F_2 ∗ R) := by
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, framelessMemcpySpec, memcpyRegionSpec, F_2, F_1] at hm1 ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_1, hx1_1, by rw [hx2_1, htail]; rfl⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  refine call_nopanic_placed (R0 := R) (memcpy_budget_ok env)
    (sp + 0x148#64, sp + 0x6f8#64, tail) hpc1 hrun1 hal1 hx30_1 hm_2 ?_
  intro sm2 hsteps_2 hpc2 hrun2 hsp2 hal2 hcs2 hm2
  dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, framelessMemcpySpec, memcpyRegionSpec] at hm2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
  obtain ⟨hvm_2, hm2⟩ := hm2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm2
  obtain ⟨⟨_hx0_2, htr2⟩, hm2⟩ := hm2
  have hcrl2 : StoreKit.LibsignalCodeRoLoaded lsmpl sm2.mem := hcrl1.of_keepsFrozen hsteps_2.keepsFrozen
  have hsp2' : sm2.sp = sp := by rw [hsp2, hsp1]
  have hx20_2 : sm2.readReg64 .x20 = sp + 0x58#64 := by rw [cs_x20 hcs2, hx20_1]
  have hx22_2 : sm2.readReg64 .x22 = x.remA := by rw [cs_x22 hcs2, hx22_1]
  have hx23_2 : sm2.readReg64 .x23 = recordCurCap g := by rw [cs_x23 hcs2, hx23_1]
  have hx25_2 : sm2.readReg64 .x25 = sp + 0x580#64 := by rw [cs_x25 hcs2, hx25_1]
  have hx26_2 : sm2.readReg64 .x26 = sp + 0x9d0#64 := by rw [cs_x26 hcs2, hx26_1]
  have hx28_2 : sm2.readReg64 .x28 = sp + 0x4a0#64 := by rw [cs_x28 hcs2, hx28_1]
  have hvm_s_2 : VmPreserved s sm2 := hvm_1.trans hvm_2
  cases hcur : r.currentSession with
  | some sess =>
    have hbud_cur : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
        st_init st3 (FromCurEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 Scope x) :=
      hbud3.narrow fun _ h => Or.inr (Or.inr h)
    have hm2_pure : sm2.mem ⊨
        ⌜recordCurCap g ≠ 0xFFFFFFFFFFFFFFFF#64⌝ ∗
        ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗ F_2) ∗ R) := by
      dsimp only [F_2] at hm2 ⊢
      refine Satisfies.mono ?_ hm2
      have hpull_rh :
          (((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail)) ∗
            ((((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
              ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
              ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
              ((sp + 0x140#64) ↦₆₄ w6) ∗
              memRegion (sp + 0x280#64) 0x1e8 ∗
              ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
              ((sp + 0x108#64) ↦₆₄ x.remA) ∗
              ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
              ((sp + 0x840#64) ↦₆₄ w6)) ∗
            (recordHeap A.repAlloc g r ∗
              memRegion (sp + 0x46a#64) 0x116 ∗
              memRegion (sp + 0x580#64) 368 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              A.pool lim st3 s ∗ stackAt sp encSubStack ∗
              memRegion (sp + 0x848#64) 0x338 ∗
              dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)) ∗ R =
          recordHeap A.repAlloc g r ∗
            ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗
              ((((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
                ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ recordCurCap g) ∗
                ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
                ((sp + 0x140#64) ↦₆₄ w6) ∗
                memRegion (sp + 0x280#64) 0x1e8 ∗
                ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
                ((sp + 0x108#64) ↦₆₄ x.remA) ∗
                ((sp + 0x830#64) ↦₆₄ w4) ∗ ((sp + 0x838#64) ↦₆₄ w5) ∗
                ((sp + 0x840#64) ↦₆₄ w6)) ∗
              (memRegion (sp + 0x46a#64) 0x116 ∗
                memRegion (sp + 0x580#64) 368 ∗
                protocolAddressAt A.repAlloc x.rem x.remA ∗
                A.pool lim st3 s ∗ stackAt sp encSubStack ∗
                memRegion (sp + 0x848#64) 0x338 ∗
                dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0))) ∗ R) := by
        sep_ac_rfl
      rw [hpull_rh]
      refine Entails.trans (sepConj_mono_left (curSession_some_of_recordTailInline htail_inl hcur)) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    obtain ⟨hw3_ne, hm2_cur⟩ := satisfies_pure_left hm2_pure
    clear hm2 hm2_pure
    have hm_cur_emp : sm2.mem ⊨
        emp ∗ ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗ F_2) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_cur
    refine SegExitBudget.of_sepWP (R0 := R) hm_cur_emp
      (segLoad_dispatch_some_cur_tail_wp_vm hpc2 hrun2 hsp2' hal2 hw3_ne hx20_2 hx23_2) ?_
    rintro sf Pf _ hsteps_3 hpcf hrunf hm_f
      ⟨hvm_3, rfl, hspf, half, htrf, hx19f, hx29f, hvregsf, hx20f, hx21f, hx25f, hx26f, hx28f⟩
    have hcrlf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl2.of_keepsFrozen hsteps_3.keepsFrozen
    have hvm_s_f : VmPreserved s sf := hvm_s_2.trans hvm_3
    refine SegExitBudget.next ⟨st3, r, g, sess, hbud_cur, hcur, ⟨hscope, hl⟩, ?_⟩
    refine ⟨hpcf,
      ⟨hrunf, hspf, hal0, half,
        by rw [hx29f, cs_x29 hcs2, hx29_1, hx29],
        by rw [hx19f, cs_x19 hcs2, hx19_1, hx19], hcrlf,
        by rw [hvregsf, cs_vregs hcs2, hvregs_1, hvregs]⟩,
      by rw [htrf, htr2, htr1, htr]; rfl,
      ⟨hx20f, hx21f, by rw [hx25f, hx25_2], by rw [hx26f, hx26_2], by rw [hx28f, hx28_2]⟩,
      hpt_lt, hrest_lt, hloc_ne, hnsec, enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩
    dsimp only [EncSeamVPlaced, curScratch, F_2, sp] at hm_f ⊢
    rw [← A.pool_transport lim st3 s sf hvm_s_f] at hm_f
    refine Satisfies.mono ?_ hm_f
    have hrec_words := recordWords56At_fold_sp110 (s0.sp - 0xbe0#64)
      g.prevCap g.prevPtr 0#64 (recordCurCap g) w4 w5 w6
    have hrec := sessionRecordAt_of_words56_sep_tail A.repAlloc
      (s0.sp - 0xbe0#64 + 0x110#64) g r htail_inl
    have h38 : (s0.sp - 0xbe0#64 + 0x110#64) + 0x38#64 = s0.sp - 0xbe0#64 + 0x148#64 := by bv_arith
    rw [h38] at hrec
    have hrec_full :
        (((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
          ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
          ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6)) ∗
        ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
        recordHeap A.repAlloc g r ⊢
        sessionRecordAt (A.atState lim st3 sf) (s0.sp - 0xbe0#64 + 0x110#64) g r :=
      Entails.trans (sepConj_mono_left hrec_words) hrec
    have h46a := memRegion_0x46a_0x716_fold (s0.sp - 0xbe0#64) w4 w5 w6 tail htail
    have hspills := encSpillsAt_fold kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x
    have hperm_cur :
        emp ∗
          ((((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
              ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
              ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
              ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
              ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
              ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6) ∗
              memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
              ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
              ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
              ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
              ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
              ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6)) ∗
            (recordHeap A.repAlloc g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
              protocolAddressAt A.repAlloc x.rem x.remA ∗
              A.pool lim st3 sf ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ∗
              memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338 ∗
              dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0))) ∗ R) =
        ((((s0.sp - 0xbe0#64 + 0x110#64) ↦₆₄ g.prevCap) ∗
          ((s0.sp - 0xbe0#64 + 0x118#64) ↦₆₄ g.prevPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x120#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0xbe0#64 + 0x128#64) ↦₆₄ recordCurCap g) ∗
          ((s0.sp - 0xbe0#64 + 0x130#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x138#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x140#64) ↦₆₄ w6)) ∗
          ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A.repAlloc g r) ∗
        (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x338) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8) ∗
          memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
          memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st3 sf) ctl x 0 s0 ∗
          (encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st3 sf) kit) st0
            (retagIdentityStore (A' := A.atState lim st3 sf) ikit) ist0 x s0 ∗ R)) := by
      dsimp only [dispatchFrameNoRecPlaced, encCommonPlaced]
      change _ = _ ∗ (_ ∗ (_ ∗ (_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗
        ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
          stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st3 sf) ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R))))
      sep_ac_rfl
    rw [hperm_cur]
    refine Entails.trans (sepConj_mono hrec_full (sepConj_mono hspills (sepConj_mono_left h46a))) ?_
    change sessionRecordAt (A.atState lim st3 sf) (s0.sp - 0xbe0#64 + 0x110#64) g r ∗
      encSpillsAtV (retagSessionStore (A' := A.atState lim st3 sf) kit).ss_vt
        (retagIdentityStore (A' := A.atState lim st3 sf) ikit).id_vt (s0.sp - 0xbe0#64) x ∗ _ ⊢ _
    exact Entails.of_eq (by sep_ac_rfl)
  | none =>
    have hbud_clone : SeamBudget lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x)
        st_init st3 (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs) :=
      hbud3.narrow fun _ h => Or.inr (Or.inl h)
    obtain ⟨_, hw3_eq⟩ := curSession_none_of_recordTailInline htail_inl hcur
    rw [hw3_eq] at hx23_2
    have hm_nocur_emp : sm2.mem ⊨
        emp ∗ ((((sp + 0x148#64) ↦ₛ tail) ∗ ((sp + 0x6f8#64) ↦ₛ tail) ∗ F_2) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2
    refine SegExitBudget.of_sepWP (R0 := R) hm_nocur_emp
      (segLoad_dispatch_some_nocur_to_clone_wp_vm hpc2 hrun2 hsp2' hal2 hx20_2 hx22_2 hx23_2) ?_
    rintro sm3 P3 _ hsteps_3a hpc3 hrun3 hm3
      ⟨hvm_3a, rfl, hsp3, hal3, htr3, hx0_3, hx8_3, hx22_3, hx30_3,
        hx19_3, hx29_3, hvregs_3, hx26_3, hx28_3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl sm3.mem := hcrl2.of_keepsFrozen hsteps_3a.keepsFrozen
    have hvm_s_3 : VmPreserved s sm3 := hvm_s_2.trans hvm_3a
    have hpref3 : s0.trace <+: sm3.trace := by
      rw [htr3, htr2, htr1, htr]
      exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩
    let F_clone : SepProp :=
      ((sp + 0x110#64) ↦₆₄ g.prevCap) ∗
        ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
        ((sp + 0x120#64) ↦₆₄ 0#64) ∗
        ((sp + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((sp + 0x130#64) ↦₆₄ w4) ∗
        ((sp + 0x138#64) ↦₆₄ w5) ∗
        ((sp + 0x140#64) ↦₆₄ w6) ∗
        ((sp + 0x148#64) ↦ₛ tail) ∗
        memRegion (sp + 0x280#64) 0x1e8 ∗
        ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x108#64) ↦₆₄ x.remA) ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗
        ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        ((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        memRegion (sp + 0x598#64) 344 ∗
        memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        memRegion (sp + 0x848#64) 0x338 ∗
        (recordHeap A.repAlloc g r ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)
    have hm_clone : sm3.mem ⊨
        (stringCloneBudgetSpec M A lim).pre (x.remA, sp + 0x580#64, x.rem.name, st3) sm3 ∗
        (F_clone ∗ R) := by
      dsimp only [stringCloneBudgetSpec, F_clone, F_2, sp] at hm3 ⊢
      rw [← A.pool_transport lim st3 s sm3 hvm_s_3, hw3_eq] at hm3
      rw [hsp3, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨⟨hx0_3, hx8_3, hbud_clone.1.seq_left⟩, ?_⟩
      refine Satisfies.mono ?_ hm3
      rw [protocolAddressAt, memRegion_0x580_split_24 (s0.sp - 0xbe0#64),
          stack_encSub_extHook (s0.sp - 0xbe0#64)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine call_rocl_alloc_placed (R0 := R) (stringClone_budget_ok env.toEncEnvBudget)
      (x.remA, sp + 0x580#64, x.rem.name, st3)
      hpc3 hrun3 hal3 hx30_3 hpref3 hcrl3 hm_clone ?_
    intro sf1 hsteps_clone hpc4 hrun4 hsp4 hal4 hcs4 hcrl4 hm4
    dsimp only [stringCloneBudgetSpec] at hm4
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj] at hm4
    obtain ⟨evs_clone, ⟨htr4, hevs_clone⟩, hm4⟩ := hm4
    have hbud4 := hbud_clone.advance hevs_clone
    set st4 := M.stepEvents evs_clone st3
    have hsp4' : sf1.sp = sp := by rw [hsp4, hsp3]
    have hx22_4 : sf1.readReg64 .x22 = x.remA := by rw [cs_x22 hcs4, hx22_3]
    have hx26_4 : sf1.readReg64 .x26 = sp + 0x9d0#64 := by rw [cs_x26 hcs4, hx26_3, hx26_2]
    have hx28_4 : sf1.readReg64 .x28 = sp + 0x4a0#64 := by rw [cs_x28 hcs4, hx28_3, hx28_2]
    have hx29_4 : sf1.readReg64 .x29 = sp + 0xb80#64 := by
      dsimp only [sp]
      rw [cs_x29 hcs4, hx29_3, cs_x29 hcs2, hx29_1, hx29, sp_sub_0x60_eq_sub_0xbe0_add_0xb80]
    have hm4_vec : sf1.mem ⊨
        vecU8 A.repAlloc (sp + 0x580#64) x.rem.name.bytes ∗
        ((vecGhostAt A.repAlloc x.rem.name x.remA ∗
          A.pool lim st4 sf1 ∗ stackAt sm3.sp extHookStack ∗ F_clone) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm4
    rw [vecU8_eq_words3_sep_buf_lt] at hm4_vec
    simp only [sepExists_sepConj_left, satisfies_sepExists, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_assoc, satisfies_pure_sepConj] at hm4_vec
    obtain ⟨cap, ptr, hcap_lt_c, hm4_vec⟩ := hm4_vec
    have hcap_ne2 : cap ≠ 0xFFFFFFFFFFFFFFFE#64 := (ne_neg_tags_of_lt_two_pow_63 hcap_lt_c).2.1
    let F_post : SepProp :=
      ((sp + 0x148#64) ↦ₛ tail) ∗
        memRegion (sp + 0x280#64) 0x1e8 ∗
        ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x108#64) ↦₆₄ x.remA) ∗
        ((sp + 0x6f8#64) ↦ₛ tail) ∗
        ((sp + 0x830#64) ↦₆₄ w4) ∗
        ((sp + 0x838#64) ↦₆₄ w5) ∗
        ((sp + 0x840#64) ↦₆₄ w6) ∗
        vecGhostAt A.repAlloc x.rem.name x.remA ∗
        memRegion (x.remA + 0x19#64) 7 ∗
        vecU8Buf A.repAlloc cap ptr x.rem.name.bytes ∗
        A.pool lim st4 sf1 ∗
        stackAt sp encSubStack ∗
        (recordHeap A.repAlloc g r ∗
          memRegion (sp + 0x46a#64) 0x116 ∗
          dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0)
    have hm_post : sf1.mem ⊨
        (((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          ((sp + 0x110#64) ↦₆₄ g.prevCap) ∗ ((sp + 0x118#64) ↦₆₄ g.prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ ((sp + 0x128#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((sp + 0x130#64) ↦₆₄ w4) ∗ ((sp + 0x138#64) ↦₆₄ w5) ∗
          ((sp + 0x140#64) ↦₆₄ w6) ∗
          ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
          ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          memRegion (sp + 0x598#64) 344 ∗
          memRegion (sp + 0x848#64) 0x338 ∗ F_post) ∗ R := by
      dsimp only [F_post, F_clone, sp] at hm4_vec ⊢
      rw [hsp3] at hm4_vec
      refine Satisfies.mono ?_ hm4_vec
      rw [← stack_encSub_extHook_back (s0.sp - 0xbe0#64)]
      exact Entails.of_eq (by sep_ac_rfl)
    refine segExit_budget_of_sepWP_frozen hcrl4 hm_post
      (segLoad_dispatch_some_nocur_post_budget_wp_vm
        hpc4 hrun4 hsp4' hal4 hcap_ne2 hx22_4 hx26_4 hx28_4 hx29_4) ?_
    intro sf P_f hpcf hrunf hpostf hcrlf hm_f
    rcases hpostf with ⟨hvm_post, w3', hdev, hspf, half, htrf, hx19f, _hx29f, hvregsf,
      hx26f, hx28f, hx27f, hx21f, hx23f, rfl⟩
    have hm_rod := rodata_message_encrypt_placed_intro hcrlf.2 hm_f
    let msgPtr := lsmpl.ρ "libsignal_cli_ratchet:.rodata..Lanon.122"
    refine segExit_budget_of_false (env.tailFreePrevSessions x st_init st4 R s0 sf
      (answersOfLoad (.ok (some r)))
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) w3' msgPtr 15#64
      (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt"))
      g.prevCap g.prevPtr
      (tailModel_load_some_none hl hcur (by rw [htrf, htr4, htr3, htr2, htr1, htr]))
      (speStaged_sessionNotFound_devWord_placed A.repAlloc x.ret cap ptr w3' msgPtr x.rem.val hdev)
      ⟨hbud4, hpcf,
        ⟨hrunf, hspf, hal0, half,
          by dsimp only [sp] at _hx29f; rw [_hx29f, ← sp_sub_0x60_eq_sub_0xbe0_add_0xb80],
          by rw [hx19f, cs_x19 hcs4, hx19_3, cs_x19 hcs2, hx19_1, hx19], hcrlf,
          by rw [hvregsf, cs_vregs hcs4, hvregs_3, cs_vregs hcs2, hvregs_1, hvregs]⟩,
        ⟨hx26f, hx28f, hx27f, hx21f, hx23f⟩,
        enc_sp_bound_of_kit kit ikit hsp_le, ?_⟩)
    dsimp only [EncTailVPlaced, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailVPlaced]
    rw [segLoad_encTail_mem_retag_eq (A' := A.atState lim st4 sf) kit st0 ikit ist0 C ctl S x
      (answersOfLoad (.ok (some r))) _ R s0]
    have hm_eq : x.model C S uuidTryParse (answersOfLoad (.ok (some r))) =
        (.error (.sessionNotFound x.rem.val "message_encrypt"), [.loadSession x.rem.val]) := by
      unfold EncryptGhost.model messageEncrypt Api.run storeCall answersOfLoad
      simp only [ExceptT.run, StateT.run, bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
        ExceptT.lift, StateT.bind, pure, ExceptT.pure, StateT.pure, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, monadLift, MonadLift.monadLift,
        MonadLiftT.monadLift, StateT.map, Functor.map, throw, throwThe, MonadExceptOf.throw, hcur]
      rfl
    have hfinal :
        kit.storeFinal st0 (answersOfLoad (.ok (some r)))
          (x.model C S uuidTryParse (answersOfLoad (.ok (some r)))).2 = st0 := by
      rw [congrArg Prod.snd hm_eq]; rfl
    have hifinal :
        ikit.idFinal ist0 (answersOfLoad (.ok (some r)))
          (x.model C S uuidTryParse (answersOfLoad (.ok (some r)))).2 = ist0 := by
      rw [congrArg Prod.snd hm_eq]; rfl
    rw [draws_answersOfLoad_some_none S x r hcur, hfinal, hifinal]
    dsimp only [F_post, sp] at hm_rod
    rw [← A.pool_transport lim st4 sf1 sf hvm_post] at hm_rod
    refine Satisfies.mono ?_ hm_rod
    have hpoll := pollWith_0x9d0_fold (s0.sp - 0xbe0#64)
      w3' msgPtr 15#64 w4 w5 w6 tail htail
    have hrec_noCur := recordNoCur_fold_sp110 A.repAlloc (s0.sp - 0xbe0#64) g r htail_inl hcur
    have h280 := memRegion_0x280_0x1ea_fold (s0.sp - 0xbe0#64)
    have hperm_end :
        (msgPtr ↦ᵣ utf8 "message_encrypt") ∗
        ((((x.remA + 0x18#64) ↦₈ x.rem.device) ∗
          recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64
            0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188 ∗
          ((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198 ∗
          (((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗
            memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
            ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64)) ∗
            ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA) ∗
            ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
            ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
            ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
            ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
            vecGhostAt A.repAlloc x.rem.name x.remA ∗
            memRegion (x.remA + 0x19#64) 7 ∗
            vecU8Buf A.repAlloc cap ptr x.rem.name.bytes ∗
            A.pool lim st4 sf ∗
            stackAt (s0.sp - 0xbe0#64) encSubStack ∗
            (recordHeap A.repAlloc g r ∗
              memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
              dispatchFrameNoRecPlaced kit st0 ikit ist0 ctl x s0))) ∗ R) =
        (memRegion (s0.sp - 0xbe0#64) 0x50 ∗
          ((s0.sp - 0xbe0#64 + 0x50#64) ↦₆₄ (s0.sp - 0xbe0#64 + 0x128#64))) ∗
        (recordWords56At (s0.sp - 0xbe0#64 + 0x110#64) g.prevCap g.prevPtr 0#64
          0xFFFFFFFFFFFFFFFF#64 w4 w5 w6 ∗
          ((s0.sp - 0xbe0#64 + 0x148#64) ↦ₛ tail) ∗ recordHeap A.repAlloc g r) ∗
        (memRegion (s0.sp - 0xbe0#64 + 0x280#64) 0x1e8 ∗
          ((s0.sp - 0xbe0#64 + 0x468#64) ↦₈ 0#8) ∗ ((s0.sp - 0xbe0#64 + 0x469#64) ↦₈ 0#8)) ∗
        ((memRegion (s0.sp - 0xbe0#64 + 0x46a#64) 0x116 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x580#64) 368 ∗
          memRegion (s0.sp - 0xbe0#64 + 0x6f0#64) 8 ∗
          ((s0.sp - 0xbe0#64 + 0x6f8#64) ↦ₛ tail) ∗
          ((s0.sp - 0xbe0#64 + 0x830#64) ↦₆₄ w4) ∗
          ((s0.sp - 0xbe0#64 + 0x838#64) ↦₆₄ w5) ∗
          ((s0.sp - 0xbe0#64 + 0x840#64) ↦₆₄ w6) ∗
          memRegion (s0.sp - 0xbe0#64 + 0x848#64) 0x188) ∗
        (((s0.sp - 0xbe0#64 + 0x9d0#64) ↦₆₄ w3') ∗
          ((s0.sp - 0xbe0#64 + 0x9d8#64) ↦₆₄ msgPtr) ∗
          ((s0.sp - 0xbe0#64 + 0x9e0#64) ↦₆₄ 15#64)) ∗
        memRegion (s0.sp - 0xbe0#64 + 0x9e8#64) 0x198) ∗
        (encSpillsInit kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
          ((s0.sp - 0xbe0#64 + 0x108#64) ↦₆₄ x.remA)) ∗
        ((vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗ (msgPtr ↦ᵣ utf8 "message_encrypt")) ∗
          memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st4 sf) ctl x 0 s0 ∗
          (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R)) := by
      dsimp only [dispatchFrameNoRecPlaced, encCommonPlaced, protocolAddressAt, AddrGhost.val]
      change _ = _ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗ (_ ∗
        ((x.ptA ↦ₛ x.ptext) ∗
          (vecGhostAt A.repAlloc x.rem.name x.remA ∗ ((x.remA + 24#64) ↦₈ x.rem.device) ∗
            memRegion (x.remA + 25#64) 7) ∗
          (vecGhostAt A.repAlloc x.loc.name x.locA ∗ ((x.locA + 24#64) ↦₈ x.loc.device) ∗
            memRegion (x.locA + 25#64) 7) ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
          stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st4 sf) ∗ _))))))
      sep_ac_rfl
    rw [hperm_end]
    refine Entails.trans (sepConj_mono (fold_sp58 _ _)
      (sepConj_mono hrec_noCur
        (sepConj_mono h280
          (sepConj_mono hpoll
            (sepConj_mono_left (encSpillsAt_fold _ _ _ _)))))) ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem segLoad_placed_okV [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegLoadSpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init R s0 hfs hpc0 hrun0 hal0 hm0
  refine segLoad_to_dispatch_budget env x st_init R s0 hfs hpc0 hrun0 hal0 hm0 ?_
  intro s st3 sp ans w0 w1 w2 w3 w4 w5 w6 v50 tail hbud3 hsp_eq hpc hmeta hbnds _hw0_ne3 htail
    hl htr hx24 hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  rcases ans with ⟨⟩ | (_ | r)
  · exact segLoad_dispatch_err_budget env x st_init st3 R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hbud3 hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx27 hx21 hx23 hx25 hx26 hx28 hps hm
  · exact segLoad_dispatch_none_budget env x st_init st3 R s0 s sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hbud3 hsp_eq hpc hmeta hbnds.2.2.2.2 htail hl htr hx24 hx26 hx28 hps hm
  · exact segLoad_dispatch_some_budget env x st_init st3 R s0 s r sp w0 w1 w2 w3 w4 w5 w6 v50 tail
      hbud3 hsp_eq hpc hmeta hbnds htail hl htr hx24 hx27 hx21 hx23
      hx25 hx26 hx28 hps hm

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlacedBudget
