/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneBase

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (wsMetaPlaced_of_steps)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore hiding segStoreVPlaced_ok drop_session_structure_local2_head_placed_ok segStore_tail_placed_ok segStore_tail_placed_err wsStoreFixedEnvPlaced wsStoreFixedRestPlaced wsFixed_wsEnv_store_split_placed wsFixed_wsEnv_store_join_placed wsStoreCallPrePlaced wsStoreFramePlaced storeCall_entails_storeCallPre_placed wsStoreCallPostSpatialPlaced wsStorePostCommonRestPlaced storeCallPost_entails_common_placed storePostCommon_err_entails_placed wsStoreTailOkPre_placed wsStoreTailOkPost_placed wsStoreTailOkFramePlaced storePostCommon_ok_pre_tail_placed storePost_ok_entails_placed segStore_call_placed_wp
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown hiding teardown_tail_placed_ok teardownFramePlaced ej_false_expose_placed teardown_post_entails_placed segErrTeardownVPlaced_false teardown_pt_placed_ok ptFramePlaced ej_true_expose_placed pt_post_entails_placed segErrTeardownVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown (
  teardownFramePlaced ej_false_expose_placed teardown_post_entails_placed
  ptFramePlaced ej_true_expose_placed pt_post_entails_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stack_ws_dropLocal2 (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) = wsCalleeStack by decide] at h

private theorem stack_ws_alloc (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (wsCalleeStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (wsCalleeStack - allocHookStack) = wsCalleeStack by decide] at h

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht; omega

private theorem prevCap_ubfm_eq {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + cap <<< 1) <<< 3).toNat = cap.toNat * 24 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  omega

private theorem noneCap_fold (a v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 336 ⊢ memRegion a 344 := by
  rw [memRegion_split a 8 336 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a v)

private theorem rep_curPre_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (ss : BitVec 64) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))) :
    curPre ({ pool := P, live := A.live }) ss cs = curPre A.repAlloc ss cs := by
  rcases cs with _ | ⟨_, _⟩ <;> rfl

private theorem rep_droppableRecordAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (r : BitVec 64) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))) :
    droppableRecordAt ({ pool := P, live := A.live }) r cs = droppableRecordAt A.repAlloc r cs := by
  rcases cs with _ | ⟨_, _⟩ <;> rfl

private theorem rep_apiDecResultAt_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (r : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    apiDecResultAt ({ pool := P, live := A.live }) r res = apiDecResultAt A.repAlloc r res := by
  rcases res with e | _
  · cases e <;> rfl
  · rfl

private theorem rep_resOk_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P1 P2 : SepProp)
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) (F : SepProp) :
    resOk ({ pool := P1, live := A.live }) x28 w20 w21 res w0 w1 w2 w3 w4 F =
    resOk ({ pool := P2, live := A.live }) x28 w20 w21 res w0 w1 w2 w3 w4 F := by
  unfold resOk
  simp only [rep_apiDecResultAt_eq]

private theorem rep_stagedRes_eq {M : AllocCostModel} (A : RustCliAllocBudget M) (P : SepProp)
    (x28 w20 w21 src : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    StagedRes ({ pool := P, live := A.live }) x28 w20 w21 src res =
    StagedRes A.repAlloc x28 w20 w21 src res := by
  unfold StagedRes
  simp only [rep_apiDecResultAt_eq]

private theorem rep_ptFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    ptFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp cs x28 w20 w21 res =
    ptFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp cs x28 w20 w21 res := by
  unfold ptFramePlaced
  simp only [rep_droppableRecordAt_eq, rep_stagedRes_eq]
  rfl

private theorem rep_teardownFrame_eq [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (P1 P2 : SepProp) (ctl : BitVec 64)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (F : SepProp) :
    teardownFramePlaced C ({ pool := P1, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P1, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P1, live := A.live }) ikit)
      x ans s0 sp F =
    teardownFramePlaced C ({ pool := P2, live := A.live }) ctl
      (retagSessionStore (A' := { pool := P2, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P2, live := A.live }) ikit)
      x ans s0 sp F := rfl

private theorem rep_decStoreExtra_eq [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (P : SepProp)
    (kit : SessionStoreSpec A.repAlloc 0#64) (ikit : IdentityStoreSpec A.repAlloc 0#64)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    decStoreExtraPlaced (retagSessionStore (A' := { pool := P, live := A.live }) kit)
      (retagIdentityStore (A' := { pool := P, live := A.live }) ikit) st ist s0 =
    decStoreExtraPlaced kit ikit st ist s0 := rfl

private theorem rep_storeFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, retagSessionStore, ih]

private theorem rep_callsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagSessionStore (A' := A') kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, retagSessionStore, ih]

private theorem rep_idFinal_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idFinal ist0 ans calls = ikit.idFinal ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [Identity.IdentityStoreSpec.idFinal, retagIdentityStore, ih]

private theorem rep_idCallsRel_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).idCallsRel ist0 ans calls = ikit.idCallsRel ist0 ans calls := by
  induction calls generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [Identity.IdentityStoreSpec.idCallsRel, retagIdentityStore, ih]

private theorem rep_callEvs_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    (retagIdentityStore (A' := A') ikit).callEvs (retagSessionStore (A' := A') kit) encRecord ans =
      ikit.callEvs kit encRecord ans := by
  ext c; cases c <;> rfl

private theorem rep_traceOfWith_eq {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (kit : SessionStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (retagIdentityStore (A' := A') ikit).traceOfWith (retagSessionStore (A' := A') kit) encRecord ans calls =
      ikit.traceOfWith kit encRecord ans calls := by
  simp only [Identity.IdentityStoreSpec.traceOfWith, rep_callEvs_eq]

set_option maxHeartbeats 1600000 in
theorem teardown_tail_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {st_b : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hdrop2 : DropSessionStructureLocal2BudgetOk A lim H)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64}
    {cs : Option (SessionGhost × SessionState (List (BitVec 8)))}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = errJoinPCPlaced false)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 ≠ pendingTag) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) :
    SepWP (lsProg_463 H) resultFinalPCPlaced s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A.repAlloc (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗
          ((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x300#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x308#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x310#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdrop := drop_session_structure_local2_head_placed_ok hdrop2
  have hdealloc := deallocBudget_463 hdealloc_sat
  have hx28n : s.readReg64 (Reg.gpr 28#5) ≠ pendingTag := hx28
  have hx28' : (s.readReg64 (Reg.gpr 28#5) + 3#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  have hx28b : (s.readReg64 (Reg.gpr 28#5) + 3#64 != 0#64) = true := by
    rw [bne_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  simp only [errJoinPCPlaced, Bool.false_eq_true, ↓reduceIte] at hpc
  unfold resultFinalPCPlaced
  dsimp only [lsProg_463] at hdrop ⊢
  rcases cs with _ | ⟨G, st⟩
  · clear hcrl hdrop
    have hnone : (noneCap + 1#64 == 0#64) = true := by decide
    simp only [curPre]
    wp_simp_pre [sepConj_assoc]
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      by_vm_open (
        wp_steps
        have hfold := noneCap_fold (s.sp + 0x138#64) noneCap
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
        apply SepWP.fold hfold (by sep_focus)
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm1 hm_final
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm1
        have hpool1 := A.pool_transport lim st_b s s_end hvm1
        rw [← hpool1] at hm_final
        refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
        refine Entails.sepExists_right [] ?_
        refine Entails.pure_right FreeOnlyEvs.nil ?_
        dsimp only [AllocCostModel.stepEvents, List.foldl]
        exact Entails.of_eq (by sep_ac_rfl))
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (A.block_valid prevPtr (prevCap.toNat * 24) 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_prev⟩, _⟩
      apply sepWP_cut_here (mid := lsρ lsRustDeallocSym)
      by_vm_open (
        wp_steps
        have hfold := noneCap_fold (s.sp + 0x138#64) noneCap
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
        apply SepWP.fold hfold (by sep_focus)
        apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm1
        refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
        have hmul := prevCap_ubfm_eq hprev_lt
        wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, st_b)
        have hsp_sf : sf.sp = s.sp := by simp_all
        wp_conv_pre => simp only [hsp_sf]
        apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm2 hm_final
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
          have hpool2 := A.pool_transport lim (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st_b) sf s_end hvm2
          rw [← hpool2] at hm_final
          refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (rustDeallocEvents (prevCap.toNat * 24) 8) ?_
          exact Entails.pure_right (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
            (Entails.of_eq (by sep_ac_rfl))))
  · simp only [curPre]
    wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
    have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hlik_cap
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp)) (by sep_focus)
    apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 442) hcrl
    clear hcrl
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1 hcrl1
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
      have ⟨hcl1, hro1⟩ := hcrl1
      wp_call hdrop (⟨s.sp + 312#64, G, st⟩, st_b)
      clear hcrl1 hcl1 hro1
      have hsp_sf : sf.sp = s.sp := by simp_all
      wp_conv_pre => simp only [hsp_sf]
      apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp).symm) (by sep_focus)
      by_cases hcap : prevCap = 0#64
      · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm2 hm_final
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
          have hpool2 := A.pool_transport lim (M.stepEvents w st_b) sf s_end hvm2
          rw [← hpool2] at hm_final
          refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right w ?_
          exact Entails.pure_right (by simp_all) (Entails.of_eq (by sep_ac_rfl)))
      · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
        simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
        apply SepWP.fold (A.block_valid prevPtr (prevCap.toNat * 24) 8) (by sep_focus)
        wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
        apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_prev⟩, _⟩
        apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
        apply sepWP_cut_here (mid := lsρ lsRustDeallocSym)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm2
          refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
          have hmul := prevCap_ubfm_eq hprev_lt
          wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, M.stepEvents w st_b)
          have hsp_sf1 : sf_1.sp = s.sp := by simp_all
          wp_conv_pre => simp only [hsp_sf1, hsp_sf]
          apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
          by_vm_open (
            wp_steps
            refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm3 hm_final
            let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm3
            have hpool3 := A.pool_transport lim
              (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) (M.stepEvents w st_b)) sf_1 s_end hvm3
            rw [← hpool3] at hm_final
            refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
            refine Entails.sepExists_right (w ++ rustDeallocEvents (prevCap.toNat * 24) 8) ?_
            have hfree : FreeOnlyEvs (w ++ rustDeallocEvents (prevCap.toNat * 24) 8) :=
              FreeOnlyEvs.append (by simp_all) (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
            refine Entails.pure_right hfree ?_
            simp only [← M.stepEvents_append]
            exact Entails.of_eq (by sep_ac_rfl))))

attribute [local semireducible] SepWP in
theorem segErrTeardownVPlaced_false [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hyps : DecHypsVBudget C A lim uuidTryParse S encRecord H kit kitEnv ikit ikitEnv Scope)
    (hdrop2 : DropSessionStructureLocal2BudgetOk A lim H)
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State}
    (hstB : ErrJoinStateVBudget C A lim ctl uuidTryParse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s) :
    DecSegVBudget C A lim ctl uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s
      (fun s' => ResultFinalStateVBudget C A lim ctl uuidTryParse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init R s0 s') := by
  intro hL
  rcases hstB with ⟨st_b, hsb, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  rw [rep_callsRel_eq] at hcalls
  rw [rep_idCallsRel_eq] at hid_calls
  rw [rep_traceOfWith_eq] at htr
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  let A0 := A.atState lim st_b s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtraPlaced kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedVPlaced kit0 ikit0 x s0 s.sp ∗ wsEnvPlaced A0 x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A0 (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A0 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
    dsimp only [A0, kit0, ikit0, R', RustCliAllocBudget.atState] at hm ⊢
    simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm
  have hm_pre := Satisfies.mono (ej_false_expose_placed C A0 ctl kit0 ikit0 x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  have hm_pre' : s.mem ⊨
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A.repAlloc (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0) ∗ ((s.sp + 0x308#64) ↦₆₄ t1) ∗ ((s.sp + 0x310#64) ↦₆₄ t2) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3) ∗ ((s.sp + 0x320#64) ↦₃₂ t4) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x588#64) ↦₆₄ w1) ∗ ((s.sp + 0x590#64) ↦₆₄ w2) ∗
        ((s.sp + 0x598#64) ↦₆₄ w3) ∗ ((s.sp + 0x5a0#64) ↦₃₂ w4) ∗
        A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack) ∗
      (teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R') := by
    unfold teardownPre at hm_pre
    dsimp only [A0, RustCliAllocBudget.atState] at hm_pre ⊢
    simpa only [rep_curPre_eq] using hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_placed_ok (st_b := st_b) (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R')
      hyps.hooks.dealloc hdrop2 hcrl hpc hrun hsp_align hx28 hx26 hprev_lt
      (teardownFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp F ∗ R') hm_pre' hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmf'
  rcases hmf' with ⟨evs_td, hmf'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'
  rcases hmf' with ⟨hevs_td, hmf'⟩
  have hsb1 := hsb.advance_freeOnly hevs_td
  let st_b1 := M.stepEvents evs_td st_b
  let A1 := A.atState lim st_b1 sf
  let kit1 := retagSessionStore (A' := A1) kit
  let ikit1 := retagIdentityStore (A' := A1) ikit
  have hres1 : resOk A1 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21)
      (x.model C S uuidTryParse ans).1 w0 w1 w2 w3 w4 F := by
    dsimp only [A0, A1, RustCliAllocBudget.atState] at hres ⊢
    rwa [rep_resOk_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 sf)] at hres
  have hmf_a1 : sf.mem ⊨
      teardownPost A1 s.sp prevCap prevPtr w0 w1 w2 w3 w4 ∗
        (teardownFramePlaced C A1 ctl kit1 ikit1 x ans s0 s.sp F ∗ R') := by
    unfold teardownPost
    dsimp only [A0, A1, kit0, ikit0, kit1, ikit1, st_b1, RustCliAllocBudget.atState] at hmf' ⊢
    rwa [rep_teardownFrame_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 sf)] at hmf'
  have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres1) hmf_a1
  refine ⟨sf, hsteps, Or.inl ⟨st_b1, hsb1, hpc2, hmeta2, ans, hpan, hscope, ?_, ?_, ?_, ?_⟩⟩
  · rwa [rep_callsRel_eq]
  · rwa [rep_idCallsRel_eq]
  · rw [htr2, htr]; exact congrArg (s0.trace ++ ·) (rep_traceOfWith_eq _ _ _ _ _).symm
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]
    dsimp only [A1, kit1, ikit1, R', RustCliAllocBudget.atState] at hm_fin ⊢
    simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm_fin

theorem teardown_pt_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {st_b : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    {s : State} {R : SepProp} {cap ptr len : BitVec 64}
    (hpc : s.pc = errJoinPCPlaced true)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (lsProg_463 H) (errJoinPCPlaced false) s
      (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗
          ((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x2a0#64) ↦₆₄ len) ∗ A.pool lim (M.stepEvents evs st_b) sf ∗
          stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdealloc := deallocBudget_463 hdealloc_sat
  simp only [errJoinPCPlaced, ↓reduceIte] at hpc
  simp only [errJoinPCPlaced, Bool.false_eq_true, ↓reduceIte]
  dsimp only [lsProg_463]
  by_cases hcap : cap = 0
  · subst hcap; simp only [↓reduceIte, emp_sepConj]
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1 hm_final
      let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm1
      have hpool1 := A.pool_transport lim st_b s s_end hvm1
      rw [← hpool1] at hm_final
      refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right [] ?_
      refine Entails.pure_right FreeOnlyEvs.nil ?_
      dsimp only [AllocCostModel.stepEvents, List.foldl]
      exact Entails.of_eq (by sep_ac_rfl))
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap, ↓reduceIte]
    apply SepWP.fold (A.block_valid ptr cap.toNat 1) (by sep_focus)
    wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow1, hbound_pt⟩, _⟩
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
    apply sepWP_cut_here (mid := lsρ lsRustDeallocSym)
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
      wp_call hdealloc (ptr, cap.toNat, 1, st_b)
      have hsp_sf : sf.sp = s.sp := by simp_all
      wp_conv_pre => simp only [hsp_sf]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (rustDeallocEvents cap.toNat 1) ?_
      exact Entails.pure_right (freeOnlyEvs_rustDeallocEvents cap.toNat 1)
        (Entails.of_eq (by sep_ac_rfl)))

attribute [local semireducible] SepWP in
theorem segErrTeardownVPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegErrTeardownSpecVBudget C A lim ctl uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope := by
  intro hyps hdrop2 x st_init pt R s0 s hstB
  cases pt with
  | false => exact segErrTeardownVPlaced_false hyps hdrop2 hstB
  | true =>
    intro hL
    rcases hstB with ⟨st_b, hsb, hst⟩
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    rw [rep_callsRel_eq] at hcalls
    rw [rep_idCallsRel_eq] at hid_calls
    rw [rep_traceOfWith_eq] at htr
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    let A0 := A.atState lim st_b s
    let kit0 := retagSessionStore (A' := A0) kit
    let ikit0 := retagIdentityStore (A' := A0) ikit
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedVPlaced kit0 ikit0 x s0 s.sp ∗ wsEnvPlaced A0 x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A0 (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A0 (s.sp + 0x290#64) p) ∗
        StagedRes A0 (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
      dsimp only [A0, kit0, ikit0, R', RustCliAllocBudget.atState] at hm ⊢
      simpa only [rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm
    have hm_pre := Satisfies.mono (ej_true_expose_placed C A0 ctl kit0 ikit0 x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    have hm_pre' : s.mem ⊨
        (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
          (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
          A.pool lim st_b s ∗ stackAt s.sp wsCalleeStack) ∗
        (ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') := by
      unfold ptPre at hm_pre
      dsimp only [A0, RustCliAllocBudget.atState] at hm_pre
      exact hm_pre
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_placed_ok (st_b := st_b) (cap := cap) (ptr := ptr) (len := len)
        (R := ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.hooks.dealloc hpc hrun hsp_align
        (ptFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre' hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_pt, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨hevs_pt, hm1'⟩
    have hsb1 := hsb.advance_freeOnly hevs_pt
    let st_b1 := M.stepEvents evs_pt st_b
    let A1 := A.atState lim st_b1 s1
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_a1 : s1.mem ⊨
        ptPost A1 s.sp cap ptr len ∗
          (ptFramePlaced C A1 ctl kit1 ikit1 x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
            (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') := by
      unfold ptPost
      dsimp only [A0, A1, kit0, ikit0, kit1, ikit1, st_b1, RustCliAllocBudget.atState] at hm1' ⊢
      rwa [rep_ptFrame_eq (P1 := A.pool lim st_b s) (P2 := A.pool lim st_b1 s1)] at hm1'
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1_a1
    have hstB1 : ErrJoinStateVBudget C A lim ctl uuidTryParse S encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope x st_init false R s0 s1 := by
      refine ⟨st_b1, hsb1, hpc1, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, ?_, ?_, ?_, ?_⟩
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rwa [rep_callsRel_eq]
      · rwa [rep_idCallsRel_eq]
      · rw [htr1, htr]; exact congrArg (s0.trace ++ ·) (rep_traceOfWith_eq _ _ _ _ _).symm
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        dsimp only [A1, kit1, ikit1, R', RustCliAllocBudget.atState] at hm1_f ⊢
        simpa only [Bool.false_eq_true, ↓reduceIte, rep_decStoreExtra_eq, rep_storeFinal_eq, rep_idFinal_eq, sepConj_assoc] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownVPlaced_false hyps hdrop2 hstB1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlacedBudget
