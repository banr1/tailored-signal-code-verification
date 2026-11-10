/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (
  pollOutPlacedRel shim_463 box_lscro_463)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore hiding drop_session_structure_local2_head_placed_ok segStore_tail_placed_ok segStore_tail_placed_err wsStoreFixedEnvPlaced wsStoreFixedRestPlaced wsFixed_wsEnv_store_split_placed wsFixed_wsEnv_store_join_placed wsStoreCallPrePlaced wsStoreFramePlaced storeCall_entails_storeCallPre_placed wsStoreCallPostSpatialPlaced wsStorePostCommonRestPlaced storeCallPost_entails_common_placed storePostCommon_err_entails_placed wsStoreTailOkPre_placed wsStoreTailOkPost_placed wsStoreTailOkFramePlaced storePostCommon_ok_pre_tail_placed storePost_ok_entails_placed segStore_call_placed_wp

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stack_seg_alloc (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - BitVec.ofNat 64 storeSegStack) (storeSegStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (storeSegStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (storeSegStack - allocHookStack) = storeSegStack by decide] at h

private theorem stack_seg_dropLocal2 (sp : BitVec 64) :
    stackAt sp storeSegStack =
      memRegion (sp - 16416#64) (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (storeSegStack - FromRecordCallees.dropSessionStructureLocal2Stack) = storeSegStack by decide] at h

def dropSessionStructureLocal2HeadBudgetSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FromRecordCallees.DropSessionStructureGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0 ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt_shared_lb A.repAlloc x.G.localIk x.ss ∗
      sessionStateAfterLocalIk_shared_lb A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗ stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

theorem drop_session_structure_local2_head_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdrop2 : DropSessionStructureLocal2BudgetOk A lim H) :
    subroutine_ok (lsProg_463 H) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2HeadBudgetSpec A lim)) := by
  refine subroutine_ok_mono_entails hdrop2 (fun (x, st) s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [StoreKit.withLsRoCl, dropSessionStructureLocal2BudgetSpec,
    dropSessionStructureLocal2HeadBudgetSpec]
  rw [sessionStateAt_unfold_cap_shared_lb]
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hx0, hlen, hcap, hptr, hlr⟩
  exact Entails.pure_right ⟨hx0, hlr⟩ (Entails.pure_right ⟨hlen, hcap, hptr⟩ (Entails.refl _))

set_option maxHeartbeats 1600000 in
theorem segStore_tail_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {st_b : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hdrop2 : DropSessionStructureLocal2BudgetOk A lim H)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64} {G : SessionGhost}
    {st : SessionState (List (BitVec 8))} {v1 : BitVec 32} {v2 v3 : BitVec 64} {v4 : BitVec 32}
    {s0_580 s1_588 : BitVec 64} {s2_lo s2_hi : BitVec 32} {s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_463).base + 9256#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.ok ())) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hx22 : s.readReg64 .x22 = s.sp + 0x294#64) (hprev_lt : prevCap.toNat * 24 < 2 ^ 63)
    (_hprev_ptr : prevPtr ≠ 0) :
    SepWP (lsProg_463 H) resultFinalPCPlaced s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        sessionStateAt A.repAlloc (s.sp + 0x138#64) G st ∗
        ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₃₂ s2_lo) ∗
        ((s.sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool lim st_b s ∗ stackAt s.sp storeSegStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ⌜FreeOnlyEvs evs⌝ ∗
          ((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
          ((s.sp + 0x300#64) ↦₆₄ v2) ∗ ((s.sp + 0x308#64) ↦₆₄ v3) ∗ ((s.sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ v2) ∗ ((s.sp + 0x588#64) ↦₆₄ v3) ∗ ((s.sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp storeSegStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = okTagVec ∧
        sf.readReg64 .x20 = (v1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = v1.zeroExtend 64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdrop := drop_session_structure_local2_head_placed_ok hdrop2
  have hdealloc := deallocBudget_463 hdealloc_sat
  unfold resultFinalPCPlaced
  dsimp only [lsProg_463] at hdrop ⊢
  simp only [pollTag] at hx28
  wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_shared_lb hlik_cap
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp)) (by sep_focus)
  apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 442) hcrl
  clear hcrl
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    rintro hvm1 ⟨hcl1, hro1⟩
    refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    wp_call hdrop (⟨s.sp + 312#64, G, st⟩, st_b)
    clear hcl1 hro1
    have hsp_sf : sf.sp = s.sp := by simp_all
    wp_conv_pre => simp only [hsp_sf]
    apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp).symm) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (pointsTo64_append32 s2_hi v4 (s.sp + 0x590#64)).symm) (by sep_focus)
    have hv1_ubfx :
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 v1 >>> 8)) =
          BitVec.setWidth 64 v1 >>> 8 := by bv_omega
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm2 hm_final
        let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2
        have hpool2 := A.pool_transport lim (M.stepEvents w st_b) sf s_end hvm2
        rw [← hpool2] at hm_final
        refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all [okTagVec]⟩
        refine Entails.sepExists_right w ?_
        exact Entails.pure_right (by simp_all) (Entails.of_eq (by sep_ac_rfl)))
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (A.block_valid prevPtr (prevCap.toNat * 24) 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_prev⟩, _⟩
      apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp)) (by sep_focus)
      apply sepWP_cut_here (mid := lsρ lsRustDeallocSym)
      by_vm_open (
        wp_steps
        refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm2
        refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
        have hmul := prevCap_ubfm_eq_shared_lb hprev_lt
        wp_call hdealloc (prevPtr, prevCap.toNat * 24, 8, M.stepEvents w st_b)
        have hsp_sf1 : sf_1.sp = s.sp := by simp_all
        wp_conv_pre => simp only [hsp_sf1, hsp_sf]
        apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp).symm) (by sep_focus)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm3 hm_final
          let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm3
          have hpool3 := A.pool_transport lim
            (M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) (M.stepEvents w st_b)) sf_1 s_end hvm3
          rw [← hpool3] at hm_final
          refine ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all [okTagVec]⟩
          refine Entails.sepExists_right (w ++ rustDeallocEvents (prevCap.toNat * 24) 8) ?_
          have hfree : FreeOnlyEvs (w ++ rustDeallocEvents (prevCap.toNat * 24) 8) :=
            FreeOnlyEvs.append (by simp_all) (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
          refine Entails.pure_right hfree ?_
          simp only [← M.stepEvents_append]
          exact Entails.of_eq (by sep_ac_rfl))))

theorem segStore_tail_placed_err [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {R : SepProp} {o1 : BitVec 32} {o2 o3 o4 o5 : BitVec 64} {o6 : BitVec 32}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    (hpc : s.pc = (blkPl_463).base + 9256#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = pollTag (.error ())) (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (lsProg_463 H) (errJoinPCPlaced true) s
      (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
        ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0))
      (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
          ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗ ((s.sp + 0x590#64) ↦₆₄ o4) ∗
          ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (o1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = o1.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)) := by
  simp only [errJoinPCPlaced, ↓reduceIte]
  dsimp only [lsProg_463]
  simp only [pollTag] at hx28
  wp_steps_vm

set_option maxHeartbeats 3200000 in
theorem segStore_call_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {st_b : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hkit : SessionOnlyKitBudgetOkSE A lim kit kitEnv Scope encRecord H)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st_b (StoreStepEnv kit kitEnv st addr.val record))
    (haddr : kit.addrOk addr.val)
    (hrecOk : kit.RecOk record)
    (hpc : s.pc = storeCallPCPlaced)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hfs : FsAt kit.envOk Q (lsProg_463 H) s) :
    SepWPp (lsProg_463 H) ((blkPl_463).base + 9256#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
        (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
        ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x550#64) ↦₆₄ d0) ∗ ((s.sp + 0x558#64) ↦₆₄ d1) ∗ ((s.sp + 0x560#64) ↦₆₄ d2) ∗
        ((s.sp + 0x568#64) ↦₆₄ d3) ∗ ((s.sp + 0x570#64) ↦₃₂ d5) ∗ memRegion (s.sp + 0x5f0#64) 48 ∗
        protocolAddressAt A.repAlloc addr addrA ∗ sessionRecordAt A.repAlloc (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool lim st_b s ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧
            sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans ∧
            StoreStepEnv kit kitEnv st addr.val record evs⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0xf8#64) ↦₆₄ self) ∗ ((s.sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
          ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
          (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
          ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
          ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff) ∗
          ((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗ ((s.sp + 0x560#64) ↦₆₄ o4) ∗
          ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ pollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗ ((s.sp + 0x60c#64) ↦₆₄ o4) ∗
          ((s.sp + 0x614#64) ↦₆₄ o5) ∗ ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          protocolAddressAt A.repAlloc addr addrA ∗ sessionRecordAt A.repAlloc (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) := by
  have hshim := shim_463 (hkit.storeShim (p := lsProg_463 H) (i := 463) (by decide))
  have hdrop := futDropBudget_463 (hkit.storeFutDrop (p := lsProg_463 H) (i := 463) (by decide))
  have hfits_sh : FitsEnv M lim st_b (BoxAllocEnv kit.storeBoxSize) := hfits.seq_left
  unfold storeCallPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc := deallocBudget_463 hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_storeCall_to_storeShim kit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := kit.storeShimOff) hcrl
  clear hcrl
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hcrl1
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    cli_messageDecrypt_call_panic_p_budget_lscro hshim hcrl1
      ((⟨self, addrA, s.readReg64 .x26 + 0x80#64⟩ : StoreShimCall), st_b)
    clear hcrl1 hshim
    apply StoreKit.sepWPp_seq_lscro (mid := kit.storePollOff) hcrl_sf
    clear hcrl_sf
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (evs_sh : List AllocEvent)
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf, hevs_sh⟩
    have hfits_rem := hfits.seq_right hevs_sh
    have hfits_pl : FitsEnv M lim (M.stepEvents evs_sh st_b) (kitEnv.storePollEnv st addr.val record) :=
      hfits_rem.seq_left
    have henv : kit.envOk sf.fs.files :=
      (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
    clear hsteps_sh hfs
    apply SepWP.fold (Entails.of_eq (stack_storeShim_to_storePoll kit s.sp hstack_lt)) (by sep_focus)
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hcrl2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      have hpoll := box_lscro_463 (hkit.storePoll (p := lsProg_463 H) (i := 463) (by decide))
      cli_messageDecrypt_call_panic_budget_lscro hpoll hcrl2
        (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64,
          ⟨addrA, addr, s.readReg64 .x26 + 0x80#64, g, record⟩⟩, self, st, M.stepEvents evs_sh st_b)
      clear hcrl2 hpoll hkit
      generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
      simp only [hsp_sf] at hsp_sf_1 ⊢
      have hdz : kit.storeFutDropOff ≠ 0#64 := by
        simpa only [BitVec.zero_add] using kit.storeFutDrop_ne_zero (by decide)
      have hdz' : (kit.storeFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
      have hbs := kit.storeBoxSize_ne_zero
      have hbs' : (BitVec.ofNat 64 kit.storeBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
      have hbs_pos : 0 < kit.storeBoxSize := Nat.pos_of_ne_zero (fun h => hbs (by simp [h]))
      have hbs_toNat : (BitVec.ofNat 64 kit.storeBoxSize).toNat = kit.storeBoxSize :=
        Nat.mod_eq_of_lt kit.storeBoxSize_lt
      have hevs_dealloc : BoxDeallocEnv kit.storeBoxSize (rustDeallocEvents kit.storeBoxSize 8) :=
        Or.inr ⟨hbs_pos, rfl⟩
      apply SepWP.fold (A.block_valid box kit.storeBoxSize 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_box⟩, _⟩
      rcases w with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
      · dsimp only [StoreKit.storePollPlacedOutAt]
        wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (strPtr : BitVec 64)
        apply SepWP.exists_elim; intro (vt : BitVec 64)
        apply SepWP.exists_elim; intro (w5 : BitVec 64)
        apply SepWP.fold
          (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
          (by sep_focus)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := kit.storeFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, kit.storeBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st_b))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
          simp only [show (9223372036854775834#64 : BitVec 64) = pollTag (.error ()) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents kit.storeBoxSize 8))
            (Entails.sepExists_right (.error ())
            (Entails.sepExists_right box
            (Entails.sepExists_right strPtr
            (Entails.sepExists_right vt
            (Entails.sepExists_right (strPtr.extractLsb' 0 32)
            (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
            (Entails.sepExists_right 4294967296#64
            (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
            (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
            (Entails.sepExists_right (w5.extractLsb' 32 32) ?_))))))))))
          have henv_step : StoreStepEnv kit kitEnv st addr.val record
              (evs_sh ++ (w_1 ++ rustDeallocEvents kit.storeBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [Bool.false_eq_true, ↓reduceIte, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))
      · dsimp only [StoreKit.storePollPlacedOutAt]
        have hm40 : memRegion (s.sp + 1528#64) 40 =
            ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
              ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
              ((s.sp + 1528#64) ↦₆₄ w5) ∗ ((s.sp + 1536#64) ↦₆₄ w4) ∗
                ((s.sp + 1544#64) ↦₆₄ w3) ∗ ((s.sp + 1552#64) ↦₆₄ w2) ∗
                ((s.sp + 1560#64) ↦₆₄ w1) := by
          rw [show (40 : Nat) = 8 + (8 + (8 + (8 + 8))) from rfl,
            memRegion_split (s.sp + 1528#64) 8 32 (by decide),
            memRegion_split (s.sp + 1528#64 + 8#64) 8 24 (by decide),
            memRegion_split (s.sp + 1528#64 + 8#64 + 8#64) 8 16 (by decide),
            memRegion_split (s.sp + 1528#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          rw [ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
            ProofLib.memRegion_eight, ProofLib.memRegion_eight]
          simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd, hm40, sepExists_sepConj_left, sepExists_sepConj_right]
        apply SepWP.exists_elim; intro (w1 : BitVec 64)
        apply SepWP.exists_elim; intro (w2 : BitVec 64)
        apply SepWP.exists_elim; intro (w3 : BitVec 64)
        apply SepWP.exists_elim; intro (w4 : BitVec 64)
        apply SepWP.exists_elim; intro (w5 : BitVec 64)
        apply SepWP.fold
          (Entails.of_eq (out_repack_sp s.sp w5 w4 w3 w2 w1))
          (by sep_focus)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := kit.storeFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, kit.storeBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st_b))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
          simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = pollTag (.ok ()) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents kit.storeBoxSize 8))
            (Entails.sepExists_right (.ok ())
            (Entails.sepExists_right box
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right (w5.extractLsb' 0 32)
            (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
            (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
            (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
            (Entails.sepExists_right (w1.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
            (Entails.sepExists_right (w1.extractLsb' 32 32) ?_))))))))))
          have henv_step : StoreStepEnv kit kitEnv st addr.val record
              (evs_sh ++ (w_1 ++ rustDeallocEvents kit.storeBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [↓reduceIte, emp_sepConj, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))))

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlacedBudget
