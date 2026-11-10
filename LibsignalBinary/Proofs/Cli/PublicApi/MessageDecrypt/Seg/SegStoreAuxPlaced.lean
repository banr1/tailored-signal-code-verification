/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStoreAux
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore hiding drop_session_structure_local2_head_placed_ok segStore_tail_placed_ok segStore_tail_placed_err wsStoreFixedEnvPlaced wsStoreFixedRestPlaced wsFixed_wsEnv_store_split_placed wsFixed_wsEnv_store_join_placed wsStoreCallPrePlaced wsStoreFramePlaced storeCall_entails_storeCallPre_placed wsStoreCallPostSpatialPlaced wsStorePostCommonRestPlaced storeCallPost_entails_common_placed storePostCommon_err_entails_placed wsStoreTailOkPre_placed wsStoreTailOkPost_placed wsStoreTailOkFramePlaced storePostCommon_ok_pre_tail_placed storePost_ok_entails_placed segStore_call_placed_wp

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
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


theorem drop_session_structure_local2_head_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H) :
    subroutine_ok (lsProg_463 H) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2HeadSpec_shared_lb A)) := by
  refine subroutine_ok_mono_entails hdrop2 (fun x s0 => ?_) (fun _ _ _ => Entails.refl _)
  dsimp only [StoreKit.withLsRoCl, FromRecordCallees.dropSessionStructureLocal2Spec,
    dropSessionStructureLocal2HeadSpec_shared_lb]
  rw [sessionStateAt_unfold_cap_shared_lb]
  simp only [sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hx0, hlen, hcap, hptr⟩
  exact Entails.pure_right hx0 (Entails.pure_right ⟨hlen, hcap, hptr⟩ (Entails.refl _))

theorem segStore_tail_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
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
        sessionStateAt A (s.sp + 0x138#64) G st ∗
        ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₃₂ s2_lo) ∗
        ((s.sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp storeSegStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x290#64) ↦₃₂ v1) ∗ ((s.sp + 0x294#64) ↦₆₄ v2) ∗ ((s.sp + 0x29c#64) ↦₆₄ v3) ∗ ((s.sp + 0x2a4#64) ↦₃₂ v4) ∗
          ((s.sp + 0x300#64) ↦₆₄ v2) ∗ ((s.sp + 0x308#64) ↦₆₄ v3) ∗ ((s.sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ v2) ∗ ((s.sp + 0x588#64) ↦₆₄ v3) ∗ ((s.sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp storeSegStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = okTagVec ∧
        sf.readReg64 .x20 = (v1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = v1.zeroExtend 64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdrop := drop_session_structure_local2_head_placed_ok hdrop2
  have hdealloc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  unfold resultFinalPCPlaced
  dsimp only [lsProg_463] at hdrop ⊢
  simp only [pollTag] at hx28
  wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
  apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_shared_lb hlik_cap
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp)) (by sep_focus)
  apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 442) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  rintro ⟨hcl1, hro1⟩
  wp_apply
  clear hcl1 hro1
  apply SepWP.fold (Entails.of_eq (stack_seg_dropLocal2 s.sp).symm) (by sep_focus)
  apply SepWP.fold (Entails.of_eq (pointsTo64_append32 s2_hi v4 (s.sp + 0x590#64)).symm) (by sep_focus)
  wp_steps
  by_cases hcap : prevCap = 0#64
  · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
  · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp)) (by sep_focus)
    wp_steps
    have hmul := prevCap_ubfm_eq_shared_lb hprev_lt
    wp_apply
    simp only [hsp_sf] at hsp_sf_1 ⊢
    apply SepWP.fold (Entails.of_eq (stack_seg_alloc s.sp).symm) (by sep_focus)
    wp_steps; wp_done

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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
          ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗ ((s.sp + 0x590#64) ↦₆₄ o4) ∗
          ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (o1 >>> 8#32).zeroExtend 64 ∧ sf.readReg64 .x21 = o1.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) := by
  simp only [errJoinPCPlaced, ↓reduceIte]
  dsimp only [lsProg_463]
  simp only [pollTag] at hx28
  wp_steps
  wp_done

def wsStoreFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  protocolAddressAt A x.rem x.remA ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFixedRestPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decSaveVtableAtV ikit ∗ decTrustVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  FromRecordCallees.lsLogOff ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - storeCallStack kit)

theorem wsFixed_wsEnv_store_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist := by
  subst hsp
  have hj := wsCalleeStack_join_extra_placed kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnvPlaced A x (s0.sp - 0xee0#64) ∗
      decStoreExtraPlaced kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsEnvPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hj) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decStoreVtableAtV
    wsStoreFixedEnvPlaced wsStoreFixedRestPlaced
  simp only [BitVec.zero_add]
  rw [stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_store_join_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  subst hsp
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  refine Entails.trans (Entails.of_eq (show
    wsStoreFixedEnvPlaced A kit x s0 (s0.sp - 0xee0#64) st ∗
      wsStoreFixedRestPlaced A kit ikit x s0 (s0.sp - 0xee0#64) ist =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeCallStack kit) ∗
        stackAt (s0.sp - 0xee0#64) (storeCallStack kit))) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decStoreVtableAtV
      wsStoreFixedEnvPlaced wsStoreFixedRestPlaced
    simp only [BitVec.zero_add]; ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPrePlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (c0 c1 d0 d1 d2 d3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x550#64) ↦₆₄ d0) ∗ ((sp + 0x558#64) ↦₆₄ d1) ∗ ((sp + 0x560#64) ↦₆₄ d2) ∗
  ((sp + 0x568#64) ↦₆₄ d3) ∗ ((sp + 0x570#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗ protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStoreFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) (pt : List (BitVec 8)) : SepProp :=
  wsStoreFixedRestPlaced A kit ikit x s0 sp ist ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storeCall_entails_storeCallPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0) ⊢
    ∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
      wsStoreCallPrePlaced A kit x s0 sp r26 g rec' st c0 c1 d0 d1 d2 d3 d5 ∗
      wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_store_split_placed A kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  rw [memRegion_300_b00_split, memRegion_300_280_store_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x550#64) 0x24) ∗
      (wsStoreFixedEnvPlaced A kit x s0 sp st ∗ memRegion (sp + 0x5f0#64) 48 ∗
        wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt) by
    unfold wsStoreFramePlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_left (sepConj_mono
    (memRegion_16_entails_cells (sp + 0x2d0#64))
    (memRegion_36_entails_cells (sp + 0x550#64))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1; apply Entails.sepExists_elim; intro g
  refine Entails.sepExists_right g (Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d5 (Entails.pure_right hbound ?_))))))))
  unfold wsStoreCallPrePlaced wsStoreFixedEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsStoreCallPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (x : DecryptGhost) (s0 : State)
    (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ans_store : Except Unit Unit)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗
  ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ kit.storeShimOff) ∗
  (kit.storeFutVtOff ↦₆₄ᵣ kit.storeFutDropOff) ∗
  ((kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
  ((kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ kit.storePollOff) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff) ∗
  ((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
  ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  protocolAddressAt A x.rem x.remA ∗
  sessionRecordAt A (r26 + 0x80#64) g rec' ∗ kit.storeAt (s0.readReg64 .x3) st ∗
  (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
  A.pool ∗ stackAt sp (storeCallStack kit)

def wsStorePostCommonRestPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtraPlaced kit ikit st ist s0

theorem storeCallPost_entails_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp r26 : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (ans_store : Except Unit Unit)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) (hr26 : r26 = sp + 0xa0#64)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreCallPostSpatialPlaced A kit x s0 sp r26 g rec' st ans_store box strPtr o2 o3 o4 o5 o1 o6 ∗
      wsStoreFramePlaced C A ctl kit ikit x ans s0 sp ist pt ⊢
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt := by
  subst hr26
  refine Entails.trans (Entails.of_eq (show _ =
    ((((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ kit.storeFutVtOff)) ∗
      (((sp + 0x5f0#64) ↦₆₄ pollTag ans_store) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6))) ∗
    (wsStoreFixedEnvPlaced A kit x s0 sp st ∗ wsStoreFixedRestPlaced A kit ikit x s0 sp ist) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗
      ((sp + 0x570#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
      sessionRecordAt A (sp + 0x120#64) g rec' ∗
      wsMsgCells x sp ∗ vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      memRegion (sp + 0x2a8#64) 0x20 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreCallPostSpatialPlaced wsStoreFramePlaced wsStoreFixedEnvPlaced
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box kit.storeFutVtOff
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (pollTag ans_store)
    o2 o3 o4 o5 o1 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono (sepConj_mono h16 h48)
    (sepConj_mono_left (wsFixed_wsEnv_store_join_placed A kit ikit x s0 sp st ist hsp hbound))) ?_
  unfold wsStorePostCommonRestPlaced
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

theorem storePostCommon_err_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (strPtr vt x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    (strPtr ↦ᵣ storeHookStr) ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0 := by
  have hrec0 : sessionRecordAt A (sp + 0x120#64) g rec' ⊢
      ∃∗ G : SessionGhost, droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) :=
    Entails.trans (Entails.sepExists_right g (Entails.refl _))
      (sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur)
  refine Entails.trans (Entails.of_eq (show _ =
    sessionRecordAt A (sp + 0x120#64) g rec' ∗
    ((((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0)) by
    unfold wsStorePostCommonRestPlaced; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_pollOutPlacedRel (α := Unit) A strPtr vt x28 w20 w21
    (sp + 0x580#64) o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec0 (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono_left hpt)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_store_split]
  exact Entails.of_eq (by ac_rfl)

def wsStoreTailOkPre_placed (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s0_580 s1_588 : BitVec 64) (s2_lo s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (t0_300 t1_308 t2_310 t3_318 : BitVec 64) (t4_320 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  (if prevCap = 0#64 then emp
   else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
  sessionStateAt A (sp + 0x138#64) G st ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ t0_300) ∗ ((sp + 0x308#64) ↦₆₄ t1_308) ∗
  ((sp + 0x310#64) ↦₆₄ t2_310) ∗ ((sp + 0x318#64) ↦₆₄ t3_318) ∗ ((sp + 0x320#64) ↦₃₂ t4_320) ∗
  ((sp + 0x580#64) ↦₆₄ s0_580) ∗ ((sp + 0x588#64) ↦₆₄ s1_588) ∗ ((sp + 0x590#64) ↦₃₂ s2_lo) ∗
  ((sp + 0x594#64) ↦₃₂ s2_hi) ∗ ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
  A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkPost_placed (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  memRegion (sp + 0x138#64) 344 ∗
  ((sp + 0x290#64) ↦₃₂ v1) ∗ ((sp + 0x294#64) ↦₆₄ v2) ∗ ((sp + 0x29c#64) ↦₆₄ v3) ∗
  ((sp + 0x2a4#64) ↦₃₂ v4) ∗ ((sp + 0x300#64) ↦₆₄ v2) ∗ ((sp + 0x308#64) ↦₆₄ v3) ∗
  ((sp + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((sp + 0x318#64) ↦₆₄ s3_598) ∗ ((sp + 0x320#64) ↦₃₂ s4_5a0) ∗
  ((sp + 0x580#64) ↦₆₄ v2) ∗ ((sp + 0x588#64) ↦₆₄ v3) ∗ ((sp + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗
  ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗ A.pool ∗ stackAt sp storeSegStack

def wsStoreTailOkFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp cap ptr : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit)) (wsCalleeStackV kit ikit - storeSegStack)) ∗
  wsMsgCells x sp ∗ vecU8BufPure A cap ptr pt ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)

theorem storePostCommon_ok_pre_tail_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (g : RecordGhost) (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (st : kit.StoreState) (ist : ikit.IdState)
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) :
    (((sp + 0x550#64) ↦₆₄ o2) ∗ ((sp + 0x558#64) ↦₆₄ o3) ∗
      ((sp + 0x560#64) ↦₆₄ o4) ∗ ((sp + 0x568#64) ↦₆₄ o5) ∗ ((sp + 0x570#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗ sessionRecordAt A (sp + 0x120#64) g rec' ∗
    wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist pt ⊢
    ∃∗ G : SessionGhost, ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
    ∃∗ s0_580 : BitVec 64, ∃∗ s1_588 : BitVec 64, ∃∗ s2_lo : BitVec 32, ∃∗ s2_hi : BitVec 32,
    ∃∗ s3_598 : BitVec 64, ∃∗ s4_5a0 : BitVec 32,
    ∃∗ t0_300 : BitVec 64, ∃∗ t1_308 : BitVec 64, ∃∗ t2_310 : BitVec 64,
    ∃∗ t3_318 : BitVec 64, ∃∗ t4_320 : BitVec 32,
      ⌜wsStackV kit ikit ≤ s0.sp.toNat ∧ g.prevCap.toNat * 24 < 2 ^ 63 ∧ g.prevPtr ≠ 0⌝ ∗
      wsStoreTailOkPre_placed A sp g.prevCap g.prevPtr G ses.state
        (cap.extractLsb' 0 32) (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
        ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
        s0_580 s1_588 s2_lo s2_hi s3_598 s4_5a0 t0_300 t1_308 t2_310 t3_318 t4_320 ∗
      wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sp cap ptr st ist pt := by
  have h550 := cells_36_entails_memRegion (sp + 0x550#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h550
  refine Entails.trans (sepConj_mono_left h550) ?_
  unfold wsStorePostCommonRestPlaced
  have hrejoin :
      (memRegion (sp + 0x550#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗
        (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
          vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
          memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          (memRegion (sp + 0x300#64) 0x250 ∗ memRegion (sp + 0x574#64) 0xc) ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
          decStoreExtraPlaced kit ikit st ist s0)) =
      ((stackAt sp wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
        sessionRecordAt A (sp + 0x120#64) g rec' ∗ vecU8 A (sp + 0x290#64) pt ∗
        memRegion (sp + 0x300#64) 0x24 ∗ memRegion (sp + 0x580#64) 0x24 ∗
        (wsFixedVPlaced kit ikit x s0 sp ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          FromRecordCallees.lsLogOff ∗ A.pool ∗ wsMsgCells x sp ∗
          memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
          memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x324#64) 0x25c ∗
          memRegion (sp + 0x5a4#64) 0x85c ∗
          memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans))) := by
    unfold wsEnvPlaced
    rw [memRegion_split (sp + 0x300#64) 0x24 0x22c (by decide),
      memRegion_split (sp + 0x324#64) 0x22c 0x30 (by decide),
      memRegion_split (sp + 0x324#64 + 0x22c#64) 0x24 0xc (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  rw [hrejoin]
  have hj := wsCalleeStack_join_extra_placed kit ikit st ist s0
  rw [← hsp] at hj
  refine Entails.trans (sepConj_mono hj
    (sepConj_mono (sessionRecordAt_some_expose A (sp + 0x120#64) g rec' ses hcur)
      (sepConj_mono (vecU8_290_expose A sp pt)
        (sepConj_mono (memRegion_36_entails_cells (sp + 0x300#64))
          (sepConj_mono_left (memRegion_36_entails_cells_split16 (sp + 0x580#64))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro s0_580; apply Entails.sepExists_elim; intro s1_588
  apply Entails.sepExists_elim; intro s2_lo; apply Entails.sepExists_elim; intro s2_hi
  apply Entails.sepExists_elim; intro s3_598; apply Entails.sepExists_elim; intro s4_5a0
  apply Entails.sepExists_elim; intro t0_300; apply Entails.sepExists_elim; intro t1_308
  apply Entails.sepExists_elim; intro t2_310; apply Entails.sepExists_elim; intro t3_318
  apply Entails.sepExists_elim; intro t4_320; apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr; apply Entails.sepExists_elim; intro G
  rw [sepConj_assoc (⌜_⌝)]; apply Entails.pure_left; intro hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  rw [sepConj_assoc (⌜_⌝), sepConj_pure_left_comm]
  apply Entails.pure_left; intro hpure
  refine Entails.sepExists_right G (Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right s0_580 (Entails.sepExists_right s1_588 (Entails.sepExists_right s2_lo
      (Entails.sepExists_right s2_hi (Entails.sepExists_right s3_598 (Entails.sepExists_right s4_5a0
        (Entails.sepExists_right t0_300 (Entails.sepExists_right t1_308 (Entails.sepExists_right t2_310
           (Entails.sepExists_right t3_318 (Entails.sepExists_right t4_320
             (Entails.pure_right ⟨hbound, hpure⟩ ?_))))))))))))))
  unfold wsStoreTailOkPre_placed wsStoreTailOkFramePlaced
  rw [stack_wsCalleeV_storeSeg kit ikit sp hn]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; exact Entails.of_eq (by ac_rfl)

theorem storePost_ok_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp prevCap prevPtr cap ptr : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState) (pt : List (BitVec 8))
    (v1 : BitVec 32) (v2 v3 : BitVec 64) (v4 : BitVec 32)
    (s2_hi : BitVec 32) (s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (x28 w20 w21 : BitVec 64) (hx28 : x28 = okTagVec)
    (hw20 : w20 = (v1 >>> 8#32).zeroExtend 64) (hw21 : w21 = v1.zeroExtend 64)
    (hv1 : v1 = cap.extractLsb' 0 32) (hv2 : v2 = ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    (hv3 : v3 = (BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    (hv4 : v4 = (BitVec.ofNat 64 pt.length).extractLsb' 32 32)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsStoreTailOkPost_placed A sp prevCap prevPtr v1 v2 v3 v4 s2_hi s3_598 s4_5a0 ∗
      wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sp cap ptr st ist pt ⊢
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) (.ok pt) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0 := by
  subst hx28 hw20 hw21 hsp
  have h120 := memRegion_120_1a8_join (s0.sp - 0xee0#64) prevCap prevPtr v1 v2 v3 v4
  have h580 := cells_36_entails_memRegion (s0.sp - 0xee0#64 + 0x580#64) v2 v3 (s2_hi ++ v4) s3_598 s4_5a0
  have hst := stagedRes_ok_pt A (s0.sp - 0xee0#64 + 0x300#64) cap ptr pt s2_hi s3_598 s4_5a0
    v1 v2 v3 v4 hv1 hv2 hv3 hv4
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h120 h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((s0.sp - 0xee0#64 + 0x120#64) ↦₆₄ prevCap) ∗ ((s0.sp - 0xee0#64 + 0x128#64) ↦₆₄ prevPtr) ∗
      ((s0.sp - 0xee0#64 + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s0.sp - 0xee0#64 + 0x138#64) 344 ∗
      ((s0.sp - 0xee0#64 + 0x290#64) ↦₃₂ v1) ∗ ((s0.sp - 0xee0#64 + 0x294#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x29c#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x2a4#64) ↦₃₂ v4) ∗ memRegion (s0.sp - 0xee0#64 + 0x2a8#64) 0x20) ∗
    ((((s0.sp - 0xee0#64 + 0x300#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x308#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x310#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x318#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x320#64) ↦₃₂ s4_5a0)) ∗ vecU8BufPure A cap ptr pt) ∗
    (((s0.sp - 0xee0#64 + 0x580#64) ↦₆₄ v2) ∗ ((s0.sp - 0xee0#64 + 0x588#64) ↦₆₄ v3) ∗
      ((s0.sp - 0xee0#64 + 0x590#64) ↦₆₄ (s2_hi ++ v4)) ∗ ((s0.sp - 0xee0#64 + 0x598#64) ↦₆₄ s3_598) ∗
      ((s0.sp - 0xee0#64 + 0x5a0#64) ↦₃₂ s4_5a0)) ∗
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - storeSegStack) ∗
        stackAt (s0.sp - 0xee0#64) storeSegStack)) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) ∗
      wsMsgCells x (s0.sp - 0xee0#64) ∗ memRegion (s0.sp - 0xee0#64) 0xa0 ∗ memRegion (s0.sp - 0xee0#64 + 0x2d0#64) 0x10 ∗
      memRegion (s0.sp - 0xee0#64 + 0x324#64) 0x25c ∗ memRegion (s0.sp - 0xee0#64 + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsStoreTailOkPost_placed wsStoreTailOkFramePlaced
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_storeSeg kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst
    (sepConj_mono h580 (sepConj_mono_left hsplit)))) ?_
  unfold wsEnvPlaced; rw [memRegion_324_adc_split (s0.sp - 0xee0#64)]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1600000 in
theorem segStore_call_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord H)
    (hstack_lt : storeCallStack kit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA : BitVec 64}
    {addr : AddrGhost} {g : RecordGhost} {record : SessionRecord (List (BitVec 8))}
    {st : kit.StoreState} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
        protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
        kit.storeAt self st ∗ A.pool ∗ stackAt s.sp (storeCallStack kit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Unit, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64,
          ∃∗ o4 : BitVec 64, ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st addr.val record ans ∧
            sf.readReg64 .x28 = pollTag ans ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord addr.val record ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans⌝ ∗
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
          protocolAddressAt A addr addrA ∗ sessionRecordAt A (s.readReg64 .x26 + 0x80#64) g record ∗
          kit.storeAt self (kit.storeUpdate st addr.val record ans) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          A.pool ∗ stackAt s.sp (storeCallStack kit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := shim_463 (hkit.storeShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hdrop := futDrop_463 (hkit.storeFutDrop (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  unfold storeCallPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_storeCall_to_storeShim kit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := kit.storeShimOff) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  cli_messageDecrypt_call_panic_p_lscro hshim hcrl1
    (⟨self, addrA, s.readReg64 .x26 + 0x80#64⟩ : StoreShimCall)
  clear hcrl1 hshim
  apply StoreKit.sepWPp_seq_lscro (mid := kit.storePollOff) hcrl_sf
  clear hcrl_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : kit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_storeShim_to_storePoll kit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl2
  have hpoll := box_lscro_463 (hkit.storePoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  cli_messageDecrypt_call_panic_lscro hpoll hcrl2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 0x5f0#64,
    ⟨addrA, addr, s.readReg64 .x26 + 0x80#64, g, record⟩⟩, self, st)
  clear hcrl2 hpoll hkit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz : kit.storeFutDropOff ≠ 0#64 := by
    simpa only [BitVec.zero_add] using kit.storeFutDrop_ne_zero (by decide)
  have hdz' : (kit.storeFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := kit.storeBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 kit.storeBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 kit.storeBoxSize).toNat = kit.storeBoxSize :=
    Nat.mod_eq_of_lt kit.storeBoxSize_lt
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
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, kit.storeBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = pollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right strPtr
      (Entails.sepExists_right vt
      (Entails.sepExists_right (strPtr.extractLsb' 0 32)
      (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32) ?_)))))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
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
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (kit.storeBoxAt_memRegion box self addrA (s.readReg64 (Reg.gpr 26#5) + 128#64) 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_storePoll_to_alloc kit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, kit.storeBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_storeCall kit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = pollTag (.ok ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.ok ())
      (Entails.sepExists_right box
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right (w5.extractLsb' 0 32)
      (Entails.sepExists_right (w4.extractLsb' 0 32 ++ w5.extractLsb' 32 32)
      (Entails.sepExists_right (w3.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
      (Entails.sepExists_right (w2.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
      (Entails.sepExists_right (w1.extractLsb' 32 32) ?_)))))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
