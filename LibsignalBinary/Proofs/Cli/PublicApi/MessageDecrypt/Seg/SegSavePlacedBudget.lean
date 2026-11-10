/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.Placed.BudgetPoolSync LibsignalBinary.Proofs.Placed.BudgetVmSteps
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlacedBudget.TempTwins
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave (
  stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err
  stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro
  shim_463 box_lscro_463 futDrop_463 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro
  clearLscroInvHyps wsMetaPlaced_of_steps
  wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed
  wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed
  wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed
  savePostCommon_ok_entails_placed savePostCommon_err_entails_placed)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 3200000 in
theorem segSave_call_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : IdentityStoreBudgetEnv ikit} {st : M.σ}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hikit : IdentityStoreKitBudgetOkI A lim ikit ikitEnv H)
    (hstack_lt : saveCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA keyA : BitVec 64} {ist : ikit.IdState}
    {addr : AddrGhost} {k : IdentityKey} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfits : FitsEnv M lim st (SaveStepEnvDec ikit ikitEnv ist addr.val k))
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = saveCallPCPlaced)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = keyA)
    (hfs : FsAt ikit.envOk Q (lsProg_463 H) s) :
    SepWPp (lsProg_463 H) ((blkPl_463).base + 9088#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
        (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
        ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
        ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x520#64) ↦₆₄ d0) ∗ ((s.sp + 0x528#64) ↦₆₄ d1) ∗ ((s.sp + 0x530#64) ↦₆₄ d2) ∗
        ((s.sp + 0x538#64) ↦₆₄ d3) ∗ ((s.sp + 0x540#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        FromRecordCallees.lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗
        (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool lim st s ∗
        stackAt s.sp (saveCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ evs : List AllocEvent, ∃∗ ans : Except Unit IdentityChange, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜sf.readReg64 .x28 = savePollTag ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist addr.val k ans ∧
            sf.trace = s.trace ++ ikit.saveEvs addr.val k ans ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans ∧
            SaveStepEnvDec ikit ikitEnv ist addr.val k evs⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗ ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
          (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
          ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
          ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
          ikit.identityAt self (ikit.saveUpdate ist addr.val k ans) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ ikit.saveFutVtOff) ∗
          ((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
          ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
          ((s.sp + 0x540#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ savePollTag ans) ∗ ((s.sp + 0x5f8#64) ↦₃₂ o1) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          FromRecordCallees.lsLogOff ∗ protocolAddressAt A.repAlloc addr addrA ∗
          (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool lim (M.stepEvents evs st) sf ∗
          stackAt s.sp (saveCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ ⌜False⌝ ∗ R)) := by
  have hshim := shim_463 (hikit.saveShim (p := lsProg_463 H) (i := 463) (by decide))
  have hdrop := futDropBudget_463 (hikit.saveFutDrop (p := lsProg_463 H) (i := 463) (by decide))
  have hfits_sh : FitsEnv M lim st (BoxAllocEnv ikit.saveBoxSize) := hfits.seq_left
  unfold saveCallPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc := deallocBudget_463 hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_saveCall_to_saveShim ikit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.saveShimOff) hcrl
  clear hcrl
  by_vm_open (
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
    intro hvm1 hcrl1
    refine SepWPp.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
    cli_messageDecrypt_call_panic_p_budget_lscro hshim hcrl1 ((⟨self, addrA, keyA⟩ : IdentityShimCall), st)
    clear hcrl1 hshim
    apply StoreKit.sepWPp_seq_lscro (mid := ikit.savePollOff) hcrl_sf
    clear hcrl_sf
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (evs_sh : List AllocEvent)
    wp_simp_pre [sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf, hevs_sh⟩
    have hfits_rem := hfits.seq_right hevs_sh
    have hfits_pl : FitsEnv M lim (M.stepEvents evs_sh st) (ikitEnv.savePollEnv ist addr.val k) :=
      hfits_rem.seq_left
    have henv : ikit.envOk sf.fs.files :=
      (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
    clear hsteps_sh hfs
    apply SepWP.fold (Entails.of_eq (stack_saveShim_to_savePoll ikit s.sp hstack_lt)) (by sep_focus)
    by_vm_open (
      wp_steps
      refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm2 hcrl2
      refine SepWPp.transport_budgetPool hvm2 (hnext := ?_); clear hvm2
      have hpoll := box_lscro_463 (hikit.savePoll (p := lsProg_463 H) (i := 463) (by decide))
      cli_messageDecrypt_call_panic_budget_lscro hpoll hcrl2
        (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, keyA, k⟩⟩, self, ist, M.stepEvents evs_sh st)
      clear hcrl2 hpoll hikit
      generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
      simp only [hsp_sf] at hsp_sf_1 ⊢
      have hdz : ikit.saveFutDropOff ≠ 0#64 := by
        simpa only [BitVec.zero_add] using ikit.saveFutDrop_ne_zero (by decide)
      have hdz' : (ikit.saveFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
      have hbs := ikit.saveBoxSize_ne_zero
      have hbs' : (BitVec.ofNat 64 ikit.saveBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
      have hbs_pos : 0 < ikit.saveBoxSize := Nat.pos_of_ne_zero (fun h => hbs (by simp [h]))
      have hbs_toNat : (BitVec.ofNat 64 ikit.saveBoxSize).toNat = ikit.saveBoxSize :=
        Nat.mod_eq_of_lt ikit.saveBoxSize_lt
      have hevs_dealloc : BoxDeallocEnv ikit.saveBoxSize (rustDeallocEvents ikit.saveBoxSize 8) :=
        Or.inr ⟨hbs_pos, rfl⟩
      apply SepWP.fold (A.block_valid box ikit.saveBoxSize 8) (by sep_focus)
      wp_simp_pre [sepConj_assoc, sepConj_pure_left_comm]
      apply SepWP.pure_elim; rintro ⟨_, _, _, ⟨_, hpow8, hbound_box⟩, _⟩
      rcases w with ⟨⟨⟩⟩ | c
      · dsimp only [StoreKit.savePollPlacedOutAt]
        wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (strPtr : BitVec 64)
        apply SepWP.exists_elim; intro (vt : BitVec 64)
        apply SepWP.exists_elim; intro (w5 : BitVec 64)
        apply SepWP.fold
          (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
          (by sep_focus)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.saveFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.saveBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
          simp only [show (9223372036854775834#64 : BitVec 64) = savePollTag (.error ()) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8))
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
          have henv_step : SaveStepEnvDec ikit ikitEnv ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [Bool.false_eq_true, ↓reduceIte, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))
      · dsimp only [StoreKit.savePollPlacedOutAt]
        apply SepWP.fold (memRegion_36_entails_cells (s.sp + 1520#64 + 0xc#64)) (by sep_focus)
        wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc,
          BitVec.add_assoc, BitVec.reduceAdd]
        apply SepWP.exists_elim; intro (o2 : BitVec 64)
        apply SepWP.exists_elim; intro (o3 : BitVec 64)
        apply SepWP.exists_elim; intro (o4 : BitVec 64)
        apply SepWP.exists_elim; intro (o5 : BitVec 64)
        apply SepWP.exists_elim; intro (o6 : BitVec 32)
        apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.saveFutDropOff)
        by_vm_open (
          wp_steps
          refine SepWP.done (by simp_all) (by simp_all) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          rintro hvm3 ⟨hcl_d, hro_d⟩
          refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
          wp_call hdrop ()
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          wp_steps
          apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
          apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
          wp_call hdealloc (box, ikit.saveBoxSize, 8, M.stepEvents w_1 (M.stepEvents evs_sh st))
          have hsp_sf2 : sf_2.sp = s.sp := by simp_all
          rw [hsp_sf2]
          apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
          simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = savePollTag (.ok c) from rfl] at *
          apply SepWP.done (by simp_all) (by simp_all)
          refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
          refine Entails.sepExists_right (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8))
            (Entails.sepExists_right (.ok c)
            (Entails.sepExists_right box
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right 0#64
            (Entails.sepExists_right (if c = .replacedExisting then 1#32 else 0#32)
            (Entails.sepExists_right o2
            (Entails.sepExists_right o3
            (Entails.sepExists_right o4
            (Entails.sepExists_right o5
            (Entails.sepExists_right o6 ?_))))))))))
          have henv_step : SaveStepEnvDec ikit ikitEnv ist addr.val k
              (evs_sh ++ (w_1 ++ rustDeallocEvents ikit.saveBoxSize 8)) :=
            SeqEnv.append hevs_sh (SeqEnv.append (by simp_all) hevs_dealloc)
          refine Entails.pure_right (by simp_all [henv_step]) ?_
          dsimp only [Except.isOk, Except.toBool]
          simp only [↓reduceIte, emp_sepConj, ← M.stepEvents_append, List.append_assoc]
          exact Entails.of_eq (by sep_ac_rfl))))

theorem segSave_tail_placed_ok [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    {c : IdentityChange}
    (hpc : s.pc = (blkPl_463).base + 9088#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = savePollTag (.ok c)) :
    SepWP (lsProg_463 H) storeCallPCPlaced s emp
      (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold storeCallPCPlaced
  dsimp only [lsProg_463]
  simp only [savePollTag] at hx28
  wp_steps_vm

theorem segSave_tail_placed_err [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    {o2 o3 o4 o5 e0 e1 e2 e3 : BitVec 64} {o1 o6 e4 : BitVec 32}
    (hpc : s.pc = (blkPl_463).base + 9088#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = savePollTag (.error ()))
    (hx21 : s.readReg64 .x21 = o1.zeroExtend 64) :
    SepWP (lsProg_463 H) (errJoinPCPlaced true) s
      (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
        ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
        ((s.sp + 0x540#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₆₄ e2) ∗ ((s.sp + 0x598#64) ↦₆₄ e3) ∗
        ((s.sp + 0x5a0#64) ↦₃₂ e4))
      (fun sf P_f => VmPreserved s sf ∧ ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
          ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
          ((s.sp + 0x540#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
          ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
          ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (o1 >>> 8#32).zeroExtend 64 ∧
        sf.readReg64 .x21 = o1.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s)) := by
  unfold errJoinPCPlaced
  dsimp only [lsProg_463, ite_true]
  simp only [savePollTag] at hx28
  wp_steps_vm

attribute [local semireducible] SepWP in
theorem segSaveVPlaced_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegSaveSpecVBudget C A lim ctl uuidTryParse S encRecord H kit kitEnv ikit ikitEnv st0 ist0 Scope := by
  intro hyps x st_init ans R s0 s haddr hfs hstB hL
  rcases hstB with ⟨st, hsb_all, hst⟩
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hsb : SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse Scope x) st_init st
      (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k) :=
    hsb_all rec rec' pt ses k hload hdec hcur hrem
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, and_self]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hpc' : s.pc = saveCallPCPlaced := hpc
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  have hfits : FitsEnv M lim st (SaveStepEnvDec ikit ikitEnv ist1 x.rem.val k) := by
    dsimp only [ist1]; rw [htrust]; exact hsb.1.seq_left
  let A0 := A.atState lim st s
  let kit0 := retagSessionStore (A' := A0) kit
  let ikit0 := retagIdentityStore (A' := A0) ikit
  rw [← hsp] at hx26 hx19 hx22 hm
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit0 ikit0 ≤ s0.sp.toNat⌝ ∗
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsSaveCallPrePlaced A0 ikit0 x s0 s.sp ist1 k c0 c1 d0 d1 d2 d3 d5 ∗
          wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_saveCallPre_placed C A0 ctl kit0 ikit0 x ans s0 s.sp st0 ist1 rec' pt k hsp)) ?_
    dsimp only [A0, kit0, ikit0, ist1] at hm ⊢
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have hstack_lt : saveCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := saveCallStack_le_wsCalleeV kit0 ikit0
    have h2 : wsCalleeStackV kit0 ikit0 ≤ wsStackV kit0 ikit0 := Nat.le_add_right _ _
    change saveCallStack ikit0 ≤ 2 ^ 64
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segSave_call_placed_wp hyps.hooks.dealloc hyps.ikit hstack_lt
      (R := wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl hfits haddr hpc' hrun hsp_align hx19 hfsAt
      (wsSaveFramePlaced C A0 ctl kit0 ikit0 x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _, hm1_pan, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨evs_save, ans_save, box, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1'⟩
    let st1 := M.stepEvents evs_save st
    let A1 := A.atState lim st1 sf
    let kit1 := retagSessionStore (A' := A1) kit
    let ikit1 := retagIdentityStore (A' := A1) ikit
    have hm1_common : sf.mem ⊨
        (⌜sf.readReg64 .x28 = savePollTag ans_save ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist1 x.rem.val k ans_save ∧
            sf.trace = s.trace ++ ikit.saveEvs x.rem.val k ans_save ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans_save ∧
            SaveStepEnvDec ikit ikitEnv ist1 x.rem.val k evs_save⌝ ∗
          (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
            ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
            ((s.sp + 0x540#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0
            (ikit.saveUpdate ist1 x.rem.val k ans_save) rec' pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.pure_right hpure ?_
      exact saveCallPost_entails_common_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist1 rec' pt k
        ans_save box strPtr o2 o3 o4 o5 o1 o6 hsp hbound
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hsaveRel, htr1, hrel1, hevs_save⟩, hm1_common⟩
    have hevs_save' : SaveStepEnvDec ikit ikitEnv
        (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k evs_save := by
      dsimp only [ist1] at hevs_save; rwa [htrust] at hevs_save
    have hsb1 := hsb.advance hevs_save'
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_save with ⟨⟨⟩⟩ | c
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.error ())
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x520#64) ↦₆₄ o2) ∗ ((sf.sp + 0x528#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x530#64) ↦₆₄ o4) ∗ ((sf.sp + 0x538#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x540#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            (strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R := by
        rw [hsp1]
        refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0
        apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2
        apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc, Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_err (H := H) (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      let A2 := A.atState lim st1 sf2
      let kit2 := retagSessionStore (A' := A2) kit
      let ikit2 := retagIdentityStore (A' := A2) ikit
      have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st1 hvm2
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
              ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗ ((s.sp + 0x540#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsSavePostCommonRestPlaced C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist2 rec' pt)) ∗ R := by
        dsimp only [kit1, ikit1, kit2, ikit2] at hm2' ⊢
        rw [hA12] at hm2'
        exact Eq.mp (congrArg (sf2.mem ⊨ ·) (by sep_ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (savePostCommon_err_entails_placed C A2 ctl kit2 ikit2 x ans s0 s.sp st0 ist2 rec' ses hcur pt
          strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ⟨st1, hsb1.narrow (fun _ h => Or.inl h), ?_⟩)⟩
      have hmod := model_of_save_err C S x
        { ans with saveIdentity := .error () } rec rec' pt ses k
        hload hdec hcur hrem htrust rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with saveIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_load_trust_save,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal, A2, kit2, ikit2, ist1, ist2] at hm2_err ⊢
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.ok c)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (savePostCommon_ok_entails_placed C A1 ctl kit1 ikit1 x ans s0 s.sp st0 ist2 rec' pt o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit1 ikit1 x s0 s.sp ∗ wsEnvPlaced A1 x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A1 (s.sp + 0x120#64) g rec') ∗
            vecU8 A1 (s.sp + 0x290#64) pt ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit1 ikit1 st0 ist2 s0) ∗ R) := by
        rwa [emp_sepConj]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hvm2, hpost2, hsp2, htr2,
        hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_ok (H := H) (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1) _ hm1_emp hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
      let A2 := A.atState lim st1 sf2
      let kit2 := retagSessionStore (A' := A2) kit
      let ikit2 := retagIdentityStore (A' := A2) ikit
      have hA12 : A1 = A2 := atState_eq_of_vmPreserved A lim st1 hvm2
      dsimp only [kit1, ikit1] at hm2'
      rw [hA12] at hm2'
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      have hsb_store : ∀ rec0 pt0 rec0',
          ({ ans with saveIdentity := .ok c } : StoreAnswers (List (BitVec 8)) Unit).loadSession = .ok (some rec0) →
          decryptRecord C S uuidTryParse x rec0 = .ok (pt0, rec0') →
          SeamBudget lim (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S uuidTryParse Scope x) st_init st1
            (FromStoreCallEnv kit kitEnv st0 x.rem.val rec0') := by
        intro rec0 pt0 rec0' hload0 hdec0
        dsimp only at hload0
        rw [hload] at hload0; cases hload0
        rw [hdec] at hdec0; cases hdec0
        exact hsb1.narrow (fun _ h => Or.inr h)
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with saveIdentity := .ok c }, st1, hsb_store, ?_⟩)⟩
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .ok c }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, rec, rec', pt, ses, k, c,
        hload, hscope, hdec, hcur, hrem, htrust, rfl, htrustRel, hsaveRel, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx22_2, hx22_1, hx22, hsp]
      · rw [htr2, htr1, htr, List.append_assoc]
      · rw [hdraws]
        dsimp only [A2, kit2, ikit2, ist1, ist2] at hm2' ⊢
        simpa only [hsp, sepConj_assoc] using hm2'
  · exact (not_satisfies_false_sepConj (hpan_post1 hm1_pan)).elim
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlacedBudget
