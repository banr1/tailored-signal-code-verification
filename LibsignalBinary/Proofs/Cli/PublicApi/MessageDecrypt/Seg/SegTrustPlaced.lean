/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrust
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustAuxPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust

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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust hiding segTrust_call_placed_wp segTrust_tail_placed_ok_true segTrust_tail_placed_ok_false segTrust_tail_placed_err segTrustVPlaced_ok trustPollOutPlacedRel trustPollOutPlacedRel_ok_false trustPollOutPlacedRel_ok_true trustPollOutPlacedRel_err wsTrustFixedEnvPlaced wsTrustFixedRestPlaced wsFixed_wsEnv_trust_split_placed wsFixed_wsEnv_trust_join_placed wsTrustCallPrePlaced wsTrustFramePlaced keyReady_entails_trustCallPre_placed wsTrustCallPostSpatialPlaced wsTrustPostCommonRestPlaced trustCallPost_entails_common_placed trustPostCommon_ok_entails_placed trustPostCommon_err_entails_placed

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


set_option maxHeartbeats 1600000 in
theorem segTrust_call_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A 0#64}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hikit : IdentityStoreKitPlacedOkI ikit H)
    (hstack_lt : trustCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    {self addrA c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 : BitVec 64} {d5 : BitVec 32}
    {ist : ikit.IdState} {addr : AddrGhost} {k : IdentityKey} {Q : Prop}
    (haddr : ikit.addrOk addr.val)
    (hpc : s.pc = keyReadyPCPlaced)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList))
    (hfs : FsAt ikit.envOk Q (lsProg_463 H) s) :
    SepWPp (lsProg_463 H) ((blkPl_463).base + 8516#64) s
      (((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
        ((s.sp + 0x108#64) ↦₆₄ self) ∗
        ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
        ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
        (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
        ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
        ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
        ikit.identityAt self ist ∗
        ((s.sp + 0x2a8#64) ↦₆₄ a0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ a1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ a2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ a3) ∗
        ((s.sp + 0x2d0#64) ↦₆₄ c0) ∗ ((s.sp + 0x2d8#64) ↦₆₄ c1) ∗
        ((s.sp + 0x4f0#64) ↦₆₄ d0) ∗ ((s.sp + 0x4f8#64) ↦₆₄ d1) ∗
        ((s.sp + 0x500#64) ↦₆₄ d2) ∗ ((s.sp + 0x508#64) ↦₆₄ d3) ∗
        ((s.sp + 0x510#64) ↦₃₂ d5) ∗
        memRegion (s.sp + 0x5f0#64) 48 ∗
        ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
        ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
        FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
        stackAt s.sp (trustCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit Bool,
          ∃∗ box : BitVec 64, ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist addr.val k .receiving ans ∧
            sf.trace = s.trace ++ ikit.trustEvs addr.val k .receiving ans ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans⌝ ∗
          ((s.sp + 0xe8#64) ↦₆₄ addrA) ∗
          ((s.sp + 0x108#64) ↦₆₄ self) ∗
          ((s.sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
          ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ ikit.trustShimOff) ∗
          (ikit.trustFutVtOff ↦₆₄ᵣ ikit.trustFutDropOff) ∗
          ((ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗
          ((ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          ((ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.trustPollOff) ∗
          ikit.identityAt self (ikit.trustUpdate ist addr.val k .receiving ans) ∗
          ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
          ((s.sp + 0x2d0#64) ↦₆₄ box) ∗ ((s.sp + 0x2d8#64) ↦₆₄ ikit.trustFutVtOff) ∗
          ((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x5f0#64) ↦₆₄ trustPollTag ans) ∗
          ((s.sp + 0x5f8#64) ↦₈ b0) ∗ ((s.sp + 0x5f9#64) ↦₁₆ h1) ∗
          ((s.sp + 0x5fb#64) ↦₈ b3) ∗
          ((s.sp + 0x5fc#64) ↦₆₄ o2) ∗ ((s.sp + 0x604#64) ↦₆₄ o3) ∗
          ((s.sp + 0x60c#64) ↦₆₄ o4) ∗ ((s.sp + 0x614#64) ↦₆₄ o5) ∗
          ((s.sp + 0x61c#64) ↦₃₂ o6) ∗
          ((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3) ∗
          (if ans.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗ A.pool ∗
          stackAt s.sp (trustCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x19 = s.sp + 0x2a8#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := shim_463 (hikit.trustShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hdrop := futDrop_463 (hikit.trustFutDrop (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  unfold keyReadyPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_trustCall_to_trustShim ikit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustShimOff) hcrl
  clear hcrl
  wp_steps
  apply SepWP.fold (Entails.of_eq hk_2a8) (by sep_focus)
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  cli_messageDecrypt_call_panic_p_lscro hshim hcrl1 ((⟨self, addrA, s.sp + 680#64⟩ : IdentityShimCall), 1#8)
  clear hcrl1 hshim
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.trustPollOff) hcrl_sf
  clear hcrl_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : ikit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_trustShim_to_trustPoll ikit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl2
  have hpoll := box_lscro_463 (hikit.trustPoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  cli_messageDecrypt_call_panic_lscro hpoll hcrl2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, s.sp + 680#64, k⟩⟩, Direction.receiving, self, ist)
  clear hcrl2 hpoll hikit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz : ikit.trustFutDropOff ≠ 0#64 := by
    simpa only [BitVec.zero_add] using ikit.trustFutDrop_ne_zero (by decide)
  have hdz' : (ikit.trustFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := ikit.trustBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 ikit.trustBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 ikit.trustBoxSize).toNat = ikit.trustBoxSize :=
    Nat.mod_eq_of_lt ikit.trustBoxSize_lt
  rcases w with ⟨⟨⟩⟩ | t
  · dsimp only [StoreKit.trustPollPlacedOutAt]
    wp_simp_pre [StoreKit.errTailPlacedAt, ProofLib.memRegion_eight,
      sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.exists_elim; intro (strPtr : BitVec 64)
    apply SepWP.exists_elim; intro (vt : BitVec 64)
    apply SepWP.exists_elim; intro (w5 : BitVec 64)
    apply SepWP.fold
      (Entails.of_eq (out_repack_sp s.sp strPtr 10#64 1#64 vt w5))
      (by sep_focus)
    apply SepWP.fold
      (Entails.of_eq (pointsTo32_split_1_2_1_sp s.sp (strPtr.extractLsb' 0 32)))
      (by sep_focus)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (0x800000000000001A#64 : BitVec 64) = trustPollTag (.error ()) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.error ())
      (Entails.sepExists_right box
      (Entails.sepExists_right strPtr
      (Entails.sepExists_right vt
      (Entails.sepExists_right (10#32 ++ strPtr.extractLsb' 32 32)
      (Entails.sepExists_right 4294967296#64
      (Entails.sepExists_right (vt.extractLsb' 0 32 ++ 0#32)
      (Entails.sepExists_right (w5.extractLsb' 0 32 ++ vt.extractLsb' 32 32)
      (Entails.sepExists_right (w5.extractLsb' 32 32)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 0 8)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 24 8)
      (Entails.sepExists_right ((strPtr.extractLsb' 0 32).extractLsb' 8 16) ?_)))))))))))
    refine Entails.pure_right ⟨by simp_all, by simp_all; bv_bits, by simp_all; bv_bits,
      by simp_all, h_20, by simp_all,
      ⟨by bv_bits, by bv_bits, by bv_bits, pollOutPlacedRel_err strPtr vt w5⟩⟩ ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)
  · dsimp only [StoreKit.trustPollPlacedOutAt]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd]
    apply SepWP.fold (memRegion_39_entails_cells_sp s.sp) (by sep_focus)
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply SepWP.exists_elim; intro (h1 : BitVec 16)
    apply SepWP.exists_elim; intro (b3 : BitVec 8)
    apply SepWP.exists_elim; intro (o2 : BitVec 64)
    apply SepWP.exists_elim; intro (o3 : BitVec 64)
    apply SepWP.exists_elim; intro (o4 : BitVec 64)
    apply SepWP.exists_elim; intro (o5 : BitVec 64)
    apply SepWP.exists_elim; intro (o6 : BitVec 32)
    apply StoreKit.sepWP_seq_lscro hcrl_poll (mid := ikit.trustFutDropOff)
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.trustBoxAt_memRegion box self addrA (s.sp + 680#64) 1#8 (directionByte .receiving)) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_trustPoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.trustBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_trustCall ikit s.sp hstack_lt)) (by sep_focus)
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte,
        show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok false) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok false)
        (Entails.sepExists_right box
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 0#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)
    · simp only [↓reduceIte,
        show (bv% (2 ^ 64 - 2) : BitVec 64) = trustPollTag (.ok true) from rfl] at *
      apply SepWP.done (by simp_all) (by simp_all)
      refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
      refine Entails.sepExists_right (.ok true)
        (Entails.sepExists_right box
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right 0#64
        (Entails.sepExists_right o2
        (Entails.sepExists_right o3
        (Entails.sepExists_right o4
        (Entails.sepExists_right o5
        (Entails.sepExists_right o6
        (Entails.sepExists_right 1#8
        (Entails.sepExists_right b3
        (Entails.sepExists_right h1 ?_)))))))))))
      refine Entails.pure_right (by simp_all) ?_
      dsimp only [Except.isOk, Except.toBool]
      simp only [↓reduceIte, emp_sepConj]
      exact Entails.of_eq (by ac_rfl)

theorem segTrust_tail_placed_ok_true [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_463).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok true))
    (hx21 : s.readReg64 .x21 = (1#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_463 H) (trustedPCPlaced true) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold trustedPCPlaced saveCallPCPlaced
  dsimp only [lsProg_463]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_placed_ok_false [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    (hpc : s.pc = (blkPl_463).base + 8516#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = trustPollTag (.ok false))
    (hx21 : s.readReg64 .x21 = (0#8 : BitVec 8).zeroExtend 64) :
    SepWP (lsProg_463 H) (trustedPCPlaced false) s
      emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  simp only [trustedPCPlaced, Bool.false_eq_true, ↓reduceIte, untrustedPCPlaced]
  dsimp only [lsProg_463]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

theorem segTrust_tail_placed_err [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    {o2 o3 o4 o5 e0 e1 e2 e3 : BitVec 64} {o6 e4 : BitVec 32}
    {b0 b3 : BitVec 8} {h1 : BitVec 16}
    (hpc : s.pc = (blkPl_463).base + 8516#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 = trustPollTag (.error ()))
    (hx21 : s.readReg64 .x21 = b0.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = b3.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = h1.zeroExtend 64) :
    SepWP (lsProg_463 H) (errJoinPCPlaced true) s
      (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
        ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
        ((s.sp + 0x510#64) ↦₃₂ o6) ∗
        ((s.sp + 0x580#64) ↦₆₄ e0) ∗ ((s.sp + 0x588#64) ↦₆₄ e1) ∗
        ((s.sp + 0x590#64) ↦₆₄ e2) ∗ ((s.sp + 0x598#64) ↦₆₄ e3) ∗
        ((s.sp + 0x5a0#64) ↦₃₂ e4))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
          ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
          ((s.sp + 0x510#64) ↦₃₂ o6) ∗
          ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
          ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
          ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x28 = 0x800000000000001A#64 ∧
        sf.readReg64 .x20 = (h1.zeroExtend 32 ||| (b3.zeroExtend 32 <<< 16#32)).zeroExtend 64 ∧
        sf.readReg64 .x21 = b0.zeroExtend 64 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold errJoinPCPlaced
  dsimp only [lsProg_463]
  simp only [trustPollTag] at hx28
  wp_steps
  wp_done

attribute [local semireducible] SepWP in
theorem segTrustVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegTrustSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htr, hm⟩
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, -⟩ := hq
      simp only [hl]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hx22 hm
  obtain ⟨k0, k1, k2, k3, _, hk_unpack⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length k.publicKey.bytes)
  have hk_ca0 :
      ((s.sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) =
        (((s.sp + 0xca0#64) ↦₆₄ k0) ∗ ((s.sp + 0xca8#64) ↦₆₄ k1) ∗
          ((s.sp + 0xcb0#64) ↦₆₄ k2) ∗ ((s.sp + 0xcb8#64) ↦₆₄ k3)) := by
    have h := hk_unpack (s.sp + 0xca0#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hk_2a8 :
      (((s.sp + 0x2a8#64) ↦₆₄ k0) ∗ ((s.sp + 0x2b0#64) ↦₆₄ k1) ∗
        ((s.sp + 0x2b8#64) ↦₆₄ k2) ∗ ((s.sp + 0x2c0#64) ↦₆₄ k3)) =
        ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) := by
    have h := (hk_unpack (s.sp + 0x2a8#64)).symm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
    exact h
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        ∃∗ a0 : BitVec 64, ∃∗ a1 : BitVec 64, ∃∗ a2 : BitVec 64, ∃∗ a3 : BitVec 64,
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsTrustCallPrePlaced A ikit x s0 s.sp ist0 c0 c1 d0 d1 d2 d3 k0 k1 k2 k3 a0 a1 a2 a3 d5 ∗
          wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (keyReady_entails_trustCallPre_placed C A ctl kit ikit x ans s0 s.sp
        st0 ist0 rec' pt k k0 k1 k2 k3 hsp hk_ca0)) ?_
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have htrust_lt : trustCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := trustCallStack_le_wsCalleeV kit ikit
    have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨a0, a1, a2, a3, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segTrust_call_placed_wp hyps.hooks.dealloc hyps.ikit htrust_lt
      (R := wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl haddr hpc hrun hsp_align hk_2a8 hfsAt
      (wsTrustFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx19_1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_trust : Except Unit Bool,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ∃∗ b0 : BitVec 8, ∃∗ b3 : BitVec 8, ∃∗ h1 : BitVec 16,
          ⌜sf.readReg64 .x28 = trustPollTag ans_trust ∧
            sf.readReg64 .x21 = b0.zeroExtend 64 ∧
            sf.readReg64 .x23 = b3.zeroExtend 64 ∧
            sf.readReg64 .x24 = h1.zeroExtend 64 ∧
            ikit.trustRel ist0 x.rem.val k .receiving ans_trust ∧
            sf.trace = s.trace ++ ikit.trustEvs x.rem.val k .receiving ans_trust ∧
            trustPollOutPlacedRel strPtr vt o2 o3 o4 o5 b0 b3 h1 ans_trust⌝ ∗
          (((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
            ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
            ((s.sp + 0x510#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_trust.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0
            (ikit.trustUpdate ist0 x.rem.val k .receiving ans_trust)
            rec' pt k) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_trust
      apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro strPtr
      apply Entails.sepExists_elim; intro vt
      apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o6
      apply Entails.sepExists_elim; intro b0
      apply Entails.sepExists_elim; intro b3
      apply Entails.sepExists_elim; intro h1
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_trust
        (Entails.sepExists_right strPtr (Entails.sepExists_right vt
          (Entails.sepExists_right o2 (Entails.sepExists_right o3
            (Entails.sepExists_right o4 (Entails.sepExists_right o5
              (Entails.sepExists_right o6 (Entails.sepExists_right b0
                (Entails.sepExists_right b3 (Entails.sepExists_right h1
                  (Entails.pure_right hpure ?_)))))))))))
      exact trustCallPost_entails_common_placed C A ctl kit ikit x ans s0 s.sp st0 ist0
        rec' pt k ans_trust box strPtr o2 o3 o4 o5 k0 k1 k2 k3 b0 b3 h1 o6 hsp hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_trust, strPtr, vt, o2, o3, o4, o5, o6, b0, b3, h1, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hx23_1, hx24_1, htrustRel, htr1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    rcases ans_trust with ⟨⟨⟩⟩ | t
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      rcases hrel1 with ⟨hb0, hh1, hb3, hsave_rel⟩
      let o1 := strPtr.extractLsb' 0 32
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((sf.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x500#64) ↦₆₄ o4) ∗ ((sf.sp + 0x508#64) ↦₆₄ o5) ∗
              ((sf.sp + 0x510#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗
              ((sf.sp + 0x590#64) ↦₆₄ e2) ∗ ((sf.sp + 0x598#64) ↦₆₄ e3) ∗
              ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R := by
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
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segTrust_tail_placed_err
          (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1 hx23_1 hx24_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x4f0#64) ↦₆₄ o2) ∗ ((s.sp + 0x4f8#64) ↦₆₄ o3) ∗
              ((s.sp + 0x500#64) ↦₆₄ o4) ∗ ((s.sp + 0x508#64) ↦₆₄ o5) ∗
              ((s.sp + 0x510#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗
              ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsTrustPostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, hb0, hb3, hh1, resWord1_trust_err]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_err_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist1
          rec' ses hcur pt k strPtr vt
          (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hsave_rel)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_trust_err C S x
        { ans with isTrustedIdentity := .error () } (kit.ScopeAt Scope st0 x.rem.val) rec rec' pt ses k
        hload hscope hdec hcur hrem rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with isTrustedIdentity := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with isTrustedIdentity := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_load_trust,
          List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving (.ok t)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (trustPostCommon_ok_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist1
          rec' pt k o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (s.sp + 0x120#64) g rec') ∗
            vecU8 A (s.sp + 0x290#64) pt ∗ ((s.sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit ikit st0 ist1 s0) ∗ R) := by
        rwa [emp_sepConj]
      cases t
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_false (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok false }, false, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok false }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
      · rw [hrel1] at hx21_1
        obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
          hx19_2, hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
          segTrust_tail_placed_ok_true (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1)
            (hx21 := hx21_1) _ hm1_emp hL1
        rotate_left
        · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
        have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
        have hsteps12 := hsteps1.trans hsteps2
        have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
          (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
        refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with isTrustedIdentity := .ok true }, true, ?_⟩)⟩
        have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
          (ans' := { ans with isTrustedIdentity := .ok true }) (ans := ans) rfl
        refine ⟨hpc2, hmeta2, ?_, ?_, ?_, rec, rec', pt, ses, k,
          hload, hscope, hdec, hcur, hrem, rfl, htrustRel, ?_, ?_⟩
        · rw [hx26_2, hx26_1, hx26, hsp]
        · rw [hx19_2, hx19_1, hsp]
        · rw [hx22_2, hx22_1, hx22, hsp]
        · rw [htr2, htr1, htr, List.append_assoc]
        · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust
