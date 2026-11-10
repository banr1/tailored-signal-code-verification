/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSave
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSaveAuxPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


set_option maxHeartbeats 3200000 in
theorem segSave_call_placed_wp [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {ikit : IdentityStoreSpec A 0#64}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hikit : IdentityStoreKitPlacedOkI ikit H)
    (hstack_lt : saveCallStack ikit ≤ 2 ^ 64)
    {s : State} {R : SepProp} {self addrA keyA : BitVec 64} {ist : ikit.IdState}
    {addr : AddrGhost} {k : IdentityKey} {c0 c1 d0 d1 d2 d3 : BitVec 64} {d5 : BitVec 32} {Q : Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
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
        FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗
        (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗
        stackAt s.sp (saveCallStack ikit))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (∃∗ ans : Except Unit IdentityChange, ∃∗ box : BitVec 64,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜sf.readReg64 .x28 = savePollTag ans ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist addr.val k ans ∧
            sf.trace = s.trace ++ ikit.saveEvs addr.val k ans ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans⌝ ∗
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
          FromRecordCallees.lsLogOff ∗ protocolAddressAt A addr addrA ∗
          (keyA ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗
          stackAt s.sp (saveCallStack ikit)) ∗ R) ∧
        sf.sp = s.sp ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := shim_463 (hikit.saveShim (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  have hdrop := futDrop_463 (hikit.saveFutDrop (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  unfold saveCallPCPlaced at hpc
  dsimp only [lsProg_463] at hfs ⊢
  have hdealloc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  refine SepWPp.congr_pre (by rw [stack_saveCall_to_saveShim ikit s.sp hstack_lt]) ?_
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.saveShimOff) hcrl
  clear hcrl
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl1
  cli_messageDecrypt_call_panic_p_lscro hshim hcrl1 (⟨self, addrA, keyA⟩ : IdentityShimCall)
  clear hcrl1 hshim
  apply StoreKit.sepWPp_seq_lscro (mid := ikit.savePollOff) hcrl_sf
  clear hcrl_sf
  wp_simp_pre [sepConj_assoc]
  apply SepWP.pure_elim; rintro ⟨hsteps_sh, hx1_sf, hx0_ne, hx0_al, htr_sf⟩
  have henv : ikit.envOk sf.fs.files :=
    (hfs.of_call hsteps_sh (by simp only [arm64_norm]) htr_sf).envOk_here
  clear hsteps_sh hfs
  apply SepWP.fold (Entails.of_eq (stack_saveShim_to_savePoll ikit s.sp hstack_lt)) (by sep_focus)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  intro hcrl2
  have hpoll := box_lscro_463 (hikit.savePoll (callerProg := lsProg_463 H) (callerBlk := 463) (by decide))
  cli_messageDecrypt_call_panic_lscro hpoll hcrl2 (⟨sf.readReg64 (Reg.gpr 0#5), s.sp + 1520#64, ⟨addrA, addr, keyA, k⟩⟩, self, ist)
  clear hcrl2 hpoll hikit
  generalize hbox : sf.readReg64 (Reg.gpr 0#5) = box at *
  simp only [hsp_sf] at hsp_sf_1 ⊢
  have hdz : ikit.saveFutDropOff ≠ 0#64 := by
    simpa only [BitVec.zero_add] using ikit.saveFutDrop_ne_zero (by decide)
  have hdz' : (ikit.saveFutDropOff == 0#64) = false := beq_eq_false_iff_ne.mpr hdz
  have hbs := ikit.saveBoxSize_ne_zero
  have hbs' : (BitVec.ofNat 64 ikit.saveBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs
  have hbs_toNat : (BitVec.ofNat 64 ikit.saveBoxSize).toNat = ikit.saveBoxSize :=
    Nat.mod_eq_of_lt ikit.saveBoxSize_lt
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
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.saveBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (9223372036854775834#64 : BitVec 64) = savePollTag (.error ()) from rfl] at *
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
    wp_steps
    refine SepWP.done (by simp_all) (by simp_all) fun ⟨hcl_d, hro_d⟩ => ?_
    wp_call hdrop ()
    wp_steps
    apply SepWP.fold (ikit.saveBoxAt_memRegion box self addrA keyA 1#8) (by sep_focus)
    apply SepWP.fold (Entails.of_eq (stack_savePoll_to_alloc ikit s.sp hstack_lt)) (by sep_focus)
    wp_call hdealloc (box, ikit.saveBoxSize, 8)
    simp only [h_22, hsp_sf_1] at hsp_sf_2 ⊢
    apply SepWP.fold (Entails.of_eq (stack_alloc_to_saveCall ikit s.sp hstack_lt)) (by sep_focus)
    simp only [show (bv% (2 ^ 64 - 2) : BitVec 64) = savePollTag (.ok c) from rfl] at *
    apply SepWP.done (by simp_all) (by simp_all)
    refine fun hm_final => ⟨Satisfies.mono (sepConj_mono_left ?_) hm_final, by simp_all⟩
    refine Entails.sepExists_right (.ok c)
      (Entails.sepExists_right box
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right 0#64
      (Entails.sepExists_right (if c = .replacedExisting then 1#32 else 0#32)
      (Entails.sepExists_right o2
      (Entails.sepExists_right o3
      (Entails.sepExists_right o4
      (Entails.sepExists_right o5
      (Entails.sepExists_right o6 ?_)))))))))
    refine Entails.pure_right (by simp_all) ?_
    dsimp only [Except.isOk, Except.toBool]
    simp only [↓reduceIte, emp_sepConj]
    exact Entails.of_eq (by ac_rfl)

def wsSaveFixedEnvPlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
  (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
  ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗ A.pool ∗ stackAt sp (saveCallStack ikit)

def wsSaveFixedRestPlaced (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (st : kit.StoreState) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ ((sp + 0xf8#64) ↦₆₄ s0.readReg64 .x3) ∗
  ((sp + 0x100#64) ↦₆₄ kit.ss_vt) ∗ ((sp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
  decLoadVtableAtV kit ∗ decStoreVtableAtV kit ∗ decTrustVtableAtV ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
  memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.loc x.locA ∗
  kit.storeAt (s0.readReg64 .x3) st ∗
  memRegion (sp - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
    (wsCalleeStackV kit ikit - saveCallStack ikit)

theorem wsFixed_wsEnv_save_split_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState) (hsp : sp = s0.sp - 0xee0#64) :
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        wsSaveFixedEnvPlaced A ikit x s0 sp ist ∗ wsSaveFixedRestPlaced A kit ikit x s0 sp st := by
  subst hsp
  have hjoin := wsCalleeStack_join_extra_placed kit ikit st ist s0
  refine Entails.trans (Entails.of_eq (show
    wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗ wsEnvPlaced A x (s0.sp - 0xee0#64) ∗
      decStoreExtraPlaced kit ikit st ist s0 =
    (stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
      (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsEnvPlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hjoin) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  refine Entails.pure_right hbound ?_
  unfold wsFixedVPlaced wsArgCellsV decVtablesAtV decSaveVtableAtV wsSaveFixedEnvPlaced wsSaveFixedRestPlaced
  simp only [BitVec.zero_add]
  rw [stack_wsCalleeV_saveCall kit ikit (s0.sp - 0xee0#64) hn]
  exact Entails.of_eq (by ac_rfl)

theorem wsFixed_wsEnv_save_join_placed [LibsignalPlacement] (A : RustAlloc)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64)
    (st : kit.StoreState) (ist : ikit.IdState)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsSaveFixedEnvPlaced A ikit x s0 sp ist ∗ wsSaveFixedRestPlaced A kit ikit x s0 sp st ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  subst hsp
  have hlt := s0.sp.isLt
  have hle : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hn : wsCalleeStackV kit ikit ≤ 2 ^ 64 := by omega
  have hsplit := wsCalleeStack_split_extra_placed kit ikit st ist s0 hbound
  refine Entails.trans (Entails.of_eq (show
    wsSaveFixedEnvPlaced A ikit x s0 (s0.sp - 0xee0#64) ist ∗
      wsSaveFixedRestPlaced A kit ikit x s0 (s0.sp - 0xee0#64) st =
    (kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      (memRegion ((s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit))
        (wsCalleeStackV kit ikit - saveCallStack ikit) ∗
        stackAt (s0.sp - 0xee0#64) (saveCallStack ikit))) ∗
    (wsFixedVPlaced kit ikit x s0 (s0.sp - 0xee0#64) ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ A.pool) by
    unfold wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixedVPlaced wsArgCellsV decVtablesAtV decSaveVtableAtV
    simp only [BitVec.zero_add]
    ac_rfl)) ?_
  rw [← stack_wsCalleeV_saveCall kit ikit (s0.sp - 0xee0#64) hn]
  refine Entails.trans (sepConj_mono_left hsplit) ?_
  unfold wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

def wsSaveCallPrePlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (k : IdentityKey) (c0 c1 d0 d1 d2 d3 : BitVec 64) (d5 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
  (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
  ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) ist ∗
  ((sp + 0x2d0#64) ↦₆₄ c0) ∗ ((sp + 0x2d8#64) ↦₆₄ c1) ∗
  ((sp + 0x520#64) ↦₆₄ d0) ∗ ((sp + 0x528#64) ↦₆₄ d1) ∗
  ((sp + 0x530#64) ↦₆₄ d2) ∗ ((sp + 0x538#64) ↦₆₄ d3) ∗ ((sp + 0x540#64) ↦₃₂ d5) ∗
  memRegion (sp + 0x5f0#64) 48 ∗ FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗
  ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗ A.pool ∗ stackAt sp (saveCallStack ikit)

def wsSaveFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsSaveFixedRestPlaced A kit ikit x s0 sp st ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
  memRegion (sp + 0x580#64) 0x24 ∗
  (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)

theorem trusted_entails_saveCallPre_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey)
    (hsp : sp = s0.sp - 0xee0#64) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist s0) ⊢
    ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
    ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
      wsSaveCallPrePlaced A ikit x s0 sp ist k c0 c1 d0 d1 d2 d3 d5 ∗
      wsSaveFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt := by
  refine Entails.trans (Entails.of_eq (show _ =
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ decStoreExtraPlaced kit ikit st ist s0) ∗
    (wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (wsFixed_wsEnv_save_split_placed A kit ikit x s0 sp st ist hsp)) ?_
  rw [sepConj_assoc (⌜_⌝)]
  apply Entails.pure_left; intro hbound
  refine Entails.pure_right hbound ?_
  rw [memRegion_300_b00_split, memRegion_300_280_split, memRegion_5a4_85c_split]
  refine Entails.trans (Entails.of_eq (show _ =
    (memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x520#64) 0x24) ∗
      (wsSaveFixedEnvPlaced A ikit x s0 sp ist ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x5f0#64) 48 ∗ wsSaveFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt) by
    unfold wsSaveFramePlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (memRegion_16_entails_cells (sp + 0x2d0#64))
    (memRegion_36_entails_cells (sp + 0x520#64)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro d0; apply Entails.sepExists_elim; intro d1
  apply Entails.sepExists_elim; intro d2; apply Entails.sepExists_elim; intro d3
  apply Entails.sepExists_elim; intro d5; apply Entails.sepExists_elim; intro c0
  apply Entails.sepExists_elim; intro c1
  refine Entails.sepExists_right c0 (Entails.sepExists_right c1
    (Entails.sepExists_right d0 (Entails.sepExists_right d1
      (Entails.sepExists_right d2 (Entails.sepExists_right d3
        (Entails.sepExists_right d5 ?_))))))
  unfold wsSaveCallPrePlaced wsSaveFixedEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

def wsSaveCallPostSpatialPlaced [LibsignalPlacement] (A : RustAlloc) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) (ist : ikit.IdState)
    (k : IdentityKey) (ans_save : Except Unit IdentityChange)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32) : SepProp :=
  ((sp + 0xe8#64) ↦₆₄ x.remA) ∗ ((sp + 0x108#64) ↦₆₄ s0.readReg64 .x5) ∗
  ((sp + 0x110#64) ↦₆₄ ikit.id_vt) ∗
  ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ ikit.saveShimOff) ∗
  (ikit.saveFutVtOff ↦₆₄ᵣ ikit.saveFutDropOff) ∗
  ((ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗
  ((ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
  ((ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ ikit.savePollOff) ∗
  ikit.identityAt (s0.readReg64 .x5) (ikit.saveUpdate ist x.rem.val k ans_save) ∗
  ((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ ikit.saveFutVtOff) ∗
  ((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
  ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗ ((sp + 0x540#64) ↦₃₂ o6) ∗
  ((sp + 0x5f0#64) ↦₆₄ savePollTag ans_save) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
  ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
  ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗ ((sp + 0x61c#64) ↦₃₂ o6) ∗
  (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
  FromRecordCallees.lsLogOff ∗ protocolAddressAt A x.rem x.remA ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
  A.pool ∗ stackAt sp (saveCallStack ikit)

def wsSavePostCommonRestPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
  vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
  memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
  memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
  decStoreExtraPlaced kit ikit st ist' s0

theorem saveCallPost_entails_common_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (k : IdentityKey)
    (ans_save : Except Unit IdentityChange)
    (box strPtr o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hsp : sp = s0.sp - 0xee0#64) (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    wsSaveCallPostSpatialPlaced A ikit x s0 sp ist k ans_save box strPtr o2 o3 o4 o5 o1 o6 ∗
      wsSaveFramePlaced C A ctl kit ikit x ans s0 sp st rec' pt ⊢
    (((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
    wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st
      (ikit.saveUpdate ist x.rem.val k ans_save) rec' pt := by
  let ist' := ikit.saveUpdate ist x.rem.val k ans_save
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      (((sp + 0x2d0#64) ↦₆₄ box) ∗ ((sp + 0x2d8#64) ↦₆₄ ikit.saveFutVtOff)) ∗
      (((sp + 0x5f0#64) ↦₆₄ savePollTag ans_save) ∗ ((sp + 0x5f8#64) ↦₃₂ o1) ∗
        ((sp + 0x5fc#64) ↦₆₄ o2) ∗ ((sp + 0x604#64) ↦₆₄ o3) ∗
        ((sp + 0x60c#64) ↦₆₄ o4) ∗ ((sp + 0x614#64) ↦₆₄ o5) ∗
        ((sp + 0x61c#64) ↦₃₂ o6)) ∗
      (wsSaveFixedEnvPlaced A ikit x s0 sp ist' ∗ wsSaveFixedRestPlaced A kit ikit x s0 sp st)) ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
      memRegion (sp + 0x580#64) 0x24 ∗
      (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
      wsMsgCells x sp ∗ (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion sp 0xa0 ∗
      (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
      (memRegion (sp + 0x5a4#64) 0x4c ∗ memRegion (sp + 0x620#64) 0x7e0) ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans)) by
    unfold wsSaveCallPostSpatialPlaced wsSaveFramePlaced wsSaveFixedEnvPlaced
    ac_rfl)) ?_
  have h16 := cells_16_entails_memRegion (sp + 0x2d0#64) box ikit.saveFutVtOff
  have h48 := cells_48_poll_entails_memRegion (sp + 0x5f0#64) (savePollTag ans_save)
    o2 o3 o4 o5 o1 o6
  have hjoin := wsFixed_wsEnv_save_join_placed A kit ikit x s0 sp st ist' hsp hbound
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h16 h48
  refine Entails.trans (sepConj_mono_left (sepConj_mono (key_entails_memRegion_32 (sp + 0x2a8#64) k)
    (sepConj_mono h16 (sepConj_mono h48 hjoin)))) ?_
  unfold wsSavePostCommonRestPlaced
  rw [memRegion_5a4_85c_split]
  exact Entails.of_eq (by ac_rfl)

theorem savePostCommon_ok_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    (((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗
      ((sp + 0x540#64) ↦₃₂ o6)) ∗
    memRegion (sp + 0x580#64) 0x24 ∗
    wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist' rec' pt ⊢
    wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0 := by
  have h36 := cells_36_entails_memRegion (sp + 0x520#64) o2 o3 o4 o5 o6
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36
  refine Entails.trans (sepConj_mono_left h36) ?_
  unfold wsSavePostCommonRestPlaced
  rw [memRegion_300_b00_split, memRegion_300_280_split]
  exact Entails.of_eq (by ac_rfl)

theorem savePostCommon_err_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (s0 : State) (sp : BitVec 64) (st : kit.StoreState) (ist' : ikit.IdState)
    (rec' : SessionRecord (List (BitVec 8)))
    (ses : Session (List (BitVec 8))) (hcur : rec'.currentSession = some ses)
    (pt : List (BitVec 8)) (strPtr vt x28 w20 w21 o2 o3 o4 o5 : BitVec 64) (o1 o6 : BitVec 32)
    (hx28 : x28 = 0x800000000000001A#64) (hw1 : resWord1 w20 w21 = o1)
    (hrel : pollOutPlacedRel (α := IdentityChange) strPtr vt o2 o3 o4 o5 o1 (.error ())) :
    (strPtr ↦ᵣ storeHookStr) ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗ ((sp + 0x540#64) ↦₃₂ o6) ∗
      ((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗ ((sp + 0x5a0#64) ↦₃₂ o6)) ∗
    wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 sp st ist' rec' pt) ⊢
    ∃∗ G : SessionGhost,
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
      (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) (.error (.store ())) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0 := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
    ((((sp + 0x520#64) ↦₆₄ o2) ∗ ((sp + 0x528#64) ↦₆₄ o3) ∗
      ((sp + 0x530#64) ↦₆₄ o4) ∗ ((sp + 0x538#64) ↦₆₄ o5) ∗ ((sp + 0x540#64) ↦₃₂ o6)) ∗
    ((((sp + 0x580#64) ↦₆₄ o2) ∗ ((sp + 0x588#64) ↦₆₄ o3) ∗
      ((sp + 0x590#64) ↦₆₄ o4) ∗ ((sp + 0x598#64) ↦₆₄ o5) ∗
      ((sp + 0x5a0#64) ↦₃₂ o6)) ∗ (strPtr ↦ᵣ storeHookStr)) ∗
    vecU8 A (sp + 0x290#64) pt ∗
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      (memRegion (sp + 0x300#64) 0x220 ∗ memRegion (sp + 0x544#64) 0x3c) ∗
      memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st ist' s0)) by
    unfold wsSavePostCommonRestPlaced; ac_rfl)) ?_
  have h36 := cells_36_entails_memRegion (sp + 0x520#64) o2 o3 o4 o5 o6
  have hst := stagedRes_storeErr_of_pollOutPlacedRel A strPtr vt x28 w20 w21 (sp + 0x580#64)
    o2 o3 o4 o5 o1 o6 hx28 hw1 hrel
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h36 hst
  have hrec := sessionRecordAt_some_entails_droppable A (sp + 0x120#64) rec' ses hcur
  have hpt : vecU8 A (sp + 0x290#64) pt ⊢ ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p :=
    Entails.sepExists_right pt (Entails.refl _)
  refine Entails.trans (sepConj_mono hrec (sepConj_mono h36
    (sepConj_mono hst (sepConj_mono_left hpt)))) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G
  refine Entails.sepExists_right G ?_
  rw [memRegion_300_280_split]
  exact Entails.of_eq (by ac_rfl)

theorem segSave_tail_placed_ok [LibsignalPlacement] {H : LibsignalHooks} {s : State} {R : SepProp}
    {c : IdentityChange}
    (hpc : s.pc = (blkPl_463).base + 9088#64)
    (hrun : s.status = .Running)
    (hx28 : s.readReg64 .x28 = savePollTag (.ok c)) :
    SepWP (lsProg_463 H) storeCallPCPlaced s emp
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ emp ∗ R)) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold storeCallPCPlaced
  dsimp only [lsProg_463]
  simp only [savePollTag] at hx28
  wp_steps
  wp_done

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
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
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
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  unfold errJoinPCPlaced
  dsimp only [lsProg_463, ite_true]
  simp only [savePollTag] at hx28
  wp_steps
  wp_done

attribute [local semireducible] SepWP in
theorem segSaveVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegSaveSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hfsAt : FsAt ikit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, -⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, and_self]).mono (fun _ h => h.2) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hpc' : s.pc = saveCallPCPlaced := hpc
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  rw [← hsp] at hx26 hx19 hx22 hm
  have hm_pre : s.mem ⊨
      (⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          wsSaveCallPrePlaced A ikit x s0 s.sp ist1 k c0 c1 d0 d1 d2 d3 d5 ∗
          wsSaveFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_saveCallPre_placed C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k hsp)) ?_
    simpa only [sepConj_assoc] using hm
  rw [sepConj_assoc (⌜_⌝), satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  have hstack_lt : saveCallStack ikit ≤ 2 ^ 64 := by
    have hlt := s0.sp.isLt
    have h1 := saveCallStack_le_wsCalleeV kit ikit
    have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
    omega
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segSave_call_placed_wp hyps.hooks.dealloc hyps.ikit hstack_lt
      (R := wsSaveFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R)
      hcrl haddr hpc' hrun hsp_align hx19 hfsAt
      (wsSaveFramePlaced C A ctl kit ikit x ans s0 s.sp st0 rec' pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx22_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_save : Except Unit IdentityChange,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜sf.readReg64 .x28 = savePollTag ans_save ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            ikit.saveRel ist1 x.rem.val k ans_save ∧
            sf.trace = s.trace ++ ikit.saveEvs x.rem.val k ans_save ∧
            pollOutPlacedRel strPtr vt o2 o3 o4 o5 o1 ans_save⌝ ∗
          (((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
            ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗
            ((s.sp + 0x540#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_save.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0
            (ikit.saveUpdate ist1 x.rem.val k ans_save) rec' pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_save
      apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro strPtr
      apply Entails.sepExists_elim; intro vt
      apply Entails.sepExists_elim; intro o1
      apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3
      apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5
      apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]
      apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_save (Entails.sepExists_right strPtr
        (Entails.sepExists_right vt (Entails.sepExists_right o1
          (Entails.sepExists_right o2 (Entails.sepExists_right o3
            (Entails.sepExists_right o4 (Entails.sepExists_right o5
              (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))))
      exact saveCallPost_entails_common_placed C A ctl kit ikit x ans s0 s.sp st0 ist1 rec' pt k
        ans_save box strPtr o2 o3 o4 o5 o1 o6 hsp hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_save, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hx28_1, hx21_1, hsaveRel, htr1, hrel1⟩, hm1_common⟩
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
            wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R := by
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
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_err (H := H) (R := ((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x520#64) ↦₆₄ o2) ∗ ((s.sp + 0x528#64) ↦₆₄ o3) ∗
              ((s.sp + 0x530#64) ↦₆₄ o4) ∗ ((s.sp + 0x538#64) ↦₆₄ o5) ∗ ((s.sp + 0x540#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            wsSavePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (savePostCommon_err_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' ses hcur pt
          strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
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
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let ist2 := ikit.saveUpdate ist1 x.rem.val k (.ok c)
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (savePostCommon_ok_entails_placed C A ctl kit ikit x ans s0 s.sp st0 ist2 rec' pt o2 o3 o4 o5 o6)) hm1_common
      have hm1_emp : sf.mem ⊨ emp ∗
          ((wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (s.sp + 0x120#64) g rec') ∗
            vecU8 A (s.sp + 0x290#64) pt ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗
            memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
            memRegion (s.sp + 0x300#64) 0xb00 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
            decStoreExtraPlaced kit ikit st0 ist2 s0) ∗ R) := by
        rwa [emp_sepConj]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2, hsp2, htr2,
        hx22_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ | ⟨_, _hoom⟩⟩ :=
        segSave_tail_placed_ok (H := H) (hpc := hpc1) (hrun := hrun1) (hx28 := hx28_1) _ hm1_emp hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      have hm2' := hpost2 hm2; rw [emp_sepConj] at hm2'
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ⟨{ ans with saveIdentity := .ok c }, ?_⟩)⟩
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with saveIdentity := .ok c }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, rec, rec', pt, ses, k, c,
        hload, hscope, hdec, hcur, hrem, htrust, rfl, htrustRel, hsaveRel, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx22_2, hx22_1, hx22, hsp]
      · rw [htr2, htr1, htr, List.append_assoc]
      · rw [hdraws]; simpa only [hsp, sepConj_assoc] using hm2'
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
