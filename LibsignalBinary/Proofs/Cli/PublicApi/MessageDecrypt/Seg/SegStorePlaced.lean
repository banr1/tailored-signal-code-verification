/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStore
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStoreAuxPlaced
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore hiding segStoreVPlaced_ok drop_session_structure_local2_head_placed_ok segStore_tail_placed_ok segStore_tail_placed_err wsStoreFixedEnvPlaced wsStoreFixedRestPlaced wsFixed_wsEnv_store_split_placed wsFixed_wsEnv_store_join_placed wsStoreCallPrePlaced wsStoreFramePlaced storeCall_entails_storeCallPre_placed wsStoreCallPostSpatialPlaced wsStorePostCommonRestPlaced storeCallPost_entails_common_placed storePostCommon_err_entails_placed wsStoreTailOkPre_placed wsStoreTailOkPost_placed wsStoreTailOkFramePlaced storePostCommon_ok_pre_tail_placed storePost_ok_entails_placed segStore_call_placed_wp

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


attribute [local semireducible] SepWP in
theorem segStoreVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegStoreSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps hdrop2 x ans R s0 s haddr hfs hst hL
  rcases hst with ⟨hpc, hmeta, hx26, hx22,
    rec, rec', pt, ses, k, c, hload, hscope, hdec, hcur, hrem, htrust, hsave, htrustRel, hsaveRel, htr, hm⟩
  have hfsAt : FsAt kit.envOk (kit.Quiet ∧ ikit.Quiet) (lsProg_463 H) s :=
    (hfs.fsAt htr fun hq => by
      obtain ⟨⟨hl, -⟩, ht, hs⟩ := hq
      simp only [NoFsEv.append_iff, hl, ht, hs, and_self]).mono (fun _ h => h.1) id
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hrecOk : kit.RecOk rec' := hyps.recOk x st0 rec rec' pt hscope hdec
  rw [← hsp] at hx26 hx22 hm
  let ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
    x.rem.val k ans.saveIdentity
  have hm_pre : s.mem ⊨
      (∃∗ g : RecordGhost, ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64,
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64, ∃∗ d5 : BitVec 32,
          ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
          wsStoreCallPrePlaced A kit x s0 s.sp (s.readReg64 .x26) g rec' st0 c0 c1 d0 d1 d2 d3 d5 ∗
          wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt) ∗ R := by
    refine Satisfies.mono (sepConj_mono_left
      (storeCall_entails_storeCallPre_placed C A ctl kit ikit x ans s0 s.sp (s.readReg64 .x26)
        st0 ist2 rec' pt hsp hx26)) ?_
    simpa only [sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨g, c0, c1, d0, d1, d2, d3, d5, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hbound, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  have hstack_lt : storeCallStack kit ≤ 2 ^ 64 := by
    have h1 := storeCallStack_le kit ikit
    have := s0.sp.isLt; unfold wsStackV at hbound; omega
  obtain ⟨sf, hsteps1, hout1⟩ :=
    segStore_call_placed_wp hyps.hooks.dealloc hyps.kit hstack_lt
      (self := s0.readReg64 .x3) (addrA := x.remA) (addr := x.rem)
      (g := g) (record := rec') (st := st0)
      (c0 := c0) (c1 := c1) (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d5 := d5)
      (R := wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt ∗ R)
      hcrl haddr hrecOk hpc hrun hsp_align hfsAt
      (wsStoreFramePlaced C A ctl kit ikit x ans s0 s.sp ist2 pt ∗ R) hm_pre hL
  rcases hout1 with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx22_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    rw [← sepConj_assoc] at hm1'
    have hm1_common : sf.mem ⊨
        (∃∗ ans_store : Except Unit Unit,
          ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
          ∃∗ o1 : BitVec 32, ∃∗ o2 : BitVec 64, ∃∗ o3 : BitVec 64, ∃∗ o4 : BitVec 64,
          ∃∗ o5 : BitVec 64, ∃∗ o6 : BitVec 32,
          ⌜kit.storeRel st0 x.rem.val rec' ans_store ∧
            sf.readReg64 .x28 = pollTag ans_store ∧
            sf.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans_store ∧
            sf.readReg64 .x21 = o1.zeroExtend 64 ∧
            pollOutPlacedRel (α := Unit) strPtr vt o2 o3 o4 o5 o1 ans_store⌝ ∗
          (((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
            ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6)) ∗
          memRegion (s.sp + 0x580#64) 0x24 ∗
          (if ans_store.isOk then emp else (strPtr ↦ᵣ storeHookStr)) ∗
          sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
          wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp
            (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt) ∗ R := by
      refine Satisfies.mono (sepConj_mono_left ?_) hm1'
      simp only [sepExists_sepConj_left]
      apply Entails.sepExists_elim; intro ans_store; apply Entails.sepExists_elim; intro box
      apply Entails.sepExists_elim; intro strPtr; apply Entails.sepExists_elim; intro vt
      apply Entails.sepExists_elim; intro o1; apply Entails.sepExists_elim; intro o2
      apply Entails.sepExists_elim; intro o3; apply Entails.sepExists_elim; intro o4
      apply Entails.sepExists_elim; intro o5; apply Entails.sepExists_elim; intro o6
      rw [sepConj_assoc]; apply Entails.pure_left; intro hpure
      refine Entails.sepExists_right ans_store (Entails.sepExists_right strPtr
        (Entails.sepExists_right vt (Entails.sepExists_right o1
          (Entails.sepExists_right o2 (Entails.sepExists_right o3
            (Entails.sepExists_right o4 (Entails.sepExists_right o5
              (Entails.sepExists_right o6 (Entails.pure_right hpure ?_)))))))))
      exact storeCallPost_entails_common_placed C A ctl kit ikit x ans s0 s.sp (s.readReg64 .x26) g rec'
        (kit.storeUpdate st0 x.rem.val rec' ans_store) ist2 pt
        ans_store box strPtr o2 o3 o4 o5 o1 o6 hsp hx26 hbound
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_common
    rcases hm1_common with ⟨ans_store, strPtr, vt, o1, o2, o3, o4, o5, o6, hm1_common⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_common
    rcases hm1_common with ⟨⟨hstoreRel, hx28_1, htr1, hx21_1, hrel1⟩, hm1_common⟩
    have hL1 := hsteps1.codeLoaded hL
    have hcrl1 := hcrl.of_keepsFrozen hsteps1.keepsFrozen
    rcases ans_store with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.error ())
      simp only [Except.isOk, Except.toBool, Bool.false_eq_true, ↓reduceIte] at hm1_common
      have hm1_err : sf.mem ⊨
          (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 32,
            (((sf.sp + 0x550#64) ↦₆₄ o2) ∗ ((sf.sp + 0x558#64) ↦₆₄ o3) ∗
              ((sf.sp + 0x560#64) ↦₆₄ o4) ∗ ((sf.sp + 0x568#64) ↦₆₄ o5) ∗ ((sf.sp + 0x570#64) ↦₃₂ o6) ∗
              ((sf.sp + 0x580#64) ↦₆₄ e0) ∗ ((sf.sp + 0x588#64) ↦₆₄ e1) ∗ ((sf.sp + 0x590#64) ↦₆₄ e2) ∗
              ((sf.sp + 0x598#64) ↦₆₄ e3) ∗ ((sf.sp + 0x5a0#64) ↦₃₂ e4)) ∗
            ((strPtr ↦ᵣ storeHookStr) ∗
              sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
              wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R := by
        rw [hsp1]; refine Satisfies.mono (sepConj_mono_left ?_) hm1_common
        refine Entails.trans (sepConj_mono_right
          (sepConj_mono_left (memRegion_36_entails_cells (s.sp + 0x580#64)))) ?_
        simp only [sepExists_sepConj_left, sepExists_sepConj_right]
        apply Entails.sepExists_elim; intro e0; apply Entails.sepExists_elim; intro e1
        apply Entails.sepExists_elim; intro e2; apply Entails.sepExists_elim; intro e3
        apply Entails.sepExists_elim; intro e4
        refine Entails.sepExists_right e0 (Entails.sepExists_right e1
          (Entails.sepExists_right e2 (Entails.sepExists_right e3
            (Entails.sepExists_right e4 ?_))))
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; exact Entails.refl _
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_err
      rcases hm1_err with ⟨e0, e1, e2, e3, e4, hm1_err⟩
      rw [sepConj_assoc] at hm1_err
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_err (R := ((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R)
          hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx21_1
          (((strPtr ↦ᵣ storeHookStr) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt) ∗ R) hm1_err hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx26_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1] at hm2'
      have hm2_ro : sf2.mem ⊨
          ((strPtr ↦ᵣ storeHookStr) ∗
            ((((s.sp + 0x550#64) ↦₆₄ o2) ∗ ((s.sp + 0x558#64) ↦₆₄ o3) ∗
              ((s.sp + 0x560#64) ↦₆₄ o4) ∗ ((s.sp + 0x568#64) ↦₆₄ o5) ∗ ((s.sp + 0x570#64) ↦₃₂ o6) ∗
              ((s.sp + 0x580#64) ↦₆₄ o2) ∗ ((s.sp + 0x588#64) ↦₆₄ o3) ∗
              ((s.sp + 0x590#64) ↦₆₄ o4) ∗ ((s.sp + 0x598#64) ↦₆₄ o5) ∗ ((s.sp + 0x5a0#64) ↦₃₂ o6)) ∗
            sessionRecordAt A (s.sp + 0x120#64) g rec' ∗
            wsStorePostCommonRestPlaced C A ctl kit ikit x ans s0 s.sp st1 ist2 pt)) ∗ R :=
        Eq.mp (congrArg (sf2.mem ⊨ ·) (by ac_rfl)) hm2'
      have hw1 : resWord1 (sf2.readReg64 .x20) (sf2.readReg64 .x21) = o1 := by
        rw [hx20_2, hx21_2, resWord1_lsr8]
      have hm2_err := Satisfies.mono (sepConj_mono_left
        (storePostCommon_err_entails_placed C A ctl kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt strPtr vt (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          o2 o3 o4 o5 o1 o6 hx28_2 hw1 hrel1)) hm2_ro
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_err
      rcases hm2_err with ⟨G, hm2_err⟩
      refine ⟨sf2, hsteps12, Or.inl (Or.inr ?_)⟩
      have hmod := model_of_store_err C S x
        { ans with storeSession := .error () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .error () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, ?_, ?_, { ans with storeSession := .error () }, some (G, ses.state),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hx26_2, hx26_1, hx26, hsp]
      · rw [hx28_2]; decide
      · rw [hmod.1]; decide
      · intro p; rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [ite_true, hsp, sepConj_assoc] using hm2_err
    · let st1 := kit.storeUpdate st0 x.rem.val rec' (.ok ())
      simp only [Except.isOk, Except.toBool, ↓reduceIte, emp_sepConj] at hm1_common
      have hm1_ok := Satisfies.mono (sepConj_mono_left
        (storePostCommon_ok_pre_tail_placed C A ctl kit ikit x ans s0 s.sp g rec' ses hcur
          st1 ist2 pt o2 o3 o4 o5 o6 hsp)) hm1_common
      simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1_ok
      rcases hm1_ok with ⟨G, cap, ptr, s0_580, s1_588, s2_lo, s2_hi, s3_598, s4_5a0,
        t0_300, t1_308, t2_310, t3_318, t4_320, hm1_ok⟩
      rw [sepConj_assoc, satisfies_pure_sepConj] at hm1_ok
      rcases hm1_ok with ⟨⟨_, hprev_lt, hprev_ptr⟩, hm1_ok⟩
      rw [sepConj_assoc, ← hsp1] at hm1_ok
      have hx26_sf : sf.readReg64 .x26 = sf.sp + 0xa0#64 := by rw [hx26_1, hx26, hsp1]
      have hx22_sf : sf.readReg64 .x22 = sf.sp + 0x294#64 := by rw [hx22_1, hx22, hsp1]
      obtain ⟨sf2, hsteps2, ⟨hpc2, hrun2, P_f2, hm2, hpost2⟩ | ⟨_, _hoom⟩⟩ :=
        segStore_tail_placed_ok hyps.hooks.dealloc hdrop2
          (R := wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R)
          hcrl1 hpc1 hrun1 (hsp1 ▸ hsp_align) hx28_1 hx26_sf hx22_sf hprev_lt hprev_ptr
          (wsStoreTailOkFramePlaced C A ctl kit ikit x ans s0 sf.sp cap ptr st1 ist2 pt ∗ R) hm1_ok hL1
      rotate_left
      · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
      obtain ⟨hm2', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost2 hm2
      have hsteps12 := hsteps1.trans hsteps2
      have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps12 hrun2 (hsp2.trans hsp1)
        (hx29_2.trans hx29_1) (hx27_2.trans hx27_1) (hvregs_2.trans hvregs_1)
      rw [hsp1, ← sepConj_assoc] at hm2'
      have hm2_ok := Satisfies.mono (sepConj_mono_left
        (storePost_ok_entails_placed C A ctl kit ikit x ans s0 s.sp g.prevCap g.prevPtr cap ptr
          st1 ist2 pt
          (cap.extractLsb' 0 32)
          (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
          ((BitVec.ofNat 64 pt.length).extractLsb' 32 32)
          s2_hi s3_598 s4_5a0 (sf2.readReg64 .x28) (sf2.readReg64 .x20) (sf2.readReg64 .x21)
          hx28_2 hx20_2 hx21_2 rfl rfl rfl rfl hsp hbound)) hm2'
      refine ⟨sf2, hsteps12, Or.inl (Or.inl ?_)⟩
      have hmod := model_of_store_ok C S x
        { ans with storeSession := .ok () } rec rec' pt ses k c
        hload hscope.1 hdec hcur hrem htrust hsave rfl
      have hdraws := draws_eq_of_loadSession_eq (C := C) (x := x)
        (ans' := { ans with storeSession := .ok () }) (ans := ans) rfl
      refine ⟨hpc2, hmeta2, { ans with storeSession := .ok () }, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hmod.1]; exact nofun
      · intro r hr; dsimp only at hr; rw [hload] at hr; cases hr; exact hscope
      · rw [hmod.2]; exact ⟨hload ▸ hscope.2, hstoreRel, trivial⟩
      · rw [hmod.2]; exact ⟨htrustRel, hsaveRel, trivial⟩
      · rw [htr2, htr1, htr, hmod.2, Identity.IdentityStoreSpec.traceOfWith_all4]
        simp only [List.append_assoc]
      · rw [hmod.1, hmod.2, hdraws]
        dsimp only [SessionStoreSpec.storeFinal, Identity.IdentityStoreSpec.idFinal]
        simpa only [hsp, sepConj_assoc] using hm2_ok
  · have hpan_m := hpan_post1 hm1; rw [← sepConj_assoc] at hpan_m
    have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R :=
      Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVPlaced ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
