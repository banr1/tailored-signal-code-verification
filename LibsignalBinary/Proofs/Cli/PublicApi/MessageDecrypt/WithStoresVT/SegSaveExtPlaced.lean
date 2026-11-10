/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local semireducible] SepWP in
set_option maxHeartbeats 800000 in
theorem segSaveVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : DecFsCtxExtPlaced kit ikit H s0 s)
    (hst : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans true R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => (∃ ans', StoreCallStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x true R s0 s') := by
  intro hL
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
    exact ⟨sf, hsteps1, Or.inr (panic_outcome_of_allocFailedInVX_placed ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
