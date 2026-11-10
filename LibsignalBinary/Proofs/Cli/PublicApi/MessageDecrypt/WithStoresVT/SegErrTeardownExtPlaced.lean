/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SegErrTeardown` (`+0x2294 / +0x22a8 → +0x24d4`)

Proves relocatable (`[LibsignalPlacement]`) `segErrTeardownVX_placed_ok` on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave hiding segSave_call_placed_wp wsSaveFixedEnvPlaced wsSaveFixedRestPlaced wsFixed_wsEnv_save_split_placed wsFixed_wsEnv_save_join_placed wsSaveCallPrePlaced wsSaveFramePlaced trusted_entails_saveCallPre_placed wsSaveCallPostSpatialPlaced wsSavePostCommonRestPlaced saveCallPost_entails_common_placed savePostCommon_ok_entails_placed savePostCommon_err_entails_placed segSave_tail_placed_ok segSave_tail_placed_err segSaveVPlaced_ok stagedRes_storeErr_placed_intro pollOutPlacedRel pollOutPlacedRel_ok pollOutPlacedRel_err stagedRes_storeErr_of_pollOutPlacedRel withLsRoClBox box_lscro subroutine_ok_withStepsPost_lscro shim_197 box_lscro_197 futDrop_197 lscro_pre_intro sepWPp_call_panic_lscro sepWPp_call_panic_p_lscro clearLscroInvHyps wsMetaPlaced_of_steps panic_outcome_of_allocFailedInVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore hiding segStoreVPlaced_ok drop_session_structure_local2_head_placed_ok segStore_tail_placed_ok segStore_tail_placed_err wsStoreFixedEnvPlaced wsStoreFixedRestPlaced wsFixed_wsEnv_store_split_placed wsFixed_wsEnv_store_join_placed wsStoreCallPrePlaced wsStoreFramePlaced storeCall_entails_storeCallPre_placed wsStoreCallPostSpatialPlaced wsStorePostCommonRestPlaced storeCallPost_entails_common_placed storePostCommon_err_entails_placed wsStoreTailOkPre_placed wsStoreTailOkPost_placed wsStoreTailOkFramePlaced storePostCommon_ok_pre_tail_placed storePost_ok_entails_placed segStore_call_placed_wp
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown hiding teardown_tail_placed_ok teardownFramePlaced ej_false_expose_placed teardown_post_entails_placed segErrTeardownVPlaced_false teardown_pt_placed_ok ptFramePlaced ej_true_expose_placed pt_post_entails_placed segErrTeardownVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_false_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
    {x : DecryptGhost} {R : SepProp} {s0 s : State}
    (hst : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtraPlaced kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
  have hm_pre := Satisfies.mono (ej_false_expose_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_placed_ok (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFramePlaced C A ctl kit ikit x ans s0 s.sp F ∗ R')
      hyps.hooks.dealloc hdrop2 hcrl hpc hrun hsp_align hx28 hx26 hprev_lt
      (teardownFramePlaced C A ctl kit ikit x ans s0 s.sp F ∗ R') hm_pre hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails_placed C A ctl kit ikit x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres) hmf'
  refine ⟨sf, hsteps, Or.inl ⟨hpc2, hmeta2, ans, hpan, hscope, hcalls, hid_calls, ?_, ?_⟩⟩
  · rw [htr2, htr]
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]; exact hm_fin

attribute [local semireducible] SepWP in
theorem segErrTeardownVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State)
    (hst : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x pt R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
  cases pt with
  | false => exact segErrTeardownVX_false_placed hyps hdrop2 hst
  | true =>
    intro hL
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (s.sp + 0x290#64) p) ∗
        StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
    have hm_pre := Satisfies.mono (ej_true_expose_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_placed_ok (cap := cap) (ptr := ptr) (len := len)
        (R := ptFramePlaced C A ctl kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.hooks.dealloc hpc hrun hsp_align
        (ptFramePlaced C A ctl kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1'
    have hst1 : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s1 := by
      refine ⟨hpc1, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, ?_, ?_⟩
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rw [htr1, htr]
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownVX_false_placed hyps hdrop2 hst1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
