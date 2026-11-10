/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.SegUntrustedExt
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlaced
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `SegUntrusted` (`+0x21b0 → +0x2294`)

Proves relocatable (`[LibsignalPlacement]`) `segUntrustedVX_placed_ok` on `lsProg_463 H`.
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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted hiding segUntrusted_placed_wp wsUntrustedFixedEnvPlaced wsUntrustedFixedRestPlaced wsFixed_wsEnv_untrusted_split_placed wsUntrustedPrePlaced wsUntrustedCommonRestPlaced wsUntrustedFramePlaced trusted_entails_untrustedPre_placed wsUntrustedPostSpatialPlaced untrustedPost_entails_placed segUntrustedVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem model_of_trust_false_noScope (C : Crypto) (S : SpqrModel) (x : DecryptGhost)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8))
    (ses : Session (List (BitVec 8))) (k : IdentityKey)
    (hload : ans.loadSession = .ok (some rec))
    (hdec : decryptRecord C S uuidTryParse x rec = .ok (pt, rec'))
    (hcur : rec'.currentSession = some ses)
    (hik : ses.state.remoteIdentity = some k)
    (htrust : ans.isTrustedIdentity = .ok false) :
    (x.model C S uuidTryParse ans).1 = .error (.untrustedIdentity x.rem.val) ∧
    (x.model C S uuidTryParse ans).2 =
      [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving] := by
  have h : x.model C S uuidTryParse ans =
      (.error (.untrustedIdentity x.rem.val),
        [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .receiving]) := by
    unfold DecryptGhost.model
    unfold decryptRecord at hdec
    rw [messageDecryptSignal_eq_flat]
    simp [decryptFlat, hload, hdec, hcur, hik, htrust]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

set_option maxHeartbeats 800000 in
attribute [local semireducible] SepWP in
theorem segUntrustedVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hyps : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hst : TrustedStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans false R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x true R s0) := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx19, hx22,
    rec, rec', pt, ses, k, hload, hscope, hdec, hcur, hrem, htrust, htrustRel, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hx19 hx22 hm
  let ist1 := ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity
  let R' : SepProp := decStoreExtraPlaced kit ikit st0 ist1 s0 ∗ R
  have hm_pre : s.mem ⊨
      (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 32,
        ∃∗ e3 : BitVec 64, ∃∗ e4 : BitVec 64, ∃∗ d0 : BitVec 8, ∃∗ pad : List (BitVec 8),
          ⌜pad.length = 7⌝ ∗
          wsUntrustedPrePlaced A x s.sp e0 e1 e3 e2 d0 pad ∗
          wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4) ∗ R' := by
    refine Satisfies.mono (sepConj_mono_left
      (trusted_entails_untrustedPre_placed C A ctl kit ikit x ans s0 s.sp rec' pt k)) ?_
    simpa only [R', ist1, sepConj_assoc] using hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨e0, e1, e2, e3, e4, d0, pad, hm_pre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pre
  rcases hm_pre with ⟨hpad, hm_pre⟩
  rw [sepConj_assoc] at hm_pre
  obtain ⟨devWord, hw4⟩ := exists_unpack64_of_length_8 (bs := x.rem.device :: pad) (by simp [hpad])
  obtain ⟨sf, hsteps, hout⟩ :=
    segUntrusted_placed_wp hyps.hooks
      (R := wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R')
      _hcrl hw4 hpc hrun hsp_align
      (wsUntrustedFramePlaced C A ctl kit ikit x ans s0 s.sp rec' pt k e4 ∗ R') hm_pre hL
  rcases hout with ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨hpan1, P_f, hm1, hpan_post1⟩ | ⟨_, _hoom⟩
  · obtain ⟨hm1', hsp1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1'
    rcases hm1' with ⟨cap, ptr, hm1'⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm1'
    rcases hm1' with ⟨⟨hx28_1, hx20_1, hx21_1, htr1⟩, hm1'⟩
    rw [← sepConj_assoc] at hm1'
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hw1 : resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = cap.extractLsb' 0 32 := by
      rw [hx20_1, hx21_1, resWord1_lsr8]
    have hm1_post := Satisfies.mono (sepConj_mono_left
      (untrustedPost_entails_placed C A ctl kit ikit x ans s0 s.sp rec' ses hcur pt k
        (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21)
        cap ptr devWord e4 pad hpad hw4 hx28_1 hw1)) hm1'
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm1_post
    rcases hm1_post with ⟨G, hm1_post⟩
    refine ⟨sf, hsteps, Or.inl ?_⟩
    have hmod := model_of_trust_false_noScope C S x ans rec rec' pt ses k
      hload hdec hcur hrem htrust
    refine ⟨hpc1, hmeta1, ?_, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx26_1, hx26, hsp]
    · rw [hx28_1]; decide
    · rw [hmod.1]; exact nofun
    · intro p; rw [hmod.1]; exact nofun
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod.2]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod.2]; exact ⟨htrustRel, trivial⟩
    · rw [htr1, htr, hmod.2]; simp
    · have hstf : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by
        rw [hmod.2]; rfl
      have histf : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist1 := by
        rw [hmod.2]; rfl
      rw [hmod.1, hstf, histf]
      simpa only [R', ite_true, hsp, sepConj_assoc] using hm1_post
  · have hpan_m' : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
      have hpan_m0 := hpan_post1 hm1
      rw [← sepConj_assoc] at hpan_m0
      have hpan_m1 := Satisfies.mono (sepConj_mono_left (shim_onPanic_entails rfl)) hpan_m0
      have hreord :
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R' ⊢
          (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
        dsimp only [R']
        rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap]
        exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))
      exact Satisfies.mono hreord hpan_m1
    exact ⟨sf, hsteps, Or.inr (panic_outcome_of_allocFailedInVX_placed ⟨_, htr.symm⟩ hpan1 hpan_m')⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
