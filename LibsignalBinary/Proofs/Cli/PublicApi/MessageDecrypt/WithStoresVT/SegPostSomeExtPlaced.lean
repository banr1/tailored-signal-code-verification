/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostSome
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegPostSomeHelpersPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordJoin

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
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
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone hiding vecU8Buf segPostNoneVPlaced_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome hiding segPostSomeVPlaced_ok panic_at_expect_failed_msgDecrypt_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome
open CryptoVerification

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxHeartbeats 800000 in
theorem segPostSomeVX_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    (hhyps : DecHypsExtPlaced C A uuidTryParse S encRecord H kit ikit st0 Scope)
    (hRemIk : RemoteIdentityKeyPlacedOk A H)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State)
    (hPre : PostSomeStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s) :
    DecSegVXPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s
      (fun s' => KeyReadyStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s') := by
  intro hL
  rcases hPre with ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    s1, rec_, ses, G, prevCap, prevPtr, hs1_sp, hs1_tr, hload, hscope, hcur, hw0, hmem⟩
  let sp := s0.sp - 0xee0#64
  let R' : SepProp := decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  change s1.sp = sp at hs1_sp
  let x_rg := recGhostOf x prevPtr G ses.state
  change s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).post x_rg s1 s ∗
    wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R' at hmem
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec, sepConj_assoc, satisfies_pure_sepConj] at hmem
  rcases hmem with ⟨⟨hno_pan, htr_s1, hs_sp1, _, _, hx26, hx28⟩, hmem⟩
  rw [hs1_sp] at hx26 hmem
  dsimp only [sp] at hx26
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have htrace : s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession :=
    htr_s1.trans hs1_tr
  have hdraws : x.draws C ans = x_rg.draws C :=
    draws_eq_region_draws C x prevPtr G ses ans rec_ hload hcur
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced at hpc
  change s.pc = (blkPl_463).base + 8016#64 at hpc
  rcases hmod_rg : x_rg.model C S uuidTryParse with ⟨res_rg, st'⟩
  cases res_rg with
  | error e =>
    have hmod1 : (x_rg.model C S uuidTryParse).1 = .error e := by rw [hmod_rg]
    have hne : e ≠ .panic := fun hp => hno_pan (hmod1.trans (congrArg Except.error hp))
    have hmod : x.model C S uuidTryParse ans = (.error (.protocol e), [.loadSession x.rem.val]) :=
      model_of_region_err C S x prevPtr G ses ans rec_ e hload hcur hmod1 hne
    rw [hmod1] at hx28 hmem
    dsimp only [x_rg, recGhostOf] at hmem
    have hmem1 : s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G ses.state) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error e) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R')) := by
      unfold wsMsgCells
      dsimp only [sp] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    clear hmem
    obtain ⟨w21, w0, w1, w2, w3, w4, bs, H_err, hbs_len, hbs_eq, hreassemble, hmem2⟩ :=
      recordResultAt_err_sat hne hmem1
    clear hmem1
    have h300_split :
        memRegion (sp + 0x300#64) 0x1b0 =
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc := by
      rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h4e0_split :
        memRegion (sp + 0x4e0#64) 0x920 =
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x580#64) 0x24 ∗
            memRegion (sp + 0x5a4#64) 0x85c := by
      rw [memRegion_split (sp + 0x4e0#64) 0xa0 0x880 (by decide),
          memRegion_split (sp + 0x4e0#64 + 0xa0#64) 0x24 0x85c (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hmem_act : s.mem ⊨
        (memRegion (sp + 0x490#64) 0x14 ∗
          ((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
          memRegion (sp + 0x580#64) 0x24) ∗
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G ses.state ∗
          H_err ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsFixedVPlaced kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') := by
      have hws_eq :
          wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr =
            wsFixedVPlaced kit ikit x s0 sp ∗
              ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              memRegion (sp + 0x300#64) 0x1b0 ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
              memRegion x.ret 48 := by
        unfold wsRegionFrameVPlaced wsFixedVPlaced
        dsimp only [sp]
        ac_rfl
      rw [hws_eq, h300_split, h4e0_split] at hmem2
      dsimp only [sp] at hmem2 ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
    clear hmem2
    have hwp : SepWP (lsProg_463 H) (errJoinPCPlaced false) s
        (memRegion (sp + 0x490#64) 0x14 ∗
          ((sp + 0x4b0#64) ↦₆₄ recordResultTag (.error e)) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
          memRegion (sp + 0x580#64) 0x24)
        (fun sf Pf =>
          (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            ((sp + 0x580#64) ↦ₛ bs)) ∧
          sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
          sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
          sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = recordResultTag (.error e) ∧
          resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0) := by
      simp only [errJoinPCPlaced, Bool.false_eq_true, ↓reduceIte]
      dsimp only [lsProg_463] at hpc ⊢
      wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
      dsimp only [sp]
      wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      repeat' (apply SepWP.exists_elim; intro _)
      have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
      have hx28_ne : recordResultTag (.error e) + 2#64 ≠ 0#64 :=
        recordResultTag_err_add_two_ne_zero e hne
      wp_steps
      apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
      apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (recordResultTag (.error e)) w21 w0 w1 w2 w3 w4) (by sep_focus)
      apply SepWP.fold (dst36_fold (s0.sp - 0xee0#64) w0 w1 w2 w3 w4 hbs_eq) (by sep_focus)
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      refine ⟨?_, rfl, hal, rfl, ?_, ?_, ?_, ?_, ?_, hvregs⟩
      · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
        exact Entails.of_eq (by ac_rfl)
      · wp_norm_lhs
      · wp_norm_lhs
      · simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
        wp_norm_lhs
      · wp_norm_lhs
      · simp only [wp_norm, arm64_norm]
        exact resWord1_ubfm_eq w21
    obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, Pf, hmf, hent_pf, hsp_sf, hal_sf, htr_sf,
      hx29_sf, hx27_sf, hx26_sf, hx28_sf, hres_w1, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
      hwp.elim hmem_act hL
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
    refine ⟨sf, hsteps, Or.inl (Or.inr ?_)⟩
    have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
    clear hmf hent_pf
    refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hcrl_sf, hvregs_sf⟩,
      hx26_sf, ?_, ans, some (G, ses.state), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx28_sf]
      exact recordResultTag_err_ne_pendingTag e hne
    · intro h; rw [hmod] at h; cases h
    · intro p h; rw [hmod] at h; cases h
    · intro r hr; rw [hload] at hr; cases hr; exact hscope
    · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
    · rw [hmod]; trivial
    · rw [htr_sf, htrace, hmod]; simp
    · have hstaged :
          ((sp + 0x580#64) ↦ₛ bs) ∗ H_err ⊢
            StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
              (x.model C S uuidTryParse ans).1 := by
        unfold StagedRes
        refine Entails.sepExists_right bs (Entails.sepExists_right H_err ?_)
        refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
        rw [hmod, hx28_sf, hres_w1]
        exact hreassemble r
      have h290_split :
          memRegion (sp + 0x290#64) 0x38 =
            memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
        rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have h300_join :
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x4e0#64) 0xa0 =
          memRegion (sp + 0x300#64) 0x280 := by
        rw [memRegion_split (sp + 0x300#64) 0x190 0xf0 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xdc (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0xd0 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0xa0 (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hcomb :
          (memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            ((sp + 0x580#64) ↦ₛ bs)) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            sessionStateAt A (sp + 0x138#64) G ses.state ∗
            H_err ∗
            memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ R') ⊢
          wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
            droppableRecordAt A (sp + 0x120#64) (some (G, ses.state)) ∗
            memRegion (sp + 0x290#64) 24 ∗
            StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
              (x.model C S uuidTryParse ans).1 ∗
            memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
        have hwsEnv_eq :
            signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
              protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
              (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
              A.pool =
            wsEnvPlaced A x sp := by
          unfold wsEnvPlaced
          rw [stackAt_root_join_wsCallee sp]
        rw [hdraws, h290_split]
        have hreord_lhs :
            (memRegion (sp + 0x490#64) 0x14 ∗
              memRegion (sp + 0x4b0#64) 0x30 ∗
              ((sp + 0x580#64) ↦ₛ bs)) ∗
            (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
              ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
              sessionStateAt A (sp + 0x138#64) G ses.state ∗
              H_err ∗
              memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
              stackAt sp rootStack ∗ A.pool ∗
              wsFixedVPlaced kit ikit x s0 sp ∗
              ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              (memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
              memRegion (sp + 0x2d0#64) 0x10 ∗
              memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
              memRegion x.ret 48 ∗ R') =
            ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
                ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
                sessionStateAt A (sp + 0x138#64) G ses.state) ∗
              (((sp + 0x580#64) ↦ₛ bs) ∗ H_err) ∗
              (wsFixedVPlaced kit ikit x s0 sp ∗
                (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
                  protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
                  (stackAt sp rootStack ∗ memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
                  A.pool) ∗
                wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
                memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
                (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
                  memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
                  memRegion (sp + 0x4e0#64) 0xa0) ∗
                memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗
                cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ R')) := by
          ac_rfl
        rw [hreord_lhs, hwsEnv_eq, h300_join]
        refine Entails.trans
          (sepConj_mono (record_some_entails_droppable A sp prevCap prevPtr G ses.state)
            (sepConj_mono_left hstaged)) ?_
        exact Entails.of_eq (by ac_rfl)
      have hmf_res := Satisfies.mono hcomb hmf1
      have hsf_eq : kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2 = st0 := by rw [hmod]; rfl
      have hif_eq : ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2 = ist0 := by rw [hmod]; rfl
      rw [hsf_eq, hif_eq]
      simpa only [R', sepConj_assoc, Bool.false_eq_true, ↓reduceIte] using hmf_res
  | ok pt =>
    have hmod1 : (x_rg.model C S uuidTryParse).1 = .ok pt := by rw [hmod_rg]
    have hmod2 : (x_rg.model C S uuidTryParse).2 = st' := by rw [hmod_rg]
    rw [hmod1] at hx28
    dsimp only [recordResultTag] at hx28
    simp only [hmod1, hmod2, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hmem
    dsimp only [x_rg, recGhostOf] at hmem
    obtain ⟨G', hmem⟩ := hmem
    have hmem_rel : s.mem ⊨ ⌜G.AfterRecordDecrypt G'⌝ ∗
        ((memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateAt A (sp + 0x138#64) G' st') ∗
         (recordResultAt A (sp + 0x4b0#64) (.ok pt) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R'))) := by
      unfold wsMsgCells
      dsimp only [sp] at hmem ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
    clear hmem
    rw [satisfies_pure_sepConj] at hmem_rel
    obtain ⟨hrel, hmem1⟩ := hmem_rel
    obtain ⟨cap, ptr, w21, w0, w1, w2, hvec_pt, hmem2⟩ := recordResultAt_ok_sat hmem1
    clear hmem1
    have hmem_ss : s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64)) ∗
        (sessionStateAt A (sp + 0x138#64) G' st' ∗
          (((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
            ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗
            ((sp + 0x4cc#64) ↦₃₂ w2) ∗ memRegion (sp + 0x4d0#64) 16 ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ∗ memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗
            wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R')) :=
      Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem2
    clear hmem2
    have hrem_inv := sessionStateAt_rem_inv hmem_ss
    have hcap_lt := sessionStateAt_localIk_cap_lt hmem_ss
    have hcap_ne : (G'.localIk.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr (cap_add_one_ne_zero hcap_lt)
    have h300_split :
        memRegion (sp + 0x300#64) 0x1b0 =
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc := by
      rw [memRegion_split (sp + 0x300#64) 0x190 0x20 (by decide),
          memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0xc (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h290_split :
        memRegion (sp + 0x290#64) 0x38 =
          memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20 := by
      rw [memRegion_split (sp + 0x290#64) 24 0x20 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have h4e0_split :
        memRegion (sp + 0x4e0#64) 0x920 =
          memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
            memRegion (sp + 0x612#64) 0x68e ∗ memRegion (sp + 0xca0#64) 32 ∗
            memRegion (sp + 0xcc0#64) 0x140 := by
      rw [memRegion_split (sp + 0x4e0#64) 0x110 0x810 (by decide),
          memRegion_split (sp + 0x4e0#64 + 0x110#64) 34 0x7ee (by decide),
          memRegion_split (sp + 0x4e0#64 + 0x110#64 + 34#64) 0x68e 0x160 (by decide),
          memRegion_split (sp + 0x4e0#64 + 0x110#64 + 34#64 + 0x68e#64) 32 0x140 (by decide)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    have hstk_split :
        stackAt sp rootStack =
          memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack := by
      simp only [stackAt, rootStack, Getters.remoteIdentityKeyStack, Nat.reducePow]
      have hsplit := memRegion_split (sp - 262144#64) 262000 144 (by decide)
      have hadd : sp - 262144#64 + 262000#64 = sp - 144#64 := by bv_omega
      rw [hsplit, hadd]
    have hmem_act : s.mem ⊨
        (memRegion (sp + 0x490#64) 0x14 ∗
          ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          memRegion (sp + 0x4d0#64) 16 ∗
          memRegion (sp + 0x290#64) 24 ∗
          ((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
          vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
          memRegion (sp + 0x5f0#64) 34 ∗
          memRegion (sp + 0xca0#64) 32 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp Getters.remoteIdentityKeyStack) ∗
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ∗
          memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
          memRegion (sp + 0xcc0#64) 0x140 ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗
          memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
          wsFixedVPlaced kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') := by
      have hws_eq :
          wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr =
            wsFixedVPlaced kit ikit x s0 sp ∗
              ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              memRegion (sp + 0x300#64) 0x1b0 ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
              memRegion x.ret 48 := by
        unfold wsRegionFrameVPlaced wsFixedVPlaced
        dsimp only [sp]
        ac_rfl
      rw [sessionStateAt_expose_rem A (sp + 0x138#64) G' st',
          hws_eq, h300_split, h290_split, h4e0_split, hstk_split] at hmem_ss
      dsimp only [sp] at hmem_ss ⊢
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem_ss
    clear hmem_ss
    have hrem_call : subroutine_ok (lsProg_463 H) (lsmpl.base 29)
        (StoreKit.withLsCodeRoLoaded lsmpl (Getters.remoteIdentityKeyPlacedSpec A)) :=
      subroutine_ok_mono hRemIk (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
        dsimp only [StoreKit.withLsRoCl] at hq
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
    have hwp_pre : SepWP (lsProg_463 H) ((blkPl_463).base + 8136#64) s
        (memRegion (sp + 0x490#64) 0x14 ∗
          ((sp + 0x4b0#64) ↦₆₄ okTagVec) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
          ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
          memRegion (sp + 0x4d0#64) 16 ∗
          memRegion (sp + 0x290#64) 24 ∗
          ((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
          vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
          memRegion (sp + 0x5f0#64) 34 ∗
          memRegion (sp + 0xca0#64) 32 ∗
          FromRecordCallees.lsLogOff ∗
          stackAt sp Getters.remoteIdentityKeyStack)
        (fun sm Pm =>
          (∃ remBs : List (BitVec 8),
            remBs.length = 32 ∧
            (∀ ik, st'.remoteIdentity = some ik → remBs = ik.publicKey.bytes.toList) ∧
            (Pm ⊢ memRegion (sp + 0x490#64) 0x14 ∗
              memRegion (sp + 0x4b0#64) 0x30 ∗
              memRegion (sp + 0x5f0#64) 34 ∗
              (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
                ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
              (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
                vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
              ((sp + 0xca0#64) ↦ₛ remBs) ∗
              FromRecordCallees.lsLogOff ∗
              stackAt sp Getters.remoteIdentityKeyStack)) ∧
          sm.sp = s.sp ∧ sm.spAligned = true ∧ sm.trace = s.trace ∧
          sm.readReg64 .x29 = s0.sp - 96#64 ∧ sm.readReg64 .x27 = x.ret ∧
          sm.readReg64 .x26 = sp + 0xa0#64 ∧ sm.readReg64 .x22 = sp + 0x294#64 ∧
          sm.readReg64 .x8 = (remoteIdentityTag st'.remoteIdentity).zeroExtend 64 ∧
          calleeSavedVRegs sm = calleeSavedVRegs s0) := by
      dsimp only [lsProg_463, FromRecordCallees.lsLogOff] at hpc hrem_call ⊢
      wp_conv_pre => rw [scratch20_split sp, slot290_split sp, slotca0_split sp]
      dsimp only [sp]
      wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      repeat' (apply SepWP.exists_elim; intro _)
      have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
      dsimp only [okTagVec] at hx28
      apply StoreKit.sepWP_seq_lscro hcrl (mid := (blkPl_463).base + 8096#64)
      wp_steps
      refine SepWP.done rfl (by wp_norm_lhs) fun ⟨hcl_call, hro_call⟩ => ?_
      wp_call hrem_call
        (Getters.RemoteIdentityKeyGhost.mk (s0.sp - 0xee0#64 + 0x138#64)
          G'.remoteIk st'.remoteIdentity (s0.sp - 0xee0#64 + 0x5f0#64))
      have hfold_rem := remoteIdentityOkAt_unified (s0.sp - 0xee0#64 + 0x5f0#64) st'.remoteIdentity
      simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hfold_rem
      refine SepWP.fold hfold_rem (by sep_focus) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine SepWP.exists_elim fun remBs => ?_
      refine SepWP.pure_elim fun ⟨hrem_len, hrem_eq⟩ => ?_
      obtain ⟨k0, k1, k2, k3, _hk_bs, hk_pts⟩ := exists_unpack64_of_length_32 hrem_len
      wp_conv_pre => rw [hk_pts (s0.sp - 2286#64)]
      wp_simp_pre [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
      wp_steps
      have hf1 := scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2
      have hf2 := slot4b0_ok_fold_memRegion (s0.sp - 0xee0#64) w21 w0 w1 w2
      have hf3 := slot5f0_fold_memRegion (s0.sp - 0xee0#64) 0#8 (remoteIdentityTag st'.remoteIdentity) k0 k1 k2 k3
      have hf4 :
          (((s0.sp - 0xee0#64 + 0xca0#64) ↦₆₄ k0) ∗
            ((s0.sp - 0xee0#64 + 0xca8#64) ↦₆₄ k1) ∗
            ((s0.sp - 0xee0#64 + 0xcb0#64) ↦₆₄ k2) ∗
            ((s0.sp - 0xee0#64 + 0xcb8#64) ↦₆₄ k3)) ⊢
          ((s0.sp - 0xee0#64 + 0xca0#64) ↦ₛ remBs) := by
        rw [hk_pts (s0.sp - 0xee0#64 + 0xca0#64)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        exact Entails.refl _
      simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub] at hf1 hf2 hf3 hf4
      apply SepWP.fold hf1 (by sep_focus)
      apply SepWP.fold hf2 (by sep_focus)
      apply SepWP.fold hf3 (by sep_focus)
      apply SepWP.fold hf4 (by sep_focus)
      apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
      refine ⟨⟨remBs, hrem_len, hrem_eq, ?_⟩,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]; exact hal0,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, hcs_sf, hx29],
        by simp only [wp_norm, arm64_norm, h_8, hx27],
        by simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, wp_norm, arm64_norm, *],
        by simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub, wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
      rw [hsp]
      simp (config := { decide := true }) only [bv_sub_add_lit, Nat.reduceSub]
      exact Entails.of_eq (by ac_rfl)
    obtain ⟨sm, hsteps1, ⟨hpc_sm, hrun_sm, Pm, hmf,
      ⟨remBs, _hrem_len, hrem_eq, hent_pm⟩,
      hsp_sm, hal_sm, htr_sm, hx29_sm, hx27_sm, hx26_sm, hx22_sm, hx8_sm, hvregs_sm⟩ | ⟨_, _hoom⟩⟩ :=
      hwp_pre.elim hmem_act hL
    rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
    clear hmem_act hwp_pre
    have hL_sm := hsteps1.codeLoaded hL
    have hcrl_sm : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem := hcrl.of_keepsFrozen hsteps1.keepsFrozen
    have hmf1 := Satisfies.mono (Entails.trans (sepConj_mono_left hent_pm)
      (Entails.of_eq (emp_sepConj _).symm)) hmf
    clear hmf hent_pm
    cases hrem_opt : st'.remoteIdentity with
    | some k =>
      rw [hrem_opt] at hx8_sm
      dsimp only [remoteIdentityTag] at hx8_sm
      simp only [wp_norm, arm64_norm] at hx29_sm hx27_sm hx26_sm hx22_sm hx8_sm
      have hwp_some : SepWP (lsProg_463 H) keyReadyPCPlaced sm emp
          (fun sf Pf =>
            (Pf ⊢ emp) ∧
            sf.sp = sm.sp ∧ sf.spAligned = true ∧ sf.trace = sm.trace ∧
            sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
            sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x22 = sp + 0x294#64 ∧
            calleeSavedVRegs sf = calleeSavedVRegs s0) := by
        unfold keyReadyPCPlaced
        dsimp only [lsProg_463] at hpc_sm ⊢
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        exact ⟨Entails.refl _, rfl, hal_sm, rfl,
          by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, hvregs_sm⟩
      obtain ⟨sf, hsteps2, ⟨hpc_sf, hrun_sf, Pf, hmf2, hent_pf,
        hsp_sf, hal_sf, htr_sf, hx29_sf, hx27_sf, hx26_sf, hx22_sf, hvregs_sf⟩ | ⟨_, _hoom⟩⟩ :=
        hwp_some.elim hmf1 hL_sm
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      clear hmf1 hwp_some
      have hcrl_sf : StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem := hcrl_sm.of_keepsFrozen hsteps2.keepsFrozen
      have hmf3 := Satisfies.mono (sepConj_mono_left hent_pf) hmf2
      clear hmf2 hent_pf
      rw [emp_sepConj] at hmf3
      refine ⟨sf, hsteps1.trans hsteps2, Or.inl (Or.inl ?_)⟩
      let ses' : Session (List (BitVec 8)) :=
        { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
      let rec' : SessionRecord (List (BitVec 8)) := { currentSession := some ses' }
      have hdec_rec : decryptRecord C S uuidTryParse x rec_ = .ok (pt, rec') :=
        decryptRecord_of_region_ok C S x prevPtr G ses rec_ pt st' hcur hmod_rg
      have hremBs_eq : remBs = k.publicKey.bytes.toList := hrem_eq k hrem_opt
      refine ⟨hpc_sf,
        ⟨hrun_sf, hsp_sf.trans (hsp_sm.trans hsp), hal0, hal_sf, hx29_sf, hx27_sf, hcrl_sf, hvregs_sf⟩,
        hx26_sf, hx22_sf, rec_, rec', pt, ses', k,
        hload, hscope, hdec_rec, rfl, hrem_opt,
        htr_sf.trans (htr_sm.trans htrace), ?_⟩
      have hbrec :
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            sessionStateAt A (sp + 0x138#64) G' st' ⊢
          ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec' := by
        have hb := MessageDecrypt.Pf.RecordJoin.recordJoin_ok A (sp + 0x120#64) prevCap prevPtr G G' ses st' hw0 hrel
        simp only [BitVec.add_assoc, BitVec.reduceAdd] at hb
        exact hb
      have h300_join :
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
            memRegion (sp + 0x612#64) 0x68e =
          memRegion (sp + 0x300#64) 0x9a0 := by
        rw [memRegion_split (sp + 0x300#64) 0x190 0x810 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64) 0x14 0x7fc (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64) 0xc 0x7f0 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64) 0x30 0x7c0 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64 + 0x30#64) 0x110 0x6b0 (by decide),
            memRegion_split (sp + 0x300#64 + 0x190#64 + 0x14#64 + 0xc#64 + 0x30#64 + 0x110#64) 34 0x68e (by decide)]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
      have hwsEnv_eq :
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
            protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
            ((memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack) ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
            A.pool =
          wsEnvPlaced A x sp := by
        unfold wsEnvPlaced
        rw [← hstk_split, stackAt_root_join_wsCallee sp]
      have hcomb :
          (memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x5f0#64) 34 ∗
            (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
              ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
            (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
              vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
            ((sp + 0xca0#64) ↦ₛ remBs) ∗
            FromRecordCallees.lsLogOff ∗
            stackAt sp Getters.remoteIdentityKeyStack) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ∗
            memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
            memRegion (sp + 0xcc0#64) 0x140 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗
            memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
            wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ R') ⊢
          wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
            (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
            vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
            memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
            memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := by
        rw [hdraws, hremBs_eq]
        have hreord_lhs :
            (memRegion (sp + 0x490#64) 0x14 ∗
              memRegion (sp + 0x4b0#64) 0x30 ∗
              memRegion (sp + 0x5f0#64) 34 ∗
              (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
                ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
              (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
                vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
              ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
              FromRecordCallees.lsLogOff ∗
              stackAt sp Getters.remoteIdentityKeyStack) ∗
            (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
              ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
              sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
              CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ∗
              memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
              memRegion (sp + 0xcc0#64) 0x140 ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageAt A x.msgG x.msgA x.msg ∗
              cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗
              memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
              wsFixedVPlaced kit ikit x s0 sp ∗
              ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
              memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
              memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
              memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
              memRegion x.ret 48 ∗ R') =
            ((((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
                ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
                (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
                  vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64) ∗
                  sessionStateRemExposedAt A (sp + 0x138#64) G' st')) ∗
              (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
                ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2) ∗
                CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt) ∗
              (wsFixedVPlaced kit ikit x s0 sp ∗
                (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
                  protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗
                  ((memRegion (sp - 262144#64) 262000 ∗ stackAt sp Getters.remoteIdentityKeyStack) ∗
                    memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack)) ∗
                  A.pool) ∗
                wsMsgCells x sp ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
                memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
                (memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x490#64) 0x14 ∗
                  memRegion (sp + 0x4a4#64) 0xc ∗ memRegion (sp + 0x4b0#64) 0x30 ∗
                  memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x5f0#64) 34 ∗
                  memRegion (sp + 0x612#64) 0x68e) ∗
                memRegion (sp + 0xcc0#64) 0x140 ∗ memRegion x.ret 48 ∗
                cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗ R')) := by
          ac_rfl
        rw [hreord_lhs, ← sessionStateAt_expose_rem A (sp + 0x138#64) G' st',
            hwsEnv_eq, h300_join]
        have hvec290 :
            ((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
              ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2) ∗
              CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ⊢
            vecU8 A (sp + 0x290#64) pt := by
          have hv := hvec_pt (sp + 0x290#64)
          simp only [BitVec.add_assoc, BitVec.reduceAdd] at hv
          exact hv
        refine Entails.trans
          (sepConj_mono hbrec (sepConj_mono_left hvec290)) ?_
        exact Entails.of_eq (by ac_rfl)
      simpa only [R', sepConj_assoc] using Satisfies.mono hcomb hmf3
    | none =>
      rw [hrem_opt] at hx8_sm
      dsimp only [remoteIdentityTag] at hx8_sm
      simp only [wp_norm, arm64_norm] at hx8_sm
      have hwp_none : SepWP (lsProg_463 H) (lsρ lsExpectFailedSym) sm emp
          (fun sc Pc => (Pc ⊢ emp) ∧ sc.trace = sm.trace) := by
        dsimp only [lsProg_463] at hpc_sm ⊢
        wp_steps
        apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        exact ⟨Entails.refl _, rfl⟩
      obtain ⟨sc, hsteps2, ⟨hpc_sc, hrun_sc, Pc, hmf2, hent_pc, htr_sc⟩ | ⟨_, _hoom⟩⟩ :=
        hwp_none.elim hmf1 hL_sm
      rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
      clear hmf1 hwp_none
      have hmf3 := Satisfies.mono (sepConj_mono_left hent_pc) hmf2
      clear hmf2 hent_pc
      rw [emp_sepConj] at hmf3
      have hext : (lsProg_463 H).externAt? sc.pc = some Rust.panicked := by
        rw [hpc_sc]
        exact panic_at_expect_failed_msgDecrypt_placed hhyps.hooks.expectFailed
      have hstep_pan : Step (lsProg_463 H) sc (Rust.panicked sc) :=
        Step.extern hrun_sc hext (Memory.KeepsFrozen.refl _) rfl
      refine ⟨Rust.panicked sc, hsteps1.trans (hsteps2.trans (Steps.step hstep_pan (Steps.refl _))),
        Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))⟩
      dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      have htr_pan : (Rust.panicked sc).trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession := by
        change sc.trace = _
        exact htr_sc.trans (htr_sm.trans htrace)
      have hload_pref :
          s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession <+: (Rust.panicked sc).trace := by
        rw [htr_pan]
      have hs0_pref : s0.trace <+: (Rust.panicked sc).trace :=
        (List.prefix_append s0.trace (kit.loadEvs encRecord x.rem.val ans.loadSession)).trans hload_pref
      have hmod_pan : (x.model C S uuidTryParse ans).1 = .error .panic :=
        model_panic_of_remoteIdentity_none C S x prevPtr G ses ans rec_ pt st'
          hload hcur hmod_rg hrem_opt
      refine ⟨⟨hs0_pref, Or.inr ⟨ans, hload ▸ hscope.2, hload_pref, Or.inl hmod_pan⟩⟩, ?_⟩
      change sc.mem ⊨ anyHeap ∗ R
      dsimp only [R'] at hmf3
      have hmf_r : sc.mem ⊨
          ((memRegion (sp + 0x490#64) 0x14 ∗
            memRegion (sp + 0x4b0#64) 0x30 ∗
            memRegion (sp + 0x5f0#64) 34 ∗
            (((sp + 0x290#64) ↦₃₂ w21) ∗ ((sp + 0x294#64) ↦₆₄ w0) ∗
              ((sp + 0x29c#64) ↦₆₄ w1) ∗ ((sp + 0x2a4#64) ↦₃₂ w2)) ∗
            (((sp + 0x138#64) ↦₆₄ G'.localIk.cap) ∗
              vecGhostAt A G'.remoteIk (sp + 0x138#64 + 0x18#64)) ∗
            ((sp + 0xca0#64) ↦ₛ remBs) ∗
            FromRecordCallees.lsLogOff ∗
            stackAt sp Getters.remoteIdentityKeyStack) ∗
          (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
            ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
            sessionStateRemExposedAt A (sp + 0x138#64) G' st' ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr pt ∗
            memRegion (sp + 0x4e0#64) 0x110 ∗ memRegion (sp + 0x612#64) 0x68e ∗
            memRegion (sp + 0xcc0#64) 0x140 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗
            cliTapeAfter ctl x.cur x.rest (x_rg.draws C) ∗
            memRegion (sp - 262144#64) 262000 ∗ A.pool ∗
            wsFixedVPlaced kit ikit x s0 sp ∗
            ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
            memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
            memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
            memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
            memRegion x.ret 48 ∗ decStoreExtraPlaced kit ikit st0 ist0 s0)) ∗ R :=
        Satisfies.mono (Entails.of_eq (by ac_rfl)) hmf3
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmf_r

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
