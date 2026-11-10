/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostNone
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone

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
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone hiding segPostNoneVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


theorem segPostNoneVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegPostNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro _hH x ans R s0 s hPN hL
  obtain ⟨hpc, ⟨hrun, hsp, hal0, hal, hx29, hx27, hcrl, hvregs⟩,
    hx26, hx28, rec, prevCap, prevPtr, hload, hscope, hcur, htrace, hmem⟩ := hPN
  have hpc' : s.pc = (blkPl_463).base + 8016#64 := hpc
  simp only [wp_norm, arm64_norm] at hx29 hx27 hx26 hx28
  have ⟨hmod, hdraws⟩ := model_of_load_current_none C S x ans rec hload hcur
  let sp := s0.sp - 0xee0#64
  let R' := decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R
  have hmem_grp :
      s.mem ⊨
        (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
          ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
        (recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
          (memRegion (sp + 0x4e0#64) 0x920 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
            stackAt sp rootStack ∗ A.pool ∗ wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ R')) := by
    dsimp only [sp, R']
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  obtain ⟨pad, cap, ptr, hpad_len, hmem⟩ := recordResultAt_decryptionFailed_sat hmem_grp
  clear hmem_grp
  let w21 := cap.extractLsb' 0 32
  let bs := unpack32 (cap.extractLsb' 32 32) ++ unpack64 ptr ++
    unpack64 (BitVec.ofNat 64 decryptionFailedStr.length) ++ [msgTypeByte .whisper] ++ pad
  have hbs_len : bs.length = 36 := by
    simp [bs, hpad_len]
  obtain ⟨w0, w1, w2, w3, w4, hbs_eq⟩ := exists_split_36_regionErr hbs_len
  have hslot_orig :
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b0#64 + 8#64) ↦₆₄ cap) ∗
        ((sp + 0x4b0#64 + 8#64 + 8#64) ↦₆₄ ptr) ∗
        ((sp + 0x4b0#64 + 8#64 + 16#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
        ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
        ((sp + 0x4b0#64 + 33#64) ↦ₛ pad) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) =
      (((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗
        ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) := by
    have h8 := pointsTo64_split32 (sp + 0x4b0#64 + 8#64) cap
    have h36 := decryptionFailed_slot_36_eq (sp + 0x4b0#64) cap ptr .whisper pad
    have h36_te := pointsToBytes_36_regionErr_eq (sp + 0x4b0#64 + 12#64) w0 w1 w2 w3 w4
    dsimp only [bs] at hbs_eq
    rw [hbs_eq, h36_te] at h36
    rw [h8]
    simp only [w21, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h36 ⊢
    have h36' := congrArg (· ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) h36.symm
    simp only [sepConj_assoc] at h36'
    rw [h36']
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
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24) ∗
      (memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
        ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
        memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
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
    rw [hws_eq, hslot_orig, h300_split, h4e0_split] at hmem
    dsimp only [sp] at hmem ⊢
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hmem
  clear hmem
  have hwp : SepWP (lsProg_463 H) (errJoinPCPlaced false) s
      (memRegion (sp + 0x490#64) 0x14 ∗
        ((sp + 0x4b0#64) ↦₆₄ speWord 24) ∗ ((sp + 0x4b8#64) ↦₃₂ w21) ∗
        ((sp + 0x4bc#64) ↦₆₄ w0) ∗ ((sp + 0x4c4#64) ↦₆₄ w1) ∗ ((sp + 0x4cc#64) ↦₃₂ w2) ∗
        ((sp + 0x4d0#64) ↦₆₄ w3) ∗ ((sp + 0x4d8#64) ↦₆₄ w4) ∗
        memRegion (sp + 0x580#64) 0x24)
      (fun sf Pf =>
        (Pf ⊢ memRegion (sp + 0x490#64) 0x14 ∗
          memRegion (sp + 0x4b0#64) 0x30 ∗
          ((sp + 0x580#64) ↦ₛ bs)) ∧
        sf.sp = s.sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧ sf.readReg64 .x27 = x.ret ∧
        sf.readReg64 .x26 = sp + 0xa0#64 ∧ sf.readReg64 .x28 = speWord 24 ∧
        resWord1 (sf.readReg64 .x20) (sf.readReg64 .x21) = w21 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0) := by
    unfold errJoinPCPlaced
    rw [ite_eq_right_iff.mpr nofun]
    dsimp only [lsProg_463]
    wp_conv_pre => rw [scratch20_split sp, dst36_split sp]
    dsimp only [sp]
    wp_simp_pre [BitVec.add_assoc, BitVec.reduceAdd,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    repeat' (apply SepWP.exists_elim; intro _)
    have hal_s : (s.sp &&& 15#64 == 0#64) = true := hal
    dsimp only [recordResultTag, speWord] at hx28
    wp_steps
    apply SepWP.fold (scratch20_fold (s0.sp - 0xee0#64) w0 w1 w2) (by sep_focus)
    apply SepWP.fold (slot48_fold_memRegion (s0.sp - 0xee0#64) (speWord 24) w21 w0 w1 w2 w3 w4) (by sep_focus)
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
  refine ⟨sf, hsteps, Or.inl ?_⟩
  have hmf1 := Satisfies.mono (sepConj_mono_left hent_pf) hmf
  clear hmf hent_pf
  refine ⟨hpc_sf, ⟨hrun_sf, hsp_sf.trans hsp, hal0, hal_sf, hx29_sf, hx27_sf, hcrl_sf, hvregs_sf⟩,
    hx26_sf, ?_, ans, none, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hx28_sf]; decide
  · intro h; rw [hmod] at h; cases h
  · intro p h; rw [hmod] at h; cases h
  · intro r hr; rw [hload] at hr; cases hr; exact hscope
  · rw [hmod]; exact ⟨hload ▸ hscope.2, trivial⟩
  · rw [hmod]; trivial
  · rw [htr_sf, htrace, hmod]; simp
  · have hstaged :
        ((sp + 0x580#64) ↦ₛ bs) ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ⊢
          StagedRes A (sf.readReg64 .x28) (sf.readReg64 .x20) (sf.readReg64 .x21) (sp + 0x580#64)
            (x.model C S uuidTryParse ans).1 := by
      unfold StagedRes
      refine Entails.sepExists_right bs
        (Entails.sepExists_right (CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ?_)
      refine Entails.pure_right ⟨hbs_len, fun r => ?_⟩ (Entails.refl _)
      rw [hmod, hx28_sf, hres_w1]
      dsimp only [apiDecResultAt, recordResultAt]
      rw [vecU8_eq_exists_buf A (r + 8#64) decryptionFailedStr]
      have h36 := decryptionFailed_slot_36_eq r cap ptr .whisper pad
      have h8 := pointsTo64_split32 (r + 8#64) cap
      have hpad_mem : ((r + 33#64) ↦ₛ pad) ⊢ memRegion (r + 33#64) 15 := by
        have h := pointsToBytes_entails_memRegion (r + 33#64) pad
        rwa [hpad_len] at h
      dsimp only [bs]
      rw [h36]
      refine Entails.trans ?_
        (sepConj_mono_right
          (sepConj_mono_left
            (Entails.sepExists_right cap
              (Entails.sepExists_right ptr (Entails.refl _)))))
      rw [h8]
      simp only [w21, BitVec.add_assoc, BitVec.reduceAdd]
      have hreord_r :
          (r ↦₆₄ speWord 24) ∗ ((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
            (((r + 12#64) ↦₃₂ cap.extractLsb' 32 32) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              ((r + 32#64) ↦₈ msgTypeByte .whisper) ∗
              ((r + 33#64) ↦ₛ pad)) ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr =
          ((r ↦₆₄ speWord 24) ∗
            ((((r + 8#64) ↦₃₂ cap.extractLsb' 0 32) ∗ ((r + 12#64) ↦₃₂ cap.extractLsb' 32 32)) ∗
              ((r + 16#64) ↦₆₄ ptr) ∗
              ((r + 24#64) ↦₆₄ BitVec.ofNat 64 decryptionFailedStr.length) ∗
              CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ∗
            ((r + 32#64) ↦₈ msgTypeByte .whisper)) ∗
          ((r + 33#64) ↦ₛ pad) := by
        ac_rfl
      rw [hreord_r]
      refine Entails.trans (sepConj_mono_right hpad_mem) ?_
      exact Entails.of_eq (by ac_rfl)
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
          ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
          CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
          memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
          protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗ A.pool ∗
          wsFixedVPlaced kit ikit x s0 sp ∗
          ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
          memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
          memRegion (sp + 0x300#64) 0x190 ∗ memRegion (sp + 0x4a4#64) 0xc ∗
          memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
          memRegion x.ret 48 ∗ R') ⊢
        wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
          droppableRecordAt A (sp + 0x120#64) none ∗
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
            ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
            CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr ∗
            memRegion (sp + 0x4e0#64) 0xa0 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
            signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
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
              ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336) ∗
            (((sp + 0x580#64) ↦ₛ bs) ∗ CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.vecU8Buf A cap ptr decryptionFailedStr) ∗
            cliTapeAt ctl x.cur x.rest ∗
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
              memRegion (sp + 0x5a4#64) 0x85c ∗ memRegion x.ret 48 ∗ R')) := by
        ac_rfl
      rw [hreord_lhs, hwsEnv_eq, h300_join]
      refine Entails.trans
        (sepConj_mono (record_none_entails_droppable A sp prevCap prevPtr)
          (sepConj_mono hstaged
            (sepConj_mono_left (cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest)))) ?_
      exact Entails.of_eq (by ac_rfl)
    have hfin := Satisfies.mono hcomb hmf1
    rw [hmod] at hfin ⊢
    exact hfin


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone
