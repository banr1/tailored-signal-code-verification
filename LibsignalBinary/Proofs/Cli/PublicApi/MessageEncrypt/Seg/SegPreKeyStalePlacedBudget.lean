/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadCommonPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatch

/-!
# Budget-Threaded Relocatable `segPreKey` Stale Session Error Path (`+0x6fc..+0x7cc`)

Proves `segPreKey_stale_placed_ok` on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M`
and `[LibsignalPlacement]`, threading the `StringCloneEnv` budget into `env.tailWriteErr`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStalePlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt hiding otrEncryptPlacedSpec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommonPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] blkPl_198_ρ_lanon122

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem vecU8_580_unpack_buf (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 1408#64) bs ⊢
      ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
        ((sp + 0x580#64) ↦₆₄ cap) ∗ ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  have h1408 : sp + 1408#64 = sp + 0x580#64 := by bv_omega
  rw [h1408, CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.vecU8_eq_words3_sep_buf]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
    Entails.sepExists_right ptr (Entails.sepExists_right cap ?_)
  have ha1 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have ha2 : sp + 0x580#64 + 0x10#64 = sp + 0x590#64 := by bv_omega
  rw [ha1, ha2]
  exact Entails.refl _

set_option maxHeartbeats 800000 in
theorem segPreKey_stale_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  rcases hadd with ⟨hbud, hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  have hbud_stale : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs) :=
    hbud.narrow fun _ h => Or.inr ⟨items, hpk, Or.inl h⟩
  have hfit_clone : FitsEnv M lim st (StringCloneEnv x.rem.name) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_stale.1
  set sp := s0.sp - 0xbe0#64
  apply segExitBudget_trans
    (mid := fun sf =>
      ∃ st' cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv x st_init st'
          (preKeyErrAnswers r)
          (encEntryPlaced + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.val.name.length))
          (fun sp => dropRecordSlots A.repAlloc sp curScratch ⟨prevCap, prevPtr, some G⟩
            (takenRecord sess taken) (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, lsmpl.ρ lsMessageEncryptRodataSym, 15#64]) ∗
            (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗
              ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · unfold encEntryPlaced at hpc
    have hclone_call := stringClone_placed_ok_at_enc env.toEncEnvBudget
    clear env
    apply segExitBudget_of_sepWPp_lscro hcrl
      (target := (blkPl_464).base + 1132#64)
      (dur_mem_group hmem)
    dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, protocolAddressAt, lsLogOff_eq]
    rw [show vecAt (A.atState lim st s) = vecAt A.repAlloc from rfl,
        show sessionStateReprAt (A.atState lim st s) = sessionStateReprAt A.repAlloc from rfl,
        show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl,
        show vecGhostAt (A.atState lim st s) = vecGhostAt A.repAlloc from rfl,
        show (A.atState lim st s).pool = A.pool lim st s from rfl]
    refine rodata_message_encrypt_placed_sepWPp hcrl.2 ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A.repAlloc sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    dsimp only [lsProg_464, ite_true] at hclone_call ⊢
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 623)
    wp_steps_sync_pool (lsmpl.base 623)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcrl_call
    refine SepWPp.call_frame_rocl hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name, st))
      (by wp_norm_goal) (by wp_norm_goal)
      (by unfold State.spAligned at hspAl ⊢; wp_norm_goal; rw [← hsp]; exact hspAl)
      (show _ = (blkPl_464).base + 1948#64 by wp_norm_goal)
      hcrl_call
      rfl ⟨by wp_norm_goal, by wp_norm_goal, hfit_clone⟩
      (by dsimp only [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun _ _ hm => by
        dsimp only [stringCloneBudgetSpec, Spec.onPanic] at hm
        rw [sepConj_assoc] at hm
        exact (not_satisfies_false_sepConj hm).elim)
      fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
    dsimp only [stringCloneBudgetSpec]
    refine sepWPp_elim_ex fun evs_clone => ?_
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htr1, hevs_clone⟩ => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack_buf A.repAlloc sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    wp_steps_sync_pool ((blkPl_464).base + 1132#64)
    apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
    refine SepWP.fold (curScratch_stale_pack sp) (by sep_focus) ?_
    refine SepWP.fold (pollWith_9d0_pack sp cap ptr _ _ _ _ _ _) (by sep_focus) ?_
    have hsp1_pack :
        (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt s1.sp extHookStack) ⊢ stackAt sp encSubStack := by
      rw [hsp1, ← encSubStack_split_ext rfl]
      exact Entails.refl _
    refine SepWP.fold hsp1_pack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1 hmf
    have hfinal :
        kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    have hidfinal :
        ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    refine ⟨M.stepEvents evs_clone st, cap, ptr,
      (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, hbud_stale.advance hevs_clone, ?_⟩
    refine ⟨?_, ?_, ?_, hstack, ?_⟩
    · dsimp only [encEntryPlaced]; wp_norm_goal
    · dsimp only [encMidMetaPlaced, sp] at hsp1 hx19_1 hx29_1 hvregs_1 ⊢
      refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
        by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hcrl1, by wp_norm_goal⟩
    · dsimp only [tailRegs, AddrGhost.val, sp] at hx26_1 hx28_1 ⊢
      refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [preKey_encTail_mem_retag_eq (A' := A.atState lim (M.stepEvents evs_clone st) _)
        kit st0 ikit ist0 C ctl S x (preKeyErrAnswers r) _ R s0]
      dsimp only [encEntryPlaced, encStoreExtraPlaced,
        tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommonPlaced,
        protocolAddressAt, lsLogOff_eq, AddrGhost.val, sp]
        at hmf ⊢
      rw [hdraws, hfinal, hidfinal,
        show vecGhostAt (A.atState lim (M.stepEvents evs_clone st) _) = vecGhostAt A.repAlloc from rfl,
        show (A.atState lim (M.stepEvents evs_clone st) _).pool =
          A.pool lim (M.stepEvents evs_clone st) _ from rfl]
      arm64_sep_close
  · intro sf ⟨st', cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have hdev_word : CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.DevWord
        x.rem.val.device devWord := by
      refine ⟨(unpack64 devWord).tail, by rw [List.length_tail, unpack64_length], ?_⟩
      unfold unpack64
      dsimp only [List.tail_cons]
      rw [← BitVec.setWidth_eq_extractLsb' (by decide), hdev]
      rfl
    have hst :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.speStaged_sessionNotFound_devWord_placed
        A.repAlloc x.ret cap ptr devWord (lsmpl.ρ lsMessageEncryptRodataSym) x.rem.val hdev_word
    exact env.tailDropRecord x st_init st' R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.val.name.length) devWord
      (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
      (vecU8Buf A.repAlloc cap ptr x.rem.val.name ∗
        ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr)) hm hst htail

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStalePlacedBudget
