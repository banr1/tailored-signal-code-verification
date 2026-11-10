/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Budget-Threaded Relocatable `segPreKey` Registration IDs, Kyber Closure, and Assembly

Proves `segPreKey_regId_kyber_placed_ok` (`+0x6fc..+0x8b4`) and the full `segPreKey_placed_okV`
segment specification on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget

open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey hiding
  segPreKey_encrypt_call_placed_ok segPreKey_encrypt_err_placed_ok segPreKey_buildMessage_placed_ok
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
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyStalePlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefsPlacedBudget
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailPlacedBudget

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

private theorem kyberMapBudgetSpec_pre_eq {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (xc : KyberMapCall) (st : M.σ) (sm : State) :
    (kyberMapBudgetSpec M A lim).pre (xc, st) sm =
      ⌜FitsEnv M lim st (KyberOptEnv (xc.kp.map (·.ciphertext))) ∧
        (sm.readReg64 .x0 = xc.out ∧ sm.readReg64 .x1 = xc.arg)⌝ ∗
      (kyberArgAt xc ∗ memRegion xc.out 24 ∗ A.pool lim st sm ∗
        stackAt sm.sp (allocHookStack + 0x40)) := by
  dsimp only [kyberMapBudgetSpec, kyberMapSpec]
  apply ProofLib.sepProp_eq_of_entails
  · exact Entails.pure_left fun h1 => Entails.pure_left fun h2 => Entails.pure_right ⟨h1, h2⟩ (Entails.refl _)
  · exact Entails.pure_left fun ⟨h1, h2⟩ => Entails.pure_right h1 (Entails.pure_right h2 (Entails.refl _))

/-! ## 1. E6b + Kyber Closure (`+0x6fc..+0x8b4`) on Block `464` (`lsProg_464 Hk`) -/

set_option maxHeartbeats 800000 in
theorem segPreKey_regId_kyber_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = false)
    (hadd : StalenessAddStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      encRecord x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk x st_init R s0 s
      (fun sf => ∃ st',
        PreKeyEncryptStateBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
          encRecord x st_init st' r sess otr taken pqCap pqPtr k items R s0 sf) := by
  rcases hadd with ⟨hbud, hts, hexp, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, hx23, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  dsimp only [retagSessionStore, retagIdentityStore] at htr hmem
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have hky_bound := (env.toEncEnvBudget.scopeIn r hscope sess hcur).2.2.2
  have hbud_ky : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (SeqEnv (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext)))
        (FromPreKeyEncEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k items)) :=
    hbud.narrow fun _ h => Or.inr ⟨items, hpk, Or.inr h⟩
  have hfit_ky : FitsEnv M lim st (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext))) :=
    FitsEnv.mono (fun _ h => Or.inl h) hbud_ky.1
  set sp := s0.sp - 0xbe0#64
  unfold encEntryPlaced at hpc
  have hkyber_call := env.calleesFull.kyber
  clear env
  apply segExitBudget_of_sepWPp_lscro hcrl
    (target := (blkPl_464).base + 2228#64)
    (dur_mem_group hmem)
  rw [show vecAt (A.atState lim st s) = vecAt A.repAlloc from rfl,
      show sessionStateReprAt (A.atState lim st s) = sessionStateReprAt A.repAlloc from rfl,
      show otrAt (A.atState lim st s) = otrAt A.repAlloc from rfl]
  refine SepWPp.fold (sessionAt_regId_unpack A.repAlloc sp G sess taken) (by sep_focus) ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hkyRel => ?_
  refine SepWPp.fold
    (preKeyScratch_regId_unpack sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
    (by sep_focus) ?_
  refine sepWPp_elim_ex fun w14 => ?_
  refine SepWPp.fold (pollWithBaseKey_regId_unpack sp items) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w590 => sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq]
  rw [show protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc from rfl,
      show (A.atState lim st s).pool = A.pool lim st s from rfl,
      encSubStack_split_kyber hsp]
  dsimp only [lsProg_464, ite_true] at hkyber_call ⊢
  cases hky : sess.pendingKyberPreKey with
  | none =>
    cases hGky : G.kyber with
    | some g =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | none =>
      rw [hky] at hbud_ky hfit_ky
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      subst hkySlice
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps_sync_pool (lsmpl.base 430)
      refine SepWP.fold (kyberArgAt_none_pack sp w580 w590) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      let call : KyberMapCall := ⟨sp + 0x8a0#64, sp + 0x580#64, 0#64, none⟩
      have hfit' : FitsEnv M lim st (KyberOptEnv (call.kp.map (·.ciphertext))) := by
        simpa [call, hky] using hfit_ky
      refine SepWPp.call_frame_rocl hkyber_call
        (x := (call, st))
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        (kyberMapBudgetSpec_pre_eq A lim call st _)
        ⟨hfit', by dsimp only [call]; wp_norm_goal, by dsimp only [call]; wp_norm_goal⟩
        (by dsimp [call, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun _ _ hm => by
          dsimp only [kyberMapBudgetSpec, Spec.onPanic] at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapBudgetSpec]
      refine SepWPp.fold (Entails.refl (∃∗ evs_ky : List AllocEvent, _)) (by sep_focus) ?_
      refine sepWPp_elim_ex fun evs_ky => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hevs_ky => ?_
      dsimp only [kyberMapSpec, call]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      set st' := M.stepEvents evs_ky st
      have hbud_enc := hbud_ky.advance (by simpa [call, hky] using hevs_ky)
      rw [show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold (kyberPost_unpack A.repAlloc (sp + 0x8a0#64) (sp + 0x580#64) 0#64 none) (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_none_to_memRegion sp) (by sep_focus) ?_
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      rw [← hGky]
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A.repAlloc sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp kyLen _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold (pollPreKeyEncrypt_pack A.repAlloc sp bp items sess.pendingKyberPreKey none (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      refine ⟨st', hbud_enc, ?_⟩
      dsimp only [PreKeyEncryptState'Placed,
        preKeyEncryptScratch, preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced,
        encEntryPlaced, encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      rw [show (retagSessionStore (A' := A.atState lim st' s1) kit).ss_vt = kit.ss_vt from rfl,
          show (retagIdentityStore (A' := A.atState lim st' s1) ikit).id_vt = ikit.id_vt from rfl,
          show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st' s1) kit) st0
            (retagIdentityStore (A' := A.atState lim st' s1) ikit) ist0 x s0 =
            encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
          show sessionRecordAt (A.atState lim st' s1) = sessionRecordAt A.repAlloc from rfl,
          show otrAt (A.atState lim st' s1) = otrAt A.repAlloc from rfl,
          show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' s1) = protocolAddressAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      arm64_sep_close
  | some ky =>
    cases hGky : G.kyber with
    | none =>
      rw [hGky, hky] at hkyRel
      exact False.elim hkyRel
    | some g =>
      rw [hky] at hbud_ky hfit_ky
      rw [hGky, hky] at hkyRel
      dsimp only [KyberRel] at hkyRel
      rcases hkyRel with ⟨hkyBytes, _⟩
      rw [hGky] at hkySlice
      dsimp only [unackKyberSliceProp] at hkySlice
      rcases hkySlice with ⟨rfl, rfl⟩
      have hkyId_eq : kyIdVal = ky.preKeyId := hkyIdVal ky.preKeyId (by simp [hky])
      subst hkyId_eq
      have hct_lt : ky.ciphertext.length < 2 ^ 32 := hky_bound ky hky
      rw [hkyBytes]
      refine SepWPp.fold (optTailVecAt_borrow A.repAlloc (sp + 0x250#64) g) (by sep_focus) ?_
      rw [sepConj_assoc, sepConj_assoc]
      refine SepWPp.pure_elim fun hptr => ?_
      rw [hkyBytes]
      dsimp only [Option.map, Option.isSome]
      have hptr_beq : (g.vec.ptr == 0#64) = false := _root_.beq_false_of_ne hptr
      apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 430)
      wp_steps_sync_pool (lsmpl.base 430)
      refine SepWP.fold (kyberArgAt_some_pack sp g.vec.ptr ky hptr hct_lt) (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
      intro hcrl_call
      let call : KyberMapCall := ⟨sp + 0x8a0#64, sp + 0x580#64, g.vec.ptr,
        some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)⟩
      have hfit' : FitsEnv M lim st (KyberOptEnv (call.kp.map (·.ciphertext))) := by
        simpa [call, hky] using hfit_ky
      refine SepWPp.call_frame_rocl hkyber_call
        (x := (call, st))
        (by wp_norm_goal) (by wp_norm_goal)
        (by dsimp [State.spAligned, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; exact hspAl)
        (show _ = (blkPl_464).base + 2228#64 by wp_norm_goal)
        hcrl_call
        (kyberMapBudgetSpec_pre_eq A lim call st _)
        ⟨hfit', by dsimp only [call]; wp_norm_goal, by dsimp only [call]; wp_norm_goal⟩
        (by dsimp [call, State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
        (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
        (fun _ _ hm => by
          dsimp only [kyberMapBudgetSpec, Spec.onPanic] at hm
          rw [sepConj_assoc] at hm
          exact (not_satisfies_false_sepConj hm).elim)
        fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
      dsimp only [kyberMapBudgetSpec]
      refine SepWPp.fold (Entails.refl (∃∗ evs_ky : List AllocEvent, _)) (by sep_focus) ?_
      refine sepWPp_elim_ex fun evs_ky => ?_
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun hevs_ky => ?_
      dsimp only [kyberMapSpec, call]
      rw [sepConj_assoc]
      refine SepWPp.pure_elim fun htr1 => ?_
      set st' := M.stepEvents evs_ky st
      have hbud_enc := hbud_ky.advance (by simpa [call, hky] using hevs_ky)
      rw [show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
      refine SepWPp.fold
        (kyberPost_unpack A.repAlloc (sp + 0x8a0#64) (sp + 0x580#64) g.vec.ptr
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)))
        (by sep_focus) ?_
      refine sepWPp_elim_ex fun bp => ?_
      refine SepWPp.fold (kyberArgAt_some_unpack sp g.vec.ptr ky) (by sep_focus) ?_
      rw [← hkyBytes]
      refine SepWPp.fold (optTailVecAt_unborrow A.repAlloc (sp + 0x250#64) g) (by sep_focus) ?_
      rw [hkyBytes, ← hGky]
      rcases hcs1 with ⟨hx19_1, hx20_1, _hx21_1, hx22_1, _hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
      simp only [wp_norm, arm64_norm]
        at hx19_1 hx20_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
      rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
      rw [hx25] at hx25_1; rw [hx26] at hx26_1
      rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
      have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
        change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
      have hsp1_al : s1.spAligned = true := by
        unfold State.spAligned at hspAl ⊢; rwa [hsp1]
      rw [hsp] at hsp1
      rw [htr] at htr1
      apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
      refine SepWP.fold (sessionAt_regId_pack A.repAlloc sp G sess taken) (by sep_focus) ?_
      refine SepWP.fold (takenRecord_sessionRecordAt_pack_exact A.repAlloc sp prevCap prevPtr G sess taken)
        (by sep_focus) ?_
      refine SepWP.fold (preKeyEncryptScratch_pack sp _ _ sess.localRegistrationId items.signedPreKeyId pkVal)
        (by sep_focus) ?_
      refine SepWP.fold
        (pollPreKeyEncrypt_pack A.repAlloc sp bp items sess.pendingKyberPreKey
          (some (⟨ky.preKeyId, ky.ciphertext⟩ : KyberPayload)) (by simp [hky]))
        (by sep_focus) ?_
      have hsp1_pack :
          (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - (allocHookStack + 0x40)) ∗
            stackAt s1.sp (allocHookStack + 0x40)) ⊢ stackAt sp encSubStack := by
        rw [hsp1, ← encSubStack_split_kyber rfl]
        exact Entails.refl _
      refine SepWP.fold hsp1_pack (by sep_focus) ?_
      apply SepWP.done hpc1 hstat1
      intro hcrl_f hmf
      refine ⟨st', hbud_enc, ?_⟩
      dsimp only [PreKeyEncryptState'Placed,
        preKeyEncryptScratch, preKeyEncryptScratch', pollPreKeyEncrypt, pollE6c', encMidMetaPlaced,
        encEntryPlaced, encSpillsAt, encSpillsAtV, encCommonPlaced, nowAt, lsLogOff_eq, sp]
        at hsp1 hx19_1 hx20_1 hx22_1 hx24_1' hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
      refine ⟨prevCap, prevPtr, G, ts, expiry, pkVal, bp, hts, hexp, hlt, hpkVal,
        hpc1,
        ⟨hstat1, hsp1, hsp0Al, hsp1_al, hx29_1, hx19_1, hcrl_f, hvregs_1⟩,
        htr1, hx20_1, hx22_1, hx24_1', hx25_1, hx26_1, hx27_1, hx28_1,
        hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
      rw [show (retagSessionStore (A' := A.atState lim st' s1) kit).ss_vt = kit.ss_vt from rfl,
          show (retagIdentityStore (A' := A.atState lim st' s1) ikit).id_vt = ikit.id_vt from rfl,
          show encStoreExtraPlaced (retagSessionStore (A' := A.atState lim st' s1) kit) st0
            (retagIdentityStore (A' := A.atState lim st' s1) ikit) ist0 x s0 =
            encStoreExtraPlaced kit st0 ikit ist0 x s0 from rfl,
          show sessionRecordAt (A.atState lim st' s1) = sessionRecordAt A.repAlloc from rfl,
          show otrAt (A.atState lim st' s1) = otrAt A.repAlloc from rfl,
          show optKyberAt (A.atState lim st' s1) = optKyberAt A.repAlloc from rfl,
          show protocolAddressAt (A.atState lim st' s1) = protocolAddressAt A.repAlloc from rfl,
          show (A.atState lim st' s1).pool = A.pool lim st' s1 from rfl]
      arm64_sep_close

/-! ## 2. Top-Level `segPreKey_placed_okV` Composition -/

theorem segPreKey_placed_okV [LibsignalPlacement] {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegPreKeySpecVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk := by
  intro env x st_init st r sess otr taken pqCap pqPtr k R s0 s his hkey
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.2.1
  have hscope : kit.ScopeAt Scope st0 x.rem.val r := hkey.2.2.1
  have hfrom := hkey.2.2.2.1
  have hrem := hkey.2.2.2.2.1
  refine segExitBudget_trans
    (segPreKey_unackItems_to_dur_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items R s0 s hpk hkey) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine segExitBudget_trans
    (segPreKey_staleness_to_add_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R s0 s1
      hcur hscope hfrom hrem hpk hdur) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact SegExitBudget.of_false
      (segPreKey_stale_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
        hcur hscope hfrom hrem hpk hlt hadd)
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine segExitBudget_trans
      (segPreKey_regId_kyber_placed_ok env x st_init st r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s2
        hcur hscope hpk hlt_f hadd) ?_
    rintro s3 ⟨st3, he6c⟩
    exact segPreKey_tail_placed_ok env x st_init st3 r sess otr taken pqCap pqPtr k items R s0 s3
      hcur hscope hfrom hrem hpk he6c

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlacedBudget
