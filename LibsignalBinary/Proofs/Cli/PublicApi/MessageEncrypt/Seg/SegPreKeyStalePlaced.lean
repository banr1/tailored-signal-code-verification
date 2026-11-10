/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStalenessPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import all Init.Data.String.Defs

/-!
# Relocatable `segPreKey` Stale Session Error Path (`+0x6fc..+0x7cc`)

Proves `segPreKey_stale_placed_ok` on Block `464` (`lsProg_464 Hk`) under `[LibsignalPlacement]`,
handling the `expiry.lt x.now = true` branch into `tailWriteErr_placed_ok` at `+0x46c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm] blkPl_198_ρ_lanon122

private theorem lsLogOff_eq [LibsignalPlacement] :
    FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl

set_option maxHeartbeats 800000 in
theorem segPreKey_stale_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
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
    (hadd : StalenessAddStatePlaced kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) := by
  rcases hadd with ⟨hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hcrl, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  set sp := s0.sp - 0xbe0#64
  apply segExitPlaced_trans
    (mid := fun sf =>
      ∃ cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r)
          (encEntryPlaced + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length))
          (fun sp => dropRecordSlots A sp curScratch ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
            (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, lsmpl.ρ lsMessageEncryptRodataSym, 15#64]) ∗
            (vecU8Body A cap ptr x.rem.name.bytes ∗
              ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · unfold encEntryPlaced at hpc
    have hclone_call := stringClone_placed_ok_at_enc env
    clear env
    apply segExitPlaced_of_sepWPp_lscro hcrl
      (target := (blkPl_464).base + 0x46c#64)
      (dur_mem_group hmem)
    refine rodata_message_encrypt_placed_sepWPp hcrl.2 ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    dsimp only [encSpillsAt, encSpillsAtV, encCommonPlaced, protocolAddressAt, lsLogOff_eq]
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    dsimp only [lsProg_464, ite_true] at hclone_call ⊢
    apply StoreKit.sepWPp_seq_lscro hcrl (mid := lsmpl.base 623)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    intro hcrl_call
    refine SepWPp.call_frame_rocl hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name))
      (by wp_norm_goal) (by wp_norm_goal) hspAl
      (show _ = (blkPl_464).base + 0x79c#64 by wp_norm_goal)
      hcrl_call
      rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
      (by dsimp only [State.sp, State.setPC, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sf _ hm => by
        rw [sepConj_assoc] at hm
        refine onPanic_of_alloc_placed (s := _) ?_ hm
        change s0.trace <+: s.trace
        rw [htr]
        exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
      fun s1 hpc1 hstat1 hsp1 hcs1 _hcrl1 => ?_
    dsimp only [stringCloneSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack A sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    apply CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.SepWPp.of_sepWP_ret
    wp_steps
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
    dsimp only [EncTailVPlaced, Pf.TailCommon.EncTailVPlaced, encEntryPlaced, encStoreExtraPlaced,
      tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommonPlaced,
      protocolAddressAt, lsLogOff_eq, sp]
      at hsp1 hx19_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
    refine ⟨cap, ptr, (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, ?_, ?_, ?_, hstack, ?_⟩
    · wp_norm_goal
    · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al, hsp1_al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hcrl1, by wp_norm_goal⟩
    · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [hdraws, hfinal, hidfinal]
      arm64_sep_close
  · intro sf ⟨cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have h15 : 15#64 = BitVec.ofNat 64 (utf8 "message_encrypt").length := by rfl_kernel
    have hst : SpeStaged A x.ret (.sessionNotFound x.rem.val "message_encrypt")
        [cap, ptr, BitVec.ofNat 64 x.rem.name.bytes.length, devWord,
          lsmpl.ρ lsMessageEncryptRodataSym, 15#64]
        (vecU8Body A cap ptr x.rem.name.bytes ∗
          ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt")) :=
      speStaged_sessionNotFound A x.ret x.rem.val "message_encrypt"
        cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
        (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
        rfl hdev h15
    exact tailDropRecord_placed_ok env x R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord
      (lsmpl.ρ lsMessageEncryptRodataSym) 15#64
      (vecU8Body A cap ptr x.rem.name.bytes ∗
        ((lsmpl.ρ lsMessageEncryptRodataSym) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr)) hm hst htail

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
