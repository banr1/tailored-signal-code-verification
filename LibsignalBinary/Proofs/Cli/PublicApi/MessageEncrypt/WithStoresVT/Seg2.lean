/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreFrame
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreSteps
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStore
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinish
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishStep
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

@[expose] public section

set_option autoImplicit false

/-!
# CLI `MessageEncrypt` `WithStoresVT` (Part 2): Segments `SegFinish` and `SegApplyStore` (`_trap`)
-/

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

section SegFinish
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
open CryptoVerification.LibsignalSession

private theorem h45_encModelOk_priv {C : Crypto} {S : SpqrModel} :
    EncModelOkStmt C S uuidTryParse := by
  rintro x r sess otr taken k m otr' c ⟨hcur, -, hfrom, hrem, hstep5⟩
  unfold EncEncryptStep at hstep5
  cases hp : sess.pendingPreKey with
  | none =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp]⟩
  | some items =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, hts, hexp, hlt, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp, hts, hexp, hlt, Option.bind]⟩

theorem h45_segFinish_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R0 : SepProp)
    (s0 s : State)
    (hstored : StoredStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' c R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let env := h45_envF hEnv
  rcases hstored with ⟨⟨h1to5, htrustRel, hsaveRel, hstoreRel⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htrace, ⟨hx26, hx28⟩, _, _, _, _, hstack_le, hmem⟩
  have ⟨hmod_eq, hdraws_eq⟩ := h45_encModelOk_priv x r sess otr taken k m otr' c (h1to5.inScope hEnv.scopeIn)
  have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s := by
    refine ⟨⟨by rw [hmod_eq], ?_, ?_⟩, ?_⟩
    · rw [hmod_eq]
      exact ⟨h1to5.2.1.2, hstoreRel, trivial⟩
    · rw [hmod_eq]
      exact ⟨htrustRel, hsaveRel, trivial⟩
    · rw [htrace, hmod_eq]
      dsimp only
      rw [ikit.traceOfWith_all4 kit]
      simp only [okAnswers, List.append_assoc]
  have hstf : kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()) := by
    rw [hmod_eq]
    rfl
  have hidf : ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2 =
      ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c) := by
    rw [hmod_eq]
    rfl
  rw [← hdraws_eq, ← hstf, ← hidf] at hmem
  let R := encStoreExtra kit (kit.storeFinal st0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2)
    ikit (ikit.idFinal ist0 (okAnswers r c) (x.model C S uuidTryParse (okAnswers r c)).2) x s0 ∗ R0
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    ((∃∗ g : RecordGhost,
        sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R at hmem
  have hmem_g : s.mem ⊨
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
       memRegion (sp + 0x46a#64) 0x716 ∗
       (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) := by
    have heq :
        (((∃∗ g : RecordGhost,
            sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1) ∗
         cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
         memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) =
        ((∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
         (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R))) := by ac_rfl
    rwa [← heq]
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_g
  obtain ⟨⟨prevCap, prevPtr, _ | G⟩, hmem_g⟩ := hmem_g
  · unfold sessionRecordAt storedRecord at hmem_g
    rw [sepConj_assoc, sepConj_comm (vecAt _ _ _ _ _ _ _ _), sepConj_assoc,
      satisfies_pure_sepConj] at hmem_g
    exact hmem_g.1.elim
  unfold sessionRecordAt storedRecord sessionStateReprAt at hmem_g
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128] at hmem_g
  dsimp only at hmem_g
  rw [sessionStateAt_unfold_cap] at hmem_g
  have hmem_cm : s.mem ⊨ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
       ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
       ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
       sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
       vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
       cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
       ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by
    have heq :
        ((vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
            G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
            (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
           (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
            (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
             sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken))))) ∗
         (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗ memRegion (sp + 0x469#64) 1 ∗
          memRegion (sp + 0x46a#64) 0x716 ∗
          (cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
           ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R))) =
        (apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x469#64) 1 ∗ memRegion (sp + 0x46a#64) 0x716 ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) := by ac_rfl
    rwa [← heq]
  obtain ⟨w0, w1, w2, w3, bws, H, hbws, hw0_ne, hst, hmem_words⟩ :=
    extract_ok_cm (ret := x.ret) hmem_cm
  have h390 : sp + 0x370#64 + 0x20#64 = sp + 0x390#64 := by bv_omega
  rw [h390] at hmem_words
  have hpoll_split :
      memRegion (sp + 0x46a#64) 0x716 =
        memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x4a0#64) (8 * 27) ∗
          memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) (8 * 27) ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [memRegion_split' (b := sp + 0x46a#64) (b' := sp + 0x4a0#64) (n := 0x36) (k := 0x6e0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x4a0#64) (b' := sp + 0x578#64) (n := 8 * 27) (k := 0x608)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x578#64) (b' := sp + 0x9d0#64) (n := 0x458) (k := 0x1b0)
          (by decide) (by bv_omega) (by decide),
        memRegion_split' (b := sp + 0x9d0#64) (b' := sp + 0xaa8#64) (n := 8 * 27) (k := 0xd8)
          (by decide) (by bv_omega) (by decide)]
  rw [hpoll_split, memRegion_one (sp + 0x469#64)] at hmem_words
  let F0 := ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
    words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
    sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R
  have hmem_p : s.mem ⊨
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
       (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0))) := by
    have heq :
        (words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗ words64At (sp + 0x390#64) bws ∗ H ∗
         (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          (∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
          (memRegion (sp + 0x46a#64) 0x36 ∗ (memRegion (sp + 0x4a0#64) (8 * 27) ∗
           (memRegion (sp + 0x578#64) 0x458 ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗
            memRegion (sp + 0xaa8#64) 0xd8)))) ∗
          cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) =
        (⌜PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
           G.alice.bytes = sess.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
           (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat⌝ ∗
         (⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((∃∗ b469 : BitVec 8, (sp + 0x469#64) ↦₈ b469) ∗
           (memRegion (sp + 0x4a0#64) (8 * 27) ∗ (memRegion (sp + 0x9d0#64) (8 * 27) ∗ F0))))) := by
      dsimp only [F0]; ac_rfl
    rw [heq, satisfies_pure_sepConj] at hmem_words
    exact hmem_words.2
  rw [satisfies_pure_sepConj] at hmem_p
  rcases hmem_p with ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmem_p⟩
  rw [sepExists_sepConj_left, satisfies_sepExists] at hmem_p
  obtain ⟨b469, hmem_p⟩ := hmem_p
  rw [sepConj_comm ((sp + 0x469#64) ↦₈ b469), sepConj_assoc] at hmem_p
  obtain ⟨dws, hdws, hmem_d⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x4a0#64) (by decide) s.mem _ hmem_p
  rw [sepConj_comm (words64At (sp + 0x4a0#64) dws), sepConj_assoc, sepConj_assoc] at hmem_d
  obtain ⟨dws9d0, hdws9d0, hmem_d2⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x9d0#64) (by decide) s.mem _ hmem_d
  let F1 := words64At (sp + 0x4a0#64) dws ∗ H ∗
    sessionStateAfterLocalIk A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x578#64) 0x458 ∗
    memRegion (sp + 0xaa8#64) 0xd8 ∗
    cmScratch sp ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R
  have hmem_stage : s.mem ⊨
      (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x469#64) ↦₈ b469) ∗
        words64At (sp + 0x9d0#64) dws9d0) ∗ F1 := by
    have heq :
        (words64At (sp + 0x9d0#64) dws9d0 ∗
         (F0 ∗ (((sp + 0x469#64) ↦₈ b469) ∗ words64At (sp + 0x4a0#64) dws))) =
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ b469) ∗
          words64At (sp + 0x9d0#64) dws9d0) ∗ F1) := by
      dsimp only [F0, F1]; ac_rfl
    rwa [← heq]
  have hpc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe88#64 := by
    rw [hpc, storedPC, Pf.SegTrust.encEntry_eq_fnAddr_trap env]
  have hwp := Pf.SegFinish.finish_stage_sepWP_trap (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (b469 := b469)
    hbws hdws9d0 hcap_lt hpc' hrun hsp_al hsp hx26
  have hexit : SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
    refine Pf.TailWriteErr.segExit_of_sepWP_trap hmem_stage hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx22_1, hx23_1, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = encEntry img + 0xef0#64 := by
      rw [hpc1, ← Pf.SegTrust.encEntry_eq_fnAddr_trap env]
    have hm1 : TailModel (h45_kitF kit) st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s1 :=
      (h45_tailModel_kitF kit st0 ikit ist0 C S uuidTryParse encRecord x (okAnswers r c) (.ok m) s0 s1).mpr
        ⟨hm.1, htr1.trans hm.2⟩
    rw [← h45_segExit_kitF_trap]
    refine Pf.SegFinish.segFinish_from_ef0_trap env x R0 s0 s1 (okAnswers r c) m
      w0 w1 w2 w3 prevCap prevPtr
      G (otr'.applyToSessionState taken) bws dws H hbws hdws hw0_ne hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hsteps1.frozenLoaded hfl, hsym1.trans hsym, hvregs1.trans hvregs⟩,
      ⟨hx22_1, hx26_1, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
      hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
          ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          memRegion (sp + 0x46a#64) 0x36) ∗
        (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
         cmScratch sp ∗
         vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
         words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by
      have heq :
          (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
            ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
            words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
            words64At (sp + 0x390#64) bws ∗
            ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
            memRegion (sp + 0x46a#64) 0x36) ∗
          (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
           cmScratch sp ∗
           vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
           words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) =
          ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
          ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
            words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
            words64At (sp + 0x390#64) bws ∗
            ((sp + 0x469#64) ↦₈ 0#8) ∗
            words64At (sp + 0x9d0#64) bws) ∗ F1) := by
        rw [sessionStateAt_unfold_cap A (sp + 0x128#64) G (otr'.applyToSessionState taken)]
        dsimp only [F1]; ac_rfl
      rw [heq, satisfies_pure_sepConj]
      exact ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hmf1⟩
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (mid_280_to_4a0_weaken sp k w0 w1 w2 w3 bws hbws)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x220 ∗
         (sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          cmScratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R)) =
        ((cmScratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G (otr'.applyToSessionState taken) ∗
          memRegion (sp + 0x280#64) 0x220 ∗
          words64At (sp + 0x4a0#64) dws ∗ memRegion (sp + 0x578#64) 0x458 ∗
          words64At (sp + 0x9d0#64) bws ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommon A ctl img x (x.draws S (okAnswers r c)) s0 ∗ R) := by ac_rfl
    rw [h45_storeFinal_kitF]
    exact Eq.mp (congrArg (s1.mem ⊨ ·) heq2) hmf3
  exact hexit

end SegFinish

section SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem h45_store_to_e80_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {kit : SessionStoreSpec A img.base}
    {st0 : kit.StoreState} {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    {x : WithStoresEncGhost} {g' : RecordGhost}
    {rec' : SessionRecord (List (BitVec 8))} {F R : SepProp} {s0 s : State}
    {next : State → Prop}
    (hrecOk : kit.RecOk rec')
    (haddr : kit.addrOk x.rem.val)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat)
    (hpc : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xde8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = s.sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x580#64)
    (hpref0 : s0.trace <+: s.trace)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hfs : FsCtx kit.envOk True (trTrapProgAt img.base C abs) s s)
    (hm : s.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive kit st0 ikit s.sp x g' rec' ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x9b0#64) 24) ∗ (F ∗ R))
    (hcont : ∀ sm (ans : Except Unit Unit) (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp),
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xe80#64 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.spAligned = true →
      sm.trace = s.trace ++ kit.storeEvs encRecord x.rem.val rec' ans →
      kit.storeRel st0 x.rem.val rec' ans →
      (ans = .ok () → H = emp) →
      (ans = .error () →
        w2 = 10#64 ∧ w3 = 1#64 ∧
          SpeStaged A x.ret (.store ()) [0x800000000000001A#64, w1, 10#64, 1#64, w4, w5] H) →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x27 = w0 →
      sm.readReg64 .x21 = w1 →
      sm.readReg64 .x23 = w2 →
      w0 = pollTag ans →
      (sm.mem ⊨ (storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' ans) ikit s.sp x g' rec' ∗
        memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗
          ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R)) →
      SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 sm next) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s next := by
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hm1 : s.mem ⊨ (((s.sp + 0xc0#64) ↦₆₄ x.remA) ∗
      ((s.sp + 0xd0#64) ↦₆₄ x.ssA) ∗
      ((s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗
      ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff))) ∗
      (((((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗
        stackAt s.sp (encSubStackV kit ikit) ∗ A.pool ∗
        kit.storeAt x.ssA st0 ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [storeVtablesAt, storeBaseActive] at hm
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  refine Pf.SegTrust.SegExit.of_sepWP_trap hm1
    (Pf.SegApplyStore.step_de8_to_df8_trap (shimOff := kit.storeShimOff) hpc hrun hsp_align hx20) ?_
  rintro s1 P1 _ hsteps1 hpc1 hrun1 hm2
    ⟨rfl, hsp1, htr1, hx0_1, hx1_1, hx2_1, hx30_1, hx19_1, hx20_1, hx25_1, hx26_1, hx28_1, hx29_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := spAligned_of_sp_eq hsp_al hsp1
  have hpref1 : s0.trace <+: s1.trace := by rw [htr1]; exact hpref0
  have hfl1 : img.FrozenLoaded s1 := hsteps1.frozenLoaded hfl
  have hsym1 : s1.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
  have hm3 : s1.mem ⊨ (kitStoreShimSpec kit).pre ⟨x.ssA, x.remA, s.sp + 0x110#64⟩ s1 ∗
      ((((s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗
        kit.storeAt x.ssA st0 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storeShimStack) ∗
        memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStoreShimSpec]
    rw [hsp1]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
      (storeShimStack_le_encSubStackV kit ikit)] at hm2
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_1, hx1_1, hx2_1⟩, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm2⟩
  refine Pf.SegTrust.call_alloc_trap hEnv.kitOk.storeShim ⟨x.ssA, x.remA, s.sp + 0x110#64⟩
    hpc1 hrun1 hsp1_al hx30_1 hpref1 (inImage_pre_intro hfl1 hsym1 hm3) ?_
    (hR := entails_anyHeap_self R)
  intro s2 hsteps2 hpc2 hrun2 hsp2 hsp2_al hcs2 hm4
  have hfl2 : img.FrozenLoaded s2 := hsteps2.frozenLoaded hfl1
  have hsym2 : s2.symtab = img.symtab := hsteps2.symtab_eq.trans hsym1
  dsimp only [Spec.inImage, kitStoreShimSpec] at hm4
  rw [hsp1] at hsp2 hm4
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm4
  obtain ⟨⟨hx1_2, htr2⟩, hm4⟩ := hm4
  set box := s2.readReg64 .x0
  have hm4' : s2.mem ⊨ memRegion (s.sp + 0x470#64) 16 ∗
      ((A.live box kit.storeBoxSize 8 ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool ∗
        kit.storeAt x.ssA st0 ∗
        stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F ∗ R) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storeShimStack
      (storeShimStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm4
  obtain ⟨u470, u478, hm5⟩ := memRegion16_exists_words2 (s.sp + 0x470#64) hm4'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm5
  have hm6 : s2.mem ⊨ (((s2.sp + 0x470#64) ↦₆₄ u470) ∗
      ((s2.sp + 0x478#64) ↦₆₄ u478) ∗
      ((img.base + (kit.storeFutVtOff + 0x18#64)) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗
      (((A.live box kit.storeBoxSize 8 ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 0#8 ∗ A.pool ∗
        kit.storeAt x.ssA st0 ∗
        stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        protocolAddressAt A x.rem x.remA ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    rw [hsp2, ← BitVec.add_assoc img.base kit.storeFutVtOff 0x18#64]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm5
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2_al
  refine Pf.SegTrust.SegExit.of_sepWP_trap hm6
    (Pf.SegApplyStore.step_dfc_to_e10_trap (futVtOff := kit.storeFutVtOff) (pollOff := kit.storePollOff)
      hpc2 hrun2 hsp2_align rfl hx1_2) ?_
  rintro s3 P3 _ hsteps3 hpc3 hrun3 hm7
    ⟨rfl, hsp3, htr3, hx0_3, _, hx8_3, hx30_3, hx19_3, hx20_3, hx25_3, hx26_3, hx28_3, hx29_3, hvregs_3⟩
  rw [hsp2] at hsp3 hx8_3 hm7
  have hsp3_al : s3.spAligned = true := spAligned_of_sp_eq hsp_al hsp3
  have hpref3 : s0.trace <+: s3.trace := by rw [htr3, htr2.2.2]; exact hpref1
  have hfl3 : img.FrozenLoaded s3 := hsteps3.frozenLoaded hfl2
  have hsym3 : s3.symtab = img.symtab := hsteps3.symtab_eq.trans hsym2
  let pollCall : StorePollCall × BitVec 64 × kit.StoreState :=
    (⟨box, s.sp + 0x580#64, ⟨x.remA, x.rem, s.sp + 0x110#64, g', rec'⟩⟩, x.ssA, st0)
  have hm8 : s3.mem ⊨ (kitStorePollSpec kit encRecord).pre pollCall s3 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - kit.storePollStack) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff)) ∗
        memRegion (s.sp + 0x9b0#64) 24) ∗ F) ∗ R) := by
    dsimp only [kitStorePollSpec, pollCall]
    rw [hsp3]
    rw [← BitVec.add_assoc img.base kit.storeFutVtOff 24#64] at hm7
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
      (storePollStack_le_encSubStackV kit ikit)] at hm7
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_3, hx8_3, hrecOk, haddr⟩, Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7⟩
  have henv3 : kit.envOk s3.fs.files :=
    (hfs.of_steps ((hsteps1.trans hsteps2).trans hsteps3)).envOk_at (evs := [])
      (by rw [htr3, htr2.2.2, htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  refine Pf.SegTrust.call_alloc_trap hEnv.kitOk.storePoll pollCall hpc3 hrun3 hsp3_al hx30_3 hpref3
    (inImage_pre_intro hfl3 hsym3
      (withEnvPre_pre_intro (φ := fun s => kit.envOk s.fs.files) henv3 hm8)) ?_
    (hR := entails_anyHeap_self R)
  intro s4 hsteps4 hpc4 hrun4 hsp4 hsp4_al hcs4 hm9
  dsimp only [Spec.inImage, kitStorePollSpecE, withEnvPre, kitStorePollSpec, pollCall] at hm9
  rw [hsp3] at hsp4 hm9
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm9
  obtain ⟨ans, ⟨hstoreRel, htr4⟩, hm9⟩ := hm9
  have hm9_poll : s4.mem ⊨
      storePollOutAt img.base (s.sp + 0x580#64) ans ∗
      (memRegion (s.sp + 0x9b0#64) 24 ∗
      ((kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F ∗ R)) := by
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp kit.storePollStack
      (storePollStack_le_encSubStackV kit ikit)]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm9
  have hm10 := Satisfies.mono (sepConj_mono_left
    (storePollOut_words A img.base (s.sp + 0x580#64) ans)) hm9_poll
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
    satisfies_pure_sepConj] at hm10
  obtain ⟨w0, w1, w2, w3, w4, w5, H, ⟨hw0, hans, hH, hstaged⟩, hm10⟩ := hm10
  have hstaged' : ans = .error () →
      w2 = 10#64 ∧ w3 = 1#64 ∧
        SpeStaged A x.ret (.store ()) [0x800000000000001A#64, w1, 10#64, 1#64, w4, w5] H := by
    intro herr
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hstaged herr
    exact ⟨rfl, rfl, speStaged_storeErr A img.base x.ret w5⟩
  have hm10' : s4.mem ⊨ memRegion (s.sp + 0x9b0#64) 24 ∗
      (((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x580#64 + 8#64) ↦₆₄ w1 ∗
        (s.sp + 0x580#64 + 0x10#64) ↦₆₄ w2 ∗ (s.sp + 0x580#64 + 0x18#64) ↦₆₄ w3 ∗
        (s.sp + 0x580#64 + 0x20#64) ↦₆₄ w4 ∗ (s.sp + 0x580#64 + 0x28#64) ↦₆₄ w5 ∗
        H ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        (s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F ∗ R) :=
    Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm10
  obtain ⟨u9b0, u9b8, u9c0, hm11⟩ := memRegion24_exists_words3 (s.sp + 0x9b0#64) hm10'
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm11
  have hm12 : s4.mem ⊨ (((s4.sp + 0x470#64) ↦₆₄ box) ∗
      ((s4.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
      ((s4.sp + 0x580#64) ↦₆₄ w0) ∗
      ((s4.sp + 0x588#64) ↦₆₄ w1) ∗
      ((s4.sp + 0x590#64) ↦₆₄ w2) ∗
      ((s4.sp + 0x598#64) ↦₆₄ w3) ∗
      ((s4.sp + 0x5a0#64) ↦₆₄ w4) ∗
      ((s4.sp + 0x5a8#64) ↦₆₄ w5) ∗
      ((s4.sp + 0x9b0#64) ↦₆₄ u9b0) ∗
      ((s4.sp + 0x9b8#64) ↦₆₄ u9b8) ∗
      ((s4.sp + 0x9c0#64) ↦₆₄ u9c0) ∗
      ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff))) ∗
      (((H ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F) ∗ R) := by
    rw [hsp4]
    exact Eq.mp (congrArg (s4.mem ⊨ ·) (by ac_rfl)) hm11
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4_al
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x580#64 := by
    rw [hsp4, Pf.SegApplyStore.cs_x25 hcs4, hx25_3, Pf.SegApplyStore.cs_x25 hcs2, hx25_1, hx25]
  have hdrop_nz : img.base + kit.storeFutDropOff ≠ 0#64 :=
    kit.storeFutDrop_ne_zero (ProofLib.ObjectLoad.base_aligned_of_loads hEnv.loads)
  refine Pf.SegTrust.SegExit.of_sepWP_trap hm12
    (Pf.SegApplyStore.step_e14_to_e68_trap (futVtOff := kit.storeFutVtOff) (futDropOff := kit.storeFutDropOff)
      hdrop_nz hpc4 hrun4 hsp4_align hx25_4 hw0) ?_
  rintro s5 _ _ hsteps5 hpc5 hrun5 hm13
    ⟨rfl, hsp5, htr5, hx0_5, hx20_5, hx21_5, hx22_5, hx23_5, hx27_5, hx30_5,
      hx19_5, hx25_5, hx26_5, hx28_5, hx29_5, hvregs_5⟩
  rw [hsp4] at hsp5 hm13
  have hsp5_al : s5.spAligned = true := spAligned_of_sp_eq hsp_al hsp5
  have hm14 : s5.mem ⊨ futDropSpec.pre () s5 ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗
        (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff))) ∗
      ((H ∗
        kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        A.live box kit.storeBoxSize 8 ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
        ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F)) ∗ R) := by
    dsimp only [futDropSpec]
    rw [emp_sepConj]
    exact Eq.mp (congrArg (s5.mem ⊨ ·) (by ac_rfl)) hm13
  refine Pf.SegTrust.call_nopanic_trap hEnv.kitOk.storeFutDrop ()
    hpc5 hrun5 hsp5_al hx30_5 hm14 ?_
  intro s6 hsteps6 hpc6 hrun6 hsp6 hsp6_al hcs6 hm15
  dsimp only [futDropSpec] at hm15
  rw [hsp5] at hsp6
  rw [satisfies_pure_sepConj] at hm15
  obtain ⟨htr6, hm15⟩ := hm15
  have hm15_box : s6.mem ⊨ kit.storeBoxAt box x.ssA x.remA (s.sp + 0x110#64) 1#8 ∗
      (((img.base + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((img.base + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗
        (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        H ∗
        A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F) ∗ R)) :=
    Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15
  have hm15_mem := Satisfies.mono (sepConj_mono_left
    (kit.storeBoxAt_memRegion box x.ssA x.remA (s.sp + 0x110#64) 1#8)) hm15_box
  have hm16 : s6.mem ⊨ (((img.base + (kit.storeFutVtOff + 8#64)) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗
      ((img.base + (kit.storeFutVtOff + 0x10#64)) ↦₆₄ᵣ 8#64)) ∗
      ((((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff) ∗
        (s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
        (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
        (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5 ∗
        (s.sp + 0x9b0#64) ↦₆₄ w3 ∗ (s.sp + 0x9b8#64) ↦₆₄ w4 ∗
        (s.sp + 0x9c0#64) ↦₆₄ w5 ∗
        ((img.base + kit.storeFutVtOff) ↦₆₄ᵣ (img.base + kit.storeFutDropOff)) ∗
        H ∗
        memRegion box kit.storeBoxSize ∗ A.live box kit.storeBoxSize 8 ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        A.pool ∗ stackAt s.sp (encSubStackV kit ikit) ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt ∗
        ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + kit.storeShimOff)) ∗
        ((img.base + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (img.base + kit.storePollOff))) ∗ F) ∗ R) := by
    rw [← BitVec.add_assoc img.base kit.storeFutVtOff 8#64,
        ← BitVec.add_assoc img.base kit.storeFutVtOff 0x10#64]
    exact Eq.mp (congrArg (s6.mem ⊨ ·) (by ac_rfl)) hm15_mem
  have hx20_6 : s6.readReg64 .x20 = box := (Pf.SegApplyStore.cs_x20 hcs6).trans hx20_5
  have hx22_6 : s6.readReg64 .x22 = img.base + kit.storeFutVtOff := (Pf.SegApplyStore.cs_x22 hcs6).trans hx22_5
  refine Pf.SegTrust.SegExit.of_sepWP_trap hm16
    (Pf.SegApplyStore.step_e6c_to_e7c_trap (futVtOff := kit.storeFutVtOff) (boxSizeBv := BitVec.ofNat 64 kit.storeBoxSize)
      kit.storeBoxSize_ne_zero hpc6 hrun6 hx20_6 hx22_6) ?_
  rintro s7 P7 _ hsteps7 hpc7 hrun7 hm17
    ⟨rfl, hsp7, htr7, hx0_7, hx1_7, hx2_7, hx30_7,
      hx19_7, hx20_7, hx21_7, hx23_7, hx25_7, hx26_7, hx27_7, hx28_7, hx29_7, hvregs_7⟩
  rw [hsp6] at hsp7
  have hsp7_al : s7.spAligned = true := spAligned_of_sp_eq hsp_al hsp7
  have hm18 : s7.mem ⊨ (rustDeallocSpec A).pre (box, kit.storeBoxSize, 8) s7 ∗
      (((storeVtablesAt kit ∗
        ((s.sp + 0x470#64) ↦₆₄ box ∗ (s.sp + 0x478#64) ↦₆₄ (img.base + kit.storeFutVtOff)) ∗
        ((s.sp + 0x580#64) ↦₆₄ w0 ∗ (s.sp + 0x588#64) ↦₆₄ w1 ∗
          (s.sp + 0x590#64) ↦₆₄ w2 ∗ (s.sp + 0x598#64) ↦₆₄ w3 ∗
          (s.sp + 0x5a0#64) ↦₆₄ w4 ∗ (s.sp + 0x5a8#64) ↦₆₄ w5) ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗ ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H ∗
        memRegion (s.sp - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit - allocHookStack) ∗
        kit.storeAt x.ssA (kit.storeUpdate st0 x.rem.val rec' ans) ∗
        protocolAddressAt A x.rem x.remA ∗ sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        (s.sp + 0xc0#64) ↦₆₄ x.remA ∗ (s.sp + 0xd0#64) ↦₆₄ x.ssA ∗
        (s.sp + 0xd8#64) ↦₆₄ kit.ss_vt) ∗ F) ∗ R) := by
    dsimp only [rustDeallocSpec, storeVtablesAt]
    rw [hsp7]
    rw [← BitVec.add_assoc img.base kit.storeFutVtOff 8#64,
        ← BitVec.add_assoc img.base kit.storeFutVtOff 0x10#64] at hm17
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
      (Pf.SegApplyStore.allocHookStack_le_encSubStackV kit ikit)] at hm17
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_7, by rw [hx1_7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kit.storeBoxSize_lt],
      by rw [hx2_7]; rfl⟩,
      Eq.mp (congrArg (s7.mem ⊨ ·) (by ac_rfl)) hm17⟩
  rw [← h45_segExit_kitF_trap]
  refine Pf.SegTrust.call_nopanic_trap (Pf.SegTrust.dealloc_ok_at_enc_trap (h45_envF hEnv))
    (box, kit.storeBoxSize, 8) hpc7 hrun7 hsp7_al hx30_7 hm18 ?_
  intro s8 hsteps8 hpc8 hrun8 hsp8 hsp8_al hcs8 hm19
  rw [h45_segExit_kitF_trap]
  dsimp only [rustDeallocSpec] at hm19
  rw [hsp7] at hsp8 hm19
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm19
  obtain ⟨htr8, hm19⟩ := hm19
  have hm20 : s8.mem ⊨ storeVtablesAt kit ∗
      ((((s.sp + 0x470#64) ↦₆₄ box) ∗ ((s.sp + 0x470#64 + 8#64) ↦₆₄ (img.base + kit.storeFutVtOff))) ∗
      (((s.sp + 0x580#64) ↦₆₄ w0) ∗ ((s.sp + 0x580#64 + 8#64) ↦₆₄ w1) ∗
        ((s.sp + 0x580#64 + 16#64) ↦₆₄ w2) ∗ ((s.sp + 0x580#64 + 24#64) ↦₆₄ w3) ∗
        ((s.sp + 0x580#64 + 32#64) ↦₆₄ w4) ∗
        ((s.sp + 0x580#64 + 40#64) ↦₆₄ w5)) ∗
      ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' ans) ikit s.sp x g' rec' ∗
        (((s.sp + 0x9b0#64) ↦₆₄ w3) ∗
          ((s.sp + 0x9b8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x9c0#64) ↦₆₄ w5)) ∗
        H) ∗ (F ∗ R))) := by
    dsimp only [storeBaseActive]
    rw [stackAt_encSubStackV_split kit ikit hbound s.sp allocHookStack
      (Pf.SegApplyStore.allocHookStack_le_encSubStackV kit ikit)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm19
  have hm21 := Satisfies.mono (sepConj_mono
    (words2_entails_memRegion16 (s.sp + 0x470#64) box (img.base + kit.storeFutVtOff))
    (sepConj_mono_left
      (words6_entails_memRegion48 (s.sp + 0x580#64) w0 w1 w2 w3 w4 w5)))
    (Satisfies.of_sep_right hm20)
  have hsteps_all :=
    hsteps1.trans (hsteps2.trans (hsteps3.trans (hsteps4.trans
      (hsteps5.trans (hsteps6.trans (hsteps7.trans hsteps8))))))
  refine hcont s8 ans w0 w1 w2 w3 w4 w5 H hsteps_all hpc8 hrun8 hsp8 hsp8_al
    (by rw [htr8, htr7, htr6, htr5, htr4, htr3, htr2.2.2, htr1])
    hstoreRel hH hstaged'
    (by rw [Pf.SegApplyStore.cs_x19 hcs8, hx19_7, Pf.SegApplyStore.cs_x19 hcs6, hx19_5,
            Pf.SegApplyStore.cs_x19 hcs4, hx19_3, Pf.SegApplyStore.cs_x19 hcs2, hx19_1])
    (by rw [Pf.SegApplyStore.cs_x25 hcs8, hx25_7, Pf.SegApplyStore.cs_x25 hcs6, hx25_5,
            Pf.SegApplyStore.cs_x25 hcs4, hx25_3, Pf.SegApplyStore.cs_x25 hcs2, hx25_1])
    (by rw [Pf.SegApplyStore.cs_x26 hcs8, hx26_7, Pf.SegApplyStore.cs_x26 hcs6, hx26_5,
            Pf.SegApplyStore.cs_x26 hcs4, hx26_3, Pf.SegApplyStore.cs_x26 hcs2, hx26_1])
    (by rw [Pf.SegApplyStore.cs_x28 hcs8, hx28_7, Pf.SegApplyStore.cs_x28 hcs6, hx28_5,
            Pf.SegApplyStore.cs_x28 hcs4, hx28_3, Pf.SegApplyStore.cs_x28 hcs2, hx28_1])
    (by rw [Pf.SegApplyStore.cs_x29 hcs8, hx29_7, Pf.SegApplyStore.cs_x29 hcs6, hx29_5,
            Pf.SegApplyStore.cs_x29 hcs4, hx29_3, Pf.SegApplyStore.cs_x29 hcs2, hx29_1])
    (by rw [Pf.SegApplyStore.cs_vregs hcs8, hvregs_7, Pf.SegApplyStore.cs_vregs hcs6, hvregs_5,
            Pf.SegApplyStore.cs_vregs hcs4, hvregs_3, Pf.SegApplyStore.cs_vregs hcs2, hvregs_1])
    (by rw [Pf.SegApplyStore.cs_x27 hcs8, hx27_7, Pf.SegApplyStore.cs_x27 hcs6, hx27_5])
    (by rw [Pf.SegApplyStore.cs_x21 hcs8, hx21_7, Pf.SegApplyStore.cs_x21 hcs6, hx21_5])
    (by rw [Pf.SegApplyStore.cs_x23 hcs8, hx23_7, Pf.SegApplyStore.cs_x23 hcs6, hx23_5])
    hans
    (Eq.mp (congrArg (s8.mem ⊨ ·) (by ac_rfl)) hm21)

theorem h45_segApplyStore_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (c : IdentityChange) (R : SepProp) (s0 s : State)
    (haddr : kit.addrOk x.rem.val)
    (hfs : EncFsCtx_trap kit ikit C abs s0 s)
    (hap : ApplyStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun s' => StoredStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' c R s0 s') := by
  let env := h45_envF hEnv
  obtain ⟨⟨h15, htrust, hsave⟩, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hap
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set rec' := storedRecord sess otr' taken
  set ist2 := ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c)
  have hsc_some : taken.senderChain.isSome = true :=
    fromSessionState_senderChain_isSome h15.2.2.1
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hpc_d9c : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0xd9c#64 := by
    rw [hpc, applyPC, Pf.SegTrust.encEntry_eq_fnAddr_trap env]
  have hm_in : s.mem ⊨
      (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
        encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
        memRegion x.ret 248 ∗ encCommon A ctl img x draws s0) ∗
      (encStoreExtra kit st0 ikit ist2 x s0 ∗ R) := by
    rw [hsp]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  rw [← h45_segExit_kitF_trap]
  refine Pf.SegApplyStore.apply_to_de8_trap env (sepConj_mono_left (entails_anyHeap _))
    hpc_d9c hrun hsp hsp_al hfl hsym hx25' hpref0 hsc_some hm_in ?_
  intro s_de8 g' hsteps_de8 hpc_de8 hrun_de8 hsp_de8 hsp_de8_al htr_de8
    hx19_de8 hx20_de8 hx25_de8 hx26_de8 hx28_de8 hx29_de8 hvregs_de8 hm_de8
  rw [h45_segExit_kitF_trap]
  have ⟨hfl_de8, hsym_de8⟩ := callInv_steps hfl hsym hsteps_de8
  have hsp_de8' : s_de8.sp = sp := hsp_de8.trans hsp
  have hsp_de8_s0 : s_de8.sp = s0.sp - 0xbe0#64 := hsp_de8'
  have hpref_de8 : s0.trace <+: s_de8.trace := by rw [htr_de8]; exact hpref0
  set F := Pf.SegApplyStore.storePassive kit ikit ist2 ctl x k m draws s0
  have hm_de8' : s_de8.mem ⊨
      (((sessionRecordAt A (s.sp + 0x110#64) g' rec' ∗
        ((s.sp + 0x280#64) ↦₆₄ (s.sp + 0x128#64)) ∗
        memRegion (s.sp + 0x288#64) 200 ∗
        ((s.sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        apiEncResultAt A (s.sp + 0x370#64) (.ok m) ∗
        ((s.sp + 0x468#64) ↦₈ 0#8) ∗
        ((s.sp + 0x469#64) ↦₈ 0#8)) ∗
      cmScratch s.sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗
      memRegion (s.sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0) ∗ encStoreExtra kit st0 ikit ist2 x s0) ∗ R :=
    Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_de8
  have hm_split := Satisfies.mono
    (sepConj_mono_left (Pf.SegApplyStore.store_mem_split kit st0 ikit ist2 ctl x g' rec' k m draws s0 s.sp hsp))
    hm_de8'
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_split
  rcases hm_split with ⟨hbound, hm_split⟩
  have hm_store_in : s_de8.mem ⊨ (storeVtablesAt kit ∗
      storeBaseActive kit st0 ikit s_de8.sp x g' rec' ∗
      memRegion (s_de8.sp + 0x470#64) 16 ∗
      memRegion (s_de8.sp + 0x580#64) 48 ∗
      memRegion (s_de8.sp + 0x9b0#64) 24) ∗ (F ∗ R) := by
    rw [hsp_de8]
    have hm_vt := storeVtablesAt_intro hEnv.vtables hfl_de8 hm_split
    dsimp only [F]
    exact Eq.mp (congrArg (s_de8.mem ⊨ ·) (by ac_rfl)) hm_vt
  have hx20_de8' : s_de8.readReg64 .x20 = s_de8.sp + 0x58#64 := by
    rw [hx20_de8, hsp_de8, hsp, hx20]
  have hx25_de8' : s_de8.readReg64 .x25 = s_de8.sp + 0x580#64 := by
    rw [hx25_de8, hsp_de8, hx25']
  have hrecOk : kit.RecOk rec' := hEnv.recOk haddr h15
  have hfs_de8 : FsCtx kit.envOk True (trTrapProgAt img.base C abs) s_de8 s_de8 :=
    ((hfs.of_steps hsteps_de8).rebase (by rw [htr_de8, htr])
      (fun hQ => NoFsEv.append (NoFsEv.append (hQ.1.1 _ _ _) (hQ.2.1 _ _ _ _))
        (hQ.2.2 _ _ _))).mono (fun _ h => h.1) (fun _ => trivial)
  refine h45_store_to_e80_trap hEnv hrecOk haddr hbound hpc_de8 hrun_de8 hsp_de8_al
    hx20_de8' hx25_de8' hpref_de8 hfl_de8 hsym_de8 hfs_de8 hm_store_in ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H hsteps_e80 hpcm hrunm hspm hspm_al htrm hstoreRel hH hstaged
    hx19m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm
  have ⟨hflm, hsymm⟩ := callInv_steps hfl_de8 hsym_de8 hsteps_e80
  have hspm' : sm.sp = sp := hspm.trans hsp_de8'
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
        (ikit.trustEvs x.rem.val k .sending (.ok true) ++
          ikit.saveEvs x.rem.val k (.ok c)) ++
        kit.storeEvs encRecord x.rem.val rec' ans) := by
    rw [htrm, htr_de8, htr]
    simp only [List.append_assoc]
  rcases ans with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · dsimp only [pollTag] at hans
    subst hans
    obtain ⟨rfl, rfl, hspe⟩ := hstaged rfl
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.error ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗
          memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗
            ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          H) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine Pf.SegTrust.SegExit.of_sepWP_trap hmm_emp (Pf.SegApplyStore.step_e80_err_trap hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have ⟨hfl_err, hsym_err⟩ := callInv_steps hflm hsymm hsteps_err
    have hm_ro' : s_err.mem ⊨
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.error ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗
          memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ 1#64) ∗
            ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5)) ∗
          H) ∗ F) ∗ R :=
      hm_err
    have htail_ent := Pf.SegApplyStore.store_mem_to_tail kit (kit.storeUpdate st0 x.rem.val rec' (.error ()))
      ikit ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound 1#64 w4 w5 H
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    have htm : Tails.TailModel (h45_kitF kit) st0 ikit ist0 C S uuidTryParse encRecord x (answersOfStoreErr r c) (.error (.store ())) s0 s_err :=
      (h45_tailModel_kitF kit st0 ikit ist0 C S uuidTryParse encRecord x (answersOfStoreErr r c) (.error (.store ())) s0 s_err).mpr
        (StepsThroughEncrypt.tailModel_store_err c (encRecord := encRecord) (s0 := s0) (s := s_err)
          h15 htrust hsave hstoreRel (htr_err.trans htrm'))
    have hdraws : x.draws S (answersOfStoreErr r c) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfStoreErr r c) rfl
    have hfinal :
        (h45_kitF kit).storeFinal st0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          kit.storeUpdate st0 x.rem.val rec' (.error ()) := by
      rw [h45_storeFinal_kitF, StepsThroughEncrypt.model_store_err c h15]
      rfl
    have hid_final :
        ikit.idFinal ist0 (answersOfStoreErr r c) (x.model C S uuidTryParse (answersOfStoreErr r c)).2 =
          ist2 := by
      rw [StepsThroughEncrypt.model_store_err c h15]
      rfl
    rw [← h45_segExit_kitF_trap]
    refine Pf.SegTrust.SegExit.of_false_trap
      (Tails.tailStoreHookErr_ok_trap env x R s0 s_err (answersOfStoreErr r c) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        H cmScratch (Or.inr rfl)
        g' rec' none m 0xf2c 0x9b0 (Or.inr (Or.inr rfl))
        htm hspe ?_)
    refine ⟨by rw [hpc_err, Pf.SegTrust.encEntry_eq_fnAddr_trap env],
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29_de8, hx29],
      by rw [hx19_err, hx19m, hx19_de8, hx19], hfl_err, hsym_err, by rw [hvregs_err, hvregsm, hvregs_de8, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26_de8, hx26],
       by rw [hx28_err, hx28m, hx28_de8, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    dsimp only
    rw [hdraws, hfinal, hid_final, ← hsp_de8_s0]
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  · dsimp only [pollTag] at hans
    subst hans
    rw [hH rfl, sepConj_emp] at hmm
    have hmm_emp : sm.mem ⊨ emp ∗
        (((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗
          memRegion (s_de8.sp + 0x580#64) 48 ∗
          (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗
            ((s_de8.sp + 0x9b8#64) ↦₆₄ w4) ∗
            ((s_de8.sp + 0x9c0#64) ↦₆₄ w5))) ∗ F) ∗ R) := by
      rw [emp_sepConj, sepConj_assoc]
      exact hmm
    refine Pf.SegTrust.SegExit.of_sepWP_trap hmm_emp (Pf.SegApplyStore.step_e80_ok_trap hpcm hrunm hx27m) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have ⟨hfl_ok, hsym_ok⟩ := callInv_steps hflm hsymm hsteps_ok
    have hm_ok_9b0 : s_ok.mem ⊨
        (((s_de8.sp + 0x9b0#64) ↦₆₄ w3) ∗
          ((s_de8.sp + 0x9b0#64 + 8#64) ↦₆₄ w4) ∗
          ((s_de8.sp + 0x9b0#64 + 16#64) ↦₆₄ w5)) ∗
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗
          memRegion (s_de8.sp + 0x580#64) 48) ∗ F ∗ R) := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s_de8.sp + 0x9b0#64) w3 w4 w5)) hm_ok_9b0
    have hm_ok_pre : s_ok.mem ⊨
        ((storeBaseActive kit (kit.storeUpdate st0 x.rem.val rec' (.ok ())) ikit s_de8.sp x g' rec' ∗
          memRegion (s_de8.sp + 0x470#64) 16 ∗
          memRegion (s_de8.sp + 0x580#64) 48 ∗
          memRegion (s_de8.sp + 0x9b0#64) 24) ∗
          Pf.SegApplyStore.storePassive kit ikit ist2 ctl x k m draws s0) ∗ R := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    have hm_ok_stored := Satisfies.mono (sepConj_mono_left
      (Pf.SegApplyStore.store_mem_to_stored kit (kit.storeUpdate st0 x.rem.val rec' (.ok ()))
        ikit ist2 ctl x g' rec' k m draws s0 s_de8.sp hsp_de8' hbound)) hm_ok_pre
    refine Pf.SegTrust.SegExit.next_trap ⟨⟨h15, htrust, hsave, hstoreRel⟩, by rw [hpc_ok, storedPC, Pf.SegTrust.encEntry_eq_fnAddr_trap env],
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29_de8, hx29],
        by rw [hx19_ok, hx19m, hx19_de8, hx19], hfl_ok, hsym_ok, by rw [hvregs_ok, hvregsm, hvregs_de8, hvregs]⟩,
      by rw [htr_ok, htrm']; simp only [List.append_assoc]; rfl,
      ⟨by rw [hx26_ok, hx26m, hx26_de8, hx26],
       by rw [hx28_ok, hx28m, hx28_de8, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only
    rw [← hsp_de8_s0]
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_stored

end SegApplyStore

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
