/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqStatement
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.Correctness.Crypto
import Computational.Proofs.LibsignalCli.PqFirstMessageSpqr
import Computational.Proofs.E2E.Pqxdh.FirstMessageRoundtrip
import Computational.Proofs.SignalWireRoundTrip
import LibsignalBinary.Proofs.SpecLemmas.SignalPqxdh.Model
import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDec

/-!
# First-Message Roundtrip Through the CLI Models

Proves `PqCliFirstMessageRoundtrip X W`: when Alice initializes a PQXDH session on Bob's honest
pre-key bundle and sends `pt`, her wire output is a valid pre-key message naming Bob's key IDs and
Bob's `pqRecvPrekeyModel` recovers `pt`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoGames.LibsignalSM.Proofs.Correctness
open CryptoVerification.SignalSession.FirstMessage

theorem pqCliFirstMessageRoundtrip_proof (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    PqCliFirstMessageRoundtrip X W := by
  intro stA stB k spkSig kpkSig t rs rc pt stA₁ stA₂ o w
    hpA hpB hpeerB hsessB hkeysAt hXcomm hXnz hKyber hCanon hAes hpt hsigs hinit hsend
  set b := honestBundle W.C stB.me k spkSig kpkSig
  unfold pqInitModel at hinit
  split at hinit
  · nomatch hinit
  · cases hIS : initiateState X W stA.party stA.me b t with
    | none =>
      rw [hIS] at hinit
      nomatch hinit
    | some xg =>
      rcases xg with ⟨x, g⟩
      rw [hIS] at hinit
      injection hinit with hinit'
      injection hinit' with hinitPair
      have hstA₁ : stA₁ = { stA with peerId := some ⟨⟨b.idPub⟩⟩, session := some (x, g) } :=
        (Prod.mk.inj hinitPair).1.symm
      subst hstA₁
      rw [hpA] at hIS
      unfold initiateState at hIS
      cases hIK : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W stA.me b t) with
      | none =>
        rw [hIK] at hIS
        contradiction
      | some dk_hdr =>
        rcases dk_hdr with ⟨dk, hdr⟩
        rw [hIK] at hIS
        dsimp only at hIS
        set idA := keyPairOf W.C stA.me.idPriv
        set rk0 := HKDF.bytesToKey32 (ofU8 dk.rootKey)
        set ck0 := HKDF.bytesToKey32 (ofU8 dk.chainKey)
        set pqr0 := HKDF.bytesToKey32 (ofU8 dk.pqrKey)
        set coinsA := HKDF.bytesToKey32 ((t.toList.drop 160).take 32)
        set ephA := KeyPair.generate W.C coinsA
        obtain ⟨stA1, salt, pqMsg, stB1, hSpqrSend, hpqLen, hSpqrRecv⟩ :=
          spqrPq_firstMessage_send_recv W pqr0 rs
        obtain ⟨stA0, hstA0⟩ : ∃ stA0, (pqxdhSpqrSession W).init .a2b pqr0 = stA0 := ⟨_, rfl⟩
        obtain ⟨stB0, hstB0⟩ : ∃ stB0, (pqxdhSpqrSession W).init .b2a pqr0 = stB0 := ⟨_, rfl⟩
        rw [hstA0] at hSpqrSend
        rw [hstB0] at hSpqrRecv
        set pA := Ratchet.rootKdf W.C.F rk0
          (W.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))
            (W.C.pubKey (Ratchet.clampScalar k.spkPriv))).toList
        set sA0 := (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
          stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
          ephA ⟨pA.2, 0#32⟩).setUnacknowledgedPreKeyMessage
        have hInitSess :
            initializeInitiatorSession W.C (pqxdhSpqrSession W) ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ ⟨b.spkPub⟩
              rk0 ck0 pqr0 coinsA =
            .ok (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
              stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
              ephA ⟨pA.2, 0#32⟩) := by
          dsimp only [initializeInitiatorSession, KeyPair.generate, b, honestBundle,
            keyPairOf, pA]
          rw [hstA0, rootCreateChain_honest W.C hXnz rk0 (Ratchet.keyToBytesVec32 coinsA) k.spkPriv]
          rfl
        rw [hInitSess] at hIS
        injection hIS with hpair
        obtain ⟨hx, hg⟩ := Prod.mk.inj hpair
        subst hx hg
        have hpqLe : pqMsg.length ≤ 64 := by omega
        set mk := ((⟨pA.2, 0#32⟩ : ChainKey).messageKeys W.C.F).generateKeys W.C.F salt
        set ctext := aesCbcEncrypt W.C.E mk.cipherKey mk.iv pt
        set msg := SignalMessage.new W.C.F protoSignalCodec currentVersion mk.macKey
          (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B) ephA.publicKey 0#32 0#32
          ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg
        have hFrom :
            Mut.exec OutgoingTripleRatchet.fromSessionState sA0 =
            (.ok ⟨ephA, ⟨pA.2, 0#32⟩, 0, stA0, currentVersion, ⟨idA.publicKey⟩, ⟨⟨b.idPub⟩⟩⟩,
             { sA0 with pqRatchetState := [] }) := rfl
        have hEnc :
            SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W) ((pqxdhSessionParams W).sendAddrs .A)
              pt rs.toList sA0 =
            (.ok msg,
             { (((SessionState.new currentVersion ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pA.1
                  stA0).addReceiverChain ⟨b.spkPub⟩ ⟨ck0, 0#32⟩).setSenderChain
                  ephA ⟨HKDF.bytesToKey32
                    (Ratchet.chainHmac W.C.F pA.2 Ratchet.chainKeySeed), 1#32⟩
                ).setUnacknowledgedPreKeyMessage
                with pqRatchetState := stA1 }) := by
          have hSpqrSendPan := spqrPq_sendPanics_false_of_send_some W stA0 rs.toList hSpqrSend
          unfold SessionState.messageEncrypt
          rw [hFrom]
          dsimp only [OutgoingTripleRatchet.encrypt,
            Mut.exec, ExceptT.run, StateT.run, Id.run,
            monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
            ExceptT.lift, Functor.map, StateT.map,
            bind, Bind.bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
            pure, Pure.pure, ExceptT.pure, StateT.bind, StateT.pure,
            get, getThe, MonadStateOf.get, StateT.get]
          simp only [hSpqrSendPan, Bool.false_eq_true, ↓reduceIte]
          rw [hSpqrSend]
          rfl
        unfold pqSendModel at hsend
        dsimp only at hsend
        rw [hEnc] at hsend
        have hremId : sA0.remoteIdentity = some ⟨⟨b.idPub⟩⟩ := rfl
        have hpend : sA0.pendingPreKey = true := rfl
        have htrustA₁ :
            ({ stA with peerId := some ⟨⟨b.idPub⟩⟩,
                        session := some (initiatorRecordExtras stA.me b ⟨u8Vec 32 hdr.ekAPk⟩
                                           (u8Vec 1568 hdr.kemCt),
                                         ⟨.A, sA0, 0, [0]⟩) } : PqParty).trusts ⟨⟨b.idPub⟩⟩ =
              true := by
          simp [PqParty.trusts]
        rw [hremId] at hsend
        dsimp only at hsend
        rw [htrustA₁, hpend] at hsend
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hsend
        injection hsend with hsend'
        injection hsend' with hrw
        have hw : w = wirePrekey :: firstMessageBody
            (initiatorRecordExtras stA.me b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt))
            sA0 msg :=
          (Prod.mk.inj hrw).2.symm
        set m : PreKeyMessageFields :=
          { regId := stA.me.regId
            opkId := b.opk.map Prod.fst
            spkId := k.spkId
            kpkId := k.kpkId
            kyberCt := u8Vec 1568 hdr.kemCt
            baseKey := u8Vec 32 hdr.ekAPk
            idPub := idA.publicKey.bytes
            inner := msg.serialized }
        have hopk : m.opkId = k.opk.map Prod.fst := by
          dsimp only [m, b, honestBundle]
          cases k.opk <;> rfl
        refine ⟨m, hw, ?_, rfl, rfl, hopk, ?_⟩
        · exact signalMessage_new_firstMsg_length_lt W.C.F
            LibsignalTripleRatchetRepr.uuidTryParse .A .B
            mk.macKey ephA.publicKey W.C.E mk.cipherKey mk.iv pt ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg
            hpt hpqLe
        · intro stB₁ hmark
          have hrt : (signalWireCodec protoSignalCodec).parse
              ((signalWireCodec protoSignalCodec).encode
                ⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
                  serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩ ctext) =
              some (⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
                serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩, ctext) :=
            LibsignalSession.signalRoundTripShort_proto
              ⟨currentVersion, ephA.publicKey, 0#32, 0#32, pqMsg,
                serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B⟩ ctext
              (signalWireShort_firstMsg LibsignalTripleRatchetRepr.uuidTryParse .A .B
                ephA.publicKey W.C.E
                mk.cipherKey mk.iv pt pqMsg hpt hpqLe)
          have htf : SignalMessage.tryFrom protoSignalCodec m.inner = .ok msg :=
            tryFrom_new W.C.F currentVersion mk.macKey
              (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
              ephA.publicKey 0#32 0#32 ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg hrt
          have hAcc :
              SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W stB.me k m) = some dk :=
            initiateKeys_acceptKeys_roundtrip X W stA.me stB.me k spkSig kpkSig t dk hdr
              msg.serialized hXcomm hXnz hKyber hCanon hAes hsigs hIK
          have hRecvState : ∃ xB gB,
              recvPrekeyState X W .B stB.me k m rc = some (some (xB, gB, pt)) := ⟨_, _, by
            unfold recvPrekeyState
            rw [htf]
            simp only [m, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
            rw [hAcc]
            dsimp only
            set st0 : SessionState Bytes :=
              initializeRecipientSession (pqxdhSpqrSession W) ⟨(keyPairOf W.C stB.me.idPriv).publicKey⟩
                ⟨⟨idA.publicKey.bytes⟩⟩ (keyPairOf W.C k.spkPriv) rk0 ck0 pqr0
            have hrc1 : rootCreateChain W.C rk0 msg.senderRatchetKey
                (keyPairOf W.C k.spkPriv).privateKey = .ok (pA.1, ⟨pA.2, 0#32⟩) := by
              change rootCreateChain W.C rk0
                ⟨W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))⟩
                ⟨Ratchet.clampScalar k.spkPriv⟩ = .ok (pA.1, ⟨pA.2, 0#32⟩)
              rw [rootCreateChain_honest W.C hXnz rk0 k.spkPriv (Ratchet.keyToBytesVec32 coinsA),
                hXcomm k.spkPriv (Ratchet.keyToBytesVec32 coinsA)]
            have hrc2 : rootCreateChain W.C pA.1 msg.senderRatchetKey
                (KeyPair.generate W.C rc).privateKey =
                .ok (let p := Ratchet.rootKdf W.C.F pA.1
                       (W.C.X (Ratchet.clampScalar (Ratchet.keyToBytesVec32 rc))
                         (W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA)))).toList
                     (p.1, ⟨p.2, 0#32⟩)) := by
              change rootCreateChain W.C pA.1
                ⟨W.C.pubKey (Ratchet.clampScalar (Ratchet.keyToBytesVec32 coinsA))⟩
                ⟨Ratchet.clampScalar (Ratchet.keyToBytesVec32 rc)⟩ = _
              exact rootCreateChain_honest W.C hXnz pA.1 (Ratchet.keyToBytesVec32 rc) (Ratchet.keyToBytesVec32 coinsA)
            have hmac : msg.verifyMacWithAddresses W.C.F ((pqxdhSessionParams W).expectedAddrs .B)
                ⟨⟨idA.publicKey.bytes⟩⟩ ⟨(keyPairOf W.C stB.me.idPriv).publicKey⟩ mk.macKey =
                true := by
              change msg.verifyMacWithAddresses W.C.F
                (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
                ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ mk.macKey = true
              exact verifyMacWithAddresses_new W.C.F protoSignalCodec currentVersion mk.macKey
                (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B)
                (serializedPartyAddresses LibsignalTripleRatchetRepr.uuidTryParse .A .B) ephA.publicKey 0#32 0#32
                ctext ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩ pqMsg (addrsOk_refl _)
            have hcbc : aesCbcDecrypt W.C.D mk.cipherKey mk.iv msg.ciphertext = some pt :=
              aesCbcDecrypt_aesCbcEncrypt' hAes mk.cipherKey mk.iv pt
            have hver : ¬ (st0.version.toNat ≠ msg.messageVersion.toNat) := by
              intro h; exact h rfl
            have hcnt : ¬ (msg.counter < (0#32 : BitVec 32)) := by
              change ¬ ((0#32 : BitVec 32) < 0#32); decide
            have hsub0 : (msg.counter - 0#32).toNat = 0 := by
              change ((0#32 : BitVec 32) - 0#32).toNat = 0; decide
            have hdrop : (1 - 5 : Nat) = 0 := rfl
            have hnext : (⟨pA.2, 0#32⟩ : ChainKey).nextChainKey W.C.F =
                .ok ⟨HKDF.bytesToKey32 (Ratchet.chainHmac W.C.F pA.2 Ratchet.chainKeySeed), 1#32⟩ :=
              rfl
            have hSpqrRecvPan := spqrPq_recvPanics_false_of_recv_ok W stB0 pqMsg hSpqrRecv
            unfold SessionState.tryDecryptFromRecord
            simp only [hver, ↓reduceIte]
            dsimp only [st0, initializeRecipientSession]
            rw [hstB0]
            dsimp only [SessionState.tryDecryptWithState, TripleRatchet.fromSessionState,
              SessionState.takeRatchetState, SessionState.takePqRatchetState,
              TripleRatchet.decrypt, TripleRatchet.onRatchet, zoom,
              RatchetState.ensureReceiverChain, RatchetState.findReceiverChainKey,
              RatchetState.findReceiverChainIndex, List.findIdx?, List.findIdx?.go,
              RatchetState.dhRatchetStep, RatchetState.takeRootKey,
              RatchetState.evictReceiverChains, maxReceiverChains,
              RatchetState.consumeMessageKey, RatchetState.advanceChain,
              RatchetState.setReceiverChainKey,
              SessionState.new, SessionState.setSenderChain,
              Mut.exec, ExceptT.run, StateT.run, Id.run,
              monadLift, MonadLift.monadLift, MonadLiftT.monadLift, liftM,
              ExceptT.lift, Functor.map, StateT.map,
              bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, get, getThe, MonadStateOf.get,
              StateT.get, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet,
              StateT.modifyGet, liftE]
            rw [hrc1]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
            rw [hrc2]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
              List.nil_append, List.length_singleton]
            simp only [hdrop, List.drop_zero, hcnt, hsub0, maxForwardJumps, Nat.not_lt_zero,
              RatchetState.advanceChain, ↓reduceIte]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE]
            rw [hnext]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
              List.findIdx?.go]
            simp only [beq_self_eq_true, ↓reduceIte]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, liftE,
              List.getElem?_cons_zero, List.set]
            rw [show msg.pqRatchet = pqMsg from rfl]
            simp only [hSpqrRecvPan, Bool.false_eq_true, ↓reduceIte]
            rw [hSpqrRecv]
            dsimp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont,
              pure, ExceptT.pure, StateT.bind, StateT.pure, StateT.map,
              get, getThe, MonadStateOf.get, StateT.get, set, StateT.set]
            rw [hmac, hcbc]
            rfl⟩
          obtain ⟨xB, gB, hRecvState⟩ := hRecvState
          have htrustB : stB.trusts ⟨⟨m.idPub⟩⟩ = true := by
            simp [PqParty.trusts, hpeerB]
          have hkeysFor : preKeysNamedBy stB m = some k := by
            change keysAt stB m.spkId m.kpkId m.opkId = some k
            rw [hopk]
            exact hkeysAt
          unfold pqRecvPrekeyModel
          rw [htf]
          dsimp only
          rw [htrustB]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [hsessB, hkeysFor, hpB]
          dsimp only
          rw [hRecvState]
          dsimp only
          rw [hmark]
          rfl

end CryptoVerification.SignalSession
