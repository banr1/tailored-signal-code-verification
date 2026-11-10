/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalPublicApi
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Panic Tightness and Wire-Length Bounds for `encrypt`

Pure model lemmas for `signal_session_ratchet::encrypt`: shows `EncryptGhost.sendPanics` implies a
model panic, proves model panics depend solely on `answers.loadSession`, and bounds serialized
`PreKeySignalMessage` wire output below `2^42` bytes.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

/-- `OutgoingTripleRatchet.encrypt` returns `.error .panic` whenever `spqr.sendPanics` holds on
the current `pqrState` and `coins`. -/
theorem otrEncrypt_panic_of_sendPanics {PQ PQC : Type} (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC) (ptext : List (BitVec 8)) (addresses : Option (List (BitVec 8)))
    (coins : PQC) (otr : OutgoingTripleRatchet PQ)
    (hp : spqr.sendPanics otr.pqrState coins = true) :
    execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext addresses coins) otr =
      .error .panic := by
  unfold OutgoingTripleRatchet.encrypt execOk Mut.exec
  dsimp only [ExceptT.run, ExceptT.mk, ExceptT.lift, StateT.run, StateT.bind, StateT.map,
    Functor.map, ExceptT.bind, ExceptT.bindCont, StateT.pure, ExceptT.pure, StateT.get, liftM,
    monadLift, MonadLift.monadLift, MonadLiftT.monadLift, get, getThe, MonadStateOf.get, bind,
    pure, throw, throwThe, MonadExceptOf.throw]
  rw [hp]
  rfl

/-- `x.sendPanics S answers` implies `(x.model C S uuidParse answers).1 = .error .panic`. -/
theorem sendPanics_imp_model_panic (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : EncryptGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (hp : x.sendPanics S answers) :
    (x.model C S uuidParse answers).1 = .error .panic := by
  obtain ⟨st, hst, hsp⟩ := hp
  simp only [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat]
  simp only [EncryptGhost.sendState, loadedSession] at hst
  rcases hl : answers.loadSession with e | (_ | r)
  · simp [hl] at hst
  · simp [hl] at hst
  · simp only [hl] at hst ⊢
    rcases hc : r.currentSession with _ | s
    · simp [hc] at hst
    · simp only [hc] at hst ⊢
      rcases hf : execOk OutgoingTripleRatchet.fromSessionState s.state with ef | ⟨otr, taken⟩
      · simp [hf] at hst
      · simp only [hf] at hst ⊢
        rcases hk : taken.remoteIdentity with _ | k
        · simp [hk, Option.isNone] at hst
        · simp only [hk, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hst ⊢
          have hsp' : S.spqr.sendPanics otr.pqrState x.rest = true := by
            rcases hpq : s.pendingPreKey with _ | items
            · simp only [hpq] at hst
              injection hst with hst_eq; subst hst_eq; exact hsp
            · simp only [hpq] at hst
              rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
              · simp [h1] at hst
              · rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry
                · simp [h1, h2] at hst
                · simp only [h1, h2, Option.bind_some] at hst
                  split at hst
                  · simp at hst
                  · injection hst with hst_eq; subst hst_eq; exact hsp
          rcases hpq : s.pendingPreKey with _ | items
          · simp only [wrapFlat, hpq, otrEncrypt_panic_of_sendPanics _ _ _ _ _ _ _ hsp',
              ApiError.ofProtocol]
          · simp only [hpq] at hst
            rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
            · simp [h1] at hst
            · rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry
              · simp [h1, h2] at hst
              · simp only [h1, h2, Option.bind_some] at hst
                by_cases hlt : expiry.lt x.now = true
                · simp [hlt] at hst
                · have hltF : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
                  simp only [wrapFlat, hpq, h1, h2, hltF, Bool.false_eq_true, ↓reduceIte,
                    otrEncrypt_panic_of_sendPanics _ _ _ _ _ _ _ hsp', ApiError.ofProtocol]

/-- Post-`wrapFlat` steps 6–8 in `encryptFlat` never produce `.error .panic`, so whether
`(x.model C S uuidParse answers).1 = .error .panic` depends solely on `answers.loadSession`. -/
theorem model_panic_of_loadSession_eq (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : EncryptGhost) (a₁ a₂ : StoreAnswers (List (BitVec 8)) Unit)
    (hl : a₁.loadSession = a₂.loadSession)
    (hp : (x.model C S uuidParse a₁).1 = .error .panic) :
    (x.model C S uuidParse a₂).1 = .error .panic := by
  simp only [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat] at hp ⊢
  rw [← hl]
  rcases hload : a₁.loadSession with e | (_ | r)
  · simp [hload] at hp
  · simp [hload] at hp
  · simp only [hload] at hp ⊢
    rcases hc : r.currentSession with _ | s
    · simp [hc] at hp
    · simp only [hc] at hp ⊢
      rcases hf : execOk OutgoingTripleRatchet.fromSessionState s.state with ef | ⟨otr, taken⟩
      · simp only [hf] at hp ⊢; exact hp
      · simp only [hf] at hp ⊢
        rcases hk : taken.remoteIdentity with _ | k
        · rfl
        · simp only [hk] at hp ⊢
          rcases hw : wrapFlat (E := Unit) C protoSignalCodec S.spqr
              (serializeAddrVals (serviceIdParse uuidParse)) x.ptext x.rem.val x.loc.val
              x.now x.rest s otr with ew | ⟨msg, otr'⟩
          · simp only [hw] at hp ⊢; exact hp
          · simp only [hw] at hp
            exfalso
            rcases hat : a₁.isTrustedIdentity with _ | (_ | _) <;>
              rcases has : a₁.saveIdentity with _ | _ <;>
              rcases hast : a₁.storeSession with _ | ⟨⟩ <;>
              simp [hat, has, hast] at hp

/-- If `x.model` returns `.ok (.preKeySignalMessage m)` from a loaded record `r` whose pending
Kyber ciphertext is `< 2^32` bytes, and `m.message.serialized.length < 2^40`, then
`m.serialized.length < 2^42`. -/
theorem model_preKey_serialized_lt (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser)
    (x : EncryptGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (r : SessionRecord (List (BitVec 8))) (m : PreKeySignalMessage)
    (hl : answers.loadSession = .ok (some r))
    (hkp : ∀ s k, r.currentSession = some s → s.pendingKyberPreKey = some k →
      k.ciphertext.length < 2 ^ 32)
    (hok : (x.model C S uuidParse answers).1 = .ok (.preKeySignalMessage m))
    (hmsg : m.message.serialized.length < 2 ^ 40) :
    m.serialized.length < 2 ^ 42 := by
  simp only [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, hl] at hok
  rcases hc : r.currentSession with _ | s
  · simp [hc] at hok
  · simp only [hc] at hok
    rcases hf : execOk OutgoingTripleRatchet.fromSessionState s.state with ef | ⟨otr, taken⟩
    · simp [hf] at hok
    · simp only [hf] at hok
      rcases hk : taken.remoteIdentity with _ | k
      · simp [hk] at hok
      · simp only [hk] at hok
        rcases hw : wrapFlat (E := Unit) C protoSignalCodec S.spqr
            (serializeAddrVals (serviceIdParse uuidParse)) x.ptext x.rem.val x.loc.val
            x.now x.rest s otr with ew | ⟨cm, otr'⟩
        · simp [hw] at hok
        · simp only [hw] at hok
          have hcm : cm = .preKeySignalMessage m := by
            rcases a_t : answers.isTrustedIdentity with _ | (_ | _)
            · simp [a_t] at hok
            · simp [a_t] at hok
            · simp only [a_t] at hok
              rcases a_s : answers.saveIdentity with _ | _
              · simp [a_s] at hok
              · simp only [a_s] at hok
                rcases a_st : answers.storeSession with _ | ⟨⟩
                · simp [a_st] at hok
                · simp only [a_st] at hok
                  exact Except.ok.inj hok
          subst hcm
          simp only [wrapFlat] at hw
          rcases hp : s.pendingPreKey with _ | items
          · rcases he : execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr
              with _ | ⟨sm, otr''⟩ <;> simp [hp, he] at hw
          · simp only [hp] at hw
            rcases h1 : SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat with _ | ts
            · simp [h1] at hw
            · simp only [h1] at hw
              rcases h2 : ts.checkedAddSecs maxUnacknowledgedSessionAge with _ | expiry
              · simp [h2] at hw
              · simp only [h2] at hw
                by_cases h3 : expiry.lt x.now = true
                · simp [h3] at hw
                · simp only [Bool.eq_false_iff.mpr h3, Bool.false_eq_true, ↓reduceIte] at hw
                  rcases he : execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
                      (serializeAddrVals (serviceIdParse uuidParse) x.loc.val x.rem.val) x.rest) otr
                    with _ | ⟨sm, otr''⟩
                  · simp [he] at hw
                  · simp only [he] at hw
                    have hm_eq : PreKeySignalMessage.new otr''.sessionVersion s.localRegistrationId
                        items.preKeyId items.signedPreKeyId
                        (s.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩)
                        items.baseKey otr''.localIdentityKey sm = m := by
                      injection hw with hpair
                      injection hpair with hmsg_eq _
                      injection hmsg_eq
                    rw [← hm_eq]
                    have hsm_eq : sm = m.message := by
                      rw [← hm_eq]; rfl
                    refine preKeySignalMessage_new_serialized_length_lt _ _ _ _ _ _ _ _
                      (hsm_eq ▸ hmsg) ?_
                    intro kp hkp_eq
                    rcases hsk : s.pendingKyberPreKey with _ | k0
                    · simp [hsk] at hkp_eq
                    · simp only [hsk, Option.map_some, Option.some.injEq] at hkp_eq
                      rw [← hkp_eq]
                      exact hkp s k0 hc hsk

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
