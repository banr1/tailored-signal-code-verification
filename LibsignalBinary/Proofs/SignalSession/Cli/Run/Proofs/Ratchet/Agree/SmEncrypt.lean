/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon

@[expose] public section

set_option autoImplicit false

/-!
# Signal-Message Model Agreement for `encrypt`

Proves `smEncryptAgrees_encDef_aux`, relating `encrypt` on a single-session store directory to the
Signal-Message ratchet model.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Agree

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine

private theorem checkedAddSecs_zero :
    SystemTime.unixEpoch.checkedAddSecs (0#64 : BitVec 64).toNat =
      some SystemTime.unixEpoch := by decide

private theorem checkedAddSecs_maxAge :
    SystemTime.unixEpoch.checkedAddSecs maxUnacknowledgedSessionAge =
      some ⟨BitVec.ofInt 64 maxUnacknowledgedSessionAge, 0#32⟩ := by decide

private theorem maxAge_lt_unixEpoch :
    (⟨BitVec.ofInt 64 maxUnacknowledgedSessionAge, 0#32⟩ : SystemTime).lt
      SystemTime.unixEpoch = false := by decide

theorem wrapFlat_sm_eq (W : PEParams) (g : GhostState (List (BitVec 8)))
    (m coins : List (BitVec 8)) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hpq : otr.pqrState = []) :
    wrapFlat (E := Unit) W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) m
      (addrValE g.party.other) (addrValE g.party)
      unixEpoch coins (Reach.sessionOf g) otr =
      match Mut.exec (OutgoingTripleRatchet.encrypt (spqrOffSessionParams W.C).C (spqrOffSessionParams W.C).codec
          (spqrOffSessionParams W.C).spqr m (g.session.encryptAddresses ((spqrOffSessionParams W.C).sendAddrs g.party)) ())
          otr with
      | (.error e, _) => .error (ApiError.ofProtocol e)
      | (.ok sm, otr') =>
        .ok (if g.session.pendingPreKey then
            .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion 0#32 none 0#32
              none placeholderBaseKey otr'.localIdentityKey sm)
          else .signalMessage sm, otr') := by
  have hunix : unixEpoch = SystemTime.unixEpoch := rfl
  have hpC : (spqrOffSessionParams W.C).C = W.C := rfl
  have hpCodec : (spqrOffSessionParams W.C).codec = protoSignalCodec := rfl
  have hpSpqr : (spqrOffSessionParams W.C).spqr = spqrOffB := rfl
  rw [hunix, hpC, hpCodec, hpSpqr]
  unfold wrapFlat SessionState.encryptAddresses
  have hpend : (Reach.sessionOf g).pendingPreKey =
      (if g.session.pendingPreKey then some ⟨none, 0#32, placeholderBaseKey, 0#64⟩ else none) := rfl
  have hkyb : (Reach.sessionOf g).pendingKyberPreKey = none := rfl
  have hloc : (Reach.sessionOf g).localRegistrationId = 0#32 := rfl
  rw [hpend, hkyb, hloc]
  cases g.session.pendingPreKey
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold execOk
    rw [otr_encrypt_spqrV1W_empty W protoSignalCodec m none coins otr hpq]
    rcases Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec
        spqrOffB m none ()) otr with ⟨e | sm, otr'⟩ <;> rfl
  · simp only [↓reduceIte]
    rw [checkedAddSecs_zero]
    dsimp only
    rw [checkedAddSecs_maxAge]
    dsimp only
    rw [maxAge_lt_unixEpoch]
    simp only [Bool.false_eq_true, ↓reduceIte, serializeAddrVals_sendAddrs_sm W.C g.party]
    unfold execOk
    rw [otr_encrypt_spqrV1W_empty W protoSignalCodec m ((spqrOffSessionParams W.C).sendAddrs g.party) coins otr hpq]
    rcases Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec
        spqrOffB m ((spqrOffSessionParams W.C).sendAddrs g.party) ()) otr with ⟨e | sm, otr'⟩ <;> rfl

theorem smEncryptAgrees_encDef_aux (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmEncryptAgrees S W.C := by
  intro g m hg _hm
  rw [hS]
  have hload : Slots.loadRec Scope (runFiles (smSendInputs g m)) (addrValE g.party.other) =
      .ok (some ⟨some (Reach.sessionOf g)⟩) := by
    rw [← Reach.toRecord_extrasM_eq g]
    exact Slots.loadRec_sm hinj g (.send (partyAddress g.party.other)) [] m (hcov g hg)
      (Slots.smSessBytes_le_fileCapBytes W.C hg)
  have hpeer : StoresGhost.opened.identity.peer cliIo.rd (runFiles (smSendInputs g m))
      (addrValE g.party.other) = .ok (some (partyIdentityKey g.party.other)) :=
    idPeer_of_get_serialize (Slots.smIdGet g (.send (partyAddress g.party.other)) [] m)
  have hpq : g.session.pqRatchetState = [] := Reach.reach_pqRatchetState_eq_nil W.C hg
  have hrem_g : g.session.remoteIdentity = some (partyIdentityKey g.party.other) :=
    Reach.reach_remoteIdentity_eq W.C hg
  unfold encDef smSendModel sendModelSpqrOff SessionState.messageEncrypt
  rw [messageEncrypt_eq_flat]
  unfold encryptFlat cliAnswers encKey
  rw [hload]
  have hst : (Reach.sessionOf g).state = g.session := rfl
  dsimp only
  rw [hst]
  rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨ef | otr, taken⟩
  · have hexFrom : execOk OutgoingTripleRatchet.fromSessionState g.session = .error ef := by
      simp [execOk, hfrom]
    rw [hexFrom]
    dsimp only
    cases ef <;> rfl
  · have hexFrom : execOk OutgoingTripleRatchet.fromSessionState g.session = .ok (otr, taken) := by
      simp [execOk, hfrom]
    obtain ⟨hrem1, hrem2, hpend_t, hloc_o, hver_o, hpq_o⟩ := fromSessionState_ok_fields hfrom
    have hkey : otr.remoteIdentityKey = partyIdentityKey g.party.other := by
      rw [hrem_g] at hrem1
      exact Option.some.inj hrem1.symm
    rw [hexFrom]
    dsimp only
    rw [hrem2, hkey]
    dsimp only
    rw [wrapFlat_sm_eq W g m [] otr (hpq_o.trans hpq)]
    rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt (spqrOffSessionParams W.C).C (spqrOffSessionParams W.C).codec
        (spqrOffSessionParams W.C).spqr m (g.session.encryptAddresses ((spqrOffSessionParams W.C).sendAddrs g.party)) ())
        otr with ⟨ee | sm, otr'⟩
    · dsimp only
      cases ee <;> rfl
    · obtain ⟨hver', hloc', _⟩ := otr_encrypt_preserves_meta henc
      have htrust : StoresGhost.opened.identity.trusted cliIo.rd (runFiles (smSendInputs g m))
          (addrValE g.party.other) (partyIdentityKey g.party.other) = .ok true := by
        rw [trusted_of_peer hpeer]
        simp
      have hsave : StoresGhost.opened.identity.saveAns cliIo.rd (runFiles (smSendInputs g m))
          (addrValE g.party.other) (partyIdentityKey g.party.other) = .ok .newOrUnchanged := by
        rw [saveAns_of_peer hpeer]
        simp
      dsimp only
      rw [htrust, hsave]
      dsimp only [finish, Option.map]
      have hwire : ctWire (if g.session.pendingPreKey then
          .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion 0#32 none 0#32
            none placeholderBaseKey otr'.localIdentityKey sm)
        else .signalMessage sm) = smSendWire g sm.serialized := by
        rw [hver'.trans hver_o, hloc'.trans hloc_o]
        unfold smSendWire smPreKeyWire
        cases g.session.pendingPreKey <;> rfl
      have hrec : E2E.Record.encodeRecord
          ⟨some { Reach.sessionOf g with state := otr'.applyToSessionState taken }⟩ =
          E2E.encodeRecord { g with session := otr'.applyToSessionState taken } := by
        have hsess : ({ Reach.sessionOf g with state := otr'.applyToSessionState taken } :
            Session (List (BitVec 8))) =
            Reach.sessionOf { g with session := otr'.applyToSessionState taken } := by
          unfold Reach.sessionOf
          have hp' : (otr'.applyToSessionState taken).pendingPreKey = g.session.pendingPreKey :=
            hpend_t
          dsimp only
          rw [hp']
        rw [hsess, Reach.encodeRecord_eq_toRecord, Reach.toRecord_extrasM_eq]
      have hwrites := cliFinal_fullTrace_namedWrites hpeer (partyIdentityKey g.party.other) .sending
        ⟨some { Reach.sessionOf g with state := otr'.applyToSessionState taken }⟩
      change observe (smSendInputs g m).files
          (some (some (namedWrites (cliFinal (runFiles (smSendInputs g m))
            (fullTrace (addrValE g.party.other) (partyIdentityKey g.party.other) .sending
              ⟨some { Reach.sessionOf g with state := otr'.applyToSessionState taken }⟩)).writes,
            ctWire _))) = _
      rw [hwrites, hrec, hwire]
      rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
