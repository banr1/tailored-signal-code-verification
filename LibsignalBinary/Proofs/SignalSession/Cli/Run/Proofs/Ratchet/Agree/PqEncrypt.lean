/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Commit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Model Agreement for `encrypt`

Proves `pqEncryptAgrees_encDef_aux`, relating `encrypt` on an encoded `PqParty` directory to the
PQXDH game transition.
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

private theorem checkedAddSecs_zero_pq :
    SystemTime.unixEpoch.checkedAddSecs (0#64 : BitVec 64).toNat =
      some SystemTime.unixEpoch := by decide

private theorem checkedAddSecs_maxAge_pq :
    SystemTime.unixEpoch.checkedAddSecs maxUnacknowledgedSessionAge =
      some ⟨BitVec.ofInt 64 maxUnacknowledgedSessionAge, 0#32⟩ := by decide

private theorem maxAge_lt_unixEpoch_pq :
    (⟨BitVec.ofInt 64 maxUnacknowledgedSessionAge, 0#32⟩ : SystemTime).lt
      SystemTime.unixEpoch = false := by decide

/-- The `Session` built by `toRecord (extrasOf fun _ => x) g`. -/
def pqSessionOf (x : RecordExtras) (g : GhostState (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { state := g.session
    pendingPreKey := if g.session.pendingPreKey then some x.pending else none
    pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
    localRegistrationId := x.localRegistrationId
    remoteRegistrationId := x.remoteRegistrationId
    aliceBaseKey := x.aliceBaseKey }

theorem toRecord_extrasOf_const (x : RecordExtras) (g : GhostState (List (BitVec 8))) :
    E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g = ⟨some (pqSessionOf x g)⟩ := rfl

theorem wrapFlat_pq_eq (W : PEParams) (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (m coins : List (BitVec 8)) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hts : x.pending.timestamp = 0#64) :
    wrapFlat (E := Unit) W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) m
      (addrValE g.party.other) (addrValE g.party)
      unixEpoch coins (pqSessionOf x g) otr =
      match Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrSession W) m
          (g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party)) coins) otr with
      | (.error e, _) => .error (ApiError.ofProtocol e)
      | (.ok sm, otr') =>
        .ok (if g.session.pendingPreKey then
            .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion x.localRegistrationId
              x.pending.preKeyId x.pending.signedPreKeyId
              (x.kyber.map fun k => ⟨k.preKeyId, k.ciphertext⟩) x.pending.baseKey
              otr'.localIdentityKey sm)
          else .signalMessage sm, otr') := by
  have hunix : unixEpoch = SystemTime.unixEpoch := rfl
  rw [hunix]
  unfold wrapFlat pqSessionOf SessionState.encryptAddresses
  dsimp only
  cases g.session.pendingPreKey
  · simp only [Bool.false_eq_true, ↓reduceIte]
    unfold execOk
    rw [otr_encrypt_spqrV1W_eq_spqrPq]
    rcases Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrSession W) m none coins) otr with
      ⟨e | sm, otr'⟩ <;> rfl
  · simp only [↓reduceIte, hts]
    rw [checkedAddSecs_zero_pq]
    dsimp only
    rw [checkedAddSecs_maxAge_pq]
    dsimp only
    rw [maxAge_lt_unixEpoch_pq]
    simp only [Bool.false_eq_true, ↓reduceIte, serializeAddrVals_sendAddrs_pq W g.party]
    unfold execOk
    rw [otr_encrypt_spqrV1W_eq_spqrPq]
    rcases Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrSession W) m
        ((pqxdhSessionParams W).sendAddrs g.party) coins) otr with ⟨e | sm, otr'⟩ <;> rfl

theorem pqEncryptAgrees_encDef_aux (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.encrypt = encDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqEncryptAgrees S W := by
  intro st m r hwf _hm
  rw [hS]
  have hload : Slots.loadRec Scope (runFiles (pqSendInputs W st m r)) (addrValE st.party.other) =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
    Slots.loadRec_pqSend hinj W st m r (fun x g hs => hcov st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf)
  have hpeer : StoresGhost.opened.identity.peer cliIo.rd (runFiles (pqSendInputs W st m r))
      (addrValE st.party.other) = .ok st.peerId :=
    idPeer_of_get_pqIdBytes (Slots.pqIdGet_send W st m r)
  unfold encDef pqxdhExpectedOutcome pqSendModel
  rw [messageEncrypt_eq_flat]
  unfold encryptFlat cliAnswers encKey
  rw [hload]
  rcases hsess : st.session with _ | ⟨x, g⟩
  · rfl
  · obtain ⟨⟨g₀, hreach, _, hgs⟩, hg_party, _⟩ := hwf.1 x g hsess
    have hinv := Slots.PqValid.reachPq_inv hreach
    obtain ⟨_, _, _, ⟨rem, hrem₀⟩, _, _, hts, _⟩ := hinv
    have hrem_g : g.session.remoteIdentity = some rem := hgs ▸ hrem₀
    dsimp only [Option.map_some]
    rw [toRecord_extrasOf_const]
    have hst : (pqSessionOf x g).state = g.session := rfl
    dsimp only
    rw [hst]
    unfold SessionState.messageEncrypt
    rcases hfrom : Mut.exec OutgoingTripleRatchet.fromSessionState g.session with ⟨ef | otr, taken⟩
    · have hexFrom : execOk OutgoingTripleRatchet.fromSessionState g.session = .error ef := by
        simp [execOk, hfrom]
      rw [hexFrom]
      dsimp only
      cases ef <;> rfl
    · have hexFrom : execOk OutgoingTripleRatchet.fromSessionState g.session = .ok (otr, taken) := by
        simp [execOk, hfrom]
      obtain ⟨hrem1, hrem2, hpend_t, hloc_o, hver_o, _⟩ := fromSessionState_ok_fields hfrom
      have hkey : otr.remoteIdentityKey = rem := by
        rw [hrem_g] at hrem1
        exact Option.some.inj hrem1.symm
      rw [hexFrom]
      dsimp only
      rw [hrem2, hkey, hrem_g]
      dsimp only
      rw [← hg_party]
      rw [wrapFlat_pq_eq W x g m r.toList otr hts]
      rcases henc : Mut.exec (OutgoingTripleRatchet.encrypt W.C protoSignalCodec (pqxdhSpqrSession W) m
          (g.session.encryptAddresses ((pqxdhSessionParams W).sendAddrs g.party)) r.toList)
          otr with ⟨ee | sm, otr'⟩
      · dsimp only
        cases ee <;> rfl
      · obtain ⟨hver', hloc', _⟩ := otr_encrypt_preserves_meta henc
        rw [hg_party]
        have htrust : StoresGhost.opened.identity.trusted cliIo.rd
            (runFiles (pqSendInputs W st m r)) (addrValE st.party.other) rem =
            .ok (st.trusts rem) := by
          rw [trusted_of_peer hpeer]
          rfl
        dsimp only
        rw [htrust]
        cases st.trusts rem
        · rfl
        · obtain ⟨sv, hsv⟩ : ∃ sv,
              StoresGhost.opened.identity.saveAns cliIo.rd (runFiles (pqSendInputs W st m r))
                (addrValE st.party.other) rem = .ok sv :=
            ⟨_, saveAns_of_peer hpeer rem⟩
          let s' := otr'.applyToSessionState taken
          let g' : GhostState (List (BitVec 8)) := { g with session := s' }
          have hg_eq :
              GhostState.mk st.party (otr'.applyToSessionState taken) g.epoch g.chainEpochs =
                g' := by
            cases g; dsimp only at hg_party; subst hg_party; rfl
          let wire := if g.session.pendingPreKey then wirePrekey :: firstMessageBody x g.session sm
            else wireWhisper :: sm.serialized
          have hwire : ctWire (if g.session.pendingPreKey then
              .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion
                x.localRegistrationId x.pending.preKeyId x.pending.signedPreKeyId
                (x.kyber.map fun k => ⟨k.preKeyId, k.ciphertext⟩) x.pending.baseKey
                otr'.localIdentityKey sm)
            else .signalMessage sm) = wire := by
            rw [hver'.trans hver_o, hloc'.trans hloc_o]
            unfold wire firstMessageBody wirePrekey wireWhisper
            cases g.session.pendingPreKey <;> rfl
          let rec' : SessionRecord (List (BitVec 8)) :=
            ⟨some { (pqSessionOf x g) with state := s' }⟩
          have hrec : E2E.Record.encodeRecord rec' = encodeRecordUnderExtras (fun _ => x) g' := by
            have hsess : ({ (pqSessionOf x g) with state := s' } : Session (List (BitVec 8))) =
                pqSessionOf x g' := by
              unfold pqSessionOf g'
              have hp' : s'.pendingPreKey = g.session.pendingPreKey := hpend_t
              dsimp only
              rw [hp']
            rw [E2E.RecordX.encodeRecordX_eq_toRecord, toRecord_extrasOf_const]
            change E2E.Record.encodeRecord ⟨some _⟩ = _
            rw [hsess]
          have hwrites := cliFinal_fullTrace_namedWrites hpeer rem .sending rec'
          have hfiles : (pqSendInputs W st m r).files =
              encodeDir W st ++ [(coinsFile, r.toList)] := by
            simp [pqSendInputs, pqInputs]
          rw [hsv, hg_eq]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          let st' : PqParty := { st with peerId := some rem, session := some (x, g') }
          change observe (pqSendInputs W st m r).files
              (some (some (namedWrites (cliFinal (runFiles (pqSendInputs W st m r))
                (fullTrace (addrValE st.party.other) rem .sending rec')).writes, ctWire _))) =
            observe (pqSendInputs W st m r).files
              (some (some (encodeDir W st', wire)))
          rw [hwrites, hrec, hwire]
          unfold observe
          rw [hfiles]
          exact congrArg (Outcome.exited 0 wire)
            (filesOf_pqCommit W st r.toList rem x g')

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
