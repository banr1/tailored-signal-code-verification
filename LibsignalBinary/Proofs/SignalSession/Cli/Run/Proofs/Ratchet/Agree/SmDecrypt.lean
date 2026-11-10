/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
import LibsignalBinary.Proofs.E2E.Run.RecvPure

@[expose] public section

set_option autoImplicit false

/-!
# Signal-Message Model Agreement for `decrypt_signal`

Proves `smDecryptSignalAgrees_decSigDef_aux`, relating `decrypt_signal` on a single-session store
directory to the Signal-Message ratchet model.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Agree

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine

theorem smDecryptSignalAgrees_decSigDef_aux (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversSm W.C Scope) :
    RunRefine.SmDecryptSignalAgrees S W.C := by
  intro g c rc msg hg _hc htry
  rw [hS]
  have hload : Slots.loadRec Scope (runFiles (smRecvInputs g c rc)) (addrValE g.party.other) =
      .ok (some ⟨some (Reach.sessionOf g)⟩) := by
    rw [← Reach.toRecord_extrasM_eq g]
    exact Slots.loadRec_sm hinj g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc)
      (msgTypeWhisper :: c) (hcov g hg) (Slots.smSessBytes_le_fileCapBytes W.C hg)
  have hpeer : StoresGhost.opened.identity.peer cliIo.rd (runFiles (smRecvInputs g c rc))
      (addrValE g.party.other) = .ok (some (partyIdentityKey g.party.other)) :=
    idPeer_of_get_serialize
      (Slots.smIdGet g (.recv (partyAddress g.party.other)) (HMAC.keyToBytes32 rc) (msgTypeWhisper :: c))
  have hpq : g.session.pqRatchetState = [] := Reach.reach_pqRatchetState_eq_nil W.C hg
  have hrem_g : g.session.remoteIdentity = some (partyIdentityKey g.party.other) :=
    Reach.reach_remoteIdentity_eq W.C hg
  unfold decSigDef smRecvModel recvModelSpqrOff
  have hpC : (spqrOffSessionParams W.C).C = W.C := rfl
  have hcodec : (spqrOffSessionParams W.C).codec = protoSignalCodec := rfl
  have hpSpqr : (spqrOffSessionParams W.C).spqr = spqrOffB := rfl
  rw [hpC, hcodec, hpSpqr, htry, messageDecryptSignal_eq_flat, E2E.Run.coinsOf_keyToBytes32]
  unfold decryptFlat cliAnswers decSigKey
  rw [E2E.Run.coinsOf_keyToBytes32, hload]
  unfold SessionRecord.tryDecryptFromRecord
  have hst : (Reach.sessionOf g).state = g.session := rfl
  dsimp only
  rw [hst, serializeAddrVals_expectedAddrs_sm W.C g.party,
      tryDecrypt_spqrV1W_empty W ((spqrOffSessionParams W.C).expectedAddrs g.party) msg .whisper rc g.session hpq]
  rcases hdec : SessionState.tryDecryptFromRecord W.C spqrOffB
      ((spqrOffSessionParams W.C).expectedAddrs g.party) msg .whisper rc g.session with ⟨ed | pt, s'⟩
  · dsimp only
    cases ed <;> rfl
  · obtain ⟨hrem', _, hpend'⟩ := tryDecryptFromRecord_ok_fields hdec
    have hs'_rem : s'.remoteIdentity = some (partyIdentityKey g.party.other) := hrem'.trans hrem_g
    dsimp only [Option.bind]
    rw [hs'_rem]
    have htrust : StoresGhost.opened.identity.trusted cliIo.rd (runFiles (smRecvInputs g c rc))
        (addrValE g.party.other) (partyIdentityKey g.party.other) = .ok true := by
      rw [trusted_of_peer hpeer]
      simp
    have hsave : StoresGhost.opened.identity.saveAns cliIo.rd (runFiles (smRecvInputs g c rc))
        (addrValE g.party.other) (partyIdentityKey g.party.other) = .ok .newOrUnchanged := by
      rw [saveAns_of_peer hpeer]
      simp
    dsimp only
    rw [htrust, hsave]
    dsimp only [finish, Option.map, id]
    let sess' : Session (List (BitVec 8)) :=
      { (Reach.sessionOf g) with
        state := s'
        pendingPreKey := none
        pendingKyberPreKey := none }
    let rec' : SessionRecord (List (BitVec 8)) := ⟨some sess'⟩
    have hrec : E2E.Record.encodeRecord rec' = E2E.encodeRecord { g with session := s' } := by
      have hsess : sess' = Reach.sessionOf { g with session := s' } := by
        unfold sess' Reach.sessionOf
        dsimp only
        rw [hpend']
        rfl
      change E2E.Record.encodeRecord ⟨some sess'⟩ = _
      rw [hsess, Reach.encodeRecord_eq_toRecord, Reach.toRecord_extrasM_eq]
    have hwrites := cliFinal_fullTrace_namedWrites hpeer (partyIdentityKey g.party.other) .receiving rec'
    change observe (smRecvInputs g c rc).files
        (some (some (namedWrites (cliFinal (runFiles (smRecvInputs g c rc))
          (fullTrace (addrValE g.party.other) (partyIdentityKey g.party.other) .receiving rec')).writes, pt))) = _
    rw [hwrites, hrec]
    rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
