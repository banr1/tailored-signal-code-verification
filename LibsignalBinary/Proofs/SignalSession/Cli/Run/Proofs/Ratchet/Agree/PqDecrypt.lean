/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Common
import LibsignalBinary.Proofs.E2E.Run.RecvPure
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.Commit

@[expose] public section

set_option autoImplicit false

/-!
# PQXDH Model Agreement for `decrypt_signal`

Proves `pqDecryptSignalAgrees_decSigDef_aux`, relating `decrypt_signal` on an encoded `PqParty`
directory to the PQXDH game transition.
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

theorem pqDecryptSignalAgrees_decSigDef_aux (S : RunSem) (W : PEParams)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (hS : S.decryptSignal = decSigDef W Scope)
    (hinj : Slots.EncodeInjOn Scope) (hcov : RatchetScopeCoversPq W Scope) :
    RunRefine.PqDecryptSignalAgrees S W := by
  intro st c rc msg hwf _hc htry
  rw [hS]
  have hload : Slots.loadRec Scope (runFiles (pqRecvInputs W st (wireWhisper :: c) rc))
      (addrValE st.party.other) =
      .ok (st.session.map fun (x, g) => E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g) :=
    Slots.loadRec_pqRecv hinj W st (wireWhisper :: c) rc (fun x g hs => hcov st x g hwf hs)
      (Slots.pqSessBytes_le_fileCapBytes hwf)
  have hpeer : StoresGhost.opened.identity.peer cliIo.rd
      (runFiles (pqRecvInputs W st (wireWhisper :: c) rc)) (addrValE st.party.other) =
      .ok st.peerId :=
    idPeer_of_get_pqIdBytes (Slots.pqIdGet_recv W st (wireWhisper :: c) rc)
  unfold decSigDef pqxdhExpectedOutcome pqRecvWhisperModel
  rw [messageDecryptSignal_eq_flat, E2E.Run.coinsOf_keyToBytes32]
  unfold decryptFlat cliAnswers decSigKey
  rw [E2E.Run.coinsOf_keyToBytes32, hload]
  rcases hsess : st.session with _ | ⟨x, g⟩
  · rfl
  · obtain ⟨_, hg_party, _⟩ := hwf.1 x g hsess
    rw [htry]
    dsimp only [Option.map_some]
    unfold SessionRecord.tryDecryptFromRecord pqxdhSessionDecryptModel
    have hst : (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g).currentSession =
        some { state := g.session
               pendingPreKey := if g.session.pendingPreKey then some x.pending else none
               pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
               localRegistrationId := x.localRegistrationId
               remoteRegistrationId := x.remoteRegistrationId
               aliceBaseKey := x.aliceBaseKey } := rfl
    rw [hst]
    dsimp only
    rw [← hg_party, serializeAddrVals_expectedAddrs_pq W g.party, tryDecrypt_spqrV1W_eq_spqrPq]
    rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨ed | pt, s'⟩
    · dsimp only
      cases ed <;> rfl
    · obtain ⟨_, ⟨k, hk⟩, hpend'⟩ := tryDecryptFromRecord_ok_fields hdec
      rw [hg_party]
      dsimp only [Option.bind]
      rw [hk]
      have htrust : StoresGhost.opened.identity.trusted cliIo.rd
          (runFiles (pqRecvInputs W st (wireWhisper :: c) rc)) (addrValE st.party.other) k =
          .ok (st.trusts k) := by
        rw [trusted_of_peer hpeer]
        rfl
      dsimp only
      rw [htrust]
      cases st.trusts k
      · rfl
      · obtain ⟨sv, hsv⟩ : ∃ sv,
            StoresGhost.opened.identity.saveAns cliIo.rd
              (runFiles (pqRecvInputs W st (wireWhisper :: c) rc))
              (addrValE st.party.other) k = .ok sv :=
          ⟨_, saveAns_of_peer hpeer k⟩
        let g' : GhostState (List (BitVec 8)) := { g with session := s' }
        have hg_eq : GhostState.mk st.party s' g.epoch g.chainEpochs = g' := by
          cases g; dsimp only at hg_party; subst hg_party; rfl
        let rec' : SessionRecord (List (BitVec 8)) :=
          ⟨some { state := s'
                  pendingPreKey := none
                  pendingKyberPreKey := none
                  localRegistrationId := x.localRegistrationId
                  remoteRegistrationId := x.remoteRegistrationId
                  aliceBaseKey := x.aliceBaseKey }⟩
        have hrec : E2E.Record.encodeRecord rec' = encodeRecordUnderExtras (fun _ => x) g' := by
          rw [E2E.RecordX.encodeRecordX_eq_toRecord]
          unfold E2E.Record.toRecord E2E.RecordX.extrasOf E2E.RecordX.toSessionExtras g'
          dsimp only
          rw [hpend']
          rfl
        have hwrites := cliFinal_fullTrace_namedWrites hpeer k .receiving rec'
        have hfiles : (pqRecvInputs W st (wireWhisper :: c) rc).files =
            encodeDir W st ++ [(coinsFile, HMAC.keyToBytes32 rc)] := by
          simp [pqRecvInputs, pqInputs]
        rw [hsv, hg_eq]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        let st' : PqParty := { st with peerId := some k, session := some (x, g') }
        change observe (pqRecvInputs W st (wireWhisper :: c) rc).files
            (some (some (namedWrites (cliFinal
              (runFiles (pqRecvInputs W st (wireWhisper :: c) rc))
              (fullTrace (addrValE st.party.other) k .receiving rec')).writes, pt))) =
          observe (pqRecvInputs W st (wireWhisper :: c) rc).files
            (some (some (encodeDir W st', pt)))
        rw [hwrites, hrec]
        unfold observe
        rw [hfiles]
        exact congrArg (Outcome.exited 0 pt)
          (filesOf_pqCommit W st (HMAC.keyToBytes32 rc) k x g')

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
