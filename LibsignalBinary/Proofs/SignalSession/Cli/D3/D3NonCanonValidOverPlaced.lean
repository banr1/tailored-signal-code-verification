/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.E2E.Epochs
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverAgreePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverFoldsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3NonCanonValidOverSlotPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3StageP3Prev1Placed
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import LibsignalBinary.Proofs.SignalSession.Cli.D3.PreKeyGeneralAux
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.S0Lemmas.AgreeStore
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds

/-!
# Non-Matching Session Pre-Key Overwrite Domain Helpers & `DecPkOkOverV4`

Defines `DecPkOkOverV4` (`DecPkOkOverD3` strengthened with version-4 active sessions) and
proves `reachPq_sessionVersion_placed` and `decPkOkOverV4_pqRecv` on reachable PQXDH
non-matching session states.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi CryptoVerification RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.E2E CryptoVerification.E2E.Bin CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator CryptoVerification.E2E.Pqxdh.WireEntries CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine CryptoVerification.SignalSession.Cli.RunProofs

/-! ## 1. Reachable Session Version 4 & `DecPkOkOverV4` -/

theorem decPkOk0_of_d3_pkToE {W : PEParams} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage} {m : PreKeyMessageFields}
    (hd3 : DecPkOkD3 W Scope F peer me pm) (hpk : pkToE? pm = some m) :
    DecPkOk₀ W Scope F peer me (pmOfE m pm.message) := by
  obtain ⟨m0, _, _, hpk0, hdec0⟩ := hd3; cases Option.some.inj (hpk0.symm.trans hpk); exact hdec0

/-- `DecPkOkOverD3` strengthened with `ScopeOverIn r` (`s.state.sessionVersion = 4#32`). -/
def DecPkOkOverV4 (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (pm : PreKeySignalMessage) : Prop :=
  DecPkOkOverD3 W Scope F peer me pm ∧
    ∃ r s, Slots.loadRec Scope F peer = .ok (some r) ∧ r.currentSession = some s ∧
      ScopeOverIn r ∧ ¬ SessMatchesPm s pm

private theorem fromSessionState_outgoing_sessionVersion {PQ : Type} [Inhabited PQ] (record : SessionState PQ) :
    (Mut.exec OutgoingTripleRatchet.fromSessionState record).2.sessionVersion = record.sessionVersion := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState
  simp only [E2E.Epochs.exec_bind, E2E.Epochs.exec_get]
  rcases record.senderChain with _ | sc
  · rfl
  · simp only [E2E.Epochs.exec_bind, E2E.Epochs.exec_modifyGet, E2E.Epochs.exec_get]
    split_ifs
    · rfl
    · rcases record.remoteIdentity with _ | remote <;> rfl

private theorem messageEncrypt_sessionVersion_placed {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC) (addresses : Option (List (BitVec 8)))
    (ptext : List (BitVec 8)) (coins : PQC) (record : SessionState PQ) :
    (SessionState.messageEncrypt C codec spqr addresses ptext coins record).2.sessionVersion = record.sessionVersion := by
  unfold SessionState.messageEncrypt
  have hf := fromSessionState_outgoing_sessionVersion record
  rcases h1 : Mut.exec OutgoingTripleRatchet.fromSessionState record with ⟨_ | session, taken⟩
  · rfl
  · rw [h1] at hf; dsimp only at hf ⊢
    rcases Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr ptext (record.encryptAddresses addresses) coins) session with ⟨_ | _, _⟩
    · rfl
    · exact hf

private theorem tryDecryptFromRecord_sessionVersion_placed {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (ciphertext : SignalMessage) (msgType : LibsignalSession.MessageType) (coins : BitVec 256) (record : SessionState PQ) :
    (SessionState.tryDecryptFromRecord C spqr expected ciphertext msgType coins record).2.sessionVersion = record.sessionVersion := by
  unfold SessionState.tryDecryptFromRecord; split_ifs; · rfl
  · unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState SessionState.takeRatchetState SessionState.takePqRatchetState
    simp only [E2E.Epochs.exec_bind, E2E.Epochs.exec_modifyGet, E2E.Epochs.exec_get]
    rcases record.remoteIdentity with _ | remote
    · rfl
    · dsimp only; simp only [E2E.Epochs.exec_pure]
      rcases Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins)
          ⟨⟨record.rootKey, record.senderChain, record.receiverChains, record.previousCounter, maxForwardJumps⟩,
            record.pqRatchetState, record.localIdentity, remote⟩ with ⟨_ | _, _⟩ <;> rfl

theorem reachPq_sessionVersion_placed {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState (List (BitVec 8))} (hr : ReachablePqxdhSession W me x g) : g.session.sessionVersion = 4#32 := by
  induction hr with
  | initiate X P me b t x g hinit =>
    unfold initiateState at hinit
    rcases h1 : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with _ | p
    · rw [h1] at hinit; nomatch hinit
    · rw [h1] at hinit; dsimp only [initializeInitiatorSession] at hinit
      rcases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 p.1.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with _ | ⟨_, _⟩
      · rw [hrc] at hinit; nomatch hinit
      · rw [hrc] at hinit
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Option.some.injEq, Prod.mk.injEq] at hinit
        rcases hinit with ⟨_, rfl⟩; rfl
  | recvPrekey X P me k m rc x g pt hrecv =>
    unfold recvPrekeyState at hrecv
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · rw [htf] at hrecv; nomatch hrecv
    · rw [htf] at hrecv; dsimp only at hrecv; split_ifs at hrecv
      · nomatch hrecv
      · rcases ha : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
        · rw [ha] at hrecv; nomatch hrecv
        · rw [ha] at hrecv; dsimp only at hrecv
          let rec0 := initializeRecipientSession (pqxdhSpqrSession W) { publicKey := (keyPairOf W.C me.idPriv).publicKey }
            { publicKey := { bytes := m.idPub } } (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hv := tryDecryptFromRecord_sessionVersion_placed W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc rec0
          rcases htd : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc rec0 with ⟨err | _, _⟩
          · rw [htd] at hrecv; cases err <;> nomatch hrecv
          · rw [htd] at hrecv hv; simp only [Option.some.injEq, Prod.mk.injEq] at hrecv
            rcases hrecv with ⟨_, rfl, _⟩; exact hv
  | @send _ _ g₀ m r _ _ ih =>
    rw [E2E.Record.send_eq_afterSend]
    have hv := messageEncrypt_sessionVersion_placed (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g₀.party) m r g₀.session
    rcases _ : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g₀.party) m r g₀.session with ⟨res, _⟩
    cases res <;> simp_all [GhostState.afterSend]
  | @recv _ _ g₀ g' c rc _ _ _ hrec ih =>
    rw [E2E.Record.receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · rw [htf] at hrec; nomatch hrec
    · rw [htf] at hrec; dsimp only at hrec
      have hv := tryDecryptFromRecord_sessionVersion_placed (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g₀.party) msg .whisper rc g₀.session
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).expectedAddrs g₀.party) msg .whisper rc g₀.session with ⟨_ | m, s⟩
      · rw [hd] at hrec; nomatch hrec
      · rw [hd] at hrec hv
        have hg' : (g₀.afterRecv msg.senderRatchetKey msg.counter s m).1 = g' := congrArg Prod.fst (Option.some.inj hrec)
        have hafter : (g₀.afterRecv msg.senderRatchetKey msg.counter s m).1.session = s := by
          unfold GhostState.afterRecv; dsimp only
        rw [← hg', hafter]; exact hv.trans ih

theorem decPkOkOverV4_pqRecv (W : PEParams) (st : PqParty)
    (x : RecordExtras) (g : GhostState (List (BitVec 8)))
    (body : List (BitVec 8)) (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (rc : BitVec 256)
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hnot : ¬ PqSessionMatches x g m) (hparse : Pksm.pksmParse body = some pm)
    (hpk : pkToE? pm = some m) (hm : m.inner.length + 2048 < 2 ^ 32) :
    DecPkOkOverV4 W Slots.scopeIn (runFiles (pqRecvInputs W st (wirePrekey :: body) rc))
      (RunRefine.addrValE st.party.other) (RunRefine.addrValE st.party) pm := by
  have hover := decPkOkOverD3_pqRecv W st x g body pm m rc hwf hsess hnot hparse hpk hm
  have hload := DecPkS0.loadRec_pqRecv_eq encodeInjOn_scopeIn_placed (ratchetScopeCoversPq_scopeIn_placed W)
    st (wirePrekey :: body) rc hwf
  rw [hsess] at hload; dsimp only [Option.map_some] at hload
  have hIn := ratchetScopeCoversPq_scopeIn_placed W st x g hwf hsess
  rcases (hwf.1 x g hsess).1 with ⟨g₀, hr, _, hsess₀⟩
  have hver4 : g.session.sessionVersion = 4#32 := hsess₀ ▸ reachPq_sessionVersion_placed hr
  refine ⟨hover, E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g, _, hload, rfl,
    ⟨hIn, fun s hs => ?_⟩, not_sessMatchesPm_toRecord_of_not_pqSessionMatches x g hIn hpk hnot _ rfl⟩
  dsimp only [E2E.Record.toRecord] at hs; injection hs with hs_eq; subst hs_eq; exact hver4

end LibsignalBinary.Proofs.SignalSession.Cli.D3
