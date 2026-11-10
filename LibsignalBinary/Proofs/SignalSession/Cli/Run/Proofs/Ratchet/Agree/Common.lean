/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.Agree.CommitEval
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

@[expose] public section

set_option autoImplicit false

/-!
# Shared Model-Agreement Definitions and Store Bridges

Store-answer mirrors, address serialization lemmas, session metadata invariants, and SPQR /
`RunFilesOk` bridges shared across the PQXDH and Signal-Message ratchet agreement proofs.
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Agree

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.E2E.Epochs CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## Store-step mirrors for `encrypt` and `decrypt_signal` -/

noncomputable def cliAnswers (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) (k : Option IdentityKey) : StoreAnswers (List (BitVec 8)) Unit where
  loadSession := Slots.loadRec Scope F peer
  isTrustedIdentity := match k with
    | some k => StoresGhost.opened.identity.trusted cliIo.rd F peer k
    | none => .ok false
  saveIdentity := match k with
    | some k => StoresGhost.opened.identity.saveAns cliIo.rd F peer k
    | none => .ok .newOrUnchanged
  storeSession := .ok ()

def cliStep (F : FsFiles) (g : StoresGhost) : StoreCall AddrVal (List (BitVec 8)) → StoresGhost
  | .saveIdentity rem k => { g with identity := g.identity.saveUpd cliIo.rd F rem k }
  | .storeSession rem r =>
    { g with sessions := g.sessions.put (Cli.addressText rem) (E2E.Record.encodeRecord r) }
  | _ => g

def cliFinal (F : FsFiles) (calls : List (StoreCall AddrVal (List (BitVec 8)))) : StoresGhost :=
  calls.foldl (cliStep F) StoresGhost.opened

noncomputable def encKey (Scope : SessionRecord (List (BitVec 8)) → Prop) (F : FsFiles)
    (peer : AddrVal) : Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match r.currentSession with
    | some s =>
      match execOk OutgoingTripleRatchet.fromSessionState s.state with
      | .ok (_, taken) => taken.remoteIdentity
      | .error _ => none
    | none => none
  | _ => none

noncomputable def encDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (ptext coins : List (BitVec 8)) :
    SlotAns CiphertextMessage :=
  match LibsignalSessionApi.messageEncrypt W.C protoSignalCodec (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse)) (cliAnswers Scope F peer (encKey Scope F peer))
      ptext peer me unixEpoch coins with
  | (.ok m, calls) => some (some (cliFinal F calls, m))
  | (.error .panic, _) => none
  | (.error _, _) => some none

def RatchetScopeCoversPq (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (st : PqParty) x g, PqxdhPartyInSpecDomain W st → st.session = some (x, g) →
    Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g)

def RatchetScopeCoversSm (C : Crypto) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ g : GhostState (List (BitVec 8)), Reach (spqrOffSessionParams C) g →
    Scope (E2E.Record.toRecord E2E.Record.extrasM g)

noncomputable def decSigKey (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    Option IdentityKey :=
  match Slots.loadRec Scope F peer with
  | .ok (some r) =>
    match LibsignalSessionApi.SessionRecord.tryDecryptFromRecord W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse) peer me) msg
        (LibsignalTripleRatchetRepr.coinsOf coins) r with
    | .ok (_, r') => r'.currentSession.bind (·.state.remoteIdentity)
    | .error _ => none
  | _ => none

noncomputable def decSigDef (W : PEParams) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (F : FsFiles) (peer me : AddrVal) (msg : SignalMessage) (coins : List (BitVec 8)) :
    SlotAns (List (BitVec 8)) :=
  match LibsignalSessionApi.messageDecryptSignal W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F peer (decSigKey W Scope F peer me msg coins)) msg peer me
      (LibsignalTripleRatchetRepr.coinsOf coins) with
  | (.ok pt, calls) => some (some (cliFinal F calls, pt))
  | (.error .panic, _) => none
  | (.error _, _) => some none

/-! ## Address serialization -/

theorem partyAddr_eq_addrValE (P : Party) : Slots.partyAddr P = addrValE P := rfl

theorem serializeAddrVals_addrValE (s r : Party) :
    serializeAddrVals (serviceIdParse uuidTryParse) (addrValE s) (addrValE r) =
      serializedPartyAddresses uuidTryParse s r := by
  cases s <;> cases r <;> rfl

theorem serializeAddrVals_sendAddrs_sm (C : Crypto) (P : Party) :
    serializeAddrVals (serviceIdParse uuidTryParse) (addrValE P) (addrValE P.other) =
      (spqrOffSessionParams C).sendAddrs P := by
  rw [serializeAddrVals_addrValE]
  cases P <;> rfl

theorem serializeAddrVals_expectedAddrs_sm (C : Crypto) (P : Party) :
    serializeAddrVals (serviceIdParse uuidTryParse) (addrValE P.other) (addrValE P) =
      (spqrOffSessionParams C).expectedAddrs P := by
  rw [serializeAddrVals_addrValE]
  cases P <;> rfl

theorem serializeAddrVals_sendAddrs_pq (W : PEParams) (P : Party) :
    serializeAddrVals (serviceIdParse uuidTryParse) (addrValE P) (addrValE P.other) =
      (pqxdhSessionParams W).sendAddrs P := by
  rw [serializeAddrVals_addrValE]
  cases P <;> rfl

theorem serializeAddrVals_expectedAddrs_pq (W : PEParams) (P : Party) :
    serializeAddrVals (serviceIdParse uuidTryParse) (addrValE P.other) (addrValE P) =
      (pqxdhSessionParams W).expectedAddrs P := by
  rw [serializeAddrVals_addrValE]
  cases P <;> rfl

/-! ## Identity store answers and `cliFinal` on `fullTrace` -/

theorem serialize_identityKey_ne_nil (k : IdentityKey) : k.serialize ≠ [] := by
  intro h
  have hlen := PublicKey.serialize_length k.publicKey
  change k.serialize.length = 33 at hlen
  rw [h] at hlen
  cases hlen

theorem record_decodeIdentityKey_serialize (k : IdentityKey) :
    Cli.record RecordCodecs.decodeIdentityKey k.serialize = .ok (some k) := by
  cases hs : k.serialize with
  | nil => exact absurd hs (serialize_identityKey_ne_nil k)
  | cons b bs =>
    simp only [Cli.record]
    rw [← hs, RecordCodecs.decodeIdentityKey_serialize k]

theorem idPeer_of_get_serialize {F : FsFiles} {P : Party} {k : IdentityKey}
    (hg : StoresGhost.opened.identity.peers.get cliIo.rd F (Slots.partyAddr P).name =
      .ok k.serialize) :
    StoresGhost.opened.identity.peer cliIo.rd F (addrValE P) = .ok (some k) := by
  unfold IdGhost.peer
  rw [← partyAddr_eq_addrValE, hg]
  exact record_decodeIdentityKey_serialize k

theorem idPeer_of_get_pqIdBytes {F : FsFiles} {st : PqParty}
    (hg : StoresGhost.opened.identity.peers.get cliIo.rd F (Slots.partyAddr st.party.other).name =
      .ok (Slots.pqIdBytes st)) :
    StoresGhost.opened.identity.peer cliIo.rd F (addrValE st.party.other) = .ok st.peerId := by
  unfold IdGhost.peer
  rw [← partyAddr_eq_addrValE, hg]
  unfold Slots.pqIdBytes
  cases st.peerId with
  | none => rfl
  | some k => exact record_decodeIdentityKey_serialize k

@[simp, reducible]
def trustedVal (p : Option IdentityKey) (k : IdentityKey) : Bool :=
  match p with | none => true | some known => decide (known = k)

@[simp, reducible]
def saveAnsVal (p : Option IdentityKey) (k : IdentityKey) : IdentityChange :=
  match p with
  | some known => if known = k then .newOrUnchanged else .replacedExisting
  | none => .newOrUnchanged

theorem trusted_of_peer {F : FsFiles} {peer : AddrVal} {p : Option IdentityKey}
    (hp : StoresGhost.opened.identity.peer cliIo.rd F peer = .ok p) (k : IdentityKey) :
    StoresGhost.opened.identity.trusted cliIo.rd F peer k = .ok (trustedVal p k) := by
  unfold IdGhost.trusted
  rw [hp]
  rfl

theorem saveAns_of_peer {F : FsFiles} {peer : AddrVal} {p : Option IdentityKey}
    (hp : StoresGhost.opened.identity.peer cliIo.rd F peer = .ok p) (k : IdentityKey) :
    StoresGhost.opened.identity.saveAns cliIo.rd F peer k = .ok (saveAnsVal p k) := by
  unfold IdGhost.saveAns
  rw [hp]
  rfl

theorem saveUpd_of_peer {F : FsFiles} {peer : AddrVal} {p : Option IdentityKey}
    (hp : StoresGhost.opened.identity.peer cliIo.rd F peer = .ok p) (k : IdentityKey) :
    StoresGhost.opened.identity.saveUpd cliIo.rd F peer k =
      { StoresGhost.opened.identity with
        peers := StoresGhost.opened.identity.peers.put peer.name k.serialize } := by
  unfold IdGhost.saveUpd
  rw [hp]

theorem cliFinal_fullTrace_namedWrites {F : FsFiles} {P : Party} {p : Option IdentityKey}
    (hp : StoresGhost.opened.identity.peer cliIo.rd F (addrValE P) = .ok p)
    (k : IdentityKey) (dir : Direction) (r : SessionRecord (List (BitVec 8))) :
    namedWrites (cliFinal F (fullTrace (addrValE P) k dir r)).writes =
      [(identityFile (partyAddressName P), k.serialize),
       (sessionFile (partyAddress P), E2E.Record.encodeRecord r)] := by
  have hf : cliFinal F (fullTrace (addrValE P) k dir r) =
      { StoresGhost.opened with
        identity := { StoresGhost.opened.identity with
                      peers := StoresGhost.opened.identity.peers.put (utf8 (partyAddressName P)) k.serialize }
        sessions := StoresGhost.opened.sessions.put
                      (Cli.addressText (addrValE P)) (E2E.Record.encodeRecord r) } := by
    unfold cliFinal fullTrace
    simp only [List.foldl_cons, List.foldl_nil, cliStep, saveUpd_of_peer hp]
    rfl
  rw [hf]
  exact namedWrites_id_session P k.serialize (E2E.Record.encodeRecord r)

/-! ## Session and ratchet metadata preservation -/

attribute [local simp] exec_pure exec_throw exec_get exec_set exec_modify exec_modifyGet
  exec_liftE exec_bind exec_map exec_onRatchet

theorem fromSessionState_ok_fields {PQ : Type} [Inhabited PQ]
    {st taken : SessionState PQ} {otr : OutgoingTripleRatchet PQ}
    (h : Mut.exec OutgoingTripleRatchet.fromSessionState st = (.ok otr, taken)) :
    st.remoteIdentity = some otr.remoteIdentityKey ∧
      taken.remoteIdentity = some otr.remoteIdentityKey ∧
      taken.pendingPreKey = st.pendingPreKey ∧
      otr.localIdentityKey = st.localIdentity ∧
      otr.sessionVersion = BitVec.ofNat 8 st.version.toNat ∧
      otr.pqrState = st.pqRatchetState := by
  unfold OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [exec_bind, exec_get, exec_modifyGet, hsc] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure, Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem otr_encrypt_preserves_meta {PQ PQC : Type} {C : Crypto} {codec : SignalMessageProtoCodec}
    {spqr : Spqr PQ PQC} {m : List (BitVec 8)} {addrs : Option (List (BitVec 8))} {coins : PQC}
    {otr otr' : OutgoingTripleRatchet PQ} {sm : SignalMessage}
    (h : Mut.exec (OutgoingTripleRatchet.encrypt C codec spqr m addrs coins) otr = (.ok sm, otr')) :
    otr'.sessionVersion = otr.sessionVersion ∧
      otr'.localIdentityKey = otr.localIdentityKey ∧
      otr'.remoteIdentityKey = otr.remoteIdentityKey := by
  unfold OutgoingTripleRatchet.encrypt at h
  simp only [exec_bind, exec_get] at h
  split_ifs at h
  · simp at h
  · rcases hspqr : spqr.send otr.pqrState coins with _ | ⟨pq', pqrKey, pqrMsg⟩
    · simp [hspqr] at h
    · simp only [hspqr, exec_bind] at h
      rcases hnext : otr.senderChainKey.nextChainKey C.F with _ | nextCk
      · simp [hnext] at h
      · simp only [hnext, exec_liftE, exec_pure, exec_set, Prod.mk.injEq, Except.ok.injEq] at h
        rcases h with ⟨_, rfl⟩
        exact ⟨rfl, rfl, rfl⟩

theorem tryDecryptFromRecord_ok_fields {PQ PQC : Type} [Inhabited PQ]
    {C : Crypto} {spqr : Spqr PQ PQC} {expected : Option (List (BitVec 8))}
    {msg : SignalMessage} {msgType : MessageType} {coins : BitVec 256}
    {st st' : SessionState PQ} {pt : List (BitVec 8)}
    (h : SessionState.tryDecryptFromRecord C spqr expected msg msgType coins st = (.ok pt, st')) :
    st'.remoteIdentity = st.remoteIdentity ∧
      (∃ k, st'.remoteIdentity = some k) ∧
      st'.pendingPreKey = false := by
  unfold SessionState.tryDecryptFromRecord at h
  split at h
  · simp at h
  · split at h
    · rename_i ptext updated hdec
      injection h with _ hst'
      subst hst'
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hdec
      simp only [exec_bind, exec_modifyGet, exec_get, exec_pure] at hdec
      cases hrem : st.remoteIdentity with
      | none => simp [hrem] at hdec
      | some remote =>
        simp only [hrem, exec_pure, exec_liftE] at hdec
        rcases htr : (TripleRatchet.decrypt C spqr expected msg msgType coins).exec
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
             st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · rw [htr] at hdec; simp at hdec
        · rw [htr] at hdec
          simp only [exec_modify, Prod.mk.injEq, Except.ok.injEq] at hdec
          rcases hdec with ⟨_, rfl⟩
          exact ⟨rfl, ⟨remote, rfl⟩, rfl⟩
    · simp at h

/-! ## SPQR V1 and `pqxdhSpqrSession` bridges -/

theorem otr_encrypt_spqrV1W_eq_spqrPq (W : PEParams) (codec : SignalMessageProtoCodec)
    (m : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8)) :
    OutgoingTripleRatchet.encrypt W.C codec (pqxdhSpqrModel W).spqr m addrs coins =
      OutgoingTripleRatchet.encrypt W.C codec (pqxdhSpqrSession W) m addrs coins := rfl

theorem tryDecrypt_spqrV1W_eq_spqrPq (W : PEParams) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (rc : BitVec 256)
    (st : SessionState (List (BitVec 8))) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrModel W).spqr expected msg msgType rc st =
      SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) expected msg msgType rc st := rfl

theorem otr_encrypt_spqrV1W_empty (W : PEParams) (codec : SignalMessageProtoCodec)
    (m : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (hpq : otr.pqrState = []) :
    Mut.exec (OutgoingTripleRatchet.encrypt W.C codec (pqxdhSpqrModel W).spqr m addrs coins) otr =
      Mut.exec (OutgoingTripleRatchet.encrypt W.C codec spqrOffB m addrs ()) otr := by
  obtain ⟨hsend, _, hnpan⟩ := LibsignalSpqrV1.spqrV1_emptyOk W.C.F W.Q.K
  have hp1 : ((pqxdhSpqrModel W).spqr).sendPanics otr.pqrState coins = false := by
    rw [hpq]
    exact Bool.eq_false_iff.mpr (hnpan coins)
  have hs1 : ((pqxdhSpqrModel W).spqr).send otr.pqrState coins = some ([], none, []) := by
    rw [hpq]
    exact hsend coins
  have hp2 : spqrOffB.sendPanics otr.pqrState () = false := rfl
  have hs2 : spqrOffB.send otr.pqrState () = some ([], none, []) := by
    rw [hpq]; rfl
  unfold OutgoingTripleRatchet.encrypt
  simp only [exec_bind, exec_get, exec_pure, hp1, hp2, Bool.false_eq_true, ↓reduceIte, hs1, hs2]

theorem tryDecrypt_spqrV1W_empty (W : PEParams) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (msgType : MessageType) (rc : BitVec 256)
    (st : SessionState (List (BitVec 8))) (hpq : st.pqRatchetState = []) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrModel W).spqr expected msg msgType rc st =
      SessionState.tryDecryptFromRecord W.C spqrOffB expected msg msgType rc st := by
  obtain ⟨hrecv, hnpan⟩ := LibsignalSpqrV1.spqrV1_recvEmptyOk W.C.F W.Q.K
  unfold SessionState.tryDecryptFromRecord
  split
  · rfl
  · suffices
      Mut.exec (SessionState.tryDecryptWithState W.C (pqxdhSpqrModel W).spqr expected msg msgType rc) st =
        Mut.exec (SessionState.tryDecryptWithState W.C spqrOffB expected msg msgType rc) st by
      rw [this]
    unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
      SessionState.takeRatchetState SessionState.takePqRatchetState
    simp only [exec_bind, exec_modifyGet, exec_get, exec_pure]
    cases st.remoteIdentity with
    | none => rfl
    | some remote =>
      simp only [exec_pure, hpq]
      suffices ∀ (rs : RatchetState),
          Mut.exec (TripleRatchet.decrypt W.C (pqxdhSpqrModel W).spqr expected msg msgType rc)
            ⟨rs, [], st.localIdentity, remote⟩ =
          Mut.exec (TripleRatchet.decrypt W.C spqrOffB expected msg msgType rc)
            ⟨rs, [], st.localIdentity, remote⟩ by
        rw [this]
      intro rs
      unfold TripleRatchet.decrypt
      simp only [exec_bind, exec_onRatchet]
      rcases (RatchetState.ensureReceiverChain W.C msg.senderRatchetKey rc).exec rs with
        ⟨e1 | ck, rs1⟩
      · rfl
      · dsimp only
        rcases (RatchetState.consumeMessageKey W.C.F msg.senderRatchetKey ck msg.counter msgType).exec rs1 with
          ⟨e2 | mkg, rs2⟩
        · rfl
        · dsimp only
          simp only [exec_get]
          have hp1 : ((pqxdhSpqrModel W).spqr).recvPanics [] msg.pqRatchet = false :=
            Bool.eq_false_iff.mpr (hnpan msg.pqRatchet)
          have hp2 : spqrOffB.recvPanics [] msg.pqRatchet = false := rfl
          have hr1 : ((pqxdhSpqrModel W).spqr).recv [] msg.pqRatchet = spqrOffB.recv [] msg.pqRatchet :=
            hrecv msg.pqRatchet
          simp only [hp1, hp2, Bool.false_eq_true, ↓reduceIte, hr1]

/-! ## `RunFilesOk` on SM and PQXDH game inputs -/

theorem runFilesOk_smSend {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {extra : FsFiles → Prop} (hS : S.filesOk = Slots.filesOk₀ Scope extra)
    (g : GhostState (List (BitVec 8))) (m : List (BitVec 8))
    (hSc : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hex : extra (runFiles (smSendInputs g m)))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    RunFilesOk S (smSendInputs g m) :=
  Slots.runFilesOk_of_peer (.send (partyAddress g.party.other)) rfl rfl
    (RunRefine.ownAddr_smSend g m)
    (hS ▸ ⟨Slots.filesOkPeer_smSend g m hSc hcap, Slots.distinctSid_party g.party, hex⟩)

theorem runFilesOk_smRecv {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {extra : FsFiles → Prop} (hS : S.filesOk = Slots.filesOk₀ Scope extra)
    (g : GhostState (List (BitVec 8))) (c : List (BitVec 8)) (rc : BitVec 256)
    (hSc : Scope (E2E.Record.toRecord E2E.Record.extrasM g))
    (hex : extra (runFiles (smRecvInputs g c rc)))
    (hcap : (E2E.encodeRecord g).length ≤ fileCapBytes) :
    RunFilesOk S (smRecvInputs g c rc) :=
  Slots.runFilesOk_of_peer (.recv (partyAddress g.party.other)) rfl rfl
    (RunRefine.ownAddr_smRecv g c rc)
    (hS ▸ ⟨Slots.filesOkPeer_smRecv g c rc hSc hcap, Slots.distinctSid_party g.party, hex⟩)

theorem runFilesOk_pqInit {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {extra : FsFiles → Prop} (hS : S.filesOk = Slots.filesOk₀ Scope extra)
    (W : PEParams) (st : PqParty) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen)
    (hSc : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hex : extra (runFiles (pqInitInputs W st b t)))
    (hcap : (Slots.pqSessBytes st).length ≤ fileCapBytes) :
    RunFilesOk S (pqInitInputs W st b t) :=
  Slots.runFilesOk_of_peer (.init (partyAddress st.party.other) bundleDir) rfl rfl
    (RunRefine.ownAddr_pqInit W st b t)
    (hS ▸ ⟨Slots.filesOkPeer_pqInit W st b t hSc hcap, Slots.distinctSid_party st.party, hex⟩)

theorem runFilesOk_pqSend {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {extra : FsFiles → Prop} (hS : S.filesOk = Slots.filesOk₀ Scope extra)
    (W : PEParams) (st : PqParty) (m : List (BitVec 8)) (r : List.Vector (BitVec 8) 64)
    (hSc : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hex : extra (runFiles (pqSendInputs W st m r)))
    (hcap : (Slots.pqSessBytes st).length ≤ fileCapBytes) :
    RunFilesOk S (pqSendInputs W st m r) :=
  Slots.runFilesOk_of_peer (.send (partyAddress st.party.other)) rfl rfl
    (RunRefine.ownAddr_pqSend W st m r)
    (hS ▸ ⟨Slots.filesOkPeer_pqSend W st m r hSc hcap, Slots.distinctSid_party st.party, hex⟩)

theorem runFilesOk_pqRecv {S : RunSem} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {extra : FsFiles → Prop} (hS : S.filesOk = Slots.filesOk₀ Scope extra)
    (W : PEParams) (st : PqParty) (c : List (BitVec 8)) (rc : BitVec 256)
    (hSc : ∀ x g, st.session = some (x, g) →
      Scope (E2E.Record.toRecord (E2E.RecordX.extrasOf fun _ => x) g))
    (hex : extra (runFiles (pqRecvInputs W st c rc)))
    (hcap : (Slots.pqSessBytes st).length ≤ fileCapBytes) :
    RunFilesOk S (pqRecvInputs W st c rc) :=
  Slots.runFilesOk_of_peer (.recv (partyAddress st.party.other)) rfl rfl
    (RunRefine.ownAddr_pqRecv W st c rc)
    (hS ▸ ⟨Slots.filesOkPeer_pqRecv W st c rc hSc hcap, Slots.distinctSid_party st.party, hex⟩)

end CryptoVerification.SignalSession.Cli.RunProofs.Agree
