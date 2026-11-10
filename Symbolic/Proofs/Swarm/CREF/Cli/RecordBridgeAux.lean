/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds

/-!
# Auxiliary Session-Record Representation and Reachability Invariants

Defines `pqSession` connecting `PqParty` session state pairs `(x, g)` to `Session HwBytes`,
relates `encodeRecordUnderExtras` to `Record.encodeRecord`, and proves the structural invariant
`ReachPqInvPure` across `ReachablePqxdhSession` transitions.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

open DY.Libsignal (HwBytes)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet (SeedsLen32)
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF.TR.Pure (PureBinCanonSession slots_NonEmptyV1Q slots_DeserializeScopeP_Q
  slots_RecordScopeP)

/-! ## `Mut.exec` Unfolding Lemmas -/

theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

theorem mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

theorem mut_exec_set {σ : Type} (s' s : σ) :
    Mut.exec (set s' : Mut σ PUnit) s = (.ok (), s') := rfl

theorem mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ PUnit) s = (.ok (), f s) := rfl

theorem mut_exec_modifyGet {σ α : Type} (f : σ → α × σ) (s : σ) :
    Mut.exec (modifyGet f : Mut σ α) s = (.ok (f s).1, (f s).2) := rfl

theorem mut_exec_liftE {σ α : Type} (r : Except SignalProtocolError α) (s : σ) :
    Mut.exec (liftE r : Mut σ α) s = (r, s) := by
  cases r <;> rfl

theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec
  change (ExceptT.run (m >>= f)).run s = _
  rw [ExceptT.run_bind]
  simp only [StateT.run_bind]
  rcases (m.run).run s with ⟨r, s'⟩
  cases r <;> rfl

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set
  mut_exec_modify mut_exec_modifyGet mut_exec_liftE mut_exec_bind

theorem mut_exec_onRatchet {PQ α : Type} (m : Mut RatchetState α)
    (t : TripleRatchet PQ) :
    Mut.exec (TripleRatchet.onRatchet m) t =
      ((Mut.exec m t.ratchet).1, { t with ratchet := (Mut.exec m t.ratchet).2 }) := by
  unfold TripleRatchet.onRatchet zoom
  simp

attribute [local simp] mut_exec_onRatchet

/-! ## `pqSession` and Record Encoding -/

/-- View of a `(RecordExtras, GhostState HwBytes)` pair from `PqParty.session` as a `Session HwBytes`. -/
def pqSession (x : RecordExtras) (g : GhostState HwBytes) : Session HwBytes where
  state := g.session
  pendingPreKey := if g.session.pendingPreKey then some x.pending else none
  pendingKyberPreKey := if g.session.pendingPreKey then x.kyber else none
  localRegistrationId := x.localRegistrationId
  remoteRegistrationId := x.remoteRegistrationId
  aliceBaseKey := x.aliceBaseKey

@[simp]
theorem pqSession_state (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).state = g.session := rfl

@[simp]
theorem pqSession_localRegistrationId (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).localRegistrationId = x.localRegistrationId := rfl

@[simp]
theorem pqSession_remoteRegistrationId (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).remoteRegistrationId = x.remoteRegistrationId := rfl

@[simp]
theorem pqSession_aliceBaseKey (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).aliceBaseKey = x.aliceBaseKey := rfl

@[simp]
theorem pqSession_pendingPreKey (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).pendingPreKey =
      if g.session.pendingPreKey then some x.pending else none := rfl

@[simp]
theorem pqSession_pendingKyberPreKey (x : RecordExtras) (g : GhostState HwBytes) :
    (pqSession x g).pendingKyberPreKey =
      if g.session.pendingPreKey then x.kyber else none := rfl

theorem pqSession_pendingPreKey_of_false (x : RecordExtras) (g : GhostState HwBytes)
    (hppk : g.session.pendingPreKey = false) :
    (pqSession x g).pendingPreKey = none := by
  simp [hppk]

theorem pqSession_pendingKyberPreKey_of_false (x : RecordExtras) (g : GhostState HwBytes)
    (hppk : g.session.pendingPreKey = false) :
    (pqSession x g).pendingKyberPreKey = none := by
  simp [hppk]

theorem encodeRecordX_eq_encodeRecord_pqSession (x : RecordExtras) (g : GhostState HwBytes) :
    encodeRecordUnderExtras (fun _ => x) g =
      CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩ := by
  unfold encodeRecordUnderExtras encStateUnderExtras CryptoVerification.E2E.Record.encodeRecord
    pqSession CryptoVerification.E2E.Record.encSession
  dsimp only [Option.map_some]
  cases g.session.pendingPreKey <;> rfl

theorem encodeRecordX_clearPending_eq_storedSession
    (x : RecordExtras) (g : GhostState HwBytes) (s' : SessionState HwBytes)
    (hppk : s'.pendingPreKey = false) :
    encodeRecordUnderExtras (fun _ => x) { g with session := s' } =
      CryptoVerification.E2E.Record.encodeRecord
        ⟨some { pqSession x g with
                  state := s', pendingPreKey := none, pendingKyberPreKey := none }⟩ := by
  rw [encodeRecordX_eq_encodeRecord_pqSession]
  apply congrArg (fun s => CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩)
  simp [pqSession, hppk]

/-! ## Reachable Session Structural Invariant -/

private theorem sessionVersion_messageEncrypt_eq {PQC : Type}
    (C : Crypto) (codec : SignalMessageProtoCodec) (S : Spqr HwBytes PQC)
    (addresses : Option HwBytes) (ptext : HwBytes) (coins : PQC)
    (st st' : SessionState HwBytes) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec S addresses ptext coins st = (.ok msg, st')) :
    st'.sessionVersion = st.sessionVersion := by
  unfold SessionState.messageEncrypt OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, mut_exec_bind, mut_exec_get, mut_exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, mut_exec_pure] at h
        split at h
        · simp at h
        · simp only [Prod.mk.injEq, Except.ok.injEq] at h
          rcases h with ⟨_, rfl⟩
          rfl

private theorem sessionVersion_tryDecryptFromRecord_eq {PQC : Type}
    (C : Crypto) (S : Spqr HwBytes PQC)
    (expected : Option HwBytes) (m : SignalMessage) (msgType : MessageType) (coins : BitVec 256)
    (st st' : SessionState HwBytes) (pt : HwBytes)
    (h : SessionState.tryDecryptFromRecord C S expected m msgType coins st = (.ok pt, st')) :
    st'.sessionVersion = st.sessionVersion := by
  unfold SessionState.tryDecryptFromRecord at h
  split_ifs at h
  · simp at h
  · rcases hd : Mut.exec (SessionState.tryDecryptWithState C S expected m msgType coins) st with
      ⟨e | ptext, updated⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      rcases h with ⟨_, rfl⟩
      unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
        SessionState.takeRatchetState SessionState.takePqRatchetState at hd
      rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at hd
      · simp only [hrem, mut_exec_bind, mut_exec_modifyGet, mut_exec_get, mut_exec_pure] at hd
        rcases hdec : Mut.exec (TripleRatchet.decrypt C S expected m msgType coins)
            ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
              st.pqRatchetState, st.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
        · simp [hdec] at hd
        · rw [hdec] at hd
          simp only [mut_exec_liftE, mut_exec_modify, Prod.mk.injEq, Except.ok.injEq] at hd
          rcases hd with ⟨_, rfl⟩
          rfl

/-- Structural invariant on `(x, g)` preserved by all `ReachablePqxdhSession` transitions. -/
def ReachPqInvPure (W : PEParams) (me : LocalIdentity) (x : RecordExtras) (g : GhostState HwBytes) : Prop :=
  g.session.sessionVersion = 4#32 ∧
    SeedsLen32 g.session ∧
    g.session.receiverChains.length ≤ maxReceiverChains ∧
    g.session.localIdentity = ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ∧
    (∃ rem, g.session.remoteIdentity = some rem) ∧
    CryptoVerification.E2E.Reach.SessRepr g.session ∧
    x.localRegistrationId = me.regId ∧
    x.pending.timestamp = 0#64 ∧
    x.pending.baseKey.serialize = x.aliceBaseKey ∧
    x.aliceBaseKey.length = 33 ∧
    ∀ k, x.kyber = some k → k.ciphertext.length = 1569

theorem reachPq_inv {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState HwBytes}
    (hr : ReachablePqxdhSession W me x g) : ReachPqInvPure W me x g := by
  induction hr with
  | initiate X P me b t x g h =>
    unfold initiateState at h
    rcases hinit : SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
      _ | ⟨dk, hdr⟩
    · simp [hinit] at h
    · rw [hinit] at h; dsimp only at h
      unfold initializeInitiatorSession at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      rcases hrc : rootCreateChain W.C (HKDF.bytesToKey32 (ofU8 dk.rootKey)) ⟨b.spkPub⟩
          (KeyPair.generate W.C (HKDF.bytesToKey32 ((t.toList.drop 160).take 32))).privateKey with
        _ | ⟨rk', ck'⟩
      · simp [hrc] at h
      · rw [hrc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨?_, ?_, ?_, ?_, ⟨⟨⟨b.idPub⟩⟩, rfl⟩, ?_, rfl, rfl, rfl,
          by simp [initiatorRecordExtras, PublicKey.serialize], fun k hk => ?_⟩
        · rfl
        · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
            SessionState.setUnacknowledgedPreKeyMessage, SeedsLen32]
        · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
            SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
        · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
            SessionState.setUnacknowledgedPreKeyMessage]
        · exact CryptoVerification.E2E.Reach.setUnacknowledgedPreKeyMessage_sessRepr _
            (CryptoVerification.E2E.Reach.setSenderChain_sessRepr _ _ _
              (CryptoVerification.E2E.Reach.clampScalar_keyPair_generate W.C _)
              (CryptoVerification.E2E.Reach.addReceiverChain_sessRepr _ _ _
                (CryptoVerification.E2E.Reach.new_sessRepr _ _ _ _ _)))
        · simp only [initiatorRecordExtras, Option.some.injEq] at hk; subst hk
          simp [CryptoVerification.E2E.kyberKey]
  | recvPrekey X P me k m rc x g pt h =>
    unfold recvPrekeyState at h
    rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
    · simp [htf] at h
    · rw [htf] at h; dsimp only at h
      split_ifs at h with hids
      · simp at h
      · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
        · simp [hacc] at h
        · rw [hacc] at h; dsimp only at h
          let st0 : SessionState HwBytes :=
            initializeRecipientSession (pqxdhSpqrSession W)
              ⟨(keyPairOf W.C me.idPriv).publicKey⟩
              ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
              (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
          have hver0 : st0.sessionVersion = 4#32 := rfl
          have hseeds0 : SeedsLen32 st0 := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain, SeedsLen32]
          have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
            simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
          have hrep0 : CryptoVerification.E2E.Reach.SessRepr st0 :=
            CryptoVerification.E2E.Reach.setSenderChain_sessRepr _ _ _
              (CryptoVerification.E2E.Reach.clampScalar_idem k.spkPriv)
              (CryptoVerification.E2E.Reach.new_sessRepr _ _ _ _ _)
          rcases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
          · rw [hdec] at h; cases e <;> simp at h
          · rw [hdec] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have hver := (sessionVersion_tryDecryptFromRecord_eq W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hdec).trans hver0
            obtain ⟨hseeds, hlen, hloc, hrem, -⟩ :=
              CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hseeds0 hlen0 hdec
            have hrep :=
              CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen W.C (pqxdhSpqrSession W)
                ((pqxdhSessionParams W).expectedAddrs P) inner .preKey rc st0 st pt' hrep0 hdec
            refine ⟨hver, hseeds, hlen, hloc, ⟨⟨⟨m.idPub⟩⟩, hrem⟩, hrep, rfl, rfl, rfl, ?_,
              fun ky hky => by cases hky⟩
            simp [responderRecordExtras, CryptoVerification.E2E.djbKey]
  | @send me_s x_s g_s m r _ _ ih =>
    change ReachPqInvPure W me_s x_s ((pqxdhSessionParams W).send g_s m r).1
    rw [CryptoVerification.E2E.Record.send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C
        (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hver, hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := ih
      have hver' := (sessionVersion_messageEncrypt_eq (pqxdhSessionParams W).C
        (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hm).trans hver
      obtain ⟨hseeds', hlen', hloc', hrem', _⟩ :=
        CryptoVerification.E2E.V1.messageEncrypt_ok_props_gen (pqxdhSessionParams W).C
          (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hseeds hlen hm
      have hrep' :=
        CryptoVerification.E2E.V1.sessRepr_messageEncrypt_gen (pqxdhSessionParams W).C
          (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hrep hm
      exact ⟨hver', hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
        hreg, hts, hbk, habk, hky⟩
  | @recv _ x_r g_r g_r' c rc res _ _ hrec ih =>
    rcases res with ⟨t, i, pt⟩
    rw [CryptoVerification.E2E.Record.receive_eq_afterRecv] at hrec
    rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
    · simp [htf] at hrec
    · rw [htf] at hrec; dsimp only at hrec
      rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session with ⟨_ | pt', s⟩
      · simp [hd] at hrec
      · rw [hd] at hrec
        simp only [Option.some.injEq] at hrec
        rcases hrec with ⟨rfl, rfl, rfl, rfl⟩
        obtain ⟨hver, hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := ih
        have hver' := (sessionVersion_tryDecryptFromRecord_eq (pqxdhSessionParams W).C
          (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hd).trans hver
        obtain ⟨hseeds', hlen', hloc', hrem', _⟩ :=
          CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr
            ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hseeds hlen hd
        have hrep' :=
          CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen (pqxdhSessionParams W).C
            (pqxdhSessionParams W).spqr
            ((pqxdhSessionParams W).expectedAddrs g_r.party) msg .whisper rc g_r.session s pt hrep hd
        exact ⟨hver', hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
          hreg, hts, hbk, habk, hky⟩

private theorem pq_length_le_encodeRecord (s : Session (List (BitVec 8))) :
    s.state.pqRatchetState.length ≤ (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  have hb : ∀ v : List (BitVec 8), v.length ≤ (CryptoVerification.E2E.Record.bytesField 15 v).length := by
    intro v; unfold CryptoVerification.E2E.Record.bytesField
    split_ifs with hv
    · simp [hv]
    · simp only [CryptoVerification.E2E.Record.lenField, List.length_append]; omega
  have hs : (CryptoVerification.E2E.Record.bytesField 15 s.state.pqRatchetState).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
    unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega
  have hr : (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
    simp only [CryptoVerification.E2E.Record.encodeRecord, CryptoVerification.E2E.Record.msgField,
      CryptoVerification.E2E.Record.lenField, Option.map_some, List.length_append]; omega
  exact Nat.le_trans (hb _) (Nat.le_trans hs hr)

theorem recordScopeP_of_encodeRecordX_length (x : RecordExtras) (g : GhostState HwBytes)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 32) :
    slots_RecordScopeP slots_NonEmptyV1Q ⟨some (pqSession x g)⟩ := by
  intro s hs
  injection hs with hs'; subst hs'
  change (pqSession x g).state.pqRatchetState.length < 2 ^ 32
  have hle := pq_length_le_encodeRecord (pqSession x g)
  rw [encodeRecordX_eq_encodeRecord_pqSession] at hlen
  omega

theorem pureBinCanonSession_of_deserializeScopeP_Q_any {s : Session (List (BitVec 8))}
    (hDeser : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some s⟩) :
    PureBinCanonSession s :=
  Symbolic.Swarm.CREF.CliPure.TR.Pure.pureBinCanonSession_of_deserializeScopeP hDeser

theorem reachPqInvPure_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    ReachPqInvPure W st.me x g ∧
    g.party = st.party ∧
    (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
  obtain ⟨⟨g₀, hrpq, _hp_eq, hs_eq⟩, hg_party, hlen31⟩ := hwf.1 x g hsess
  obtain ⟨hver, hseeds, hlen, hloc, hrem, hrep, hreg, hts, hbk, habk, hkyb⟩ := reachPq_inv hrpq
  exact ⟨⟨hs_eq ▸ hver, hs_eq ▸ hseeds, hs_eq ▸ hlen, hs_eq ▸ hloc, hs_eq ▸ hrem,
    hs_eq ▸ hrep, hreg, hts, hbk, habk, hkyb⟩, hg_party, hlen31⟩

theorem pqSession_version_and_remote_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    (pqSession x g).state.sessionVersion = 4#32 ∧
      (pqSession x g).state.remoteIdentity.isSome = true := by
  obtain ⟨⟨hver, _, _, _, ⟨rem, hrem⟩, _⟩, _, _⟩ := reachPqInvPure_of_wfPq hwf hsess
  exact ⟨hver, by simp [hrem]⟩

theorem pqSession_sessionVersion_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    (pqSession x g).state.sessionVersion = 4#32 :=
  (pqSession_version_and_remote_of_wfPq hwf hsess).1

end Symbolic.Swarm.CREF.Cli
