/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Proofs.E2E.V1.BinDefs
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow
public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
public import LibsignalBinary.Specifications.LibsignalE2E.ParamsEWith
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.E2E.V1.SpqrV1Facts
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize

/-!
# SPQR V1 Invariants and State Validity on Reachable PQXDH Sessions

Defines the SPQR V1 session parameters (`paramsPV1`, `initiateStateV1`, `recvPrekeyStateV1`),
bounded step invariants (`ReachPqInvV1`, `PqStep`, `PqInV1`, `PqOutV1`), and encoded record length
bounds, proving that every `ReachablePqxdhSession` satisfies `ReachPqInvV1` (`reachPq_inv`) and has
a valid SPQR state (`reachPq_validState`).
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli.Slots.PqValid

set_option autoImplicit false

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoGames.HKDF (Salt)
open CryptoVerification CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E CryptoVerification.E2E.Reach CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record hiding Bytes bytesField
open CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.V1
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1 spqrV1Init spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1.Top.StateSize (ValidState validState_spqrV1Init
  spqrV1_send_validState_length_le spqrV1_recv_validState_length_le)
/-- Session-model `Params` with SPQR V1 enabled (`spqrV1SessionUniformCoins C.F K` with 512-bit
coins in place of `spqrOffB`). -/
def paramsPV1 (C : Crypto) (K : MlKem) : Params Bytes (BitVec 512) :=
  ⟨C, protoSignalCodec, spqrV1SessionUniformCoins C.F K, partyIdentityKey .A, partyIdentityKey .B, serializedPartyAddresses uuidTryParse .A .B,
    serializedPartyAddresses uuidTryParse .B .A⟩

/-- Initiator state after `session_initiate` with SPQR V1 enabled (`spqrV1Init W.C.F K .a2b`). -/
def initiateStateV1 (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) :
    Option (RecordExtras × GhostState Bytes) :=
  match SignalPqxdh.Model.initiateKeys (modelPrims X W) (initiateInput W me b t) with
  | none => none
  | some (dk, hdr) =>
    let idA := keyPairOf W.C me.idPriv
    match initializeInitiatorSession W.C (spqrV1SessionUniformCoins W.C.F K) ⟨idA.publicKey⟩ ⟨⟨b.idPub⟩⟩
        ⟨b.spkPub⟩ (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
        (HKDF.bytesToKey32 (ofU8 dk.pqrKey)) (HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | .error _ => none
    | .ok st =>
      some (initiatorRecordExtras me b ⟨u8Vec 32 hdr.ekAPk⟩ (u8Vec 1568 hdr.kemCt),
        ⟨P, st.setUnacknowledgedPreKeyMessage, 0, [0]⟩)

/-- Responder state after `session_recv_prekey` with SPQR V1 enabled (`spqrV1Init W.C.F K .b2a` followed by `spqr::recv`). -/
def recvPrekeyStateV1 (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party) (me : LocalIdentity)
    (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) :
    Option (Option (RecordExtras × GhostState Bytes × Bytes)) :=
  match SignalMessage.tryFrom protoSignalCodec m.inner with
  | .error _ => some none
  | .ok inner =>
    if m.spkId ≠ k.spkId ∨ m.kpkId ≠ k.kpkId then some none
    else
      match SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with
      | none => some none
      | some dk =>
        let st0 : SessionState Bytes :=
          initializeRecipientSession (spqrV1SessionUniformCoins W.C.F K)
            ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
            (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
            (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F K)
            ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 with
        | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
        | (.error .panic, _) => none
        | (.error _, _) => some none

/-- Any record whose `encodeRecordUnderExtras E g` has length `< 2^32` has a post-quantum ratchet
state shorter than `2^32` bytes. -/
theorem recordPqBound_of_encodeRecordX_length (E : Party → RecordExtras) (g : GhostState Bytes)
    (hlen : (encodeRecordUnderExtras E g).length < 2 ^ 32) :
    LibsignalSpqrV1.RecordPqStateLengthBelow2Pow32 ⟨some (sessionOfX E g)⟩ := by
  intro s hs
  injection hs with hs'
  subst hs'
  change g.session.pqRatchetState.length < 2 ^ 32
  have h1 : g.session.pqRatchetState.length ≤ (bytesField 15 g.session.pqRatchetState).length := by
    unfold bytesField
    split_ifs with h
    · simp [h]
    · exact lenField_length_ge' 15 g.session.pqRatchetState
  have h2 : (bytesField 15 g.session.pqRatchetState).length ≤
      (encStateUnderExtras (E g.party) g.session).length := by
    unfold encStateUnderExtras
    simp only [List.length_append]
    omega
  have h3 : (encStateUnderExtras (E g.party) g.session).length ≤ (encodeRecordUnderExtras E g).length :=
    lenField_length_ge' 1 (encStateUnderExtras (E g.party) g.session)
  omega

/-- Session invariant `ReachPqInv` with the empty-PQ-state conjunct (`pqRatchetState = []`) omitted. -/
def ReachPqInvV1 (W : PEParams) (me : LocalIdentity) (x : RecordExtras) (g : GhostState Bytes) : Prop :=
  SeedsLen32 g.session ∧
    g.session.receiverChains.length ≤ maxReceiverChains ∧
    g.session.localIdentity = ⟨(keyPairOf W.C me.idPriv).publicKey⟩ ∧
    (∃ rem, g.session.remoteIdentity = some rem) ∧
    Reach.SessRepr g.session ∧
    x.localRegistrationId = me.regId ∧
    x.pending.timestamp = 0#64 ∧
    x.pending.baseKey.serialize = x.aliceBaseKey ∧
    x.aliceBaseKey.length = 33 ∧
    ∀ k, x.kyber = some k → k.ciphertext.length = 1569

section Steps

variable {PQC : Type}

/-- `send` under `sessionParamsForSpqr W.C S` preserves `ReachPqInvV1` for any SPQR model `S`. -/
theorem reachPqInvV1_send (W : PEParams) (S : Spqr Bytes PQC) {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (m : Bytes) (r : PQC) (hg : ReachPqInvV1 W me x g) :
    ReachPqInvV1 W me x ((sessionParamsForSpqr W.C S).send g m r).1 := by
  rw [Record.send_eq_afterSend]
  rcases hm : SessionState.messageEncrypt (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).codec
      (sessionParamsForSpqr W.C S).spqr ((sessionParamsForSpqr W.C S).sendAddrs g.party) m r g.session with ⟨_ | msg, s⟩
  · exact hg
  · obtain ⟨hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := hg
    obtain ⟨hseeds', hlen', hloc', hrem', _⟩ :=
      messageEncrypt_ok_props_gen (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).codec
        (sessionParamsForSpqr W.C S).spqr ((sessionParamsForSpqr W.C S).sendAddrs g.party)
        m r g.session s msg hseeds hlen hm
    have hrep' :=
      sessRepr_messageEncrypt_gen (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).codec
        (sessionParamsForSpqr W.C S).spqr ((sessionParamsForSpqr W.C S).sendAddrs g.party)
        m r g.session s msg hrep hm
    exact ⟨hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
      hreg, hts, hbk, habk, hky⟩

/-- `receive` under `sessionParamsForSpqr W.C S` preserves `ReachPqInvV1` for any SPQR model `S`. -/
theorem reachPqInvV1_recv (W : PEParams) (S : Spqr Bytes PQC) {me : LocalIdentity} {x : RecordExtras}
    {g g' : GhostState Bytes} {c : Bytes} {rc : BitVec 256} {res : ℕ × ℕ × Bytes}
    (hg : ReachPqInvV1 W me x g)
    (h : (sessionParamsForSpqr W.C S).receive g c rc = some (g', res)) :
    ReachPqInvV1 W me x g' := by
  rcases res with ⟨t, i, pt⟩
  rw [Record.receive_eq_afterRecv] at h
  rcases htf : SignalMessage.tryFrom (sessionParamsForSpqr W.C S).codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).spqr
        ((sessionParamsForSpqr W.C S).expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt', s⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := hg
      obtain ⟨hseeds', hlen', hloc', hrem', _⟩ :=
        tryDecryptFromRecord_ok_props_gen (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).spqr
          ((sessionParamsForSpqr W.C S).expectedAddrs g.party) msg .whisper rc g.session s pt hseeds hlen hd
      have hrep' :=
        sessRepr_tryDecryptFromRecord_gen (sessionParamsForSpqr W.C S).C (sessionParamsForSpqr W.C S).spqr
          ((sessionParamsForSpqr W.C S).expectedAddrs g.party) msg .whisper rc g.session s pt hrep hd
      exact ⟨hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
        hreg, hts, hbk, habk, hky⟩

end Steps

/-- `initiateStateV1` establishes `ReachPqInvV1`. -/
theorem reachPqInvV1_initiate (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party) (me : LocalIdentity)
    (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) (x : RecordExtras)
    (g : GhostState Bytes) (h : initiateStateV1 X W K P me b t = some (x, g)) :
    ReachPqInvV1 W me x g := by
  unfold initiateStateV1 at h
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
      refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, SeedsLen32]
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage, maxReceiverChains]
      · simp [SessionState.new, SessionState.addReceiverChain, SessionState.setSenderChain,
          SessionState.setUnacknowledgedPreKeyMessage]
      · exact ⟨⟨⟨b.idPub⟩⟩, rfl⟩
      · exact Reach.setUnacknowledgedPreKeyMessage_sessRepr _
          (Reach.setSenderChain_sessRepr _ _ _
            (Reach.clampScalar_keyPair_generate W.C _)
            (Reach.addReceiverChain_sessRepr _ _ _ (Reach.new_sessRepr _ _ _ _ _)))
      · exact PublicKey.serialize_length _
      · intro k hk
        simp only [initiatorRecordExtras, Option.some.injEq] at hk
        subst hk
        simp [kyberKey]

/-- `recvPrekeyStateV1` establishes `ReachPqInvV1`. -/
theorem reachPqInvV1_recvPrekey (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) (x : RecordExtras)
    (g : GhostState Bytes) (pt : Bytes)
    (h : recvPrekeyStateV1 X W K P me k m rc = some (some (x, g, pt))) :
    ReachPqInvV1 W me x g := by
  unfold recvPrekeyStateV1 at h
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    split_ifs at h with hids
    · simp at h
    · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        let st0 : SessionState Bytes :=
          initializeRecipientSession (spqrV1SessionUniformCoins W.C.F K)
            ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        have hseeds0 : SeedsLen32 st0 := by
          simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
            SeedsLen32]
        have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
          simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
        have hrep0 : Reach.SessRepr st0 :=
          Reach.setSenderChain_sessRepr _ _ _
            (Reach.clampScalar_idem k.spkPriv)
            (Reach.new_sessRepr _ _ _ _ _)
        change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F K)
            ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = some (some (x, g, pt)) at h
        rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F K)
            ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
        · rw [hdec] at h; cases e <;> simp at h
        · rw [hdec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          obtain ⟨hseeds, hlen, hloc, hrem, -⟩ :=
            tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F K)
              ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 st pt' hseeds0 hlen0 hdec
          have hrep :=
            sessRepr_tryDecryptFromRecord_gen W.C (spqrV1SessionUniformCoins W.C.F K)
              ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 st pt' hrep0 hdec
          refine ⟨hseeds, hlen, hloc, ⟨⟨⟨m.idPub⟩⟩, hrem⟩, hrep, rfl, rfl, rfl, ?_, ?_⟩
          · simp [responderRecordExtras, djbKey]
          · intro ky hky; cases hky

/-- Bounded single-step SPQR invariant mapping pre-states `PqIn` into post-states `PqOut` of length
`< 2^32` (`RecordPqStateLengthBelow2Pow32`). -/
structure PqStep (S : SpqrModel) (PqIn PqOut : List (BitVec 8) → Prop) : Prop where
  in_out : ∀ st, PqIn st → PqOut st
  out_bound : ∀ st, PqOut st → st.length < 2 ^ 32
  send : ∀ st rest st' salt pm, PqIn st → S.send st rest = some (st', salt, pm) → PqOut st'
  recv : ∀ st msg st' salt, PqIn st → S.recv st msg = .ok (st', salt) → PqOut st'
  msg : SendMsgBoundOn S PqIn

theorem PqStep.in_bound {S : SpqrModel} {PqIn PqOut : List (BitVec 8) → Prop}
    (h : PqStep S PqIn PqOut) (st : List (BitVec 8)) (hst : PqIn st) : st.length < 2 ^ 32 :=
  h.out_bound st (h.in_out st hst)

/-- Pre-states of SPQR V1 wire entries: `ValidState st ∧ st.length < 2^31`. -/
def PqInV1 (st : List (BitVec 8)) : Prop :=
  ValidState st ∧ st.length < 2 ^ 31

/-- Post-states of SPQR V1 wire entries: `st.length < 2^31 + 2^21`. -/
def PqOutV1 (st : List (BitVec 8)) : Prop :=
  st.length < 2 ^ 31 + 2 ^ 21

/-- `spqrV1 F K` satisfies `PqStep (spqrV1 F K) PqInV1 PqOutV1`. -/
theorem pqStep_spqrV1 (F : ShaCompress) (K : MlKem) : PqStep (spqrV1 F K) PqInV1 PqOutV1 where
  in_out st h := by
    have := h.2
    unfold PqOutV1
    omega
  out_bound st h := by
    unfold PqOutV1 at h
    omega
  send st rest st' salt pm h hs := by
    have h31 := h.2
    have := (CryptoVerification.SpqrV1.Top.StateSize.spqrV1_send_validState_length_le F K st rest
      st' salt pm h.1 (by omega) hs).2
    unfold PqOutV1
    omega
  recv st msg st' salt h hr := by
    have h31 := h.2
    have := (CryptoVerification.SpqrV1.Top.StateSize.spqrV1_recv_validState_length_le F K st msg
      st' salt h.1 (by omega) hr).2
    unfold PqOutV1
    omega
  msg := sendMsgBoundOn_spqrV1 F K PqInV1

theorem pqRatchetState_length_le_encodeRecordX (E : Party → RecordExtras) (g : GhostState Bytes) :
    g.session.pqRatchetState.length ≤ (encodeRecordUnderExtras E g).length := by
  have h1 : g.session.pqRatchetState.length ≤ (bytesField 15 g.session.pqRatchetState).length := by
    unfold bytesField
    split_ifs with h
    · simp [h]
    · exact lenField_length_ge' 15 g.session.pqRatchetState
  have h2 : (bytesField 15 g.session.pqRatchetState).length ≤
      (encStateUnderExtras (E g.party) g.session).length := by
    unfold encStateUnderExtras
    simp only [List.length_append]
    omega
  have h3 : (encStateUnderExtras (E g.party) g.session).length ≤ (encodeRecordUnderExtras E g).length :=
    lenField_length_ge' 1 (encStateUnderExtras (E g.party) g.session)
  omega

/-- Clears `s.state.pqRatchetState` to `[]` to reduce non-PQ record length bounds to `RecordX`. -/
def stripPq (s : Session (List (BitVec 8))) : Session (List (BitVec 8)) :=
  { s with state := { s.state with pqRatchetState := [] } }

private theorem encSession_stripPq_length (s : Session (List (BitVec 8))) :
    (Record.encSession s).length =
      (Record.encSession (stripPq s)).length +
        (Record.bytesField 15 s.state.pqRatchetState).length := by
  simp only [Record.encSession, stripPq, show (Record.bytesField 15 []).length = 0 from rfl,
    List.length_append]
  omega

theorem encodeRecord_length_lt_32_of_stripPq_bounded {s : Session (List (BitVec 8))}
    (hb : DeserializeScopeBounded ⟨some (stripPq s)⟩)
    (hpq : PqOutV1 s.state.pqRatchetState) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 32 := by
  have h21 : (Record.encodeRecord ⟨some (stripPq s)⟩).length < 2 ^ 21 :=
    encodeRecord_length_lt_21_of_bounded hb
  have hge : (Record.encSession (stripPq s)).length ≤ (Record.encodeRecord ⟨some (stripPq s)⟩).length := by
    unfold Record.encodeRecord Record.msgField
    dsimp only [Option.map_some]
    exact lenField_length_ge' 1 (Record.encSession (stripPq s))
  have hle : (Record.encodeRecord ⟨some s⟩).length ≤ (Record.encSession s).length + 20 := by
    unfold Record.encodeRecord Record.msgField
    dsimp only [Option.map_some]
    exact lenField_length_le' 1 (Record.encSession s)
  have heq := encSession_stripPq_length s
  have hb15 : (Record.bytesField 15 s.state.pqRatchetState).length ≤ s.state.pqRatchetState.length + 20 :=
    bytesField_length_le' 15 s.state.pqRatchetState
  unfold PqOutV1 at hpq
  omega

/-- `(spqrV1 F K).send` preserves `ValidState` on states shorter than `2^64` bytes. -/
theorem validState_spqrV1_send (F : ShaCompress) (K : MlKem) (s tape s' : List (BitVec 8))
    (salt : Salt) (msg : List (BitVec 8)) (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).send s tape = some (s', salt, msg)) : ValidState s' :=
  (spqrV1_send_validState_length_le F K s tape s' salt msg hval hlen h).1

/-- `(spqrV1 F K).recv` preserves `ValidState` on states shorter than `2^64` bytes. -/
theorem validState_spqrV1_recv (F : ShaCompress) (K : MlKem) (s msg s' : List (BitVec 8))
    (salt : Salt) (hval : ValidState s) (hlen : s.length < 2 ^ 64)
    (h : (spqrV1 F K).recv s msg = .ok (s', salt)) : ValidState s' :=
  (spqrV1_recv_validState_length_le F K s msg s' salt hval hlen h).1

private theorem spqrV1Init_length_lt (F : ShaCompress) (K : MlKem) (dir : SpqrDirection)
    (k : BitVec 256) : (spqrV1Init F K dir k).length < 2 ^ 64 := by
  unfold spqrV1Init LibsignalSpqrV1.spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [LibsignalSpqrV1.initialState, LibsignalSpqrV1.libsignalSpqrParams] at hst
    rcases hi : LibsignalSpqrV1.initInner (LibsignalSpqrV1.spqrDeps F K) LibsignalSpqrV1.Version.v1
        (LibsignalSpqrV1.Direction.ofSpqrDirection dir) (HMAC.keyToBytes32 k) with p | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst
      subst hst'
      have hin := CryptoVerification.SpqrV1.Top.StateSize.initInner_spqrDeps_raw_le hi
      have hk : (HMAC.keyToBytes32 k).length = 32 := by simp [HMAC.keyToBytes32]
      refine (CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_lt_of_rawPqState_le ?_).2.2.2
      simp only [CryptoVerification.SpqrV1.Top.StateSize.rawPqState, LibsignalSpqrV1.pbToPqRatchetState,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_none, CryptoVerification.SpqrV1.Top.StateSize.rawVN,
        hk]
      omega
  · simp

/-- `Params.send` at `paramsPV1` preserves `ValidState` of `pqRatchetState`. -/
theorem validState_paramsPV1_send (W : PEParams) (K : MlKem) {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (m : Bytes) (r : BitVec 512) (hinv : ReachPqInvV1 W me x g)
    (hval : ValidState g.session.pqRatchetState) (hpq : g.session.pqRatchetState.length < 2 ^ 64) :
    ValidState ((paramsPV1 W.C K).send g m r).1.session.pqRatchetState := by
  rw [Record.send_eq_afterSend]
  rcases hm : SessionState.messageEncrypt (paramsPV1 W.C K).C (paramsPV1 W.C K).codec
      (paramsPV1 W.C K).spqr ((paramsPV1 W.C K).sendAddrs g.party) m r g.session with
    ⟨_ | msg, s⟩
  · exact hval
  · obtain ⟨hseeds, hlen, -⟩ := hinv
    obtain ⟨-, -, -, -, key, pm, hsend, -⟩ :=
      messageEncrypt_ok_props_gen (paramsPV1 W.C K).C (paramsPV1 W.C K).codec
        (paramsPV1 W.C K).spqr ((paramsPV1 W.C K).sendAddrs g.party) m r g.session s msg
        hseeds hlen hm
    exact validState_spqrV1_send W.C.F K _ _ _ key pm hval hpq hsend

/-- `Params.receive` at `paramsPV1` preserves `ValidState` of `pqRatchetState`. -/
theorem validState_paramsPV1_recv (W : PEParams) (K : MlKem) {me : LocalIdentity} {x : RecordExtras}
    {g g' : GhostState Bytes} {c : Bytes} {rc : BitVec 256} {res : ℕ × ℕ × Bytes}
    (hinv : ReachPqInvV1 W me x g) (hval : ValidState g.session.pqRatchetState)
    (hpq : g.session.pqRatchetState.length < 2 ^ 64)
    (h : (paramsPV1 W.C K).receive g c rc = some (g', res)) :
    ValidState g'.session.pqRatchetState := by
  rcases res with ⟨t, i, pt⟩
  rw [Record.receive_eq_afterRecv] at h
  rcases htf : SignalMessage.tryFrom (paramsPV1 W.C K).codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord (paramsPV1 W.C K).C (paramsPV1 W.C K).spqr
        ((paramsPV1 W.C K).expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt', s⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hseeds, hlen, -⟩ := hinv
      obtain ⟨-, -, -, -, key, hrecv⟩ :=
        tryDecryptFromRecord_ok_props_gen (paramsPV1 W.C K).C (paramsPV1 W.C K).spqr
          ((paramsPV1 W.C K).expectedAddrs g.party) msg .whisper rc g.session s pt hseeds hlen hd
      exact validState_spqrV1_recv W.C.F K _ _ _ key hval hpq hrecv

/-- `initiateStateV1` produces a valid initial SPQR state (`ValidState`). -/
theorem validState_initiateStateV1 (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party)
    (me : LocalIdentity) (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen) (x : RecordExtras)
    (g : GhostState Bytes) (h : initiateStateV1 X W K P me b t = some (x, g)) :
    ValidState g.session.pqRatchetState := by
  unfold initiateStateV1 at h
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
      exact validState_spqrV1Init W.C.F K .a2b _

/-- `recvPrekeyStateV1` produces a valid SPQR state (`ValidState`). -/
theorem validState_recvPrekeyStateV1 (X : UnreachedPqxdhPrimitives) (W : PEParams) (K : MlKem) (P : Party)
    (me : LocalIdentity) (k : ResponderPreKeySecrets) (m : PreKeyMessageFields) (rc : BitVec 256) (x : RecordExtras)
    (g : GhostState Bytes) (pt : Bytes)
    (h : recvPrekeyStateV1 X W K P me k m rc = some (some (x, g, pt))) :
    ValidState g.session.pqRatchetState := by
  unfold recvPrekeyStateV1 at h
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    split_ifs at h with hids
    · simp at h
    · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        let st0 : SessionState Bytes :=
          initializeRecipientSession (spqrV1SessionUniformCoins W.C.F K)
            ⟨(keyPairOf W.C me.idPriv).publicKey⟩
            ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv) (HKDF.bytesToKey32 (ofU8 dk.rootKey))
            (HKDF.bytesToKey32 (ofU8 dk.chainKey)) (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
        have hseeds0 : SeedsLen32 st0 := by
          simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain,
            SeedsLen32]
        have hlen0 : st0.receiverChains.length ≤ maxReceiverChains := by
          simp [st0, initializeRecipientSession, SessionState.new, SessionState.setSenderChain]
        have hval0 : ValidState st0.pqRatchetState :=
          validState_spqrV1Init W.C.F K .b2a _
        have hpq0 : st0.pqRatchetState.length < 2 ^ 64 :=
          spqrV1Init_length_lt W.C.F K .b2a _
        change (match SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F K)
            ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = some (some (x, g, pt)) at h
        rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1SessionUniformCoins W.C.F K)
            ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
        · rw [hdec] at h; cases e <;> simp at h
        · rw [hdec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          obtain ⟨-, -, -, -, key, hrecv⟩ :=
            tryDecryptFromRecord_ok_props_gen W.C (spqrV1SessionUniformCoins W.C.F K)
              ((paramsPV1 W.C K).expectedAddrs P) inner .preKey rc st0 st pt' hseeds0 hlen0 hdec
          exact validState_spqrV1_recv W.C.F K _ _ _ key hval0 hpq0 hrecv

theorem pqLength_lt_2_64_of_encodeRecordX (x : RecordExtras) (g : GhostState Bytes)
    (hlen : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31) :
    g.session.pqRatchetState.length < 2 ^ 64 := by
  have h32 := recordPqBound_of_encodeRecordX_length (fun _ => x) g (by omega) _ rfl
  change g.session.pqRatchetState.length < 2 ^ 32 at h32
  omega

/-- Every `ReachablePqxdhSession W me x g` session satisfies `ReachPqInvV1 W me x g`. -/
theorem reachPq_inv {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ReachPqInvV1 W me x g := by
  induction h with
  | initiate X P me b t x g hi => exact reachPqInvV1_initiate X W W.Q.K P me b t x g hi
  | recvPrekey X P me k m rc x g pt hr =>
    exact reachPqInvV1_recvPrekey X W W.Q.K P me k m rc x g pt hr
  | send m r _ _ ih => exact reachPqInvV1_send W (pqxdhSpqrSession W) m r ih
  | recv _ _ hrec ih => exact reachPqInvV1_recv W (pqxdhSpqrSession W) ih hrec

/-- Every `ReachablePqxdhSession W me x g` session has a valid SPQR state (`ValidState`). -/
theorem reachPq_validState {W : PEParams} {me : LocalIdentity} {x : RecordExtras}
    {g : GhostState Bytes} (h : ReachablePqxdhSession W me x g) :
    ValidState g.session.pqRatchetState := by
  induction h with
  | initiate X P me b t x g hi => exact validState_initiateStateV1 X W W.Q.K P me b t x g hi
  | recvPrekey X P me k m rc x g pt hr =>
    exact validState_recvPrekeyStateV1 X W W.Q.K P me k m rc x g pt hr
  | @send _ x_s g_s m r hr hlen ih =>
    have hpq : g_s.session.pqRatchetState.length < 2 ^ 64 :=
      pqLength_lt_2_64_of_encodeRecordX x_s g_s hlen
    rw [Record.send_eq_afterSend]
    rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
        (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session with ⟨_ | msg, s⟩
    · exact ih
    · obtain ⟨hseeds, hlen', -⟩ := reachPq_inv hr
      obtain ⟨-, -, -, -, key, pm, hsend, -⟩ :=
        messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec
          (pqxdhSessionParams W).spqr ((pqxdhSessionParams W).sendAddrs g_s.party) m r g_s.session s msg hseeds hlen' hm
      exact validState_spqrV1_send W.C.F W.Q.K _ _ _ key pm ih hpq hsend
  | @recv _ x_r g_r g'_r c rc res hr hlen hrec ih =>
    exact validState_paramsPV1_recv W W.Q.K (reachPq_inv hr) ih
      (pqLength_lt_2_64_of_encodeRecordX x_r g_r hlen) hrec
end CryptoVerification.SignalSession.Cli.Slots.PqValid
