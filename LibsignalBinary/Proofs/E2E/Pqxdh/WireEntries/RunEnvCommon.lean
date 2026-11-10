/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.PqxdhSessionModel
public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Bin.Record
public import LibsignalBinary.Proofs.E2E.Reach.BundleCommon
public import LibsignalBinary.Proofs.E2E.Run.SendPure
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.Specs -- shake: keep

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Pqxdh.WireEntries

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalAesCbc (toLEBytes)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E CryptoVerification.E2E.Run
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec
abbrev _root_.CryptoVerification.E2E.PEParams.params (W : PEParams) :
    Params Bytes Unit := spqrOffSessionParams W.C
open CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX

section ReachPqInv

/-- A record `encodeRecordUnderExtras E g` shorter than `2^32` bytes has a post-quantum state shorter
than `2^32` bytes, for any extras `E`. -/
theorem recordPqBound_of_encodeRecordX_length (E : Party → RecordExtras) (g : GhostState Bytes)
    (hlen : (encodeRecordUnderExtras E g).length < 2 ^ 32) :
    g.session.pqRatchetState.length < 2 ^ 32 := by
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

/-- Inductive session and record-extras invariant for reachable V1 PQXDH sessions `(me, x, g)`. -/
def ReachPqInv (W : PEParams) (me : LocalIdentity) (x : RecordExtras) (g : GhostState Bytes) : Prop :=
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

theorem reachPqInv_initiate (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) (x : RecordExtras) (g : GhostState Bytes)
    (h : initiateState X W P me b t = some (x, g)) :
    ReachPqInv W me x g := by
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

set_option maxHeartbeats 1200000 in
theorem reachPqInv_recvPrekey (X : UnreachedPqxdhPrimitives) (W : PEParams) (P : Party) (me : LocalIdentity) (k : ResponderPreKeySecrets)
    (m : PreKeyMessageFields) (rc : BitVec 256) (x : RecordExtras) (g : GhostState Bytes) (pt : Bytes)
    (h : recvPrekeyState X W P me k m rc = some (some (x, g, pt))) :
    ReachPqInv W me x g := by
  unfold recvPrekeyState at h
  rcases htf : SignalMessage.tryFrom protoSignalCodec m.inner with _ | inner
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    split_ifs at h with hids
    · simp at h
    · rcases hacc : SignalPqxdh.Model.acceptKeys (modelPrims X W) (acceptInput W me k m) with _ | dk
      · simp [hacc] at h
      · rw [hacc] at h; dsimp only at h
        let st0 : SessionState Bytes :=
          initializeRecipientSession (spqrV1Session W.C.F W.Q.K)
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
        change (match SessionState.tryDecryptFromRecord W.C (spqrV1Session W.C.F W.Q.K)
            (W.params.expectedAddrs P) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (responderRecordExtras me m, ⟨P, st, 1, [1]⟩, pt))
          | (.error .panic, _) => none
          | (.error _, _) => some none) = some (some (x, g, pt)) at h
        rcases hdec : SessionState.tryDecryptFromRecord W.C (spqrV1Session W.C.F W.Q.K)
            (W.params.expectedAddrs P) inner .preKey rc st0 with ⟨e | pt', st⟩
        · rw [hdec] at h; cases e <;> simp at h
        · rw [hdec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          obtain ⟨hseeds, hlen, hloc, hrem, -⟩ :=
            V1.tryDecryptFromRecord_ok_props_gen W.C (spqrV1Session W.C.F W.Q.K)
              (W.params.expectedAddrs P) inner .preKey rc st0 st pt' hseeds0 hlen0 hdec
          have hrep :=
            V1.sessRepr_tryDecryptFromRecord_gen W.C (spqrV1Session W.C.F W.Q.K)
              (W.params.expectedAddrs P) inner .preKey rc st0 st pt' hrep0 hdec
          refine ⟨hseeds, hlen, hloc, ⟨⟨⟨m.idPub⟩⟩, hrem⟩, hrep, rfl, rfl, rfl, ?_, ?_⟩
          · simp [responderRecordExtras, djbKey]
          · intro ky hky; cases hky

theorem reachPqInv_send (W : PEParams) {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (m r : Bytes) (hg : ReachPqInv W me x g) :
    ReachPqInv W me x ((pqxdhSessionParams W).send g m r).1 := by
  rw [Record.send_eq_afterSend]
  rcases hm : SessionState.messageEncrypt (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
      ((pqxdhSessionParams W).sendAddrs g.party) m r g.session with ⟨_ | msg, s⟩
  · exact hg
  · obtain ⟨hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := hg
    obtain ⟨hseeds', hlen', hloc', hrem', -⟩ :=
      V1.messageEncrypt_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session s msg hseeds hlen hm
    have hrep' :=
      V1.sessRepr_messageEncrypt_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).codec (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).sendAddrs g.party) m r g.session s msg hrep hm
    exact ⟨hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
      hreg, hts, hbk, habk, hky⟩

theorem reachPqInv_recv (W : PEParams) {me : LocalIdentity} {x : RecordExtras} {g g' : GhostState Bytes}
    {c : Bytes} {rc : BitVec 256} {r : ℕ × ℕ × Bytes}
    (hg : ReachPqInv W me x g)
    (h : (pqxdhSessionParams W).receive g c rc = some (g', r)) :
    ReachPqInv W me x g' := by
  rcases r with ⟨t, i, pt⟩
  rw [Record.receive_eq_afterRecv] at h
  rcases htf : SignalMessage.tryFrom (pqxdhSessionParams W).codec c with _ | msg
  · simp [htf] at h
  · rw [htf] at h; dsimp only at h
    rcases hd : SessionState.tryDecryptFromRecord (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
        ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session with ⟨_ | pt', s⟩
    · simp [hd] at h
    · rw [hd] at h
      simp only [Option.some.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hseeds, hlen, hloc, ⟨rem, hrem⟩, hrep, hreg, hts, hbk, habk, hky⟩ := hg
      obtain ⟨hseeds', hlen', hloc', hrem', -⟩ :=
        V1.tryDecryptFromRecord_ok_props_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session s pt hseeds hlen hd
      have hrep' :=
        V1.sessRepr_tryDecryptFromRecord_gen (pqxdhSessionParams W).C (pqxdhSessionParams W).spqr
          ((pqxdhSessionParams W).expectedAddrs g.party) msg .whisper rc g.session s pt hrep hd
      exact ⟨hseeds', hlen', hloc'.trans hloc, ⟨rem, hrem'.trans hrem⟩, hrep',
        hreg, hts, hbk, habk, hky⟩

/-- Every reachable PQXDH session `(me, x, g)` satisfies `ReachPqInv W me x g`. -/
theorem reachPq_inv {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (h : ReachablePqxdhSession W me x g) :
    ReachPqInv W me x g := by
  induction h with
  | initiate X P me b t x g hi => exact reachPqInv_initiate X W P me b t x g hi
  | recvPrekey X P me k m rc x g pt hr => exact reachPqInv_recvPrekey X W P me k m rc x g pt hr
  | send m r _ _ ih => exact reachPqInv_send W m r ih
  | recv _ _ hrec ih => exact reachPqInv_recv W ih hrec

theorem encodeRecordX_eq_encodeRecord_sessionOfX (E : Party → RecordExtras) (g : GhostState Bytes) :
    encodeRecordUnderExtras E g = Record.encodeRecord ⟨some (sessionOfX E g)⟩ := by
  rw [RecordX.encodeRecordX_eq_toRecord, RecordX.toRecord_extrasOf_eq]

/-- Every reachable PQXDH session satisfies `BinCanonSession` on
`canonGhostOf (sessionOfX (fun _ => x) g)`
whenever `(encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 32`. -/
theorem reachPq_binCanonSession {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (h : ReachablePqxdhSession W me x g)
    (hlen32 : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 32) :
    BinCanonSession (Run.canonGhostOf (sessionOfX (fun _ => x) g)) (sessionOfX (fun _ => x) g) := by
  obtain ⟨hseeds, hlen, _, _, hrep, _, _, _, habk, hky⟩ := reachPq_inv h
  let s := sessionOfX (fun _ => x) g
  refine ⟨Run.serializationCanonSession_canonGhostOf s, sessionOfX_wf (fun _ => x) g, rfl,
    Run.canonGhostOf_remoteIk s, Run.canonGhostOf_sender s,
    hlen,
    fun rc hrc => ⟨hrep.1 rc hrc, hseeds rc hrc⟩,
    Run.canonGhostOf_chains_srk_priv s, ?_, ?_, ?_, ?_⟩
  · change x.aliceBaseKey.length < 2 ^ 32
    omega
  · dsimp only [s, sessionOfX]
    cases g.session.pendingPreKey
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte]
      cases hky_opt : x.kyber with
      | none => exact True.intro
      | some k =>
        have hk := hky k hky_opt
        omega
  · exact recordPqBound_of_encodeRecordX_length (fun _ => x) g hlen32
  · have hle := Run.encSession_length_le_encodeRecord s
    have heq : (encodeRecordUnderExtras (fun _ => x) g).length = (Record.encodeRecord ⟨some s⟩).length := by
      rw [RecordX.encodeRecordX_eq_toRecord, RecordX.toRecord_extrasOf_eq]
    change (Record.encSession s).length < 2 ^ 62
    omega

theorem reachPq_remoteIdentity_isSome {W : PEParams} {me : LocalIdentity}
    {x : RecordExtras} {g : GhostState Bytes}
    (h : ReachablePqxdhSession W me x g) :
    (sessionOfX (fun _ => x) g).state.remoteIdentity.isSome = true := by
  obtain ⟨rem, hrem⟩ := (reachPq_inv h).2.2.2.1
  change g.session.remoteIdentity.isSome = true
  rw [hrem]; rfl

theorem reachPq_sessionScopeP {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (h : ReachablePqxdhSession W me x g) :
    RecordX.SessionScopeP (sessionOfX (fun _ => x) g) := by
  obtain ⟨_, hlen, _, _, _, _, hts, _, habk, hky⟩ := reachPq_inv h
  refine ⟨hlen, ?_, ?_, Or.inr habk⟩
  · intro p hp
    unfold sessionOfX at hp
    dsimp only at hp
    split at hp
    · injection hp with hp'
      subst hp'
      exact hts
    · cases hp
  · intro k hk
    unfold sessionOfX at hk
    dsimp only at hk
    split at hk
    · exact hky k hk
    · cases hk

theorem reachPq_recordInScopeP {W : PEParams} {me : LocalIdentity} {x : RecordExtras} {g : GhostState Bytes}
    (h : ReachablePqxdhSession W me x g) :
    RecordX.RecordInScopeP ⟨some (sessionOfX (fun _ => x) g)⟩ := by
  obtain ⟨hseeds, hlen, _, _, _, _, _, _, _, hky⟩ := reachPq_inv h
  intro s hs
  injection hs with hs'
  subst hs'
  refine ⟨hseeds, Nat.lt_of_le_of_lt hlen (by decide), ?_⟩
  intro k hk
  unfold sessionOfX at hk
  dsimp only at hk
  split at hk
  · rw [hky k hk]; decide
  · cases hk

end ReachPqInv

def UuidNamesDistinct (uuidParse : UuidParser) : Prop :=
  ¬∃ u, uuidParse (utf8 (partyAddressName .A)) = some u ∧
    uuidParse (utf8 (partyAddressName .B)) = some u

theorem uuidNamesDistinct_uuidTryParse : UuidNamesDistinct uuidTryParse := by
  rintro ⟨u, hA, hB⟩
  have hfalse :
      (Option.map List.Vector.toList (uuidTryParse (utf8 (partyAddressName .A))) ==
       Option.map List.Vector.toList (uuidTryParse (utf8 (partyAddressName .B)))) = false := by
    rfl_kernel
  rw [hA, hB, beq_self_eq_true] at hfalse
  cases hfalse

end CryptoVerification.E2E.Pqxdh.WireEntries

namespace CryptoVerification.E2E.Pqxdh.TopLevel

open CryptoGames.LibsignalSession
open CryptoVerification.E2E CryptoVerification.E2E.Record CryptoVerification.E2E.RecordX
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.WireEntries

theorem encodeRecordX_initiateExtras_eq (me : LocalIdentity) (b : PreKeyBundleFields) (base : PublicKey)
    (ct : List.Vector (BitVec 8) 1568) (g : GhostState Bytes) :
    encodeRecordUnderExtras (fun _ => initiatorRecordExtras me b base ct) g =
      Record.encodeRecord ⟨some (RecordX.sessionOfX (fun _ => initiatorRecordExtras me b base ct) g)⟩ :=
  encodeRecordX_eq_encodeRecord_sessionOfX (fun _ => initiatorRecordExtras me b base ct) g

end CryptoVerification.E2E.Pqxdh.TopLevel
