/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs

/-!
# Session-Record Canonicality and Primitive Bridges

Establishes canonical-scope properties (`slots_RecordScopeP`, `slots_RecordInScopeP`,
`slots_DeserializeScopeP_Q`, and `slots_RecordCanonical_Q`) for `PqxdhPartyInSpecDomain` sessions,
equates `encodeRecordUnderExtras` with `recordBytes`, and bridges `PEParams` encryption and
decryption primitives to `ExternInterpretation` via `ModelHookBridge`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY.Libsignal (HwBytes)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.RecordX
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (AesW interpW cbcW)
open Symbolic.Swarm.CREF.TR.Pure (PureRecordRepr slots_SessionScopeP slots_NonEmptyV1Q
  slots_DeserializeScopeP_Q slots_RecordScopeP slots_RecordInScopeP slots_RecordCanonical_Q)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

attribute [local simp] mut_exec_pure mut_exec_throw mut_exec_get mut_exec_set
  mut_exec_modify mut_exec_modifyGet mut_exec_liftE mut_exec_bind mut_exec_onRatchet

/-! ## Canonical Scope under `PqxdhPartyInSpecDomain` -/

theorem recordScopeP_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    slots_RecordScopeP slots_NonEmptyV1Q ⟨some (pqSession x g)⟩ :=
  recordScopeP_of_encodeRecordX_length x g (by have := (reachPqInvPure_of_wfPq hwf hsess).2.2; omega)

theorem recordInScopeP_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    slots_RecordInScopeP ⟨some (pqSession x g)⟩ := by
  obtain ⟨⟨_, hseeds, hrcLe, _, _, _, _, _, _, _, hkyb⟩, _, _⟩ := reachPqInvPure_of_wfPq hwf hsess
  intro s hs; injection hs with hs'; subst hs'
  refine ⟨hseeds, by dsimp [pqSession]; unfold maxReceiverChains at hrcLe; omega, fun k hk => ?_⟩
  simp only [pqSession_pendingKyberPreKey] at hk
  split at hk
  · have := hkyb k hk; omega
  · cases hk

theorem deserializeScopeP_Q_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some (pqSession x g)⟩ := by
  obtain ⟨⟨_, _, hrcLe, _, _, hrep, _, hts, _, habk, hkyb⟩, _, _⟩ := reachPqInvPure_of_wfPq hwf hsess
  let sx := pqSession x g
  have hrecRepr : PureRecordRepr ⟨some sx⟩ := by
    intro s hs; injection hs with hs'; subst hs'
    refine ⟨hrep.1, hrep.2, ?_, by simp only [sx, pqSession_aliceBaseKey]; omega⟩
    dsimp [Session.Wf, sx, pqSession]; cases g.session.pendingPreKey <;> rfl
  have hsessScopeP : slots_SessionScopeP sx := by
    refine ⟨hrcLe, fun p hp => ?_, fun k hk => ?_, Or.inr (by simpa only [sx, pqSession_aliceBaseKey] using habk)⟩
    · simp only [sx, pqSession_pendingPreKey] at hp
      split at hp
      · injection hp with hp'; subst hp'; exact hts
      · cases hp
    · simp only [sx, pqSession_pendingKyberPreKey] at hk
      split at hk
      · exact hkyb k hk
      · cases hk
  exact ⟨⟨recordInScopeP_of_wfPq hwf hsess, recordScopeP_of_wfPq hwf hsess, hrecRepr⟩, sx, rfl, hsessScopeP⟩

/-- Every session stored in a `PqxdhPartyInSpecDomain` state encodes canonically under
`slots_NonEmptyV1Q`. -/
theorem recordCanonical_Q_of_wfPq {W : PEParams} {st : PqParty}
    {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    slots_RecordCanonical_Q slots_NonEmptyV1Q (encodeRecordUnderExtras (fun _ => x) g) (pqSession x g) := by
  have hdeser := deserializeScopeP_Q_of_wfPq hwf hsess
  have henc := encodeRecordX_eq_encodeRecord_pqSession x g
  exact ⟨henc, hdeser, pureBinCanonSession_of_deserializeScopeP_Q_any hdeser⟩

/-! ## Session-Record Serialization Bridges -/

/-- Converts a `Session HwBytes` (including any `pendingPreKey` and `pendingKyberPreKey` payloads)
into a `DY.Libsignal.Rust.RecordRec` with `previous = []`. -/
def sessionToRecordRecPending (s : Session HwBytes) : DY.Libsignal.Rust.RecordRec where
  current :=
    { Swarm.Phase0WholeFunctionBridge.sessionToSessionRec s with
      pendingPreKey := s.pendingPreKey.map fun p =>
        (CryptoVerification.E2E.Record.encPendingPreKey p, [])
      pendingKyberPreKey := s.pendingKyberPreKey.map fun p =>
        (CryptoVerification.E2E.Record.encPendingKyber p, []) }
  previous := []

theorem sessionToRecordRecPending_eq_sessionToRecordRec (s : Session HwBytes)
    (hppk : s.pendingPreKey = none) (hpkp : s.pendingKyberPreKey = none) :
    sessionToRecordRecPending s = Swarm.Phase0WholeFunctionBridge.sessionToRecordRec s := by
  simp [sessionToRecordRecPending, Swarm.Phase0WholeFunctionBridge.sessionToRecordRec,
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec, hppk, hpkp]

private theorem lenField_payload_le (tag : Nat) (b : HwBytes) :
    b.length ≤ (CryptoVerification.E2E.Record.lenField tag b).length := by
  unfold CryptoVerification.E2E.Record.lenField
  simp only [List.length_append]
  omega

private theorem record_bytesField_payload_le (tag : Nat) (b : HwBytes) :
    b.length ≤ (CryptoVerification.E2E.Record.bytesField tag b).length := by
  unfold CryptoVerification.E2E.Record.bytesField
  split_ifs with hb
  · simp [hb]
  · exact lenField_payload_le tag b

private theorem record_msgField_some_payload_le (tag : Nat) (b : HwBytes) :
    b.length ≤ (CryptoVerification.E2E.Record.msgField tag (some b)).length :=
  lenField_payload_le tag b

private theorem flatten_map_lenField_ge {α : Type} (tag : Nat) (f : α → HwBytes)
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤ (l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten.length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have := lenField_payload_le tag (f x); omega
    · have := ih hmem; omega

private theorem encReceiverChain_le_encSession (s : Session HwBytes)
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := flatten_map_lenField_ge 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

private theorem seed_le_encReceiverChain (rc : ReceiverChain)
    (mk : MessageKeyGenerator) (hmk : mk ∈ rc.messageKeys) :
    mk.seed.length ≤ (CryptoVerification.E2E.Record.encReceiverChain rc).length := by
  have h1 := flatten_map_lenField_ge 4 CryptoVerification.E2E.Record.encMessageKey
    rc.messageKeys mk hmk
  have h2 := record_bytesField_payload_le 5 mk.seed
  have h3 : (CryptoVerification.E2E.Record.bytesField 5 mk.seed).length ≤
      (CryptoVerification.E2E.Record.encMessageKey mk).length := by
    unfold CryptoVerification.E2E.Record.encMessageKey; simp only [List.length_append]; omega
  unfold CryptoVerification.E2E.Record.encReceiverChain; simp only [List.length_append]; omega

private theorem encSession_le_encodeRecord (s : Session HwBytes) :
    (CryptoVerification.E2E.Record.encSession s).length ≤
      (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length := by
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
  dsimp only [Option.map_some]
  exact lenField_payload_le 1 (CryptoVerification.E2E.Record.encSession s)

theorem recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
    (s : Session HwBytes)
    (hlen : (CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩).length < 2 ^ 63) :
    DY.Libsignal.Composed.Refinement.recordBytes (sessionToRecordRecPending s) =
      CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  have hsess_full : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (encSession_le_encodeRecord s) hlen
  let recEnc := CryptoVerification.E2E.Record.encSession
  have hsess : (recEnc s).length < 2 ^ 63 := hsess_full
  have hbf_lt : ∀ (tag : Nat) (b : HwBytes),
      (CryptoVerification.E2E.Record.bytesField tag b).length ≤ (recEnc s).length →
      b.length < 2 ^ 64 := fun tag b hle => by
    have := record_bytesField_payload_le tag b; omega
  have hloc_len : s.state.localIdentity.serialize.length < 2 ^ 64 :=
    hbf_lt 2 _ (by dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; simp only [List.length_append]; omega)
  have hrem_len : ((s.state.remoteIdentity.map
      CryptoGames.LibsignalSession.IdentityKey.serialize).getD []).length < 2 ^ 64 :=
    hbf_lt 3 _ (by dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; simp only [List.length_append]; omega)
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 s.state.rootKey).length < 2 ^ 64 :=
    hbf_lt 4 _ (by dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; simp only [List.length_append]; omega)
  have halice : s.aliceBaseKey.length < 2 ^ 64 :=
    hbf_lt 13 _ (by dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; simp only [List.length_append]; omega)
  have hpq : s.state.pqRatchetState.length < 2 ^ 64 :=
    hbf_lt 15 _ (by dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; simp only [List.length_append]; omega)
  have hsc_eq :
      ((s.state.senderChain.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec).map
        fun sc => DY.Libsignal.Composed.Refinement.msgField 6
          (DY.Libsignal.Composed.Refinement.chainBytes sc)).getD [] =
      CryptoVerification.E2E.Record.msgField 6
        (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
    cases hsc : s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 6 (CryptoVerification.E2E.Record.encSenderChain sc)
        have h2 : (CryptoVerification.E2E.Record.msgField 6
            (some (CryptoVerification.E2E.Record.encSenderChain sc))).length ≤ (recEnc s).length := by
          dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; rw [hsc]
          simp only [Option.map_some, List.length_append]; omega
        omega
      unfold Swarm.Phase0WholeFunctionBridge.senderChainToChainRec
      rw [Swarm.Phase0WholeFunctionBridge.chainBytes_sender_eq_encSenderChain sc,
          Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 6 _ hsc_len]
  have hrc_eq :
      ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).flatMap
        fun rc => DY.Libsignal.Composed.Refinement.msgField 7
          (DY.Libsignal.Composed.Refinement.chainBytes rc)) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7
          (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
    rw [List.flatMap_map, List.flatMap_def]; congr 1
    apply List.map_congr_left; intro rc hrc
    have hrc_lt : (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 := by
      have := encReceiverChain_le_encSession s rc hrc; omega
    have hseeds : ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := fun mk hmk => by
      have := seed_le_encReceiverChain rc mk hmk
      have := encReceiverChain_le_encSession s rc hrc; omega
    rw [Swarm.Phase0WholeFunctionBridge.chainBytes_receiver_eq_encReceiverChain rc hseeds,
        Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 7 _ hrc_lt]
  have hppk_eq :
      (((s.pendingPreKey.map fun p =>
          (CryptoVerification.E2E.Record.encPendingPreKey p, ([] : HwBytes))).map
        fun p => DY.Libsignal.Composed.Refinement.msgField 9 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 9
        (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hp_len : (CryptoVerification.E2E.Record.encPendingPreKey p).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 9 (CryptoVerification.E2E.Record.encPendingPreKey p)
        have h2 : (CryptoVerification.E2E.Record.msgField 9
            (some (CryptoVerification.E2E.Record.encPendingPreKey p))).length ≤ (recEnc s).length := by
          dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; rw [hppk]
          simp only [Option.map_some, List.length_append]; omega
        omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 9 _ hp_len
  have hpkp_eq :
      (((s.pendingKyberPreKey.map fun p =>
          (CryptoVerification.E2E.Record.encPendingKyber p, ([] : HwBytes))).map
        fun p => DY.Libsignal.Composed.Refinement.msgField 14 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 14
        (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hp_len : (CryptoVerification.E2E.Record.encPendingKyber p).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 14 (CryptoVerification.E2E.Record.encPendingKyber p)
        have h2 : (CryptoVerification.E2E.Record.msgField 14
            (some (CryptoVerification.E2E.Record.encPendingKyber p))).length ≤ (recEnc s).length := by
          dsimp only [recEnc, CryptoVerification.E2E.Record.encSession]; rw [hpkp]
          simp only [Option.map_some, List.length_append]; omega
        omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 14 _ hp_len
  unfold DY.Libsignal.Composed.Refinement.recordBytes sessionToRecordRecPending
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
    CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
  simp only [List.flatMap_nil, List.append_nil, Option.map_some, Function.comp_def]
  have hbody :
      DY.Libsignal.Composed.Refinement.u32Field 1 s.state.sessionVersion ++
        DY.Libsignal.Composed.Refinement.bytesField 2 s.state.localIdentity.serialize ++
        DY.Libsignal.Composed.Refinement.bytesField 3 ((s.state.remoteIdentity.map
          CryptoGames.LibsignalSession.IdentityKey.serialize).getD []) ++
        DY.Libsignal.Composed.Refinement.bytesField 4 (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ++
        DY.Libsignal.Composed.Refinement.u32Field 5 s.state.previousCounter ++
        ((s.state.senderChain.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec).map
          fun sc => DY.Libsignal.Composed.Refinement.msgField 6
            (DY.Libsignal.Composed.Refinement.chainBytes sc)).getD [] ++
        ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).flatMap
          fun rc => DY.Libsignal.Composed.Refinement.msgField 7
            (DY.Libsignal.Composed.Refinement.chainBytes rc)) ++
        (((s.pendingPreKey.map fun p =>
            (CryptoVerification.E2E.Record.encPendingPreKey p, ([] : HwBytes))).map
          fun p => DY.Libsignal.Composed.Refinement.msgField 9 (p.1 ++ p.2)).getD []) ++
        DY.Libsignal.Composed.Refinement.u32Field 10 s.remoteRegistrationId ++
        DY.Libsignal.Composed.Refinement.u32Field 11 s.localRegistrationId ++
        DY.Libsignal.Composed.Refinement.bytesField 13 s.aliceBaseKey ++
        (((s.pendingKyberPreKey.map fun p =>
            (CryptoVerification.E2E.Record.encPendingKyber p, ([] : HwBytes))).map
          fun p => DY.Libsignal.Composed.Refinement.msgField 14 (p.1 ++ p.2)).getD []) ++
        DY.Libsignal.Composed.Refinement.bytesField 15 s.state.pqRatchetState =
      CryptoVerification.E2E.Record.encSession s := by
    unfold CryptoVerification.E2E.Record.encSession
    rw [Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 1,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 2 _ hloc_len,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 3 _ hrem_len,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 4 _ hrk_len,
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 5,
        hsc_eq, hrc_eq, hppk_eq,
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 10,
        Swarm.Phase0WholeFunctionBridge.u32Field_eq_uint32Field 11,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 13 _ halice,
        hpkp_eq,
        Swarm.Phase0WholeFunctionBridge.bytesField_eq_record_bytesField 15 _ hpq]
  rw [hbody, Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 1 _ (by omega)]

theorem encodeRecordX_eq_recordBytesPending_of_wfPq
    {W : PEParams} {st : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g)) :
    encodeRecordUnderExtras (fun _ => x) g =
      DY.Libsignal.Composed.Refinement.recordBytes
        (sessionToRecordRecPending (pqSession x g)) := by
  have hlen31 := (reachPqInvPure_of_wfPq hwf hsess).2.2
  have henc := encodeRecordX_eq_encodeRecord_pqSession x g
  have hlen63 : (CryptoVerification.E2E.Record.encodeRecord ⟨some (pqSession x g)⟩).length < 2 ^ 63 := by
    rw [← henc]; omega
  rw [henc, recordBytes_sessionToRecordRecPending_of_encodeRecord_lt (pqSession x g) hlen63]

theorem encodeRecordX_eq_recordBytes_of_wfPq
    {W : PEParams} {st : PqParty} {x : RecordExtras} {g : GhostState HwBytes}
    (hwf : PqxdhPartyInSpecDomain W st) (hsess : st.session = some (x, g))
    (hppk : g.session.pendingPreKey = false) :
    encodeRecordUnderExtras (fun _ => x) g =
      DY.Libsignal.Composed.Refinement.recordBytes
        (Swarm.Phase0WholeFunctionBridge.sessionToRecordRec (pqSession x g)) := by
  rw [encodeRecordX_eq_recordBytesPending_of_wfPq hwf hsess,
      sessionToRecordRecPending_eq_sessionToRecordRec (pqSession x g)
        (pqSession_pendingPreKey_of_false x g hppk)
        (pqSession_pendingKyberPreKey_of_false x g hppk)]

/-! ## Primitive Hook Bridge and Coin Irrelevance -/

theorem tryDecryptFromRecordW_congr_crypto {PQ PQC : Type} [Inhabited PQ]
    {C₁ C₂ : Crypto} (hF : C₁.F = C₂.F) (hX : C₁.X = C₂.X) (hpub : C₁.pubKey = C₂.pubKey)
    (W_aes : AesW) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (ty : MessageType) (coins : BitVec 256) (st : SessionState PQ) :
    Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C₁ W_aes spqr expected msg ty coins st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C₂ W_aes spqr expected msg ty coins st := by
  cases C₁; cases C₂; dsimp at hF hX hpub; subst hF hX hpub; rfl

theorem messageEncryptW_congr_crypto {PQ PQC : Type} [Inhabited PQ]
    {C₁ C₂ : Crypto} (hF : C₁.F = C₂.F) (W_aes : AesW) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (addrs : Option (List (BitVec 8))) (m : List (BitVec 8)) (r : PQC) (st : SessionState PQ) :
    Proofs.libsignal.SR.SessionState.messageEncryptW C₁ W_aes codec spqr addrs m r st =
      Proofs.libsignal.SR.SessionState.messageEncryptW C₂ W_aes codec spqr addrs m r st := by
  cases C₁; cases C₂; dsimp at hF; subst hF; rfl

/-- Agreement of cryptographic, AES-CBC, and SPQR primitives between `interp : ExternInterpretation`
and `W : PEParams`. -/
structure ModelHookBridge (interp : ExternInterpretation) (W : PEParams) : Prop where
  crypto    : W.C = cryptoOf' interp W.C.E W.C.D
  aesCbc    : interpW interp = cbcW W.C
  spqrModel : pqxdhSpqrModel W = spqrModelOf interp

/-- Pure `Spqr` record induced by `spqrModelOf interp`. -/
def pureSpqrOf (interp : ExternInterpretation) : Spqr HwBytes HwBytes :=
  let M := spqrModelOf interp
  ⟨fun _ _ => [], M.send, M.recv, M.sendPanics, M.recvPanics⟩

theorem tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_bridge
    {interp : ExternInterpretation} {W : PEParams} (hb : ModelHookBridge interp W)
    (expected : Option HwBytes) (msg : SignalMessage) (ty : MessageType)
    (coins : BitVec 256) (st : SessionState HwBytes) :
    SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) expected msg ty coins st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
        (interpW interp) (pureSpqrOf interp) expected msg ty coins st := by
  have hcbc : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) expected msg ty coins st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW (cryptoOf' interp)
        (interpW interp) (pqxdhSpqrSession W) expected msg ty coins st := by
    rw [← Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW_cbcW, ← hb.aesCbc]
    exact tryDecryptFromRecordW_congr_crypto (by rw [hb.crypto]; rfl) (by rw [hb.crypto]; rfl)
      (by rw [hb.crypto]; rfl) (interpW interp) (pqxdhSpqrSession W) expected msg ty coins st
  rw [hcbc]
  have hrecv : (pqxdhSpqrSession W).recv = (pureSpqrOf interp).recv := by
    change (pqxdhSpqrModel W).recv = (spqrModelOf interp).recv; rw [hb.spqrModel]
  have hpan : (pqxdhSpqrSession W).recvPanics = (pureSpqrOf interp).recvPanics := by
    change (pqxdhSpqrModel W).recvPanics = (spqrModelOf interp).recvPanics; rw [hb.spqrModel]
  unfold Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
  split
  · rfl
  · suffices h : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        (cryptoOf' interp) (interpW interp) (pqxdhSpqrSession W) expected msg ty coins) st =
        Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
          (cryptoOf' interp) (interpW interp) (pureSpqrOf interp) expected msg ty coins) st by
      rw [h]
    unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      Proofs.libsignal.SR.TripleRatchet.decryptW
    simp only [hrecv, hpan]

theorem messageEncrypt_eq_messageEncryptW_of_bridge
    {interp : ExternInterpretation} {W : PEParams} (hb : ModelHookBridge interp W)
    (addrs : Option HwBytes) (m r : HwBytes) (st : SessionState HwBytes) :
    SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W) addrs m r st =
      Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
        (interpW interp) protoSignalCodec (pureSpqrOf interp) addrs m r st := by
  have hcbc : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W) addrs m r st =
      Proofs.libsignal.SR.SessionState.messageEncryptW (cryptoOf' interp)
        (interpW interp) protoSignalCodec (pqxdhSpqrSession W) addrs m r st := by
    rw [← Proofs.libsignal.SR.SessionState.messageEncryptW_cbcW, ← hb.aesCbc]
    exact messageEncryptW_congr_crypto (by rw [hb.crypto]; rfl)
      (interpW interp) protoSignalCodec (pqxdhSpqrSession W) addrs m r st
  rw [hcbc]
  have hsend : (pqxdhSpqrSession W).send = (pureSpqrOf interp).send := by
    change (pqxdhSpqrModel W).send = (spqrModelOf interp).send; rw [hb.spqrModel]
  have hpan : (pqxdhSpqrSession W).sendPanics = (pureSpqrOf interp).sendPanics := by
    change (pqxdhSpqrModel W).sendPanics = (spqrModelOf interp).sendPanics; rw [hb.spqrModel]
  unfold Proofs.libsignal.SR.SessionState.messageEncryptW
  rcases Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | session, taken⟩
  · rfl
  · suffices h : Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW
        (cryptoOf' interp) (interpW interp) protoSignalCodec (pqxdhSpqrSession W) m
        (st.encryptAddresses addrs) r) session =
        Mut.exec (Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW
          (cryptoOf' interp) (interpW interp) protoSignalCodec (pureSpqrOf interp) m
          (st.encryptAddresses addrs) r) session by
      dsimp only; rw [h]
    unfold Proofs.libsignal.SR.OutgoingTripleRatchet.encryptW
    simp only [hsend, hpan]

/-- Predicate characterizing when `tryDecryptWithState` draws fresh DH ratchet coins. -/
def drawsCoins {PQ : Type} (C : Crypto) (st : SessionState PQ) (their : PublicKey) : Bool :=
  st.remoteIdentity.isSome &&
    match RatchetState.findReceiverChainKey
        ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
        their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false

theorem ensureReceiverChain_coins_irrel_of_drawsCoins_false {PQ : Type}
    (C : Crypto) (st : SessionState PQ) (their : PublicKey) (c₁ c₂ : BitVec 256)
    (hrem : st.remoteIdentity.isSome = true)
    (hno : drawsCoins C st their = false) :
    let r0 : RatchetState :=
      ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩
    Mut.exec (RatchetState.ensureReceiverChain C their c₁) r0 =
      Mut.exec (RatchetState.ensureReceiverChain C their c₂) r0 := by
  intro r0
  unfold drawsCoins at hno
  rw [hrem, Bool.true_and] at hno
  change (match RatchetState.findReceiverChainKey r0 their with
    | .ok none =>
      match st.senderChain with
      | some sc =>
        match rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with
        | .ok _ => true
        | .error _ => false
      | none => false
    | _ => false) = false at hno
  unfold RatchetState.ensureReceiverChain
  simp only [mut_exec_bind, mut_exec_get, mut_exec_liftE]
  rcases hf : r0.findReceiverChainKey their with e | (_ | ck)
  · rfl
  · simp only [hf] at hno
    unfold RatchetState.dhRatchetStep
    simp only [mut_exec_bind, mut_exec_get]
    rcases hsc : st.senderChain with _ | sc
    · simp only [r0, hsc]
    · simp only [hsc] at hno
      simp only [r0, hsc, RatchetState.takeRootKey, mut_exec_modifyGet, mut_exec_bind, mut_exec_liftE]
      rcases hrc : rootCreateChain C st.rootKey their sc.ratchetKey.privateKey with err | rkck
      · rfl
      · rw [hrc] at hno; cases hno
  · rfl

/-- When `drawsCoins C st msg.senderRatchetKey = false` and `st.remoteIdentity.isSome = true`,
`SessionState.tryDecryptFromRecordW` is independent of the coin input. -/
theorem tryDecryptFromRecordW_coins_irrel_of_drawsCoins_false {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (W_aes : AesW) (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (msg : SignalMessage) (msgType : MessageType)
    (c₁ c₂ : BitVec 256) (st : SessionState PQ)
    (hrem : st.remoteIdentity.isSome = true)
    (hno : drawsCoins C st msg.senderRatchetKey = false) :
    Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr expected msg msgType c₁ st =
      Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW C W_aes spqr expected msg msgType c₂ st := by
  unfold Proofs.libsignal.SR.SessionState.tryDecryptFromRecordW
  split
  · rfl
  · suffices h : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
        expected msg msgType c₁) st =
        Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW C W_aes spqr
          expected msg msgType c₂) st by
      rw [h]
    cases hrem_opt : st.remoteIdentity with
    | none => rw [hrem_opt] at hrem; cases hrem
    | some remIk =>
      have hens := ensureReceiverChain_coins_irrel_of_drawsCoins_false C st msg.senderRatchetKey
        c₁ c₂ hrem hno
      unfold Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        TripleRatchet.fromSessionState SessionState.takeRatchetState SessionState.takePqRatchetState
      simp only [hrem_opt, mut_exec_bind, mut_exec_modifyGet, mut_exec_get, mut_exec_pure]
      suffices htr : ∀ (tr : TripleRatchet PQ),
          tr.ratchet = ⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩ →
          Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W_aes spqr expected msg msgType c₁) tr =
            Mut.exec (Proofs.libsignal.SR.TripleRatchet.decryptW C W_aes spqr expected msg msgType c₂) tr by
        rw [htr _ rfl]
      intro tr htr_eq
      unfold Proofs.libsignal.SR.TripleRatchet.decryptW
      simp only [mut_exec_bind, mut_exec_onRatchet]
      rw [htr_eq, hens]

end Symbolic.Swarm.CREF.Cli
