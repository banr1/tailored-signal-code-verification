/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
public import Symbolic.Proofs.Swarm.TRREF.B3DefsPure
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# SPQR State Agreement Across Canonical Session Records

Relates `pqRatchetState` and `sessionVersion` across `StateRel`, canonical session
records with optional pending pre-key fields, and `SpqrRecvStepOut`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents
open DY.Libsignal.Rust
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Record (encSession encSenderChain encReceiverChain encChainKey
  encPendingPreKey encPendingKyber)
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)

open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.TRREF.SpqrSemOf (saltToBytes)
open Swarm.Phase0WholeFunctionBridge
  (senderChainToChainRec receiverChainToChainRec sessionToSessionRec sessionToRecordRec
   u32Field_eq_uint32Field msgField_eq_lenField bytesField_eq_record_bytesField
   lenField_length_le record_bytesField_length_le encChainKey_length_lt encMessageKey_length_le
   chainBytes_sender_eq_encSenderChain chainBytes_receiver_eq_encReceiverChain)
open DY.Libsignal.Refinement (PbValue encodeField)

/-! ## Field preservation and pending-pre-key normalization -/

@[simp] theorem eraseSkipped_pqRatchetState (s : SessionRec) :
    (eraseSkipped s).pqRatchetState = s.pqRatchetState := rfl

@[simp] theorem eraseUnmodelled_pqRatchetState (s : SessionRec) :
    (eraseUnmodelled s).pqRatchetState = s.pqRatchetState := rfl

@[simp] theorem sessionOf_pqRatchetState (i : ExternInterpretation) (gam : DY.Bytes → HwBytes)
    (st : TRState) :
    (sessionOf i gam st).pqRatchetState = gam st.spqr := rfl

@[simp] theorem eraseSkipped_sessionVersion (s : SessionRec) :
    (eraseSkipped s).sessionVersion = s.sessionVersion := rfl

@[simp] theorem eraseUnmodelled_sessionVersion (s : SessionRec) :
    (eraseUnmodelled s).sessionVersion = s.sessionVersion := rfl

@[simp] theorem sessionOf_sessionVersion (i : ExternInterpretation) (gam : DY.Bytes → HwBytes)
    (st : TRState) :
    (sessionOf i gam st).sessionVersion = 4#32 := rfl

@[simp] theorem eraseSkipped_pendingPreKey (s : SessionRec) :
    (eraseSkipped s).pendingPreKey = s.pendingPreKey := rfl

@[simp] theorem eraseUnmodelled_pendingPreKey (s : SessionRec) :
    (eraseUnmodelled s).pendingPreKey = none := rfl

@[simp] theorem sessionOf_pendingPreKey (i : ExternInterpretation) (gam : DY.Bytes → HwBytes)
    (st : TRState) :
    (sessionOf i gam st).pendingPreKey = none := rfl

@[simp] theorem eraseSkipped_pendingKyberPreKey (s : SessionRec) :
    (eraseSkipped s).pendingKyberPreKey = s.pendingKyberPreKey := rfl

@[simp] theorem eraseUnmodelled_pendingKyberPreKey (s : SessionRec) :
    (eraseUnmodelled s).pendingKyberPreKey = none := rfl

@[simp] theorem sessionOf_pendingKyberPreKey (i : ExternInterpretation) (gam : DY.Bytes → HwBytes)
    (st : TRState) :
    (sessionOf i gam st).pendingKyberPreKey = none := rfl

@[simp] theorem sessionToSessionRec_pqRatchetState (s : Session (List (BitVec 8))) :
    (sessionToSessionRec s).pqRatchetState = s.state.pqRatchetState := rfl

@[simp] theorem sessionToSessionRec_sessionVersion (s : Session (List (BitVec 8))) :
    (sessionToSessionRec s).sessionVersion = s.state.sessionVersion := rfl

@[simp] theorem sessionToRecordRec_current (s : Session (List (BitVec 8))) :
    (sessionToRecordRec s).current = sessionToSessionRec s := rfl

@[simp] theorem sessionToRecordRec_previous (s : Session (List (BitVec 8))) :
    (sessionToRecordRec s).previous = [] := rfl

/-- `sessionToRecordRecPending` preserves `pendingPreKey` (field 9) and `pendingKyberPreKey`
(field 14) as `(encPendingPreKey p, [])` and `(encPendingKyber p, [])` so composed `recordBytes`
matches `encodeRecord ⟨some s⟩` without any no-pending hypothesis. -/
def sessionToRecordRecPending (s : Session (List (BitVec 8))) : RecordRec :=
  { current :=
      { (sessionToSessionRec s) with
        pendingPreKey := s.pendingPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingPreKey p, []),
        pendingKyberPreKey := s.pendingKyberPreKey.map fun p => (CryptoVerification.E2E.Record.encPendingKyber p, []) },
    previous := [] }

@[simp] theorem normPendingS_pqRatchetState (s : SessionRec) :
    (normPendingS s).pqRatchetState = s.pqRatchetState := rfl

@[simp] theorem normPendingS_sessionVersion (s : SessionRec) :
    (normPendingS s).sessionVersion = s.sessionVersion := rfl

@[simp] theorem normPendingS_receiverChains (s : SessionRec) :
    (normPendingS s).receiverChains = s.receiverChains := rfl

@[simp] theorem normPending_current (rec : RecordRec) :
    (normPending rec).current = normPendingS rec.current := rfl

@[simp] theorem normPending_previous (rec : RecordRec) :
    (normPending rec).previous = rec.previous := rfl

@[simp] theorem eraseUnmodelled_normPendingS (s : SessionRec) :
    eraseUnmodelled (normPendingS s) = eraseUnmodelled s := rfl

@[simp] theorem eraseUnmodelled_sessionToRecordRecPending (s : Session (List (BitVec 8))) :
    eraseUnmodelled (sessionToRecordRecPending s).current =
      eraseUnmodelled (sessionToSessionRec s) := rfl

theorem stateRel_normPending_iff (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st : TRState) (rec : RecordRec) :
    StateRel interpretation S g st (normPending rec) ↔ StateRel interpretation S g st rec := Iff.rfl

theorem stateRel_sessionToRecordRecPending_iff (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st : TRState) (s : Session (List (BitVec 8))) :
    StateRel interpretation S g st (sessionToRecordRecPending s) ↔
      StateRel interpretation S g st (sessionToRecordRec s) := Iff.rfl

theorem stateRel_pqRatchetState_and_sessionVersion
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {rec : RecordRec}
    (hrel : StateRel interpretation S g st rec) :
    rec.current.pqRatchetState = gamma interpretation S g st.spqr ∧
    rec.current.sessionVersion = 4#32 := by
  have hpq := congrArg SessionRec.pqRatchetState hrel.2
  have hver := congrArg SessionRec.sessionVersion hrel.2
  simp only [eraseSkipped_pqRatchetState, eraseUnmodelled_pqRatchetState, sessionOf_pqRatchetState,
    eraseSkipped_sessionVersion, eraseUnmodelled_sessionVersion, sessionOf_sessionVersion] at hpq hver
  exact ⟨hpq, hver⟩

/-! ## Canonical record encoding bridge -/

private def pbFields (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap (fun p => encodeField p.1 0 0 p.2)

private theorem pbFields_append_spqr (l₁ l₂ : List (Nat × PbValue)) :
    pbFields (l₁ ++ l₂) = pbFields l₁ ++ pbFields l₂ := by
  simp only [pbFields, List.flatMap_append]

private def bytesFieldList_spqr (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private def u32FieldList_spqr (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

private theorem pbFields_bytesFieldList_spqr (tag : Nat) (b : HwBytes) :
    pbFields (bytesFieldList_spqr tag b) = bytesField tag b := by
  unfold bytesFieldList_spqr bytesField; split <;> simp [pbFields]

private theorem pbFields_u32FieldList_spqr (tag : Nat) (v : BitVec 32) :
    pbFields (u32FieldList_spqr tag v) = u32Field tag v := by
  unfold u32FieldList_spqr u32Field; split <;> simp [pbFields]

private theorem pbFields_map_msgField7_spqr (l : List ChainRec) :
    pbFields (l.map fun c => (7, PbValue.bytes (chainBytes c))) =
    l.flatMap (msgField 7 ∘ chainBytes) := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, pbFields, List.flatMap_cons, msgField, Function.comp_apply]
    congr 1

private def encSessionFields_spqr (s : Session (List (BitVec 8))) : List (Nat × PbValue) :=
  let st := s.state
  u32FieldList_spqr 1 st.sessionVersion ++
  bytesFieldList_spqr 2 st.localIdentity.serialize ++
  bytesFieldList_spqr 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesFieldList_spqr 4 (HMAC.keyToBytes32 st.rootKey) ++
  u32FieldList_spqr 5 st.previousCounter ++
  ((st.senderChain.map (fun c => [(6, PbValue.bytes (chainBytes (senderChainToChainRec c)))])).getD []) ++
  (st.receiverChains.map receiverChainToChainRec).map (fun c => (7, PbValue.bytes (chainBytes c))) ++
  ((s.pendingPreKey.map (fun p => [(9, PbValue.bytes (encPendingPreKey p))])).getD []) ++
  u32FieldList_spqr 10 s.remoteRegistrationId ++
  u32FieldList_spqr 11 s.localRegistrationId ++
  bytesFieldList_spqr 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map (fun p => [(14, PbValue.bytes (encPendingKyber p))])).getD []) ++
  bytesFieldList_spqr 15 st.pqRatchetState

private theorem flatten_map_lenField_length_ge_spqr {α : Type} (tag : Nat) (f : α → List (BitVec 8))
    (l : List α) (x : α) (hx : x ∈ l) :
    (f x).length ≤
      ((l.map fun c => CryptoVerification.E2E.Record.lenField tag (f c)).flatten).length := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · unfold CryptoVerification.E2E.Record.lenField; simp only [List.length_append]; omega
    · have := ih hmem; omega

private theorem encReceiverChain_length_le_encSession_spqr (s : Session (List (BitVec 8)))
    (rc : ReceiverChain) (hrc : rc ∈ s.state.receiverChains) :
    (CryptoVerification.E2E.Record.encReceiverChain rc).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  have h1 := flatten_map_lenField_length_ge_spqr 7 CryptoVerification.E2E.Record.encReceiverChain
    s.state.receiverChains rc hrc
  unfold CryptoVerification.E2E.Record.encSession; simp only [List.length_append]; omega

private theorem encPendingPreKey_length_le_encSession_spqr (s : Session (List (BitVec 8)))
    (p : PendingPreKey) (hp : s.pendingPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingPreKey p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

private theorem encPendingKyber_length_le_encSession_spqr (s : Session (List (BitVec 8)))
    (p : PendingKyberPreKey) (hp : s.pendingKyberPreKey = some p) :
    (CryptoVerification.E2E.Record.encPendingKyber p).length ≤
      (CryptoVerification.E2E.Record.encSession s).length := by
  unfold CryptoVerification.E2E.Record.encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]; simp only [List.length_append]; omega

private theorem pbFields_singleton_bytes_spqr (tag : Nat) (b : HwBytes) :
    pbFields [(tag, PbValue.bytes b)] = msgField tag b := by
  simp [pbFields, msgField]

private theorem pbFields_encSessionFields_spqr (s : Session (List (BitVec 8)))
    (halice : s.aliceBaseKey.length < 2 ^ 63) (hpq : s.state.pqRatchetState.length < 2 ^ 63)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    pbFields (encSessionFields_spqr s) = CryptoVerification.E2E.Record.encSession s := by
  have hloc_len : s.state.localIdentity.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hrem_len :
      ((s.state.remoteIdentity.map IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases s.state.remoteIdentity <;> simp [IdentityKey.serialize, PublicKey.serialize]
  have hrk_len : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by simp [HMAC.keyToBytes32]
  have hsc_eq :
      pbFields ((s.state.senderChain.map
        (fun c => [(6, PbValue.bytes (chainBytes (senderChainToChainRec c)))])).getD []) =
      CryptoVerification.E2E.Record.msgField 6
        (s.state.senderChain.map CryptoVerification.E2E.Record.encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_spqr]
      have hcb : chainBytes (senderChainToChainRec sc) =
          CryptoVerification.E2E.Record.encSenderChain sc := chainBytes_sender_eq_encSenderChain sc
      rw [hcb]
      have hsc_len : (CryptoVerification.E2E.Record.encSenderChain sc).length < 2 ^ 64 := by
        unfold CryptoVerification.E2E.Record.encSenderChain; dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := lenField_length_le 3 (CryptoVerification.E2E.Record.encChainKey sc.chainKey)
        have h4 := encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by simp [PublicKey.serialize]
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 := List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact msgField_eq_lenField 6 _ hsc_len
  have hrc_eq :
      pbFields ((s.state.receiverChains.map receiverChainToChainRec).map
        (fun c => (7, PbValue.bytes (chainBytes c)))) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7
          (CryptoVerification.E2E.Record.encReceiverChain c)).flatten := by
    rw [pbFields_map_msgField7_spqr, List.flatMap_map, List.flatMap_def]; congr 1
    apply List.map_congr_left; intro rc hrc; dsimp only [Function.comp_apply]
    have hrc_len : (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64 :=
      lt_of_le_of_lt (encReceiverChain_length_le_encSession_spqr s rc hrc) hsess_len
    have hcb : chainBytes (receiverChainToChainRec rc) =
        CryptoVerification.E2E.Record.encReceiverChain rc :=
      chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc)
    rw [hcb]; exact msgField_eq_lenField 7 _ hrc_len
  have hppk_eq :
      pbFields ((s.pendingPreKey.map
        (fun p => [(9, PbValue.bytes (CryptoVerification.E2E.Record.encPendingPreKey p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 9
        (s.pendingPreKey.map CryptoVerification.E2E.Record.encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_spqr]
      exact msgField_eq_lenField 9 _
        (lt_of_le_of_lt (encPendingPreKey_length_le_encSession_spqr s p hppk) hsess_len)
  have hpkp_eq :
      pbFields ((s.pendingKyberPreKey.map
        (fun p => [(14, PbValue.bytes (CryptoVerification.E2E.Record.encPendingKyber p))])).getD []) =
      CryptoVerification.E2E.Record.msgField 14
        (s.pendingKyberPreKey.map CryptoVerification.E2E.Record.encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      rw [pbFields_singleton_bytes_spqr]
      exact msgField_eq_lenField 14 _
        (lt_of_le_of_lt (encPendingKyber_length_le_encSession_spqr s p hpkp) hsess_len)
  unfold encSessionFields_spqr CryptoVerification.E2E.Record.encSession; dsimp only
  repeat rw [pbFields_append_spqr]
  rw [hsc_eq, hrc_eq, hppk_eq, hpkp_eq]
  repeat rw [pbFields_u32FieldList_spqr]
  repeat rw [pbFields_bytesFieldList_spqr]
  change DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 3
        ((Option.map IdentityKey.serialize s.state.remoteIdentity).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
      CryptoVerification.E2E.Record.msgField 6 (Option.map encSenderChain s.state.senderChain) ++
      (List.map (fun c => CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c))
        s.state.receiverChains).flatten ++
      CryptoVerification.E2E.Record.msgField 9 (Option.map encPendingPreKey s.pendingPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
      CryptoVerification.E2E.Record.msgField 14 (Option.map encPendingKyber s.pendingKyberPreKey) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState = _
  rw [u32Field_eq_uint32Field 1, bytesField_eq_record_bytesField 2 _ (by omega),
      bytesField_eq_record_bytesField 3 _ hrem_len, bytesField_eq_record_bytesField 4 _ (by omega),
      u32Field_eq_uint32Field 5, u32Field_eq_uint32Field 10, u32Field_eq_uint32Field 11,
      bytesField_eq_record_bytesField 13 _ (by omega), bytesField_eq_record_bytesField 15 _ (by omega)]

private theorem pbFields_encSessionFields_eq_sessionToRecordRecPending (s : Session (List (BitVec 8))) :
    msgField 1 (pbFields (encSessionFields_spqr s)) = recordBytes (sessionToRecordRecPending s) := by
  unfold encSessionFields_spqr recordBytes sessionToRecordRecPending sessionToSessionRec
  dsimp only [List.flatMap_nil, List.append_nil]
  repeat rw [pbFields_append_spqr]
  rw [pbFields_u32FieldList_spqr, pbFields_bytesFieldList_spqr, pbFields_bytesFieldList_spqr,
      pbFields_bytesFieldList_spqr, pbFields_u32FieldList_spqr, pbFields_map_msgField7_spqr,
      pbFields_u32FieldList_spqr, pbFields_u32FieldList_spqr, pbFields_bytesFieldList_spqr,
      pbFields_bytesFieldList_spqr]
  cases s.state.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
    simp [Function.comp_def, pbFields, msgField]

theorem recordBytes_sessionToRecordRecPending_eq_encodeRecord
    (s : Session (List (BitVec 8)))
    (halice : s.aliceBaseKey.length < 2 ^ 63)
    (hpq : s.state.pqRatchetState.length < 2 ^ 63)
    (hseeds : ∀ rc ∈ s.state.receiverChains,
      ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (_hrc_len : ∀ rc ∈ s.state.receiverChains,
      (CryptoVerification.E2E.Record.encReceiverChain rc).length < 2 ^ 64)
    (hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  rw [← pbFields_encSessionFields_eq_sessionToRecordRecPending,
      pbFields_encSessionFields_spqr s halice hpq hseeds hsess_len]
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
  dsimp only [Option.map_some]
  exact msgField_eq_lenField 1 _ hsess_len

theorem recordBytes_sessionToRecordRecPending_of_canonical_Q
    {Q : List (BitVec 8) → Prop} {bs : HwBytes} {s : Session (List (BitVec 8))}
    (hc : Pure.slots_RecordCanonical_Q Q bs s) :
    recordBytes (sessionToRecordRecPending s) = CryptoVerification.E2E.Record.encodeRecord ⟨some s⟩ := by
  obtain ⟨_, _, ⟨_, _, hchains_sc, halice_lt, _, hpq_lt, hsess_lt⟩⟩ := hc
  have hsess_lt' : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 62 := hsess_lt
  have hsess_len : (CryptoVerification.E2E.Record.encSession s).length < 2 ^ 64 := by omega
  have hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
    intro rc hrc mk hmk; have h32 := (hchains_sc rc hrc).2 mk hmk; omega
  refine recordBytes_sessionToRecordRecPending_eq_encodeRecord s
    (by omega) (by omega) hseeds (fun rc hrc' => ?_) hsess_len
  exact lt_of_le_of_lt (encReceiverChain_length_le_encSession_spqr s rc hrc') hsess_len

theorem rec_eq_sessionToRecordRec_of_canonical_Q
    {Q : List (BitVec 8) → Prop} {rec : RecordRec} {recBytes : HwBytes}
    {s : Session (List (BitVec 8))}
    (hrecBytes : recBytes = recordBytes rec) (hc : Pure.slots_RecordCanonical_Q Q recBytes s) :
    normPending rec = normPending (sessionToRecordRecPending s) := by
  have hb := recordBytes_sessionToRecordRecPending_of_canonical_Q hc
  apply Symbolic.Swarm.CREF.TR.recordBytes_injective
  rw [← hrecBytes, hc.1, hb]

/-! ## Pre-call and post-call SPQR step witnesses -/

theorem pqRatchetState_eq_gamma_pending
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (recBytes : HwBytes) (rec : RecordRec) (st st_in : TRState) (g_rw : RecvWireGhost)
    (hrecBytes : recBytes = recordBytes rec) (hrel : StateRel interpretation S g st rec)
    (hcanon_q : Pure.slots_RecordCanonical_Q Pure.slots_NonEmptyV1Q recBytes g_rw.sess)
    (hspqr_in : st_in.spqr = st.spqr) :
    normPending rec = normPending (sessionToRecordRecPending g_rw.sess) ∧
    StateRel interpretation S g st (sessionToRecordRec g_rw.sess) ∧
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr ∧
    g_rw.sess.state.pqRatchetState = gamma interpretation S g st_in.spqr ∧
    gamma interpretation S g st_in.spqr =
      (sessionOf interpretation (gamma interpretation S g) st_in).pqRatchetState ∧
    g_rw.sess.state.sessionVersion = 4#32 ∧
    (∃ r : RecordRec, recBytes = recordBytes r ∧ r.current.sessionVersion = 4#32) := by
  obtain ⟨hpq, hver⟩ := stateRel_pqRatchetState_and_sessionVersion hrel
  have hrec_eq := rec_eq_sessionToRecordRec_of_canonical_Q hrecBytes hcanon_q
  have hrel_sess : StateRel interpretation S g st (sessionToRecordRec g_rw.sess) := by
    rw [← stateRel_sessionToRecordRecPending_iff, ← stateRel_normPending_iff, ← hrec_eq,
        stateRel_normPending_iff]
    exact hrel
  have hpq_norm : rec.current.pqRatchetState = g_rw.sess.state.pqRatchetState :=
    congrArg (fun r => r.current.pqRatchetState) hrec_eq
  have hver_norm : rec.current.sessionVersion = g_rw.sess.state.sessionVersion :=
    congrArg (fun r => r.current.sessionVersion) hrec_eq
  have hpq_sess : g_rw.sess.state.pqRatchetState = gamma interpretation S g st.spqr := by
    rw [← hpq_norm, hpq]
  have hver_sess : g_rw.sess.state.sessionVersion = 4#32 := by
    rw [← hver_norm, hver]
  refine ⟨hrec_eq, hrel_sess, hpq_sess, ?_, rfl, hver_sess, ⟨rec, hrecBytes, hver⟩⟩
  rw [hpq_sess, hspqr_in]

/-- Relational output witness connecting `(spqrModelOf interpretation).recv` to
symbolic `Spqr.spqrRecv` on pre-state, post-state, and derived key bytes. -/
structure SpqrRecvStepOut
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st_in : TRState) (msg : TRSignalMsg) (newPqrState : HwBytes)
    (pqrKey : HKDF.Salt) : Prop where
  pre_pq_eq : gamma interpretation S g st_in.spqr =
    (sessionOf interpretation (gamma interpretation S g) st_in).pqRatchetState
  exists_step :
    ∃ (spqrMsgIdx : UInt32) (spqr' key : DY.Bytes),
      Spqr.spqrRecv st_in.spqr msg.pqRatchet spqrMsgIdx = some (spqr', key) ∧
      gamma interpretation S g spqr' = newPqrState ∧
      gamma interpretation S g
        (({ st := st_in.spqr, msg := msg.pqRatchet } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) =
        spqrKeyBytes (saltToBytes pqrKey)

/-- When `(spqrModelOf i).recv stBytes msgBytes = .ok (st', salt?)`, `spqrRecvStateOf i` and
`spqrRecvKeyOf i` evaluate to `st'` and `saltToBytes salt?`. -/
theorem spqrRecvOf_of_recv_ok (i : ExternInterpretation)
    {stBytes msgBytes st' : HwBytes} {salt? : HKDF.Salt}
    (hrecv : (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf i).recv stBytes msgBytes = .ok (st', salt?)) :
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvStateOf i stBytes msgBytes = st' ∧
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvKeyOf i stBytes msgBytes = saltToBytes salt? := by
  dsimp only [Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf,
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1WithMac,
    CryptoVerification.LibsignalSpqrV1.toSpqrModel] at hrecv
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvStateOf Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvKeyOf
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvStateB Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvKeyB
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1RecvWithMac
    CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel; dsimp only
  cases htop : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.TRREF.SpqrSemOf.spqrDepsWithMac
        (DY.Libsignal.Refinement.sha256CompressFunction i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.mlkemOf i)
        (Symbolic.Swarm.TRREF.SpqrSemOf.hmacFnOf i))
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith
        (DY.Libsignal.Refinement.sha256CompressFunction i))
      stBytes msgBytes with
  | error e => rw [htop] at hrecv; cases e <;> cases hrecv
  | ok r =>
    rw [htop] at hrecv; dsimp only at hrecv ⊢
    cases hkey : r.key with
    | none =>
      rw [hkey] at hrecv
      dsimp only [CryptoVerification.LibsignalSpqrV1.recvKeyToSalt?,
        CryptoVerification.LibsignalSpqrV1.messageKeyToSalt?] at hrecv
      injection hrecv with hpair; injection hpair with hst hsalt; subst hst hsalt; exact ⟨rfl, rfl⟩
    | some k =>
      rcases k with _ | ⟨b, bs⟩
      · rw [hkey] at hrecv
        dsimp only [CryptoVerification.LibsignalSpqrV1.recvKeyToSalt?] at hrecv
        injection hrecv with hpair; injection hpair with hst hsalt; subst hst hsalt; exact ⟨rfl, rfl⟩
      · rw [hkey] at hrecv
        dsimp only [CryptoVerification.LibsignalSpqrV1.recvKeyToSalt?,
          CryptoVerification.LibsignalSpqrV1.messageKeyToSalt?] at hrecv
        by_cases hk : (b :: bs).length = 32
        · simp only [hk, ↓reduceDIte] at hrecv
          injection hrecv with hpair; injection hpair with hst hsalt; subst hst hsalt; exact ⟨rfl, rfl⟩
        · simp only [hk, ↓reduceDIte] at hrecv; cases hrecv

/-- When `DY.Spqr.spqrEmptyMsg msg = false` and any `InitState.SubF` view of `st` has valid
`spqrParamsDir?`, `DY.Spqr.spqrRecv st msg 0` returns `some (st', key)`. -/
theorem spqrRecv_zero_isSome_of_not_empty_of_initDir
    {st msg : DY.Bytes}
    (hempty : DY.Spqr.spqrEmptyMsg msg = false)
    (hinit : ∀ authKey params,
      st.view? DY.Spqr.InitState.SubF = some ⟨authKey, params⟩ →
      (DY.Spqr.spqrParamsDir? params).isSome = true) :
    ∃ spqr' key, DY.Spqr.spqrRecv st msg 0 = some (spqr', key) := by
  rcases hview : st.view? DY.Spqr.InitState.SubF with _ | ⟨authKey, params⟩
  · refine ⟨({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack,
      ({ st := st, msg := msg } : DY.Spqr.RecvKey.SubF DY.Bytes).pack, ?_⟩
    simp [DY.Spqr.spqrRecv, hempty, hview]
  · have hdir := hinit authKey params hview
    rcases hpdir : DY.Spqr.spqrParamsDir? params with _ | dir
    · rw [hpdir] at hdir; cases hdir
    · refine ⟨({ st := st, msg := msg } : DY.Spqr.RecvState.SubF DY.Bytes).pack,
        DY.Spqr.zeroKey, ?_⟩
      simp [DY.Spqr.spqrRecv, hempty, hview, hpdir]

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
