/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RelPure
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BobKyberNone
public import Symbolic.Proofs.Swarm.CREF.Initiate.Is1aRunPure
import Symbolic.Proofs.Swarm.CREF.Grow.PqInit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj

/-!
# Session Record Serialization and Initial Out-of-Order SPQR Bounds

Relates `recordBytes`, `pqStateOf`, and `encodeRecord` for pending sessions, and establishes
`SpqrOooBounded` and length bounds for Alice's initial SPQR state.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record
  (encodeRecord encSession encSenderChain encReceiverChain encChainKey encPendingPreKey encPendingKyber)
open Swarm.Phase0WholeFunctionBridge
  (senderChainToChainRec receiverChainToChainRec sessionToSessionRec sessionToRecordRec
   u32Field_eq_uint32Field msgField_eq_lenField bytesField_eq_record_bytesField
   lenField_length_le record_bytesField_length_le encChainKey_length_lt
   chainBytes_sender_eq_encSenderChain chainBytes_receiver_eq_encReceiverChain)

@[scoped simp] theorem sessionToRecordRecPending_pqRatchetState (s : Session HwBytes) :
    (sessionToRecordRecPending s).current.pqRatchetState = s.state.pqRatchetState := rfl

@[scoped simp] theorem sessionToRecordRec_pqRatchetState (s : Session HwBytes) :
    (sessionToRecordRec s).current.pqRatchetState = s.state.pqRatchetState := rfl

theorem recordBytes_pqRatchetState_inj {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.pqRatchetState = r₂.current.pqRatchetState := by
  have hn := TR.recordBytes_injective h
  exact congrArg (fun r => r.current.pqRatchetState) hn

@[scoped simp] theorem pqStateOf_recordBytes (r : RecordRec) :
    pqStateOf (recordBytes r) = r.current.pqRatchetState := by
  have hex : ∃ r' : RecordRec, recordBytes r = recordBytes r' := ⟨r, rfl⟩
  simp only [pqStateOf, hex, ↓reduceDIte]
  exact recordBytes_pqRatchetState_inj (Classical.choose_spec hex).symm

private theorem encPendingPreKey_length_le_encSession (s : Session HwBytes)
    (p : PendingPreKey) (hp : s.pendingPreKey = some p) :
    (encPendingPreKey p).length ≤ (encSession s).length := by
  unfold encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]
  simp only [List.length_append]; omega

private theorem encPendingKyber_length_le_encSession (s : Session HwBytes)
    (p : PendingKyberPreKey) (hp : s.pendingKyberPreKey = some p) :
    (encPendingKyber p).length ≤ (encSession s).length := by
  unfold encSession; rw [hp]
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField,
    CryptoVerification.E2E.Record.lenField]
  simp only [List.length_append]; omega

/-- `recordBytes (sessionToRecordRecPending s)` equals `encodeRecord ⟨some s⟩` for any session `s`
satisfying the 64-bit field-length bounds. -/
theorem recordBytes_sessionToRecordRecPending_eq_encodeRecord
    (s : Session HwBytes)
    (halice : s.aliceBaseKey.length < 2 ^ 64)
    (hpq : s.state.pqRatchetState.length < 2 ^ 64)
    (hseeds : ∀ rc ∈ s.state.receiverChains, ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63)
    (hrc_len : ∀ rc ∈ s.state.receiverChains, (encReceiverChain rc).length < 2 ^ 64)
    (hsess_len : (encSession s).length < 2 ^ 64) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ := by
  unfold recordBytes sessionToRecordRecPending sessionToSessionRec encodeRecord
  dsimp only [Option.map_some, CryptoVerification.E2E.Record.msgField]
  rw [List.flatMap_nil, List.append_nil, ← msgField_eq_lenField 1 (encSession s) hsess_len]
  congr 1
  unfold encSession
  have hloc_len : s.state.localIdentity.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize]
  have hrem_len :
      ((s.state.remoteIdentity.map IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    cases s.state.remoteIdentity <;> simp [IdentityKey.serialize, PublicKey.serialize]
  have hrk_len : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by
    simp [HMAC.keyToBytes32]
  have hsc_eq :
      ((Option.map senderChainToChainRec s.state.senderChain).map
        (msgField 6 ∘ chainBytes)).getD [] =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map encSenderChain) := by
    cases s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, Function.comp_apply,
        CryptoVerification.E2E.Record.msgField, senderChainToChainRec]
      change DY.Libsignal.TripleRatchet.Refinement.msgField 6
        (DY.Libsignal.TripleRatchet.Refinement.chainBytes (senderChainToChainRec sc)) = _
      unfold senderChainToChainRec
      rw [chainBytes_sender_eq_encSenderChain sc]
      have hsc_len : (encSenderChain sc).length < 2 ^ 64 := by
        unfold encSenderChain
        dsimp [CryptoVerification.E2E.Record.msgField]
        have h1 := record_bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
        have h2 := record_bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
        have h3 := lenField_length_le 3 (encChainKey sc.chainKey)
        have h4 := encChainKey_length_lt sc.chainKey
        have hpub : sc.ratchetKey.publicKey.serialize.length = 33 := by
          simp [PublicKey.serialize]
        have hpriv : sc.ratchetKey.privateKey.bytes.toList.length = 32 :=
          List.Vector.toList_length _
        simp only [List.length_append]; omega
      exact msgField_eq_lenField 6 _ hsc_len
  have hrc_eq :
      (List.map receiverChainToChainRec s.state.receiverChains).flatMap
        (msgField 7 ∘ chainBytes) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)).flatten := by
    rw [List.flatMap_map, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro rc hrc
    dsimp only [Function.comp_apply]
    change DY.Libsignal.TripleRatchet.Refinement.msgField 7
      (DY.Libsignal.TripleRatchet.Refinement.chainBytes (receiverChainToChainRec rc)) = _
    rw [chainBytes_receiver_eq_encReceiverChain rc (hseeds rc hrc),
        msgField_eq_lenField 7 _ (hrc_len rc hrc)]
  have hppk_eq :
      (((Option.map (fun p => (encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
        fun p => msgField 9 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some,
        CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hlen_p : (encPendingPreKey p).length < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (encPendingPreKey_length_le_encSession s p hppk) hsess_len
      exact msgField_eq_lenField 9 _ hlen_p
  have hpkp_eq :
      (((Option.map (fun p => (encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
        fun p => msgField 14 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      dsimp only [Option.map_some, Option.getD_some,
        CryptoVerification.E2E.Record.msgField]
      rw [List.append_nil]
      have hlen_p : (encPendingKyber p).length < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (encPendingKyber_length_le_encSession s p hpkp) hsess_len
      exact msgField_eq_lenField 14 _ hlen_p
  change DY.Libsignal.TripleRatchet.Refinement.u32Field 1 s.state.sessionVersion ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 2 s.state.localIdentity.serialize ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 3
        ((s.state.remoteIdentity.map IdentityKey.serialize).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 4 (HMAC.keyToBytes32 s.state.rootKey) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 5 s.state.previousCounter ++
      ((Option.map senderChainToChainRec s.state.senderChain).map (msgField 6 ∘ chainBytes)).getD [] ++
      (List.map receiverChainToChainRec s.state.receiverChains).flatMap (msgField 7 ∘ chainBytes) ++
      (((Option.map (fun p => (encPendingPreKey p, ([] : HwBytes))) s.pendingPreKey).map
        fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 10 s.remoteRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.u32Field 11 s.localRegistrationId ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 13 s.aliceBaseKey ++
      (((Option.map (fun p => (encPendingKyber p, ([] : HwBytes))) s.pendingKyberPreKey).map
        fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
      DY.Libsignal.TripleRatchet.Refinement.bytesField 15 s.state.pqRatchetState = _
  rw [u32Field_eq_uint32Field 1,
      bytesField_eq_record_bytesField 2 _ (by omega),
      bytesField_eq_record_bytesField 3 _ hrem_len,
      bytesField_eq_record_bytesField 4 _ (by omega),
      u32Field_eq_uint32Field 5,
      hsc_eq, hrc_eq, hppk_eq,
      u32Field_eq_uint32Field 10,
      u32Field_eq_uint32Field 11,
      bytesField_eq_record_bytesField 13 _ halice,
      hpkp_eq,
      bytesField_eq_record_bytesField 15 _ hpq]

/-- `SpqrOooBounded` and `< 2 ^ 32` length for Alice's initial SPQR state `spqrInitOf i k [0#8]`,
when `1176 + k.length < 2 ^ 32`. -/
theorem spqrOooBounded_spqrInitOf_a2b (i : ExternInterpretation) (k : HwBytes)
    (hk : 1176 + k.length < 2 ^ 32) :
    SpqrOooBounded (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf i k [0#8]) ∧
      (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf i k [0#8]).length < 2 ^ 32 := by
  rw [Grow.spqrInitOf_a2b_eq_is1StateRaw]
  exact ⟨Grow.spqrOooBounded_is1StateRaw _ .a2b k (by omega),
    is1StateRaw_encodeRaw_length_lt_2_32 _ .a2b k hk⟩

end Symbolic.Swarm.CREF
