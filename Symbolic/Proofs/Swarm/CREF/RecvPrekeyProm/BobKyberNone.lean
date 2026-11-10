/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.RecordBytesBridge
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj

/-!
# `pendingKyberPreKey` Record-Encoding Bridge

Defines `sessionToRecordRecPending` retaining `pendingPreKey` and `pendingKyberPreKey` payloads,
proves `recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩` under the `< 2 ^ 63`
length bound, and deduces `pendingKyberPreKey_eq_none_of_encodeRecord_lt` via `recordBytes`
injectivity.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record
  (encodeRecord encSession encSenderChain encReceiverChain encMessageKey
   encPendingPreKey encPendingKyber)

/-- Converts a `Session HwBytes` (including `pendingPreKey` and `pendingKyberPreKey` payloads) into
a `RecordRec` with `previous = []`. -/
def sessionToRecordRecPending (s : Session HwBytes) : RecordRec where
  current :=
    { Swarm.Phase0WholeFunctionBridge.sessionToSessionRec s with
      pendingPreKey := s.pendingPreKey.map fun p => (encPendingPreKey p, [])
      pendingKyberPreKey := s.pendingKyberPreKey.map fun p => (encPendingKyber p, []) }
  previous := []

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
    (encReceiverChain rc).length ≤ (encSession s).length := by
  have h1 := flatten_map_lenField_ge 7 encReceiverChain s.state.receiverChains rc hrc
  unfold encSession; simp only [List.length_append]; omega

private theorem seed_le_encReceiverChain (rc : ReceiverChain)
    (mk : MessageKeyGenerator) (hmk : mk ∈ rc.messageKeys) :
    mk.seed.length ≤ (encReceiverChain rc).length := by
  have h1 := flatten_map_lenField_ge 4 encMessageKey rc.messageKeys mk hmk
  have h2 := record_bytesField_payload_le 5 mk.seed
  have h3 : (CryptoVerification.E2E.Record.bytesField 5 mk.seed).length ≤ (encMessageKey mk).length := by
    unfold encMessageKey; simp only [List.length_append]; omega
  unfold encReceiverChain; simp only [List.length_append]; omega

private theorem encSession_le_encodeRecord (s : Session HwBytes) :
    (encSession s).length ≤ (encodeRecord ⟨some s⟩).length := by
  unfold encodeRecord CryptoVerification.E2E.Record.msgField
  dsimp only [Option.map_some]
  exact lenField_payload_le 1 (encSession s)

/-- Any session `s` whose encoded record has length `< 2 ^ 63` satisfies
`recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩`. -/
theorem recordBytes_sessionToRecordRecPending_of_encodeRecord_lt
    (s : Session HwBytes) (hlen : (encodeRecord ⟨some s⟩).length < 2 ^ 63) :
    recordBytes (sessionToRecordRecPending s) = encodeRecord ⟨some s⟩ := by
  have hsess : (encSession s).length < 2 ^ 63 :=
    Nat.lt_of_le_of_lt (encSession_le_encodeRecord s) hlen
  have hloc_len : s.state.localIdentity.serialize.length < 2 ^ 64 := by
    have h1 := record_bytesField_payload_le 2 s.state.localIdentity.serialize
    have h2 : (CryptoVerification.E2E.Record.bytesField 2 s.state.localIdentity.serialize).length ≤
        (encSession s).length := by
      dsimp only [encSession]; simp only [List.length_append]; omega
    omega
  have hrem_len : ((s.state.remoteIdentity.map
      CryptoGames.LibsignalSession.IdentityKey.serialize).getD []).length < 2 ^ 64 := by
    have h1 := record_bytesField_payload_le 3
      ((s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD [])
    have h2 : (CryptoVerification.E2E.Record.bytesField 3
        ((s.state.remoteIdentity.map CryptoGames.LibsignalSession.IdentityKey.serialize).getD [])).length ≤
        (encSession s).length := by
      dsimp only [encSession]; simp only [List.length_append]; omega
    omega
  have hrk_len : (CryptoGames.HMAC.keyToBytes32 s.state.rootKey).length < 2 ^ 64 := by
    have h1 := record_bytesField_payload_le 4 (CryptoGames.HMAC.keyToBytes32 s.state.rootKey)
    have h2 : (CryptoVerification.E2E.Record.bytesField 4
        (CryptoGames.HMAC.keyToBytes32 s.state.rootKey)).length ≤ (encSession s).length := by
      dsimp only [encSession]; simp only [List.length_append]; omega
    omega
  have halice : s.aliceBaseKey.length < 2 ^ 64 := by
    have h1 := record_bytesField_payload_le 13 s.aliceBaseKey
    have h2 : (CryptoVerification.E2E.Record.bytesField 13 s.aliceBaseKey).length ≤ (encSession s).length := by
      dsimp only [encSession]; simp only [List.length_append]; omega
    omega
  have hpq : s.state.pqRatchetState.length < 2 ^ 64 := by
    have h1 := record_bytesField_payload_le 15 s.state.pqRatchetState
    have h2 : (CryptoVerification.E2E.Record.bytesField 15 s.state.pqRatchetState).length ≤ (encSession s).length := by
      dsimp only [encSession]; simp only [List.length_append]; omega
    omega
  have hsc_eq :
      ((s.state.senderChain.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec).map
        fun sc => msgField 6 (chainBytes sc)).getD [] =
      CryptoVerification.E2E.Record.msgField 6 (s.state.senderChain.map encSenderChain) := by
    cases hsc : s.state.senderChain with
    | none => rfl
    | some sc =>
      dsimp only [Option.map_some, Option.getD_some, CryptoVerification.E2E.Record.msgField]
      have hsc_len : (encSenderChain sc).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 6 (encSenderChain sc)
        have h2 : (CryptoVerification.E2E.Record.msgField 6 (some (encSenderChain sc))).length ≤
            (encSession s).length := by
          dsimp only [encSession]; rw [hsc]; simp only [Option.map_some, List.length_append]; omega
        omega
      unfold Swarm.Phase0WholeFunctionBridge.senderChainToChainRec
      rw [Swarm.Phase0WholeFunctionBridge.chainBytes_sender_eq_encSenderChain sc,
          Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 6 _ hsc_len]
  have hrc_eq :
      ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).flatMap
        fun rc => msgField 7 (chainBytes rc)) =
      (s.state.receiverChains.map fun c =>
        CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)).flatten := by
    rw [List.flatMap_map, List.flatMap_def]
    congr 1
    apply List.map_congr_left
    intro rc hrc
    have hrc_lt : (encReceiverChain rc).length < 2 ^ 64 := by
      have := encReceiverChain_le_encSession s rc hrc; omega
    have hseeds : ∀ mk ∈ rc.messageKeys, mk.seed.length < 2 ^ 63 := by
      intro mk hmk
      have h1 := seed_le_encReceiverChain rc mk hmk
      have h2 := encReceiverChain_le_encSession s rc hrc
      omega
    rw [Swarm.Phase0WholeFunctionBridge.chainBytes_receiver_eq_encReceiverChain rc hseeds,
        Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 7 _ hrc_lt]
  have hppk_eq :
      (((s.pendingPreKey.map fun p => (encPendingPreKey p, ([] : HwBytes))).map
        fun p => msgField 9 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 9 (s.pendingPreKey.map encPendingPreKey) := by
    cases hppk : s.pendingPreKey with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some, List.append_nil,
        CryptoVerification.E2E.Record.msgField]
      have hp_len : (encPendingPreKey p).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 9 (encPendingPreKey p)
        have h2 : (CryptoVerification.E2E.Record.msgField 9 (some (encPendingPreKey p))).length ≤
            (encSession s).length := by
          dsimp only [encSession]; rw [hppk]; simp only [Option.map_some, List.length_append]; omega
        omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 9 _ hp_len
  have hpkp_eq :
      (((s.pendingKyberPreKey.map fun p => (encPendingKyber p, ([] : HwBytes))).map
        fun p => msgField 14 (p.1 ++ p.2)).getD []) =
      CryptoVerification.E2E.Record.msgField 14 (s.pendingKyberPreKey.map encPendingKyber) := by
    cases hpkp : s.pendingKyberPreKey with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Option.getD_some, List.append_nil,
        CryptoVerification.E2E.Record.msgField]
      have hp_len : (encPendingKyber p).length < 2 ^ 64 := by
        have h1 := record_msgField_some_payload_le 14 (encPendingKyber p)
        have h2 : (CryptoVerification.E2E.Record.msgField 14 (some (encPendingKyber p))).length ≤
            (encSession s).length := by
          dsimp only [encSession]; rw [hpkp]; simp only [Option.map_some, List.length_append]; omega
        omega
      exact Swarm.Phase0WholeFunctionBridge.msgField_eq_lenField 14 _ hp_len
  unfold recordBytes sessionToRecordRecPending
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec encodeRecord
    CryptoVerification.E2E.Record.msgField
  simp only [List.flatMap_nil, List.append_nil, Option.map_some, Function.comp_def]
  have hbody :
      u32Field 1 s.state.sessionVersion ++
        bytesField 2 s.state.localIdentity.serialize ++
        bytesField 3 ((s.state.remoteIdentity.map
          CryptoGames.LibsignalSession.IdentityKey.serialize).getD []) ++
        bytesField 4 (CryptoGames.HMAC.keyToBytes32 s.state.rootKey) ++
        u32Field 5 s.state.previousCounter ++
        ((s.state.senderChain.map Swarm.Phase0WholeFunctionBridge.senderChainToChainRec).map
          fun sc => msgField 6 (chainBytes sc)).getD [] ++
        ((s.state.receiverChains.map Swarm.Phase0WholeFunctionBridge.receiverChainToChainRec).flatMap
          fun rc => msgField 7 (chainBytes rc)) ++
        (((s.pendingPreKey.map fun p => (encPendingPreKey p, ([] : HwBytes))).map
          fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
        u32Field 10 s.remoteRegistrationId ++
        u32Field 11 s.localRegistrationId ++
        bytesField 13 s.aliceBaseKey ++
        (((s.pendingKyberPreKey.map fun p => (encPendingKyber p, ([] : HwBytes))).map
          fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
        bytesField 15 s.state.pqRatchetState =
      encSession s := by
    unfold encSession
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

/-- `recordBytes` uniquely determines whether `current.pendingKyberPreKey` is `none`. -/
theorem recordBytes_pendingKyberPreKey_eq_none_iff {r₁ r₂ : RecordRec}
    (h : recordBytes r₁ = recordBytes r₂) :
    r₁.current.pendingKyberPreKey = none ↔ r₂.current.pendingKyberPreKey = none := by
  have hn := TR.recordBytes_injective h
  have hp := congrArg (fun r => r.current.pendingKyberPreKey) hn
  dsimp only [TR.normPending, TR.normPendingS] at hp
  constructor <;> intro hnone
  · rw [hnone] at hp
    exact Option.map_eq_none_iff.mp hp.symm
  · rw [hnone] at hp
    exact Option.map_eq_none_iff.mp hp

@[simp] theorem sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff (s : Session HwBytes) :
    (sessionToRecordRecPending s).current.pendingKyberPreKey = none ↔
      s.pendingKyberPreKey = none := by
  dsimp only [sessionToRecordRecPending]
  exact Option.map_eq_none_iff

/-- Post-state bridge: if `bs = encodeRecord ⟨some s'⟩`, `bs.length < 2 ^ 63`, and
`s'.pendingKyberPreKey = none`, then every `rr : RecordRec` with `bs = recordBytes rr` has
`rr.current.pendingKyberPreKey = none`. -/
theorem pendingKyberPreKey_eq_none_of_encodeRecord_lt
    {bs : HwBytes} {s' : Session HwBytes} {rr : RecordRec}
    (henc : bs = encodeRecord ⟨some s'⟩)
    (hlen : bs.length < 2 ^ 63)
    (hkyb : s'.pendingKyberPreKey = none)
    (hrr : bs = recordBytes rr) :
    rr.current.pendingKyberPreKey = none := by
  have hrec := recordBytes_sessionToRecordRecPending_of_encodeRecord_lt s' (henc ▸ hlen)
  have heq : recordBytes rr = recordBytes (sessionToRecordRecPending s') :=
    hrr.symm.trans (henc.trans hrec.symm)
  exact (recordBytes_pendingKyberPreKey_eq_none_iff heq).mpr
    ((sessionToRecordRecPending_pendingKyberPreKey_eq_none_iff s').mpr hkyb)

end Symbolic.Swarm.CREF
