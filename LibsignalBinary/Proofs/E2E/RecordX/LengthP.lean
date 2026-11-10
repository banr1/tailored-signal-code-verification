/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.E2E.RecordX.Length

/-!
# Record length bounds under `DeserializeScopeBounded`, `DeserializeScopeX`, and `DeserializeScopeP`

**Checked by Lean.** Shows that every record in `DeserializeScopeBounded` (and hence in
`DeserializeScopeX` and `DeserializeScopeP`) encodes to fewer than `2 ^ 21` bytes (`< 2 ^ 32`) by
projecting out PQXDH-specific fields to `DeserializeGeneral.DeserializeScope`.
-/

@[expose] public section

namespace CryptoVerification.E2E.RecordX

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec

/-! ## Protobuf field length bounds -/

theorem bytesField2_ik_length_eq (ik1 ik2 : IdentityKey) :
    (Record.bytesField 2 ik1.serialize).length = (Record.bytesField 2 ik2.serialize).length := by
  have h1 : ik1.serialize.length = 33 := serialize_pk_length' ik1.publicKey
  have h2 : ik2.serialize.length = 33 := serialize_pk_length' ik2.publicKey
  have hne1 : ik1.serialize ≠ [] := by intro h; rw [h] at h1; cases h1
  have hne2 : ik2.serialize ≠ [] := by intro h; rw [h] at h2; cases h2
  simp [Record.bytesField, hne1, hne2, Record.lenField, h1, h2]

/-- The pending-pre-key field is at most 133 bytes. -/
theorem msgField9_length_leP (op : Option PendingPreKey) :
    (Record.msgField 9 (op.map Record.encPendingPreKey)).length ≤ 133 := by
  rcases op with _ | p
  · simp [Record.msgField]
  · dsimp only [Option.map_some, Record.msgField]
    have h0 : (Record.lenField 9 (Record.encPendingPreKey p)).length ≤
        (Record.encPendingPreKey p).length + 20 :=
      lenField_length_le' 9 (Record.encPendingPreKey p)
    have heq : (Record.encPendingPreKey p).length =
        (Record.optUint32Field 1 p.preKeyId).length + (Record.bytesField 2 p.baseKey.serialize).length +
        (Record.int32Field 3 p.signedPreKeyId).length + (Record.uint64Field 4 p.timestamp).length := by
      simp only [Record.encPendingPreKey, List.length_append]
    have ha : (Record.optUint32Field 1 p.preKeyId).length ≤ 20 :=
      optUint32FieldX_length_le 1 p.preKeyId
    have hb : (Record.bytesField 2 p.baseKey.serialize).length ≤ p.baseKey.serialize.length + 20 :=
      bytesField_length_le' 2 p.baseKey.serialize
    rw [serialize_pk_length'] at hb
    have hc : (Record.int32Field 3 p.signedPreKeyId).length ≤ 20 :=
      int32FieldX_length_le 3 p.signedPreKeyId
    have hd : (Record.uint64Field 4 p.timestamp).length ≤ 20 :=
      uint64FieldX_length_le 4 p.timestamp
    omega

/-! ## Projection to `DeserializeGeneral.DeserializeScope` -/

/-- `s` projected into `DeserializeGeneral.DeserializeScope`. -/
def stripP (s : Session Bytes) : Session Bytes :=
  { s with
    state := { s.state with localIdentity := freshLocalId s.state.remoteIdentity }
    localRegistrationId := 0
    remoteRegistrationId := 0
    aliceBaseKey := []
    pendingKyberPreKey := none
    pendingPreKey := s.pendingPreKey.map fun p =>
      { p with preKeyId := none, signedPreKeyId := 0 } }

abbrev stripBounded (s : Session Bytes) : Session Bytes := stripP s

theorem deserializeScope_stripBounded {s : Session Bytes} (h : DeserializeScopeBounded ⟨some s⟩) :
    DeserializeGeneral.DeserializeScope ⟨some (stripP s)⟩ := by
  obtain ⟨⟨hin, hpq, hrep⟩, s', hs', hsc⟩ := h
  injection hs' with hs'
  subst hs'
  obtain ⟨hc, hp, _, _⟩ := hsc
  obtain ⟨hin2, hin3, _⟩ := hin s rfl
  obtain ⟨hrep1, hrep2, hwf, _⟩ := hrep s rfl
  refine ⟨⟨?_, ?_, ?_⟩, stripP s, rfl, hc, rfl, rfl, rfl, rfl, ?_⟩
  · intro t ht
    injection ht with ht
    subst ht
    exact ⟨remoteIdentity_ne_freshLocalId s.state.remoteIdentity, hin2, hin3,
      fun k hk => by cases hk⟩
  · intro t ht
    injection ht with ht
    subst ht
    exact hpq s rfl
  · intro t ht
    injection ht with ht
    subst ht
    refine ⟨hrep1, hrep2, ?_, by simp [stripP]⟩
    unfold Session.Wf at hwf ⊢
    simp only [stripP, Option.isSome_map]
    exact hwf
  · intro p hp'
    simp only [stripP, Option.map_eq_some_iff] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    exact ⟨rfl, rfl, hp q hq⟩

theorem deserializeScope_stripP {s : Session Bytes} (h : DeserializeScopeP ⟨some s⟩) :
    DeserializeGeneral.DeserializeScope ⟨some (stripP s)⟩ :=
  deserializeScope_stripBounded (deserializeScopeBounded_of_deserializeScopeP h)

private def sessionExtraLen (s : Session Bytes) : Nat :=
  (Record.msgField 9 (s.pendingPreKey.map Record.encPendingPreKey)).length +
  (Record.uint32Field 10 s.remoteRegistrationId).length +
  (Record.uint32Field 11 s.localRegistrationId).length +
  (Record.bytesField 13 s.aliceBaseKey).length +
  (Record.msgField 14 (s.pendingKyberPreKey.map Record.encPendingKyber)).length

private theorem encSession_stripBounded_length (s : Session Bytes) :
    (Record.encSession s).length + sessionExtraLen (stripP s) =
      (Record.encSession (stripP s)).length + sessionExtraLen s := by
  have e2 := bytesField2_ik_length_eq (stripP s).state.localIdentity s.state.localIdentity
  simp only [Record.encSession, sessionExtraLen, stripP, List.length_append] at e2 ⊢
  omega

private theorem sessionExtraLen_le (s : Session Bytes)
    (ha : s.aliceBaseKey.length < 2 ^ 16)
    (hk : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 16) :
    sessionExtraLen s ≤ 2 * 2 ^ 16 + 300 := by
  unfold sessionExtraLen
  have h9 := msgField9_length_leP s.pendingPreKey
  have h10 : (Record.uint32Field 10 s.remoteRegistrationId).length ≤ 20 :=
    uint32Field_length_le' 10 s.remoteRegistrationId
  have h11 : (Record.uint32Field 11 s.localRegistrationId).length ≤ 20 :=
    uint32Field_length_le' 11 s.localRegistrationId
  have h13 : (Record.bytesField 13 s.aliceBaseKey).length ≤ s.aliceBaseKey.length + 20 :=
    bytesField_length_le' 13 s.aliceBaseKey
  have h14 : (Record.msgField 14 (s.pendingKyberPreKey.map Record.encPendingKyber)).length ≤ 2 ^ 16 + 60 := by
    rcases hkx : s.pendingKyberPreKey with _ | k
    · simp [Record.msgField]
    · dsimp only [Option.map_some, Record.msgField]
      have h0 : (Record.lenField 14 (Record.encPendingKyber k)).length ≤
          (Record.encPendingKyber k).length + 20 :=
        lenField_length_le' 14 (Record.encPendingKyber k)
      have heq : (Record.encPendingKyber k).length =
          (Record.uint32Field 1 k.preKeyId).length + (Record.bytesField 2 k.ciphertext).length := by
        simp only [Record.encPendingKyber, List.length_append]
      have ha' : (Record.uint32Field 1 k.preKeyId).length ≤ 20 := uint32Field_length_le' 1 k.preKeyId
      have hb' : (Record.bytesField 2 k.ciphertext).length ≤ k.ciphertext.length + 20 :=
        bytesField_length_le' 2 k.ciphertext
      have hc' := hk k hkx
      omega
  omega

private theorem encodeRecord_some_length_le (s : Session Bytes) :
    (Record.encodeRecord ⟨some s⟩).length ≤ (Record.encSession s).length + 20 := by
  unfold Record.encodeRecord Record.msgField
  dsimp only [Option.map_some]
  exact lenField_length_le' 1 (Record.encSession s)

private theorem encodeRecord_some_length_ge (s : Session Bytes) :
    (Record.encSession s).length ≤ (Record.encodeRecord ⟨some s⟩).length := by
  unfold Record.encodeRecord Record.msgField
  dsimp only [Option.map_some]
  exact lenField_length_ge' 1 (Record.encSession s)

private theorem len_bound_arith (a b c d x1 x2 : Nat)
    (hs : a < 2 ^ 20)
    (hge : b ≤ a)
    (hle : c ≤ d + 20)
    (heq : d + x2 = b + x1)
    (hx : x1 ≤ 2 * 2 ^ 16 + 300) :
    c < 2 ^ 21 := by
  omega

/-- Every record in `DeserializeScopeBounded` encodes to fewer than `2 ^ 21` bytes. -/
theorem encodeRecord_length_lt_21_of_bounded {s : Session Bytes} (h : DeserializeScopeBounded ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 21 := by
  have hs := DeserializeGeneral.encodeRecord_length_lt (deserializeScope_stripBounded h)
  have hsc : SessionScopeBounded s := by
    rcases h with ⟨_, s', hs', hsc⟩
    injection hs' with hs'
    exact hs' ▸ hsc
  exact len_bound_arith
    (Record.encodeRecord ⟨some (stripP s)⟩).length
    (Record.encSession (stripP s)).length
    (Record.encodeRecord ⟨some s⟩).length
    (Record.encSession s).length
    (sessionExtraLen s)
    (sessionExtraLen (stripP s))
    hs
    (encodeRecord_some_length_ge (stripP s))
    (encodeRecord_some_length_le s)
    (encSession_stripBounded_length s)
    (sessionExtraLen_le s hsc.2.2.2 hsc.2.2.1)

theorem encodeRecord_length_lt_32_of_bounded {s : Session Bytes} (h : DeserializeScopeBounded ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 32 :=
  Nat.lt_trans (encodeRecord_length_lt_21_of_bounded h) (by decide)

theorem encodeRecord_length_lt_21_of_deserializeScopeX {s : Session Bytes} (h : DeserializeScopeX ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 21 :=
  encodeRecord_length_lt_21_of_bounded (deserializeScopeBounded_of_deserializeScopeX h)

theorem encodeRecord_length_lt_32_of_deserializeScopeX {s : Session Bytes} (h : DeserializeScopeX ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 32 :=
  encodeRecord_length_lt_32_of_bounded (deserializeScopeBounded_of_deserializeScopeX h)

theorem encodeRecord_length_lt_21_of_deserializeScopeP {s : Session Bytes} (h : DeserializeScopeP ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 21 :=
  encodeRecord_length_lt_21_of_bounded (deserializeScopeBounded_of_deserializeScopeP h)

abbrev encodeRecord_length_lt_P {s : Session Bytes} (h : DeserializeScopeP ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 21 :=
  encodeRecord_length_lt_21_of_deserializeScopeP h

theorem encodeRecord_length_lt_32_of_deserializeScopeP {s : Session Bytes} (h : DeserializeScopeP ⟨some s⟩) :
    (Record.encodeRecord ⟨some s⟩).length < 2 ^ 32 :=
  encodeRecord_length_lt_32_of_bounded (deserializeScopeBounded_of_deserializeScopeP h)

end CryptoVerification.E2E.RecordX
