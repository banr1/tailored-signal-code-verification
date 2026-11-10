/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.PureCanon
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Ghost-Free Session Encoding Length Bounds

Proves ghost-free length bounds for protobuf field encodings (`encSession`, `encReceiverChain`,
`encSenderChain`, `encodeRecord`) and establishes `PureBinCanonSession` (`BinSessionInv`) from
deserialization scope predicates (`pureBinCanonSession_of_deserializeScopeP`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure.TR.Pure
open Symbolic.Swarm.CREF.TR.Pure

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

abbrev BinSessionInv : Session (List (BitVec 8)) → Prop := PureBinCanonSession

theorem encodeVarintAux_length_le (n : Nat) (v : BitVec 64) :
    (encodeVarintAux n v).length ≤ n := by
  induction n generalizing v with
  | zero => simp [encodeVarintAux]
  | succ n ih =>
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have h := ih (v >>> 7)
      omega

theorem encodeVarint_length_le_10 (v : BitVec 64) :
    (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

theorem encodeKey_length_le_10 (tag : Nat) (wt : WireType) :
    (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le_10 _

theorem lenField_length_le (tag : Nat) (b : List (BitVec 8)) :
    (lenField tag b).length ≤ b.length + 20 := by
  unfold lenField
  have h1 := encodeKey_length_le_10 tag .lengthDelimited
  have h2 := encodeVarint_length_le_10 (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

theorem bytesField_length_le (tag : Nat) (b : List (BitVec 8)) :
    (bytesField tag b).length ≤ b.length + 20 := by
  unfold bytesField
  split_ifs
  · simp
  · exact lenField_length_le tag b

theorem uint32Field_length_le (tag : Nat) (v : BitVec 32) :
    (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

theorem uint64Field_length_le (tag : Nat) (v : BitVec 64) :
    (uint64Field tag v).length ≤ 20 := by
  unfold uint64Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 v
    simp only [List.length_append]
    omega

theorem int32Field_length_le (tag : Nat) (v : BitVec 32) :
    (int32Field tag v).length ≤ 20 := by
  unfold int32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.signExtend 64)
    simp only [List.length_append]
    omega

theorem optUint32Field_length_le (tag : Nat) (ov : Option (BitVec 32)) :
    (optUint32Field tag ov).length ≤ 20 := by
  rcases ov with _ | v
  · simp [optUint32Field]
  · unfold optUint32Field
    have h1 := encodeKey_length_le_10 tag .varint
    have h2 := encodeVarint_length_le_10 (v.setWidth 64)
    simp only [List.length_append]
    omega

theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

theorem encChainKey_length_le (ck : ChainKey) :
    (encChainKey ck).length ≤ 72 := by
  unfold encChainKey
  have h1 := uint32Field_length_le 1 ck.index
  have h2 := bytesField_length_le 2 (HMAC.keyToBytes32 ck.key)
  rw [keyToBytes32_length] at h2
  simp only [List.length_append]
  omega

theorem lenField_encMessageKey_length_le (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) :
    (lenField 4 (encMessageKey mk)).length ≤ 92 := by
  have h0 := lenField_length_le 4 (encMessageKey mk)
  have heq : (encMessageKey mk).length =
      (uint32Field 1 mk.counter).length + (bytesField 5 mk.seed).length := by
    simp [encMessageKey]
  have h1 := uint32Field_length_le 1 mk.counter
  have h2 := bytesField_length_le 5 mk.seed
  rw [hseed] at h2
  omega

theorem flatten_encMessageKeys_length_le (mks : List MessageKeyGenerator)
    (hseeds : ∀ mk ∈ mks, mk.seed.length = 32) :
    ((mks.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ 92 * mks.length := by
  induction mks with
  | nil => simp
  | cons mk mks ih =>
    have hmk := lenField_encMessageKey_length_le mk (hseeds mk (by simp))
    have hmks := ih (fun m hm => hseeds m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem lenField_encReceiverChain_length_le (c : ReceiverChain)
    (hmax : c.messageKeys.length ≤ maxMessageKeys)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (lenField 7 (encReceiverChain c)).length ≤ 184165 := by
  have h0 := lenField_length_le 7 (encReceiverChain c)
  have heq : (encReceiverChain c).length =
      (bytesField 1 c.senderRatchetKey.serialize).length +
      (msgField 3 (c.chainKey.map encChainKey)).length +
      ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
    simp only [encReceiverChain, List.length_append]
  have h1 := bytesField_length_le 1 c.senderRatchetKey.serialize
  rw [publicKey_serialize_length] at h1
  have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤ 92 := by
    rcases c.chainKey with _ | ck
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have hck := encChainKey_length_le ck
      have hlf := lenField_length_le 3 (encChainKey ck)
      omega
  have h3 := flatten_encMessageKeys_length_le c.messageKeys hseeds
  have hmax_val : maxMessageKeys = 2000 := rfl
  omega

theorem flatten_encReceiverChains_length_le (cs : List ReceiverChain)
    (hrc_mk : ∀ c ∈ cs, c.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    ((cs.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤ 184165 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc := lenField_encReceiverChain_length_le c (hrc_mk c (by simp)).1 (hrc_mk c (by simp)).2
    have hcs := ih (fun c' hc' => hrc_mk c' (List.mem_cons_of_mem _ hc'))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- Canonical `encSession s` has byte length strictly below `2 ^ 62` under standard session bounds. -/
theorem encodeSession_length_lt_62 (s : Session (List (BitVec 8)))
    (hrc_len : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrc_mk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32)
    (halice : s.aliceBaseKey.length < 2 ^ 32)
    (hkyber : match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32)
    (hpq : s.state.pqRatchetState.length < 2 ^ 32) :
    (encSession s).length < 2 ^ 62 := by
  have hMaxChains_val : maxReceiverChains = 5 := rfl
  have hlen : (encSession s).length =
      (uint32Field 1 s.state.sessionVersion).length +
      (bytesField 2 s.state.localIdentity.serialize).length +
      (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length +
      (bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length +
      (uint32Field 5 s.state.previousCounter).length +
      (msgField 6 (s.state.senderChain.map encSenderChain)).length +
      ((s.state.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten).length +
      (msgField 9 (s.pendingPreKey.map encPendingPreKey)).length +
      (uint32Field 10 s.remoteRegistrationId).length +
      (uint32Field 11 s.localRegistrationId).length +
      (bytesField 13 s.aliceBaseKey).length +
      (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length +
      (bytesField 15 s.state.pqRatchetState).length := by
    simp only [encSession, List.length_append]
  have h1 := uint32Field_length_le 1 s.state.sessionVersion
  have h2 := bytesField_length_le 2 s.state.localIdentity.serialize
  rw [identityKey_serialize_length] at h2
  have h3 : (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤ 53 := by
    rcases s.state.remoteIdentity with _ | ik
    · simp [bytesField]
    · dsimp only [Option.map_some, Option.getD_some]
      have h := bytesField_length_le 3 ik.serialize
      rw [identityKey_serialize_length] at h
      exact h
  have h4 := bytesField_length_le 4 (HMAC.keyToBytes32 s.state.rootKey)
  rw [keyToBytes32_length] at h4
  have h5 := uint32Field_length_le 5 s.state.previousCounter
  have h6 : (msgField 6 (s.state.senderChain.map encSenderChain)).length ≤ 217 := by
    rcases s.state.senderChain with _ | sc
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 := lenField_length_le 6 (encSenderChain sc)
      have heq : (encSenderChain sc).length =
          (bytesField 1 sc.ratchetKey.publicKey.serialize).length +
          (bytesField 2 sc.ratchetKey.privateKey.bytes.toList).length +
          (lenField 3 (encChainKey sc.chainKey)).length := by
        simp only [encSenderChain, msgField, List.length_append]
      have ha := bytesField_length_le 1 sc.ratchetKey.publicKey.serialize
      rw [publicKey_serialize_length] at ha
      have hb := bytesField_length_le 2 sc.ratchetKey.privateKey.bytes.toList
      rw [List.Vector.toList_length] at hb
      have hc := lenField_length_le 3 (encChainKey sc.chainKey)
      have hd := encChainKey_length_le sc.chainKey
      omega
  have h7 := flatten_encReceiverChains_length_le s.state.receiverChains hrc_mk
  have h9 : (msgField 9 (s.pendingPreKey.map encPendingPreKey)).length ≤ 133 := by
    rcases s.pendingPreKey with _ | p
    · simp [msgField]
    · dsimp only [Option.map_some, msgField]
      have h0 := lenField_length_le 9 (encPendingPreKey p)
      have heq : (encPendingPreKey p).length =
          (optUint32Field 1 p.preKeyId).length +
          (bytesField 2 p.baseKey.serialize).length +
          (int32Field 3 p.signedPreKeyId).length +
          (uint64Field 4 p.timestamp).length := by
        simp only [encPendingPreKey, List.length_append]
      have ha := optUint32Field_length_le 1 p.preKeyId
      have hb := bytesField_length_le 2 p.baseKey.serialize
      rw [publicKey_serialize_length] at hb
      have hc := int32Field_length_le 3 p.signedPreKeyId
      have hd := uint64Field_length_le 4 p.timestamp
      omega
  have h10 := uint32Field_length_le 10 s.remoteRegistrationId
  have h11 := uint32Field_length_le 11 s.localRegistrationId
  have h13 := bytesField_length_le 13 s.aliceBaseKey
  have h14 : (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length < 2 ^ 32 + 60 := by
    rcases hp : s.pendingKyberPreKey with _ | pkp
    · simp [msgField]
    · rw [hp] at hkyber
      dsimp only [Option.map_some, msgField]
      have h0 := lenField_length_le 14 (encPendingKyber pkp)
      have heq : (encPendingKyber pkp).length =
          (uint32Field 1 pkp.preKeyId).length + (bytesField 2 pkp.ciphertext).length := by
        simp [encPendingKyber]
      have ha := uint32Field_length_le 1 pkp.preKeyId
      have hb := bytesField_length_le 2 pkp.ciphertext
      omega
  have h15 := bytesField_length_le 15 s.state.pqRatchetState
  omega

theorem encodeRecord_some_length_le (s : Session (List (BitVec 8))) :
    (encodeRecord ⟨some s⟩).length ≤ (encSession s).length + 20 :=
  lenField_length_le 1 (encSession s)

theorem binSessionInv_of_bounds {s : Session (List (BitVec 8))}
    (hwf : s.Wf)
    (hrc_len : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrc_mk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32)
    (halice : s.aliceBaseKey.length < 2 ^ 32)
    (hkyber : match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32)
    (hpq : s.state.pqRatchetState.length < 2 ^ 32) :
    BinSessionInv s :=
  ⟨hwf, hrc_len, hrc_mk, halice, hkyber, hpq,
   encodeSession_length_lt_62 s hrc_len hrc_mk halice hkyber hpq⟩

theorem pureBinCanonSession_of_bounds {s : Session (List (BitVec 8))}
    (hwf : s.Wf)
    (hrc_len : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrc_mk : ∀ rc ∈ s.state.receiverChains, rc.messageKeys.length ≤ maxMessageKeys ∧
      ∀ mkg ∈ rc.messageKeys, mkg.seed.length = 32)
    (halice : s.aliceBaseKey.length < 2 ^ 32)
    (hkyber : match s.pendingKyberPreKey with | none => True | some pkp => pkp.ciphertext.length < 2 ^ 32)
    (hpq : s.state.pqRatchetState.length < 2 ^ 32) :
    PureBinCanonSession s :=
  binSessionInv_of_bounds hwf hrc_len hrc_mk halice hkyber hpq

/-- `slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some s⟩` implies `PureBinCanonSession s`. -/
theorem pureBinCanonSession_of_deserializeScopeP {s : Session (List (BitVec 8))}
    (h : slots_DeserializeScopeP_Q slots_NonEmptyV1Q ⟨some s⟩) :
    PureBinCanonSession s := by
  obtain ⟨⟨hrin, hrq, hrepr⟩, s', hs', hss⟩ := h
  injection hs' with hs_eq
  subst hs_eq
  obtain ⟨hseeds, _, hkyb⟩ := hrin s rfl
  have hpq : s.state.pqRatchetState.length < 2 ^ 32 := hrq s rfl
  obtain ⟨hmks, _, hwf, halice⟩ := hrepr s rfl
  refine pureBinCanonSession_of_bounds hwf hss.1 ?_ halice ?_ hpq
  · exact fun rc hrc => ⟨hmks rc hrc, hseeds rc hrc⟩
  · cases hk : s.pendingKyberPreKey with
    | none => trivial
    | some pkp => exact hkyb pkp hk

end Symbolic.Swarm.CREF.CliPure.TR.Pure
