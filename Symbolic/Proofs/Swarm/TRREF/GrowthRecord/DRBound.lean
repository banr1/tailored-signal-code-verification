/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.CliPureBytes

/-!
# Double-Ratchet Record Encoding Size Bounds

Decomposes `encSession` into double-ratchet fields (`drLen`), session extra fields (`extLen`), and
the post-quantum ratchet state field, proves `drLen s ≤ DRMAX` (`600000`) under `DRCaps`, and
derives absolute and single-step growth bounds for `encodeRecord`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecord

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec CryptoVerification.E2E.Record

/-! ## Field-Length Lemmas -/

theorem encodeVarintAux_length_le (n : Nat) (v : BitVec 64) :
    (encodeVarintAux n v).length ≤ n := by
  induction n generalizing v with
  | zero => simp [encodeVarintAux]
  | succ n ih =>
    unfold encodeVarintAux
    split
    · simp
    · simp only [List.length_cons]
      have := ih (v >>> 7)
      omega

theorem encodeVarint_length_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  encodeVarintAux_length_le 10 v

theorem encodeKey_length_le (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  encodeVarint_length_le _

theorem lenField_length_le' (tag : Nat) (b : List (BitVec 8)) :
    (lenField tag b).length ≤ b.length + 20 := by
  unfold lenField
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 b.length)
  simp only [List.length_append]
  omega

theorem lenField_length_ge' (tag : Nat) (b : List (BitVec 8)) :
    b.length ≤ (lenField tag b).length := by
  unfold lenField
  simp only [List.length_append]
  omega

theorem bytesField_length_le' (tag : Nat) (b : List (BitVec 8)) :
    (bytesField tag b).length ≤ b.length + 20 := by
  unfold bytesField
  split_ifs
  · simp
  · exact lenField_length_le' tag b

theorem uint32Field_length_le' (tag : Nat) (v : BitVec 32) : (uint32Field tag v).length ≤ 20 := by
  unfold uint32Field
  split_ifs
  · simp
  · have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.setWidth 64)
    simp only [List.length_append]
    omega

theorem serialize_pk_length' (pk : PublicKey) : pk.serialize.length = 33 := by
  simp [PublicKey.serialize]

theorem encodeVarint_length_of_lt (v : BitVec 64) (hv : v.toNat < 0x80) :
    (encodeVarint v).length = 1 := by
  unfold encodeVarint
  rw [encodeVarintAux]
  simp [hv]

theorem encodeKey_length_of_lt (tag : Nat) (wt : WireType) (htag : tag < 16) :
    (encodeKey tag wt).length = 1 := by
  unfold encodeKey
  apply encodeVarint_length_of_lt
  have hwt : wt.toNat ≤ 5 := by cases wt <;> simp [WireType.toNat]
  rw [BitVec.toNat_ofNat]
  have h : tag * 8 + wt.toNat < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h]
  omega

/-- Exact `lenField` length (`b.length + 2`) when `tag < 16` and `b.length < 128`. -/
theorem lenField_length_eq_small (tag : Nat) (b : List (BitVec 8)) (htag : tag < 16)
    (hb : b.length < 128) : (lenField tag b).length = b.length + 2 := by
  unfold lenField
  have h1 := encodeKey_length_of_lt tag .lengthDelimited htag
  have h2 : (encodeVarint (BitVec.ofNat 64 b.length)).length = 1 := by
    apply encodeVarint_length_of_lt
    rw [BitVec.toNat_ofNat]
    have h : b.length < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt h]
    omega
  simp only [List.length_append]
  omega

theorem bytesField_length_le_small (tag : Nat) (b : List (BitVec 8)) (htag : tag < 16)
    (hb : b.length < 128) : (bytesField tag b).length ≤ b.length + 2 := by
  unfold bytesField
  split_ifs
  · simp
  · exact (lenField_length_eq_small tag b htag hb).le

theorem msgField_length_le (tag : Nat) (o : Option (List (BitVec 8))) (B : Nat)
    (h : ∀ b, o = some b → b.length ≤ B) : (msgField tag o).length ≤ B + 20 := by
  cases o with
  | none => simp [msgField]
  | some b =>
    have := lenField_length_le' tag b
    have := h b rfl
    simp only [msgField]
    omega

theorem flatten_map_length_le {α : Type} (l : List α) (f : α → List (BitVec 8)) (B : Nat)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.map f).flatten.length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have ha := h a (by simp)
    have hl := ih (fun x hx => h x (by simp [hx]))
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem keyToBytes32_length (k : BitVec 256) : (HMAC.keyToBytes32 k).length = 32 := by
  simp [HMAC.keyToBytes32]

/-! ## Submessage and Session Decomposition Bounds -/

theorem encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 54 := by
  unfold encChainKey
  have h1 := uint32Field_length_le' 1 ck.index
  have h2 := bytesField_length_le_small 2 (HMAC.keyToBytes32 ck.key) (by norm_num)
    (by rw [keyToBytes32_length]; norm_num)
  rw [keyToBytes32_length] at h2
  simp only [List.length_append]
  omega

theorem encMessageKey_length_le (mk : MessageKeyGenerator) (hs : mk.seed.length = 32) :
    (encMessageKey mk).length ≤ 54 := by
  unfold encMessageKey
  have h1 := uint32Field_length_le' 1 mk.counter
  have h2 := bytesField_length_le_small 5 mk.seed (by norm_num) (by omega)
  simp only [List.length_append]
  omega

theorem lenField4_encMessageKey_le (mk : MessageKeyGenerator) (hs : mk.seed.length = 32) :
    (lenField 4 (encMessageKey mk)).length ≤ 56 := by
  have h := encMessageKey_length_le mk hs
  rw [lenField_length_eq_small 4 _ (by norm_num) (by omega)]
  omega

theorem encReceiverChain_length_le (c : ReceiverChain)
    (hk : c.messageKeys.length ≤ maxMessageKeys) (hs : ∀ mk ∈ c.messageKeys, mk.seed.length = 32) :
    (encReceiverChain c).length ≤ 112127 := by
  unfold encReceiverChain
  have h1 := bytesField_length_le' 1 c.senderRatchetKey.serialize
  rw [serialize_pk_length'] at h1
  have h2 := msgField_length_le 3 (c.chainKey.map encChainKey) 54 (by
    intro b hb
    rcases hc : c.chainKey with _ | ck
    · simp [hc] at hb
    · simp only [hc, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact encChainKey_length_le ck)
  have h3 := flatten_map_length_le c.messageKeys (fun mk => lenField 4 (encMessageKey mk)) 56
    (fun mk hmk => lenField4_encMessageKey_le mk (hs mk hmk))
  have hk' : c.messageKeys.length ≤ 2000 := hk
  simp only [List.length_append]
  omega

theorem encSenderChain_length_le (c : SenderChain) : (encSenderChain c).length ≤ 201 := by
  unfold encSenderChain
  have h1 := bytesField_length_le' 1 c.ratchetKey.publicKey.serialize
  rw [serialize_pk_length'] at h1
  have h2 := bytesField_length_le' 2 c.ratchetKey.privateKey.bytes.toList
  rw [List.Vector.toList_length] at h2
  have h3 := msgField_length_le 3 (some (encChainKey c.chainKey)) 54 (by
    intro b hb
    simp only [Option.some.injEq] at hb
    subst hb
    exact encChainKey_length_le _)
  simp only [List.length_append]
  omega

/-- Byte length of fields 1 to 7 of `encSession` (the double-ratchet state). -/
def drLen (s : Session (List (BitVec 8))) : Nat :=
  (uint32Field 1 s.state.sessionVersion).length +
  (bytesField 2 s.state.localIdentity.serialize).length +
  (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length +
  (bytesField 4 (HMAC.keyToBytes32 s.state.rootKey)).length +
  (uint32Field 5 s.state.previousCounter).length +
  (msgField 6 (s.state.senderChain.map encSenderChain)).length +
  (s.state.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten.length

/-- Byte length of fields 9, 10, 11, 13, and 14 of `encSession` (session metadata and pending
pre-keys). -/
def extLen (s : Session (List (BitVec 8))) : Nat :=
  (msgField 9 (s.pendingPreKey.map encPendingPreKey)).length +
  (uint32Field 10 s.remoteRegistrationId).length +
  (uint32Field 11 s.localRegistrationId).length +
  (bytesField 13 s.aliceBaseKey).length +
  (msgField 14 (s.pendingKyberPreKey.map encPendingKyber)).length

theorem encSession_length (s : Session (List (BitVec 8))) :
    (encSession s).length =
      drLen s + extLen s + (bytesField 15 s.state.pqRatchetState).length := by
  simp only [encSession, drLen, extLen, List.length_append]
  omega

theorem encodeRecord_some_length_le (s : Session (List (BitVec 8))) :
    (encodeRecord ⟨some s⟩).length ≤ (encSession s).length + 20 := by
  simp only [encodeRecord, Option.map_some, msgField]
  exact lenField_length_le' 1 _

theorem encSession_length_le_encodeRecord (s : Session (List (BitVec 8))) :
    (encSession s).length ≤ (encodeRecord ⟨some s⟩).length := by
  simp only [encodeRecord, Option.map_some, msgField]
  exact lenField_length_ge' 1 _

theorem bytesField_length_ge (tag : Nat) (b : List (BitVec 8)) : b.length ≤ (bytesField tag b).length := by
  unfold bytesField
  split_ifs with h
  · simp [h]
  · exact lenField_length_ge' tag b

/-! ## Double-Ratchet Caps and Record Growth Bounds -/

/-- Double-ratchet caps bounding `drLen`: at most `maxReceiverChains` (5) receiver chains, at most
`maxMessageKeys` (2000) skipped keys per chain, and 32-byte seeds. -/
def DRCaps (s : Session (List (BitVec 8))) : Prop :=
  s.state.receiverChains.length ≤ maxReceiverChains ∧
    ∀ c ∈ s.state.receiverChains,
      c.messageKeys.length ≤ maxMessageKeys ∧ ∀ mk ∈ c.messageKeys, mk.seed.length = 32

abbrev DRMAX : Nat := 600000

theorem drLen_le_DRMAX (s : Session (List (BitVec 8))) (h : DRCaps s) : drLen s ≤ DRMAX := by
  obtain ⟨hn, hc⟩ := h
  have hn' : s.state.receiverChains.length ≤ 5 := hn
  have h1 := uint32Field_length_le' 1 s.state.sessionVersion
  have h2 := bytesField_length_le' 2 s.state.localIdentity.serialize
  rw [IdentityKey.serialize, serialize_pk_length'] at h2
  have h3 : (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length
      ≤ 53 := by
    rcases s.state.remoteIdentity with _ | ik
    · simp [bytesField]
    · have h := bytesField_length_le' 3 ik.serialize
      have hl : ik.serialize.length = 33 := serialize_pk_length' _
      simp only [Option.map_some, Option.getD_some]
      omega
  have h4 := bytesField_length_le' 4 (HMAC.keyToBytes32 s.state.rootKey)
  rw [keyToBytes32_length] at h4
  have h5 := uint32Field_length_le' 5 s.state.previousCounter
  have h6 := msgField_length_le 6 (s.state.senderChain.map encSenderChain) 201 (by
    intro b hb
    rcases hs : s.state.senderChain with _ | sc
    · simp [hs] at hb
    · simp only [hs, Option.map_some, Option.some.injEq] at hb
      subst hb
      exact encSenderChain_length_le sc)
  have h7 := flatten_map_length_le s.state.receiverChains
    (fun c => lenField 7 (encReceiverChain c)) 112147 (by
      intro c hcm
      obtain ⟨hk, hs⟩ := hc c hcm
      have := lenField_length_le' 7 (encReceiverChain c)
      have := encReceiverChain_length_le c hk hs
      omega)
  have h7' : s.state.receiverChains.length * 112147 ≤ 5 * 112147 :=
    Nat.mul_le_mul_right _ hn'
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5) h6) (h7.trans h7')
  refine le_trans hsum ?_
  norm_num

theorem encodeRecord_le_of_caps (s : Session (List (BitVec 8))) (h : DRCaps s) :
    (encodeRecord ⟨some s⟩).length ≤ DRMAX + 40 + extLen s + s.state.pqRatchetState.length := by
  have h1 := encodeRecord_some_length_le s
  have h2 := encSession_length s
  have h3 := drLen_le_DRMAX s h
  have h4 := bytesField_length_le' 15 s.state.pqRatchetState
  omega

theorem extLen_add_pq_le_encodeRecord (s : Session (List (BitVec 8))) :
    extLen s + s.state.pqRatchetState.length ≤ (encodeRecord ⟨some s⟩).length := by
  have h1 := encSession_length_le_encodeRecord s
  have h2 := encSession_length s
  have h3 := bytesField_length_ge 15 s.state.pqRatchetState
  omega

/-- If `extLen s' ≤ extLen s` and the PQ ratchet state grows by at most `2^17` bytes under
`DRCaps s'`, the encoded session record grows by at most `2^20 - 1` bytes. -/
theorem encodeRecord_growth_le (s s' : Session (List (BitVec 8))) (hcaps : DRCaps s')
    (hext : extLen s' ≤ extLen s)
    (hpq : s'.state.pqRatchetState.length ≤ s.state.pqRatchetState.length + 2 ^ 17) :
    (encodeRecord ⟨some s'⟩).length ≤ (encodeRecord ⟨some s⟩).length + (2 ^ 20 - 1) := by
  have h1 := encodeRecord_le_of_caps s' hcaps
  have h2 := extLen_add_pq_le_encodeRecord s
  have hD : DRMAX = 600000 := rfl
  have h17 : (2 : Nat) ^ 17 = 131072 := by norm_num
  have h20 : (2 : Nat) ^ 20 - 1 = 1048575 := by norm_num
  rw [h17] at hpq
  rw [h20]
  omega

theorem encodeRecord_lt_of_growth (s s' : Session (List (BitVec 8))) (hcaps : DRCaps s')
    (hext : extLen s' ≤ extLen s)
    (hpq : s'.state.pqRatchetState.length ≤ s.state.pqRatchetState.length + 2 ^ 17)
    (hrec : (encodeRecord ⟨some s⟩).length < 2 ^ 32 - 2 ^ 20) :
    (encodeRecord ⟨some s'⟩).length < 2 ^ 32 := by
  have h := encodeRecord_growth_le s s' hcaps hext hpq
  have h20 : (2 : Nat) ^ 20 - 1 = 1048575 := by norm_num
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have h3220 : (2 : Nat) ^ 32 - 2 ^ 20 = 4293918720 := by norm_num
  rw [h20] at h
  rw [h3220] at hrec
  rw [h32]
  omega

theorem extLen_applyState_eq (s : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8))) :
    extLen { s with state := st } = extLen s := rfl

theorem extLen_decrypt_le (s : Session (List (BitVec 8))) (st : SessionState (List (BitVec 8))) :
    extLen { s with state := st, pendingPreKey := none, pendingKyberPreKey := none } ≤
      extLen s := by
  simp only [extLen, Option.map_none, msgField, List.length_nil]
  omega

end Symbolic.Swarm.TRREF.GrowthRecord
