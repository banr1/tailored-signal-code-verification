/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.SM.RecordInj.Primitives

/-!
# Bottom-Up Protobuf Message Injectivity

Proves injectivity of `encChainKey`, `encMessageKey`, `encSenderChain`, `encReceiverChain`,
`encSessionStructureSeed`, and `encodeRecord` on encodings of total byte length `< 2 ^ 64` via
`ChainEq` prefix cancellation.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.SM.RecordInj

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E

theorem chainEq_of_eq_lt {b₁ b₂ : Bytes} (hlen : b₁.length < 2 ^ 64) (heq : b₁ = b₂) :
    ChainEq (b₁ ++ []) (b₂ ++ []) := by
  refine ⟨by rw [heq], ?_⟩
  simpa using hlen

/-! ## Sub-message Injectivity -/

theorem encChainKey_inj (ck₁ ck₂ : ChainKey) (hlen : (encChainKey ck₁).length < 2 ^ 64)
    (h : encChainKey ck₁ = encChainKey ck₂) : ck₁ = ck₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encChainKey, List.append_assoc] at hc0
  obtain ⟨hidx, hc1⟩ := peel_uint32 (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc0
  obtain ⟨hk, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc1
  cases ck₁
  cases ck₂
  cases hidx
  cases keyToBytes32_inj hk
  rfl

theorem encMessageKey_inj (mk₁ mk₂ : MessageKeyGenerator)
    (hlen : (encMessageKey mk₁).length < 2 ^ 64)
    (h : encMessageKey mk₁ = encMessageKey mk₂) : mk₁ = mk₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encMessageKey, List.append_assoc] at hc0
  obtain ⟨hctr, hc1⟩ := peel_uint32 (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc0
  obtain ⟨hseed, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc1
  cases mk₁
  cases mk₂
  cases hctr
  cases hseed
  rfl

theorem encSenderChain_inj (c₁ c₂ : SenderChain) (hlen : (encSenderChain c₁).length < 2 ^ 64)
    (h : encSenderChain c₁ = encSenderChain c₂) : c₁ = c₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encSenderChain, List.append_assoc] at hc0
  obtain ⟨hpub, hc1⟩ := peel_bytes (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))) hc0
  obtain ⟨hpriv, hc2⟩ := peel_bytes (by omega) (by omega)
    (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc1
  change ChainEq (msgField 3 ((some c₁.chainKey).map encChainKey) ++ [])
    (msgField 3 ((some c₂.chainKey).map encChainKey) ++ []) at hc2
  obtain ⟨hck, _⟩ := peel_msg encChainKey (by omega) (by omega) encChainKey_inj
    (tagGe_nil _) (tagGe_nil _) hc2
  obtain ⟨⟨pub₁, priv₁⟩, ck₁⟩ := c₁
  obtain ⟨⟨pub₂, priv₂⟩, ck₂⟩ := c₂
  cases publicKey_serialize_inj hpub
  cases privateKey_toList_inj hpriv
  cases Option.some.inj hck
  rfl

theorem encReceiverChain_inj (c₁ c₂ : ReceiverChain)
    (hlen : (encReceiverChain c₁).length < 2 ^ 64)
    (h : encReceiverChain c₁ = encReceiverChain c₂) : c₁ = c₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encReceiverChain, List.append_assoc] at hc0
  obtain ⟨hsrk, hc1⟩ := peel_bytes (by omega) (by omega)
    (tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))
    (tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _))) hc0
  obtain ⟨hck, hc2⟩ := peel_msg encChainKey (by omega) (by omega) encChainKey_inj
    (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc1
  obtain ⟨hmks, _⟩ := peel_repeated encMessageKey (by omega) (by omega) encMessageKey_inj
    (tagGe_nil _) (tagGe_nil _) hc2
  cases c₁
  cases c₂
  cases publicKey_serialize_inj hsrk
  cases hck
  cases hmks
  rfl

/-! ## `SessionState` and `SessionRecord` Injectivity -/

private theorem stateTail_tagGe (st : SessionState Bytes) :
    let t9 := bytesField 15 st.pqRatchetState ++ []
    let t8 := msgField 9 (if st.pendingPreKey then some encPlaceholderPendingPreKey else none) ++ t9
    let t7 := (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++ t8
    let t6 := msgField 6 (st.senderChain.map encSenderChain) ++ t7
    let t5 := uint32Field 5 st.previousCounter ++ t6
    let t4 := bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++ t5
    let t3 := bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++ t4
    let t2 := bytesField 2 st.localIdentity.serialize ++ t3
    TagGe 2 t2 ∧ TagGe 3 t3 ∧ TagGe 4 t4 ∧ TagGe 5 t5 ∧
      TagGe 6 t6 ∧ TagGe 7 t7 ∧ TagGe 8 t8 ∧ TagGe 10 t9 := by
  intro t9 t8 t7 t6 t5 t4 t3 t2
  have h10 : TagGe 10 t9 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)
  have h8 : TagGe 8 t8 :=
    tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h10 t ht))
  have h7 : TagGe 7 t7 :=
    tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h8 t ht))
  have h6 : TagGe 6 t6 :=
    tagGe_msgField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h7 t ht))
  have h5 : TagGe 5 t5 :=
    tagGe_uint32Field _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h6 t ht))
  have h4 : TagGe 4 t4 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h5 t ht))
  have h3 : TagGe 3 t3 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h4 t ht))
  have h2 : TagGe 2 t2 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (h3 t ht))
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h10⟩

private theorem remoteIdentity_opt_inj {r₁ r₂ : Option IdentityKey}
    (h : (r₁.map IdentityKey.serialize).getD [] = (r₂.map IdentityKey.serialize).getD []) :
    r₁ = r₂ := by
  cases r₁ with
  | none =>
    cases r₂ with
    | none => rfl
    | some ik₂ => simp [IdentityKey.serialize, PublicKey.serialize] at h
  | some ik₁ =>
    cases r₂ with
    | none => simp [IdentityKey.serialize, PublicKey.serialize] at h
    | some ik₂ =>
      simp only [Option.map_some, Option.getD_some] at h
      exact congrArg some (identityKey_serialize_inj h)

theorem encStateE_inj (st₁ st₂ : SessionState Bytes)
    (hlen : (encSessionStructureSeed st₁).length < 2 ^ 64)
    (h : encSessionStructureSeed st₁ = encSessionStructureSeed st₂) : st₁ = st₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encSessionStructureSeed, List.append_assoc] at hc0
  obtain ⟨g2, g3, g4, g5, g6, g7, g8, g10⟩ := stateTail_tagGe st₁
  obtain ⟨g2', g3', g4', g5', g6', g7', g8', g10'⟩ := stateTail_tagGe st₂
  obtain ⟨hf1, hc1⟩ := peel_uint32 (by omega) (by omega) g2 g2' hc0
  obtain ⟨hf2, hc2⟩ := peel_bytes (by omega) (by omega) g3 g3' hc1
  obtain ⟨hf3, hc3⟩ := peel_bytes (by omega) (by omega) g4 g4' hc2
  obtain ⟨hf4, hc4⟩ := peel_bytes (by omega) (by omega) g5 g5' hc3
  obtain ⟨hf5, hc5⟩ := peel_uint32 (by omega) (by omega) g6 g6' hc4
  obtain ⟨hf6, hc6⟩ := peel_msg encSenderChain (by omega) (by omega) encSenderChain_inj g7 g7' hc5
  obtain ⟨hf7, hc7⟩ := peel_repeated encReceiverChain (by omega) (by omega) encReceiverChain_inj
    g8 g8' hc6
  have hpend : st₁.pendingPreKey = st₂.pendingPreKey ∧
      ChainEq (bytesField 15 st₁.pqRatchetState ++ [])
              (bytesField 15 st₂.pqRatchetState ++ []) := by
    have hmap : ∀ b : Bool,
        Option.map (fun _ : Unit => encPlaceholderPendingPreKey) (if b then some () else none) =
          (if b then some encPlaceholderPendingPreKey else none) := by
      intro b; cases b <;> rfl
    rw [← hmap st₁.pendingPreKey, ← hmap st₂.pendingPreKey] at hc7
    obtain ⟨hov, hc8⟩ := peel_msg (fun _ : Unit => encPlaceholderPendingPreKey) (by omega) (by omega)
      (fun ⟨⟩ ⟨⟩ _ _ => rfl) g10 g10' hc7
    refine ⟨?_, hc8⟩
    cases hp₁ : st₁.pendingPreKey <;> cases hp₂ : st₂.pendingPreKey <;>
      simp [hp₁, hp₂] at hov ⊢
  obtain ⟨hf9, hc8⟩ := hpend
  obtain ⟨hf15, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc8
  cases st₁
  cases st₂
  cases hf1
  cases identityKey_serialize_inj hf2
  cases remoteIdentity_opt_inj hf3
  cases keyToBytes32_inj hf4
  cases hf5
  cases hf6
  cases hf7
  cases hf9
  cases hf15
  rfl

theorem encodeRecord_inj_of_length_lt {g g' : GhostState Bytes}
    (h₁ : (encodeRecord g).length < 2 ^ 64)
    (h₂ : (encodeRecord g').length < 2 ^ 64)
    (h : encodeRecord g = encodeRecord g') : g.session = g'.session := by
  have hs₁ : (encSessionStructureSeed g.session).length < 2 ^ 64 := by
    have := length_le_lenField 1 (encSessionStructureSeed g.session)
    simp only [encodeRecord, msgField] at h₁
    omega
  have hs₂ : (encSessionStructureSeed g'.session).length < 2 ^ 64 := by
    have := length_le_lenField 1 (encSessionStructureSeed g'.session)
    simp only [encodeRecord, msgField] at h₂
    omega
  have hrec : lenField 1 (encSessionStructureSeed g.session) ++ [] = lenField 1 (encSessionStructureSeed g'.session) ++ [] := by
    simpa [encodeRecord, msgField] using h
  exact encStateE_inj g.session g'.session hs₁ (lenField_append_inj hs₁ hs₂ hrec).1

end CryptoVerification.SignalSession.SM.RecordInj
