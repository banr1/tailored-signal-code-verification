/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.EncOk
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3Defs
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.SignalSession.SM.RecordInj.Fields

/-!
# Injectivity of `SessionRecord::serialize` on `DeserializeScopeP_Q NonEmptyV1Q`

Proves `encodeInjOn_deserializeScopeP_Q` (`EncodeInjOn` for `DeserializeScopeP_Q NonEmptyV1Q`, i.e.
`scopeKit`):
1. Peels outer `RecordStructure.current_session` (`msgField 1`) using a `< 2^64` byte-length bound
   on all 13 fields of `Record.encSession`.
2. Peels `Record.encSession` in ascending tag order `1..7, 9..11, 13..15` via `TagGe`/`ChainEq`
   combinators.
3. Recovers `s.state.pendingPreKey : Bool` from `Session.Wf` (`s.state.pendingPreKey = s.pendingPreKey.isSome`)
   and equality of tag `9`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.SM.RecordInj

/-! ## Equality between `E2E.Record` and `E2E` field encoders -/

@[local simp] private theorem record_lenField_eq (tag : ℕ) (b : Bytes) :
    Record.lenField tag b = E2E.lenField tag b := rfl

@[local simp] private theorem record_bytesField_eq (tag : ℕ) (v : Bytes) :
    Record.bytesField tag v = E2E.bytesField tag v := rfl

@[local simp] private theorem record_uint32Field_eq (tag : ℕ) (v : BitVec 32) :
    Record.uint32Field tag v = E2E.uint32Field tag v := rfl

@[local simp] private theorem record_uint64Field_eq (tag : ℕ) (v : BitVec 64) :
    Record.uint64Field tag v = E2E.uint64FieldX tag v := rfl

@[local simp] private theorem record_int32Field_eq (tag : ℕ) (v : BitVec 32) :
    Record.int32Field tag v = E2E.int32FieldX tag v := rfl

@[local simp] private theorem record_optUint32Field_eq (tag : ℕ) (ov : Option (BitVec 32)) :
    Record.optUint32Field tag ov = E2E.optUint32FieldX tag ov := by
  cases ov <;> rfl

@[local simp] private theorem record_msgField_eq (tag : ℕ) (ov : Option Bytes) :
    Record.msgField tag ov = E2E.msgField tag ov := by
  cases ov <;> rfl

@[local simp] private theorem record_encChainKey_eq :
    Record.encChainKey = E2E.encChainKey := rfl

@[local simp] private theorem record_encMessageKey_eq :
    Record.encMessageKey = E2E.encMessageKey := rfl

@[local simp] private theorem record_encSenderChain_eq :
    Record.encSenderChain = E2E.encSenderChain := by
  funext c
  simp [Record.encSenderChain, E2E.encSenderChain]

@[local simp] private theorem record_encReceiverChain_eq :
    Record.encReceiverChain = E2E.encReceiverChain := by
  funext c
  simp [Record.encReceiverChain, E2E.encReceiverChain]

@[local simp] private theorem record_encPendingPreKey_eq :
    Record.encPendingPreKey = E2E.encPendingPreKeyX := by
  funext p
  simp [Record.encPendingPreKey, E2E.encPendingPreKeyX]

@[local simp] private theorem record_encPendingKyber_eq :
    Record.encPendingKyber = E2E.encPendingKyberX := rfl

/-! ## Field-peeling combinators (`uint64FieldX`, `int32FieldX`, `optUint32FieldX`) -/

private theorem tagGe_mono {T₁ T₂ : ℕ} {bs : Bytes} (hle : T₁ ≤ T₂) (h : TagGe T₂ bs) :
    TagGe T₁ bs :=
  fun t ht => Nat.le_trans hle (h t ht)

private theorem int32_signExtend64_inj {v₁ v₂ : BitVec 32}
    (h : v₁.signExtend 64 = v₂.signExtend 64) : v₁ = v₂ := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbit := congrArg (·.getLsbD i) h
  have hi64 : i < 64 := by omega
  simp only [BitVec.getLsbD_signExtend, hi, hi64, decide_true, Bool.true_and, ↓reduceIte] at hbit
  exact hbit

private theorem tagGe_uint64FieldX {T tag : ℕ} (v : BitVec 64) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (uint64FieldX tag v ++ rest) := by
  unfold uint64FieldX
  split_ifs
  · simpa using hrest
  · intro t ht
    simp only [List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2, Option.some.injEq] at ht
    omega

private theorem tagGe_int32FieldX {T tag : ℕ} (v : BitVec 32) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (int32FieldX tag v ++ rest) := by
  unfold int32FieldX
  split_ifs
  · simpa using hrest
  · intro t ht
    simp only [List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2, Option.some.injEq] at ht
    omega

private theorem tagGe_optUint32FieldX {T tag : ℕ} (ov : Option (BitVec 32)) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (optUint32FieldX tag ov ++ rest) := by
  cases ov with
  | none => simpa [optUint32FieldX] using hrest
  | some _ =>
    intro t ht
    simp only [optUint32FieldX, List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2,
      Option.some.injEq] at ht
    omega

private theorem uint64FieldX_append_inj {tag : ℕ} {v₁ v₂ : BitVec 64} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : uint64FieldX tag v₁ ++ r₁ = uint64FieldX tag v₂ ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  unfold uint64FieldX at h
  by_cases hv₁ : v₁ = 0 <;> by_cases hv₂ : v₂ = 0
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exact ⟨hv₁.trans hv₂.symm, h⟩
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₁
    rw [h]
    simp [List.append_assoc, peekTag_encodeKey tag .varint _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₂
    rw [← h]
    simp [List.append_assoc, peekTag_encodeKey tag .varint _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte, List.append_assoc] at h
    exact encodeVarint_append_inj (encodeKey_append_inj h)

private theorem int32FieldX_append_inj {tag : ℕ} {v₁ v₂ : BitVec 32} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : int32FieldX tag v₁ ++ r₁ = int32FieldX tag v₂ ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  unfold int32FieldX at h
  by_cases hv₁ : v₁ = 0 <;> by_cases hv₂ : v₂ = 0
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exact ⟨hv₁.trans hv₂.symm, h⟩
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₁
    rw [h]
    simp [List.append_assoc, peekTag_encodeKey tag .varint _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₂
    rw [← h]
    simp [List.append_assoc, peekTag_encodeKey tag .varint _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte, List.append_assoc] at h
    obtain ⟨hw, hr⟩ := encodeVarint_append_inj (encodeKey_append_inj h)
    exact ⟨int32_signExtend64_inj hw, hr⟩

private theorem optUint32FieldX_append_inj {tag : ℕ} {ov₁ ov₂ : Option (BitVec 32)} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : optUint32FieldX tag ov₁ ++ r₁ = optUint32FieldX tag ov₂ ++ r₂) :
    ov₁ = ov₂ ∧ r₁ = r₂ := by
  cases ov₁ with
  | none =>
    cases ov₂ with
    | none => exact ⟨rfl, by simpa [optUint32FieldX] using h⟩
    | some _ =>
      simp only [optUint32FieldX, List.nil_append, List.append_assoc] at h
      exfalso
      apply hr₁
      rw [h]
      simp [peekTag_encodeKey tag .varint _ htag1 htag2]
  | some _ =>
    cases ov₂ with
    | none =>
      simp only [optUint32FieldX, List.nil_append, List.append_assoc] at h
      exfalso
      apply hr₂
      rw [← h]
      simp [peekTag_encodeKey tag .varint _ htag1 htag2]
    | some _ =>
      simp only [optUint32FieldX, List.append_assoc] at h
      obtain ⟨hw, hr⟩ := encodeVarint_append_inj (encodeKey_append_inj h)
      exact ⟨congrArg some (uint32_setWidth64_inj hw), hr⟩

private theorem peel_uint64FieldX {tag : ℕ} {v₁ v₂ : BitVec 64} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (uint64FieldX tag v₁ ++ r₁) (uint64FieldX tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  obtain ⟨hv, hr⟩ := uint64FieldX_append_inj htag1 htag2
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  rw [List.length_append] at hlen
  exact ⟨hv, hr, by omega⟩

private theorem peel_int32FieldX {tag : ℕ} {v₁ v₂ : BitVec 32} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (int32FieldX tag v₁ ++ r₁) (int32FieldX tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  obtain ⟨hv, hr⟩ := int32FieldX_append_inj htag1 htag2
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  rw [List.length_append] at hlen
  exact ⟨hv, hr, by omega⟩

private theorem peel_optUint32FieldX {tag : ℕ} {ov₁ ov₂ : Option (BitVec 32)} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (optUint32FieldX tag ov₁ ++ r₁) (optUint32FieldX tag ov₂ ++ r₂)) :
    ov₁ = ov₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  obtain ⟨hv, hr⟩ := optUint32FieldX_append_inj htag1 htag2
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  rw [List.length_append] at hlen
  exact ⟨hv, hr, by omega⟩

private theorem encPendingPreKeyX_inj (p₁ p₂ : PendingPreKey)
    (hlen : (encPendingPreKeyX p₁).length < 2 ^ 64)
    (h : encPendingPreKeyX p₁ = encPendingPreKeyX p₂) : p₁ = p₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encPendingPreKeyX, List.append_assoc] at hc0
  obtain ⟨hf1, hc1⟩ := peel_optUint32FieldX (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_int32FieldX _ _ (by omega) (by omega) (by omega)
        (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _))))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (tagGe_int32FieldX _ _ (by omega) (by omega) (by omega)
        (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))) hc0
  obtain ⟨hf2, hc2⟩ := peel_bytes (by omega) (by omega)
    (tagGe_int32FieldX _ _ (by omega) (by omega) (by omega)
      (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _)))
    (tagGe_int32FieldX _ _ (by omega) (by omega) (by omega)
      (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _))) hc1
  obtain ⟨hf3, hc3⟩ := peel_int32FieldX (by omega) (by omega)
    (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc2
  obtain ⟨hf4, _⟩ := peel_uint64FieldX (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc3
  cases p₁
  cases p₂
  cases hf1
  cases publicKey_serialize_inj hf2
  cases hf3
  cases hf4
  rfl

private theorem encPendingKyberX_inj (p₁ p₂ : PendingKyberPreKey)
    (hlen : (encPendingKyberX p₁).length < 2 ^ 64)
    (h : encPendingKyberX p₁ = encPendingKyberX p₂) : p₁ = p₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encPendingKyberX, List.append_assoc] at hc0
  obtain ⟨hf1, hc1⟩ := peel_uint32 (by omega) (by omega)
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _))
    (tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)) hc0
  obtain ⟨hf2, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc1
  cases p₁
  cases p₂
  cases hf1
  cases hf2
  rfl

/-! ## `Record.encSession` tag-peeling injectivity -/

private theorem sessionTail_tagGe (s : Session Bytes) :
    let st := s.state
    let t15 := bytesField 15 st.pqRatchetState ++ []
    let t14 := msgField 14 (s.pendingKyberPreKey.map encPendingKyberX) ++ t15
    let t13 := bytesField 13 s.aliceBaseKey ++ t14
    let t11 := uint32Field 11 s.localRegistrationId ++ t13
    let t10 := uint32Field 10 s.remoteRegistrationId ++ t11
    let t9 := msgField 9 (s.pendingPreKey.map encPendingPreKeyX) ++ t10
    let t7 := (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++ t9
    let t6 := msgField 6 (st.senderChain.map encSenderChain) ++ t7
    let t5 := uint32Field 5 st.previousCounter ++ t6
    let t4 := bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++ t5
    let t3 := bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++ t4
    let t2 := bytesField 2 st.localIdentity.serialize ++ t3
    TagGe 2 t2 ∧ TagGe 3 t3 ∧ TagGe 4 t4 ∧ TagGe 5 t5 ∧ TagGe 6 t6 ∧ TagGe 7 t7 ∧
      TagGe 8 t9 ∧ TagGe 10 t10 ∧ TagGe 11 t11 ∧ TagGe 12 t13 ∧ TagGe 14 t14 ∧ TagGe 15 t15 := by
  intro st t15 t14 t13 t11 t10 t9 t7 t6 t5 t4 t3 t2
  have h15 : TagGe 15 t15 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)
  have h14 : TagGe 14 t14 :=
    tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h15)
  have h12 : TagGe 12 t13 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h14)
  have h11 : TagGe 11 t11 :=
    tagGe_uint32Field _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h12)
  have h10 : TagGe 10 t10 :=
    tagGe_uint32Field _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h11)
  have h8 : TagGe 8 t9 :=
    tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h10)
  have h7 : TagGe 7 t7 :=
    tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h8)
  have h6 : TagGe 6 t6 :=
    tagGe_msgField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h7)
  have h5 : TagGe 5 t5 :=
    tagGe_uint32Field _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h6)
  have h4 : TagGe 4 t4 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h5)
  have h3 : TagGe 3 t3 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h4)
  have h2 : TagGe 2 t2 :=
    tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_mono (by omega) h3)
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h14, h15⟩

private theorem remoteIdentity_opt_inj {r₁ r₂ : Option IdentityKey}
    (h : (r₁.map IdentityKey.serialize).getD [] = (r₂.map IdentityKey.serialize).getD []) :
    r₁ = r₂ := by
  cases r₁ with
  | none =>
    cases r₂ with
    | none => rfl
    | some _ => simp [IdentityKey.serialize, PublicKey.serialize] at h
  | some _ =>
    cases r₂ with
    | none => simp [IdentityKey.serialize, PublicKey.serialize] at h
    | some _ =>
      simp only [Option.map_some, Option.getD_some] at h
      exact congrArg some (identityKey_serialize_inj h)

private theorem encSession_inj (s₁ s₂ : Session Bytes)
    (hwf₁ : s₁.Wf) (hwf₂ : s₂.Wf)
    (hlen : (Record.encSession s₁).length < 2 ^ 64)
    (h : Record.encSession s₁ = Record.encSession s₂) : s₁ = s₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [Record.encSession, record_uint32Field_eq, record_bytesField_eq, record_msgField_eq,
    record_lenField_eq, record_encSenderChain_eq, record_encReceiverChain_eq,
    record_encPendingPreKey_eq, record_encPendingKyber_eq, List.append_assoc] at hc0
  obtain ⟨g2, g3, g4, g5, g6, g7, g8, g10, g11, g12, g14, g15⟩ := sessionTail_tagGe s₁
  obtain ⟨g2', g3', g4', g5', g6', g7', g8', g10', g11', g12', g14', g15'⟩ := sessionTail_tagGe s₂
  obtain ⟨hf1, hc1⟩ := peel_uint32 (by omega) (by omega) g2 g2' hc0
  obtain ⟨hf2, hc2⟩ := peel_bytes (by omega) (by omega) g3 g3' hc1
  obtain ⟨hf3, hc3⟩ := peel_bytes (by omega) (by omega) g4 g4' hc2
  obtain ⟨hf4, hc4⟩ := peel_bytes (by omega) (by omega) g5 g5' hc3
  obtain ⟨hf5, hc5⟩ := peel_uint32 (by omega) (by omega) g6 g6' hc4
  obtain ⟨hf6, hc6⟩ := peel_msg encSenderChain (by omega) (by omega) encSenderChain_inj g7 g7' hc5
  obtain ⟨hf7, hc7⟩ := peel_repeated encReceiverChain (by omega) (by omega) encReceiverChain_inj
    g8 g8' hc6
  obtain ⟨hf9, hc9⟩ := peel_msg encPendingPreKeyX (by omega) (by omega) encPendingPreKeyX_inj
    g10 g10' hc7
  obtain ⟨hf10, hc10⟩ := peel_uint32 (by omega) (by omega) g11 g11' hc9
  obtain ⟨hf11, hc11⟩ := peel_uint32 (by omega) (by omega) g12 g12' hc10
  obtain ⟨hf13, hc13⟩ := peel_bytes (by omega) (by omega) g14 g14' hc11
  obtain ⟨hf14, hc14⟩ := peel_msg encPendingKyberX (by omega) (by omega) encPendingKyberX_inj
    g15 g15' hc13
  obtain ⟨hf15, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc14
  have hpendBool : s₁.state.pendingPreKey = s₂.state.pendingPreKey := by
    unfold Session.Wf at hwf₁ hwf₂
    rw [hwf₁, hwf₂, hf9]
  cases s₁ with
  | mk st₁ ppk₁ pkyb₁ lreg₁ rreg₁ abk₁ =>
  cases s₂ with
  | mk st₂ ppk₂ pkyb₂ lreg₂ rreg₂ abk₂ =>
  cases st₁
  cases st₂
  cases hf1
  cases identityKey_serialize_inj hf2
  cases remoteIdentity_opt_inj hf3
  cases keyToBytes32_inj hf4
  cases hf5
  cases hf6
  cases hf7
  cases hpendBool
  cases hf15
  cases hf9
  cases hf14
  cases hf11
  cases hf10
  cases hf13
  rfl

/-! ## `< 2^64` encoded-length bound on `DeserializeScopeP_Q NonEmptyV1Q` -/

private theorem pk_serialize_length (k : PublicKey) : k.serialize.length = 33 := by
  simp [PublicKey.serialize]

private theorem ik_serialize_length (k : IdentityKey) : k.serialize.length = 33 :=
  pk_serialize_length k.publicKey

private theorem encChainKey_length_le (ck : ChainKey) : (encChainKey ck).length ≤ 72 := by
  have h1 := RecordX.uint32Field_length_le' 1 ck.index
  have h2 := RecordX.bytesField_length_le' 2 (HMAC.keyToBytes32 ck.key)
  have hk : (HMAC.keyToBytes32 ck.key).length = 32 := by simp [HMAC.keyToBytes32]
  simp only [encChainKey, List.length_append]
  omega

private theorem encSenderChain_length_le (c : SenderChain) : (encSenderChain c).length ≤ 200 := by
  have h1 := RecordX.bytesField_length_le' 1 c.ratchetKey.publicKey.serialize
  have h1k := pk_serialize_length c.ratchetKey.publicKey
  have h2 := RecordX.bytesField_length_le' 2 c.ratchetKey.privateKey.bytes.toList
  have h2k : c.ratchetKey.privateKey.bytes.toList.length = 32 := c.ratchetKey.privateKey.bytes.2
  have h3 := RecordX.lenField_length_le' 3 (encChainKey c.chainKey)
  have h3c := encChainKey_length_le c.chainKey
  simp only [encSenderChain, msgField, List.length_append]
  omega

private theorem messageKeys_flatten_length_le :
    ∀ (ms : List MessageKeyGenerator),
      (∀ mk ∈ ms, mk.seed.length = 32) →
      ((ms.map fun mk => lenField 4 (encMessageKey mk)).flatten).length ≤ 100 * ms.length
  | [], _ => by simp
  | mk :: ms, hseeds => by
    have hmk : (lenField 4 (encMessageKey mk)).length ≤ 100 := by
      have h0 := RecordX.lenField_length_le' 4 (encMessageKey mk)
      have h1 := RecordX.uint32Field_length_le' 1 mk.counter
      have h2 := RecordX.bytesField_length_le' 5 mk.seed
      have hs := hseeds mk List.mem_cons_self
      simp only [encMessageKey, List.length_append] at h0 ⊢
      omega
    have htail := messageKeys_flatten_length_le ms (fun m hm => hseeds m (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

private theorem receiverChains_flatten_length_le :
    ∀ (cs : List ReceiverChain),
      (∀ c ∈ cs, c.messageKeys.length ≤ maxMessageKeys) →
      (∀ c ∈ cs, ∀ mk ∈ c.messageKeys, mk.seed.length = 32) →
      ((cs.map fun c => lenField 7 (encReceiverChain c)).flatten).length ≤ 200200 * cs.length
  | [], _, _ => by simp
  | c :: cs, hmax, hseeds => by
    have hc : (lenField 7 (encReceiverChain c)).length ≤ 200200 := by
      have h0 := RecordX.lenField_length_le' 7 (encReceiverChain c)
      have h1 := RecordX.bytesField_length_le' 1 c.senderRatchetKey.serialize
      have h1k := pk_serialize_length c.senderRatchetKey
      have h2 : (msgField 3 (c.chainKey.map encChainKey)).length ≤ 100 := by
        cases c.chainKey with
        | none => simp [msgField]
        | some ck =>
          have h2a := RecordX.lenField_length_le' 3 (encChainKey ck)
          have h2b := encChainKey_length_le ck
          simp only [Option.map_some, msgField]
          omega
      have h3 := messageKeys_flatten_length_le c.messageKeys (hseeds c List.mem_cons_self)
      have hm : c.messageKeys.length ≤ 2000 := hmax c List.mem_cons_self
      have hrc_eq : (encReceiverChain c).length =
          (bytesField 1 c.senderRatchetKey.serialize).length +
          (msgField 3 (c.chainKey.map encChainKey)).length +
          ((c.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length := by
        simp only [encReceiverChain, List.length_append]
      omega
    have htail := receiverChains_flatten_length_le cs
      (fun d hd => hmax d (List.mem_cons_of_mem _ hd))
      (fun d hd => hseeds d (List.mem_cons_of_mem _ hd))
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

private theorem encSession_length_lt_64 {s : Session Bytes}
    (h : Symbolic.Swarm.TRREF.B3Defs.InScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q ⟨some s⟩) :
    (Record.encSession s).length < 2 ^ 64 := by
  obtain ⟨hin, hpq, hrep⟩ := h
  obtain ⟨hseeds, hrc_lt, hkyb_lt⟩ := hin s rfl
  have hpq_lt : s.state.pqRatchetState.length < 2 ^ 32 := hpq s rfl
  obtain ⟨hmk_le, _, _, habk_lt⟩ := hrep s rfl
  have h1 := RecordX.uint32Field_length_le' 1 s.state.sessionVersion
  have h2 := RecordX.bytesField_length_le' 2 s.state.localIdentity.serialize
  have h2k := ik_serialize_length s.state.localIdentity
  have h3 : (bytesField 3 ((s.state.remoteIdentity.map IdentityKey.serialize).getD [])).length ≤
      53 := by
    cases s.state.remoteIdentity with
    | none => simp [bytesField]
    | some ik =>
      have ha := RecordX.bytesField_length_le' 3 ik.serialize
      have hb := ik_serialize_length ik
      simp only [Option.map_some, Option.getD_some]
      omega
  have h4 := RecordX.bytesField_length_le' 4 (HMAC.keyToBytes32 s.state.rootKey)
  have h4k : (HMAC.keyToBytes32 s.state.rootKey).length = 32 := by simp [HMAC.keyToBytes32]
  have h5 := RecordX.uint32Field_length_le' 5 s.state.previousCounter
  have h6 : (msgField 6 (s.state.senderChain.map encSenderChain)).length ≤ 220 := by
    cases s.state.senderChain with
    | none => simp [msgField]
    | some sc =>
      have ha := RecordX.lenField_length_le' 6 (encSenderChain sc)
      have hb := encSenderChain_length_le sc
      simp only [Option.map_some, msgField]
      omega
  have h7 := receiverChains_flatten_length_le s.state.receiverChains hmk_le hseeds
  have h9 : (msgField 9 (s.pendingPreKey.map encPendingPreKeyX)).length ≤ 133 := by
    cases s.pendingPreKey with
    | none => simp [msgField]
    | some p =>
      have ha := RecordX.lenField_length_le' 9 (encPendingPreKeyX p)
      have hb1 := RecordX.optUint32FieldX_length_le 1 p.preKeyId
      have hb2 := RecordX.bytesField_length_le' 2 p.baseKey.serialize
      have hb2k := pk_serialize_length p.baseKey
      have hb3 := RecordX.int32FieldX_length_le 3 p.signedPreKeyId
      have hb4 := RecordX.uint64FieldX_length_le 4 p.timestamp
      simp only [Option.map_some, msgField, encPendingPreKeyX, List.length_append] at ha ⊢
      omega
  have h10 := RecordX.uint32Field_length_le' 10 s.remoteRegistrationId
  have h11 := RecordX.uint32Field_length_le' 11 s.localRegistrationId
  have h13 := RecordX.bytesField_length_le' 13 s.aliceBaseKey
  have h14 : (msgField 14 (s.pendingKyberPreKey.map encPendingKyberX)).length < 2 ^ 32 + 60 := by
    cases hkp : s.pendingKyberPreKey with
    | none => simp [msgField]
    | some k =>
      have ha := RecordX.lenField_length_le' 14 (encPendingKyberX k)
      have hb1 := RecordX.uint32Field_length_le' 1 k.preKeyId
      have hb2 := RecordX.bytesField_length_le' 2 k.ciphertext
      have hkc := hkyb_lt k hkp
      simp only [Option.map_some, msgField, encPendingKyberX, List.length_append] at ha ⊢
      omega
  have h15 := RecordX.bytesField_length_le' 15 s.state.pqRatchetState
  simp only [Record.encSession, record_uint32Field_eq, record_bytesField_eq, record_msgField_eq,
    record_lenField_eq, record_encSenderChain_eq, record_encReceiverChain_eq,
    record_encPendingPreKey_eq, record_encPendingKyber_eq, List.length_append]
  omega

/-- `SessionRecord::serialize` (`E2E.Record.encodeRecord`) is injective on `DeserializeScopeP_Q NonEmptyV1Q`. -/
theorem encodeInjOn_deserializeScopeP_Q :
    EncodeInjOn (Symbolic.Swarm.TRREF.B3Defs.DeserializeScopeP_Q Symbolic.Swarm.TRREF.B3Defs.NonEmptyV1Q) := by
  intro r₁ r₂ h₁ h₂ henc
  obtain ⟨hin₁, s₁, hs₁, _⟩ := h₁
  obtain ⟨hin₂, s₂, hs₂, _⟩ := h₂
  cases r₁ with | mk cur₁ =>
  cases r₂ with | mk cur₂ =>
  simp only at hs₁ hs₂
  subst hs₁ hs₂
  have hlen₁ : (Record.encSession s₁).length < 2 ^ 64 := encSession_length_lt_64 hin₁
  have hlen₂ : (Record.encSession s₂).length < 2 ^ 64 := encSession_length_lt_64 hin₂
  have hwf₁ : s₁.Wf := (hin₁.2.2 s₁ rfl).2.2.1
  have hwf₂ : s₂.Wf := (hin₂.2.2 s₂ rfl).2.2.1
  have hrec : lenField 1 (Record.encSession s₁) ++ [] =
      lenField 1 (Record.encSession s₂) ++ [] := by
    simpa [Record.encodeRecord, Record.msgField, record_lenField_eq] using henc
  have hsess : s₁ = s₂ :=
    encSession_inj s₁ s₂ hwf₁ hwf₂ hlen₁ (lenField_append_inj hlen₁ hlen₂ hrec).1
  exact congrArg (fun s => SessionRecord.mk (some s)) hsess

end CryptoVerification.SignalSession.Cli.Slots
