/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.SpecLemmas.CliPureBytes
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.Refinement.RecordBytesBridge

@[expose] public section

set_option autoImplicit false

/-!
# Top-Level Protobuf Field Injectivity for `encodeRecord` and `encSession`

Proves that `encodeRecord ⟨some s⟩` and `encSession s` uniquely determine `s.state.pqRatchetState`
(as well as `encSession s` from `encodeRecord ⟨some s⟩`) whenever the encoded byte length is
`< 2 ^ 64`, without requiring `pendingPreKey = none` or `pendingKyberPreKey = none`.
-/

namespace Symbolic.Swarm.TRREF.EncodeRecordPqInj

open CryptoGames.LibsignalSessionApi
open CryptoGames.LibsignalSession
open CryptoVerification.E2E.Record
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (PbValue encodeField paddedVarint readVarint readVarint_paddedVarint)
open DY.Libsignal.Composed.Refinement
  (pbFields PbOk u32Field)
open Swarm.Phase0WholeFunctionBridge
  (u32Field_eq_uint32Field msgField_eq_lenField bytesField_eq_record_bytesField)

private theorem readVarint_encodeField_varint (tag : Nat) (n : Nat) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.varint n) ++ rest) =
      some (tag * 8, paddedVarint n 0 ++ rest) := by
  rw [encodeField, List.append_assoc, readVarint_paddedVarint]

private theorem readVarint_encodeField_bytes (tag : Nat) (b : List (BitVec 8)) (rest : List (BitVec 8)) :
    readVarint (encodeField tag 0 0 (.bytes b) ++ rest) =
      some (tag * 8 + 2, paddedVarint b.length 0 ++ (b ++ rest)) := by
  rw [encodeField, List.append_assoc, List.append_assoc, readVarint_paddedVarint]

private theorem pbFields_inj {l₁ l₂ : List (Nat × PbValue)}
    (h₁ : ∀ x ∈ l₁, PbOk x) (h₂ : ∀ x ∈ l₂, PbOk x)
    (h : pbFields l₁ = pbFields l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons p₂ rest₂ =>
      obtain ⟨t₂, v₂⟩ := p₂
      have hok := h₂ (t₂, v₂) (by simp)
      cases v₂ with
      | varint n₂ =>
        have hread := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
        have hnil : pbFields [] = [] := rfl
        have hcons : pbFields ((t₂, .varint n₂) :: rest₂) =
            encodeField t₂ 0 0 (.varint n₂) ++ pbFields rest₂ := rfl
        rw [hnil, hcons] at h
        rw [← h] at hread
        nomatch hread
      | bytes b₂ =>
        have hread := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
        have hnil : pbFields [] = [] := rfl
        have hcons : pbFields ((t₂, .bytes b₂) :: rest₂) =
            encodeField t₂ 0 0 (.bytes b₂) ++ pbFields rest₂ := rfl
        rw [hnil, hcons] at h
        rw [← h] at hread
        nomatch hread
      | unknown _ _ => contradiction
  | cons p₁ rest₁ ih =>
    cases l₂ with
    | nil =>
      obtain ⟨t₁, v₁⟩ := p₁
      have hok := h₁ (t₁, v₁) (by simp)
      cases v₁ with
      | varint n₁ =>
        have hread := readVarint_encodeField_varint t₁ n₁ (pbFields rest₁)
        have hnil : pbFields [] = [] := rfl
        have hcons : pbFields ((t₁, .varint n₁) :: rest₁) =
            encodeField t₁ 0 0 (.varint n₁) ++ pbFields rest₁ := rfl
        rw [hnil, hcons] at h
        rw [h] at hread
        nomatch hread
      | bytes b₁ =>
        have hread := readVarint_encodeField_bytes t₁ b₁ (pbFields rest₁)
        have hnil : pbFields [] = [] := rfl
        have hcons : pbFields ((t₁, .bytes b₁) :: rest₁) =
            encodeField t₁ 0 0 (.bytes b₁) ++ pbFields rest₁ := rfl
        rw [hnil, hcons] at h
        rw [h] at hread
        nomatch hread
      | unknown _ _ => contradiction
    | cons p₂ rest₂ =>
      obtain ⟨t₁, v₁⟩ := p₁
      obtain ⟨t₂, v₂⟩ := p₂
      have hok₁ := h₁ (t₁, v₁) (by simp)
      have hok₂ := h₂ (t₂, v₂) (by simp)
      have hcons₁ : pbFields ((t₁, v₁) :: rest₁) = encodeField t₁ 0 0 v₁ ++ pbFields rest₁ := rfl
      have hcons₂ : pbFields ((t₂, v₂) :: rest₂) = encodeField t₂ 0 0 v₂ ++ pbFields rest₂ := rfl
      rw [hcons₁, hcons₂] at h
      cases v₁ with
      | unknown _ _ => contradiction
      | varint n₁ =>
        have hr₁ := readVarint_encodeField_varint t₁ n₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => contradiction
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁
          rw [hr₁] at hr₂
          injection hr₂ with hp
          injection hp with hk
          exfalso; omega
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁
          rw [hr₁] at hr₂
          injection hr₂ with hp
          injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint n₁ (pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint n₂ (pbFields rest₂)
          rw [hrest'] at hrp₁
          rw [hrp₁] at hrp₂
          injection hrp₂ with hp'
          injection hp' with hn hr
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx))
                              hr
          subst t₁; subst n₁; subst rest₁
          rfl
      | bytes b₁ =>
        have hr₁ := readVarint_encodeField_bytes t₁ b₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => contradiction
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁
          rw [hr₁] at hr₂
          injection hr₂ with hp
          injection hp with hk
          exfalso; omega
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁
          rw [hr₁] at hr₂
          injection hr₂ with hp
          injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint b₁.length (b₁ ++ pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint b₂.length (b₂ ++ pbFields rest₂)
          rw [hrest'] at hrp₁
          rw [hrp₁] at hrp₂
          injection hrp₂ with hp'
          injection hp' with hlen happ
          obtain ⟨hb, hr⟩ := List.append_inj happ hlen
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx))
                              hr
          subst t₁; subst b₁; subst rest₁
          rfl

private theorem filter_eq_self_of_tag {tag : Nat} {l : List (Nat × PbValue)}
    (h : ∀ x ∈ l, x.1 = tag) :
    l.filter (fun p => p.1 == tag) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.1 = tag := h x (by simp)
    have hbeq : (x.1 == tag) = true := by simp [hx]
    simp only [List.filter_cons, hbeq, ↓reduceIte]
    congr 1
    exact ih (fun y hy => h y (by simp [hy]))

private theorem filter_eq_nil_of_tag_ne {tag t : Nat} (hne : tag ≠ t) {l : List (Nat × PbValue)}
    (h : ∀ x ∈ l, x.1 = tag) :
    l.filter (fun p => p.1 == t) = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x.1 = tag := h x (by simp)
    have hbeq : (x.1 == t) = false := by simp [hx, hne]
    simp only [List.filter_cons, hbeq]
    exact ih (fun y hy => h y (by simp [hy]))

private theorem pbFields_append (l₁ l₂ : List (Nat × PbValue)) :
    pbFields (l₁ ++ l₂) = pbFields l₁ ++ pbFields l₂ := by
  simp only [pbFields, List.flatMap_append]

private def bytesFieldList (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private def u32FieldList (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

private def optMsgFieldList (tag : Nat) : Option HwBytes → List (Nat × PbValue)
  | none => []
  | some b => [(tag, .bytes b)]

private theorem bytesFieldList_inj {tag₁ tag₂ : Nat} {b₁ b₂ : HwBytes}
    (h : bytesFieldList tag₁ b₁ = bytesFieldList tag₂ b₂) : b₁ = b₂ := by
  unfold bytesFieldList at h
  by_cases h₁ : b₁ = [] <;> by_cases h₂ : b₂ = []
  · rw [h₁, h₂]
  · simp [h₁, h₂] at h
  · simp [h₁, h₂] at h
  · simp only [h₁, h₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq, PbValue.bytes.injEq, and_true] at h
    exact h.2

private theorem pbOk_bytesFieldList (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList tag b, PbOk x := by
  intro x hx
  unfold bytesFieldList at hx
  split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx
    exact trivial

private theorem pbOk_u32FieldList (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList tag v, PbOk x := by
  intro x hx
  unfold u32FieldList at hx
  split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx
    exact trivial

private theorem pbOk_optMsgFieldList (tag : Nat) (opt : Option HwBytes) :
    ∀ x ∈ optMsgFieldList tag opt, PbOk x := by
  intro x hx
  cases opt with
  | none => cases hx
  | some b =>
    simp only [optMsgFieldList, List.mem_singleton] at hx
    subst hx
    exact trivial

private theorem tag_bytesFieldList (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList tag b, x.1 = tag := by
  intro x hx
  unfold bytesFieldList at hx
  split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx
    rfl

private theorem tag_u32FieldList (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList tag v, x.1 = tag := by
  intro x hx
  unfold u32FieldList at hx
  split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx
    rfl

private theorem tag_optMsgFieldList (tag : Nat) (opt : Option HwBytes) :
    ∀ x ∈ optMsgFieldList tag opt, x.1 = tag := by
  intro x hx
  cases opt with
  | none => cases hx
  | some b =>
    simp only [optMsgFieldList, List.mem_singleton] at hx
    subst hx
    rfl

private theorem lenField_payload_length_le (tag : Nat) (b : HwBytes) :
    b.length ≤ (CryptoVerification.E2E.Record.lenField tag b).length := by
  unfold CryptoVerification.E2E.Record.lenField
  simp only [List.length_append]
  omega

private theorem pbFields_u32FieldList_eq_uint32Field (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    pbFields (u32FieldList tag v) = CryptoVerification.E2E.Record.uint32Field tag v := by
  have h1 : pbFields (u32FieldList tag v) = u32Field tag v := by
    unfold u32FieldList u32Field
    split <;> simp [pbFields]
  rw [h1, u32Field_eq_uint32Field tag v htag]

private theorem pbFields_bytesFieldList_eq_record_bytesField (tag : Nat) (b : HwBytes)
    (hlen : (CryptoVerification.E2E.Record.bytesField tag b).length < 2 ^ 64)
    (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    pbFields (bytesFieldList tag b) = CryptoVerification.E2E.Record.bytesField tag b := by
  have h1 : pbFields (bytesFieldList tag b) =
      DY.Libsignal.Composed.Refinement.bytesField tag b := by
    unfold bytesFieldList DY.Libsignal.Composed.Refinement.bytesField
    split <;> simp [pbFields]
  rw [h1]
  unfold DY.Libsignal.Composed.Refinement.bytesField CryptoVerification.E2E.Record.bytesField
  split_ifs with hb
  · rfl
  · unfold CryptoVerification.E2E.Record.bytesField at hlen
    simp only [hb, ↓reduceIte] at hlen
    have hblen : b.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (lenField_payload_length_le tag b) hlen
    exact msgField_eq_lenField tag b hblen htag

private theorem pbFields_optMsgFieldList_eq_record_msgField (tag : Nat) (opt : Option HwBytes)
    (hlen : (CryptoVerification.E2E.Record.msgField tag opt).length < 2 ^ 64)
    (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    pbFields (optMsgFieldList tag opt) = CryptoVerification.E2E.Record.msgField tag opt := by
  cases opt with
  | none => rfl
  | some b =>
    dsimp only [optMsgFieldList, CryptoVerification.E2E.Record.msgField] at hlen ⊢
    have hblen : b.length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (lenField_payload_length_le tag b) hlen
    have h1 : pbFields [(tag, .bytes b)] =
        DY.Libsignal.Composed.Refinement.msgField tag b := by
      simp [pbFields, DY.Libsignal.Composed.Refinement.msgField]
    rw [h1, msgField_eq_lenField tag b hblen htag]

private theorem pbFields_receiverChains_eq (cs : List ReceiverChain)
    (hlen : ((cs.map fun c =>
      CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)).flatten).length < 2 ^ 64) :
    pbFields (cs.map fun c => (7, PbValue.bytes (encReceiverChain c))) =
      (cs.map fun c => CryptoVerification.E2E.Record.lenField 7 (encReceiverChain c)).flatten := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append] at hlen ⊢
    have hc_len : (encReceiverChain c).length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (lenField_payload_length_le 7 (encReceiverChain c)) (by omega)
    have hcons : pbFields ((7, PbValue.bytes (encReceiverChain c)) ::
        rest.map fun c => (7, PbValue.bytes (encReceiverChain c))) =
        DY.Libsignal.Composed.Refinement.msgField 7 (encReceiverChain c) ++
          pbFields (rest.map fun c => (7, PbValue.bytes (encReceiverChain c))) := rfl
    rw [hcons, msgField_eq_lenField 7 (encReceiverChain c) hc_len, ih (by omega)]

private def topSessionFields (s : Session HwBytes) : List (Nat × PbValue) :=
  let st := s.state
  u32FieldList 1 st.sessionVersion ++
  bytesFieldList 2 st.localIdentity.serialize ++
  bytesFieldList 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesFieldList 4 (CryptoGames.HMAC.keyToBytes32 st.rootKey) ++
  u32FieldList 5 st.previousCounter ++
  optMsgFieldList 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => (7, PbValue.bytes (encReceiverChain c))) ++
  optMsgFieldList 9 (s.pendingPreKey.map encPendingPreKey) ++
  u32FieldList 10 s.remoteRegistrationId ++
  u32FieldList 11 s.localRegistrationId ++
  bytesFieldList 13 s.aliceBaseKey ++
  optMsgFieldList 14 (s.pendingKyberPreKey.map encPendingKyber) ++
  bytesFieldList 15 st.pqRatchetState

private theorem pbOk_topSessionFields (s : Session HwBytes) :
    ∀ x ∈ topSessionFields s, PbOk x := by
  intro x hx
  unfold topSessionFields at hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ((((((((((((h1 | h2) | h3) | h4) | h5) | h6) | ⟨c, _, rfl⟩) | h9) | h10) | h11) | h13) | h14) | h15)
  · exact pbOk_u32FieldList _ _ x h1
  · exact pbOk_bytesFieldList _ _ x h2
  · exact pbOk_bytesFieldList _ _ x h3
  · exact pbOk_bytesFieldList _ _ x h4
  · exact pbOk_u32FieldList _ _ x h5
  · exact pbOk_optMsgFieldList _ _ x h6
  · exact trivial
  · exact pbOk_optMsgFieldList _ _ x h9
  · exact pbOk_u32FieldList _ _ x h10
  · exact pbOk_u32FieldList _ _ x h11
  · exact pbOk_bytesFieldList _ _ x h13
  · exact pbOk_optMsgFieldList _ _ x h14
  · exact pbOk_bytesFieldList _ _ x h15

private theorem pbFields_topSessionFields_eq_encSession (s : Session HwBytes)
    (hlen : (encSession s).length < 2 ^ 64) :
    pbFields (topSessionFields s) = encSession s := by
  unfold topSessionFields encSession
  unfold encSession at hlen
  simp only [List.length_append] at hlen
  simp only [pbFields_append]
  rw [pbFields_u32FieldList_eq_uint32Field 1,
      pbFields_bytesFieldList_eq_record_bytesField 2 _ (by omega),
      pbFields_bytesFieldList_eq_record_bytesField 3 _ (by omega),
      pbFields_bytesFieldList_eq_record_bytesField 4 _ (by omega),
      pbFields_u32FieldList_eq_uint32Field 5,
      pbFields_optMsgFieldList_eq_record_msgField 6 _ (by omega),
      pbFields_receiverChains_eq _ (by omega),
      pbFields_optMsgFieldList_eq_record_msgField 9 _ (by omega),
      pbFields_u32FieldList_eq_uint32Field 10,
      pbFields_u32FieldList_eq_uint32Field 11,
      pbFields_bytesFieldList_eq_record_bytesField 13 _ (by omega),
      pbFields_optMsgFieldList_eq_record_msgField 14 _ (by omega),
      pbFields_bytesFieldList_eq_record_bytesField 15 _ (by omega)]

private theorem filter_15_topSessionFields (s : Session HwBytes) :
    (topSessionFields s).filter (fun p => p.1 == 15) =
      bytesFieldList 15 s.state.pqRatchetState := by
  have hrc : ∀ x ∈ (s.state.receiverChains.map fun c => (7, PbValue.bytes (encReceiverChain c))),
      x.1 = 7 := by
    intro x hx
    simp only [List.mem_map] at hx
    rcases hx with ⟨_, _, rfl⟩
    rfl
  unfold topSessionFields
  simp only [List.filter_append,
    filter_eq_nil_of_tag_ne (by decide : 1 ≠ 15) (tag_u32FieldList 1 _),
    filter_eq_nil_of_tag_ne (by decide : 2 ≠ 15) (tag_bytesFieldList 2 _),
    filter_eq_nil_of_tag_ne (by decide : 3 ≠ 15) (tag_bytesFieldList 3 _),
    filter_eq_nil_of_tag_ne (by decide : 4 ≠ 15) (tag_bytesFieldList 4 _),
    filter_eq_nil_of_tag_ne (by decide : 5 ≠ 15) (tag_u32FieldList 5 _),
    filter_eq_nil_of_tag_ne (by decide : 6 ≠ 15) (tag_optMsgFieldList 6 _),
    filter_eq_nil_of_tag_ne (by decide : 7 ≠ 15) hrc,
    filter_eq_nil_of_tag_ne (by decide : 9 ≠ 15) (tag_optMsgFieldList 9 _),
    filter_eq_nil_of_tag_ne (by decide : 10 ≠ 15) (tag_u32FieldList 10 _),
    filter_eq_nil_of_tag_ne (by decide : 11 ≠ 15) (tag_u32FieldList 11 _),
    filter_eq_nil_of_tag_ne (by decide : 13 ≠ 15) (tag_bytesFieldList 13 _),
    filter_eq_nil_of_tag_ne (by decide : 14 ≠ 15) (tag_optMsgFieldList 14 _),
    filter_eq_self_of_tag (tag_bytesFieldList 15 _),
    List.nil_append]

/-- `encSession` is injective on `state.pqRatchetState` whenever the encoded byte length is
`< 2 ^ 64` (even when `pendingPreKey` or `pendingKyberPreKey` are `some`). -/
theorem encSession_pqRatchetState_inj
    {s₁ s₂ : Session (List (BitVec 8))}
    (hlen : (encSession s₁).length < 2 ^ 64)
    (heq : encSession s₁ = encSession s₂) :
    s₁.state.pqRatchetState = s₂.state.pqRatchetState := by
  have hlen₂ : (encSession s₂).length < 2 ^ 64 := heq ▸ hlen
  have hpb : pbFields (topSessionFields s₁) = pbFields (topSessionFields s₂) := by
    rw [pbFields_topSessionFields_eq_encSession s₁ hlen,
        pbFields_topSessionFields_eq_encSession s₂ hlen₂, heq]
  have hfields := pbFields_inj (pbOk_topSessionFields s₁) (pbOk_topSessionFields s₂) hpb
  have hfilt := congrArg (List.filter (fun p => p.1 == 15)) hfields
  rw [filter_15_topSessionFields s₁, filter_15_topSessionFields s₂] at hfilt
  exact bytesFieldList_inj hfilt

/-- `encodeRecord ⟨some s⟩` is injective on `encSession s` whenever `(encodeRecord ⟨some s₁⟩).length < 2 ^ 64`. -/
theorem encodeRecord_encSession_inj
    {s₁ s₂ : Session (List (BitVec 8))}
    (hlen : (encodeRecord ⟨some s₁⟩).length < 2 ^ 64)
    (heq : encodeRecord ⟨some s₁⟩ = encodeRecord ⟨some s₂⟩) :
    encSession s₁ = encSession s₂ := by
  have hlen₂ : (encodeRecord ⟨some s₂⟩).length < 2 ^ 64 := heq ▸ hlen
  have hpb₁ : pbFields (optMsgFieldList 1 (some (encSession s₁))) = encodeRecord ⟨some s₁⟩ :=
    pbFields_optMsgFieldList_eq_record_msgField 1 (some (encSession s₁)) hlen
  have hpb₂ : pbFields (optMsgFieldList 1 (some (encSession s₂))) = encodeRecord ⟨some s₂⟩ :=
    pbFields_optMsgFieldList_eq_record_msgField 1 (some (encSession s₂)) hlen₂
  have hpb : pbFields (optMsgFieldList 1 (some (encSession s₁))) =
      pbFields (optMsgFieldList 1 (some (encSession s₂))) := by
    rw [hpb₁, hpb₂, heq]
  have hfields := pbFields_inj
    (pbOk_optMsgFieldList 1 (some (encSession s₁)))
    (pbOk_optMsgFieldList 1 (some (encSession s₂))) hpb
  simp only [optMsgFieldList, List.cons.injEq, Prod.mk.injEq, PbValue.bytes.injEq,
    true_and, and_true] at hfields
  exact hfields

/-- `encodeRecord ⟨some s⟩` uniquely determines `s.state.pqRatchetState` whenever
`(encodeRecord ⟨some s₁⟩).length < 2 ^ 64`. -/
theorem encodeRecord_pq_inj
    {s₁ s₂ : Session (List (BitVec 8))}
    (hlen : (encodeRecord ⟨some s₁⟩).length < 2 ^ 64)
    (heq : encodeRecord ⟨some s₁⟩ = encodeRecord ⟨some s₂⟩) :
    s₁.state.pqRatchetState = s₂.state.pqRatchetState := by
  have hsess_len : (encSession s₁).length < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (lenField_payload_length_le 1 (encSession s₁)) hlen
  exact encSession_pqRatchetState_inj hsess_len (encodeRecord_encSession_inj hlen heq)

/-- `< 2 ^ 62` specialization of `encodeRecord_pq_inj`, matching `WireRecCanon`'s record byte-length bound. -/
theorem encodeRecord_pq_inj_of_lt_2_62
    {s₁ s₂ : Session (List (BitVec 8))}
    (hlen : (encodeRecord ⟨some s₁⟩).length < 2 ^ 62)
    (heq : encodeRecord ⟨some s₁⟩ = encodeRecord ⟨some s₂⟩) :
    s₁.state.pqRatchetState = s₂.state.pqRatchetState :=
  encodeRecord_pq_inj (by omega) heq

/-- Equality of two `< 2 ^ 62`-byte `encodeRecord ⟨some ·⟩` encodings implies equal
`pqRatchetState`. -/
theorem encodeRecord_pq_inj_of_eq
    {bs : List (BitVec 8)}
    {s₁ s₂ : Session (List (BitVec 8))}
    (h₁ : bs = encodeRecord ⟨some s₁⟩)
    (h₂ : bs = encodeRecord ⟨some s₂⟩)
    (hlen : bs.length < 2 ^ 62) :
    s₁.state.pqRatchetState = s₂.state.pqRatchetState := by
  have hlen₁ : (encodeRecord ⟨some s₁⟩).length < 2 ^ 62 := h₁ ▸ hlen
  exact encodeRecord_pq_inj_of_lt_2_62 hlen₁ (h₁.symm.trans h₂)

end Symbolic.Swarm.TRREF.EncodeRecordPqInj
