/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
public import LibsignalBinary.Proofs.SignalSession.NonVacuityPq
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Refinement.LemmasPure

/-!
# SPQR-V1 Model-Initiated Session Record

Constructs `chevalSessionBytes` from the SPQR-V1 `initiateState` model and `encodeRecordUnderExtras`,
proves its non-emptiness and `< 2^31` length bound, and shows via top-level protobuf field injectivity
(`pbFields`) that any `RecordRec` encoding to `chevalSessionBytes` has `aliceBaseKey` starting with
`[0x05#8, 0x01#8]` without kernel-reducing `spqrV1Init`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Refinement.Cli.Cheval26

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E CryptoVerification.SignalSession
open CryptoVerification.SignalSession.NonVacuityPq
  (W0 b0 t0 X0 initiateState_W0_isSome pqInitModel_W0_creates_wfSession)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (PbValue encodeField paddedVarint readVarint readVarint_paddedVarint)
open DY.Libsignal.TripleRatchet.Refinement (pbFields PbOk)

/-! ## `chevalSessionBytes` and Length Bounds -/

/-- Session file bytes produced by running `initiateState` (SPQR V1 active) and `encodeRecordUnderExtras`. -/
def chevalSessionBytes : List (BitVec 8) :=
  match initiateState X0 W0 .A emptyParty.me b0 t0 with
  | some (x, g) => encodeRecordUnderExtras (fun _ => x) g
  | none => []

theorem chevalSessionBytes_ne_nil : chevalSessionBytes ≠ [] := by
  have hSome := initiateState_W0_isSome
  unfold chevalSessionBytes
  cases hInit : initiateState X0 W0 .A emptyParty.me b0 t0 with
  | none => simp [hInit] at hSome
  | some xg =>
    rcases xg with ⟨x, g⟩
    have htag : CryptoVerification.LibsignalProtoCodec.encodeKey 1 .lengthDelimited = [0x0a#8] := by
      decide
    dsimp only [encodeRecordUnderExtras, msgField, lenField]
    rw [htag]
    simp

theorem chevalSessionBytes_lt : chevalSessionBytes.length < 2 ^ 31 := by
  obtain ⟨st1, x, g, hpm, hs, hwf⟩ := pqInitModel_W0_creates_wfSession X0
  have hparty : emptyParty.party = .A := rfl
  have htrusts : emptyParty.trusts ⟨⟨b0.idPub⟩⟩ = true := rfl
  simp only [pqInitModel, htrusts, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hparty] at hpm
  unfold chevalSessionBytes
  cases hInit : initiateState X0 W0 .A emptyParty.me b0 t0 with
  | none => simp [hInit] at hpm
  | some xg =>
    rcases xg with ⟨x', g'⟩
    simp only [hInit, Option.some.injEq, Prod.mk.injEq] at hpm
    obtain ⟨hst1, _⟩ := hpm
    rw [← hst1] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact (hwf.1 x' g' (by rw [← hst1])).2.2

private theorem initiateState_aliceBaseKey {x : RecordExtras} {g : GhostState Bytes}
    (h : initiateState X0 W0 .A emptyParty.me b0 t0 = some (x, g)) :
    x.aliceBaseKey.take 2 = [0x05#8, 0x01#8] := by
  unfold initiateState at h
  have hkeys : (match SignalPqxdh.Model.initiateKeys (modelPrims X0 W0)
      (initiateInput W0 emptyParty.me b0 t0) with
    | none => false
    | some (_, hdr) =>
      ((initiatorRecordExtras emptyParty.me b0 ⟨u8Vec 32 hdr.ekAPk⟩
          (u8Vec 1568 hdr.kemCt)).aliceBaseKey.take 2 == [0x05#8, 0x01#8])) = true := by
    decide +kernel
  cases hk : SignalPqxdh.Model.initiateKeys (modelPrims X0 W0)
      (initiateInput W0 emptyParty.me b0 t0) with
  | none => simp [hk] at h
  | some p =>
    rcases p with ⟨dk, hdr⟩
    simp only [hk] at h hkeys
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact eq_of_beq hkeys

/-! ## Top-Level Protobuf Field Injectivity -/

private theorem paddedVarint_zero_of_lt_128 {n : Nat} (h : n < 128) :
    paddedVarint n 0 = [BitVec.ofNat 8 n] := by
  rw [paddedVarint]; simp [h]

private theorem paddedVarint_zero_of_ge_128 {n : Nat} (h : 128 ≤ n) :
    paddedVarint n 0 = BitVec.ofNat 8 (n % 128 + 128) :: paddedVarint (n / 128) 0 := by
  rw [paddedVarint]; have hnot : ¬(n < 128) := by omega
  simp [hnot]

private theorem varint_cont_byte_eq (v : BitVec 64) :
    ((v &&& 0x7F) ||| 0x80).setWidth 8 = (v &&& 127#64).setWidth 8 + 128#8 := by
  have h1 : ((v &&& 0x7F) ||| 0x80).setWidth 8 = (v.setWidth 8 &&& 127#8) ||| 128#8 := by
    ext i hi; simp
  have h2 : (v &&& 127#64).setWidth 8 = v.setWidth 8 &&& 127#8 := by
    ext i hi; simp
  rw [h1, h2]
  generalize v.setWidth 8 = b
  revert b
  decide

private theorem paddedVarint_zero_eq_encodeVarintAux :
    ∀ (k : Nat) (n : Nat),
      k ≠ 0 → n < 2 ^ (7 * k) → n < 2 ^ 64 →
      paddedVarint n 0 =
        CryptoVerification.LibsignalProtoCodec.encodeVarintAux k (BitVec.ofNat 64 n)
  | 0, _, hk, _, _ => absurd rfl hk
  | k + 1, n, _, hpow, hn => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    have htoNat : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    by_cases hlt : n < 128
    · rw [paddedVarint_zero_of_lt_128 hlt]
      have hlt' : (BitVec.ofNat 64 n).toNat < 0x80 := by rw [htoNat]; exact hlt
      simp only [hlt', ↓reduceIte, List.cons.injEq, and_true]
      apply BitVec.eq_of_toNat_eq; simp
    · rw [paddedVarint_zero_of_ge_128 (by omega)]
      have hlt' : ¬((BitVec.ofNat 64 n).toNat < 0x80) := by rw [htoNat]; omega
      simp only [hlt', ↓reduceIte, List.cons.injEq]
      have hk_ne : k ≠ 0 := by rintro rfl; simp at hpow; omega
      have hdiv_pow : n / 128 < 2 ^ (7 * k) := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        have : 2 ^ (7 * k) * 128 = 2 ^ (7 * (k + 1)) := by
          rw [show 7 * (k + 1) = 7 * k + 7 by omega, Nat.pow_add]
        omega
      constructor
      · rw [varint_cont_byte_eq]
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 7]
      · rw [paddedVarint_zero_eq_encodeVarintAux k (n / 128) hk_ne hdiv_pow (by omega)]
        congr 1; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ushiftRight, htoNat, Nat.shiftRight_eq_div_pow]; omega

private theorem paddedVarint_zero_eq_encodeVarint (n : Nat) (hn : n < 2 ^ 64) :
    paddedVarint n 0 =
      CryptoVerification.LibsignalProtoCodec.encodeVarint (BitVec.ofNat 64 n) :=
  paddedVarint_zero_eq_encodeVarintAux 10 n (by decide) (by omega) hn

private theorem readVarint_encodeField_varint (tag : Nat) (n : Nat) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.varint n) ++ rest) =
      some (tag * 8, paddedVarint n 0 ++ rest) := by
  rw [encodeField, List.append_assoc, readVarint_paddedVarint]

private theorem readVarint_encodeField_bytes (tag : Nat) (b rest : List (BitVec 8)) :
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
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk
          exfalso; omega
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint n₁ (pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint n₂ (pbFields rest₂)
          rw [hrest'] at hrp₁; rw [hrp₁] at hrp₂
          injection hrp₂ with hp'; injection hp' with hn hr
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr
          subst t₁; subst n₁; subst rest₁; rfl
      | bytes b₁ =>
        have hr₁ := readVarint_encodeField_bytes t₁ b₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => contradiction
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk
          exfalso; omega
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint b₁.length (b₁ ++ pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint b₂.length (b₂ ++ pbFields rest₂)
          rw [hrest'] at hrp₁; rw [hrp₁] at hrp₂
          injection hrp₂ with hp'; injection hp' with hlen happ
          obtain ⟨hb, hr⟩ := List.append_inj happ hlen
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr
          subst t₁; subst b₁; subst rest₁; rfl

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
  · simp only [h₁, h₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq, PbValue.bytes.injEq,
      and_true] at h
    exact h.2

private theorem pbFields_append (l₁ l₂ : List (Nat × PbValue)) :
    pbFields (l₁ ++ l₂) = pbFields l₁ ++ pbFields l₂ := by
  simp only [pbFields, List.flatMap_append]

private theorem pbOk_append {l₁ l₂ : List (Nat × PbValue)}
    (h₁ : ∀ x ∈ l₁, PbOk x) (h₂ : ∀ x ∈ l₂, PbOk x) : ∀ x ∈ l₁ ++ l₂, PbOk x := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

private theorem pbOk_bytesFieldList (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList tag b, PbOk x := by
  intro x hx; unfold bytesFieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; exact trivial

private theorem pbOk_u32FieldList (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList tag v, PbOk x := by
  intro x hx; unfold u32FieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; exact trivial

private theorem pbOk_optMsgFieldList (tag : Nat) (opt : Option HwBytes) :
    ∀ x ∈ optMsgFieldList tag opt, PbOk x := by
  intro x hx; cases opt with
  | none => cases hx
  | some b => simp only [optMsgFieldList, List.mem_singleton] at hx; subst hx; exact trivial

private theorem lenField_payload_le (tag : Nat) (b : HwBytes) :
    b.length ≤ (CryptoVerification.E2E.lenField tag b).length := by
  unfold CryptoVerification.E2E.lenField; simp only [List.length_append]; omega

private theorem e2e_u32Field_eq (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    DY.Libsignal.Composed.Refinement.u32Field tag v =
      CryptoVerification.E2E.uint32Field tag v := by
  unfold DY.Libsignal.Composed.Refinement.u32Field CryptoVerification.E2E.uint32Field
  split_ifs with hv
  · rfl
  · unfold DY.Libsignal.Refinement.encodeField CryptoVerification.LibsignalProtoCodec.encodeKey
    dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat]
    rw [paddedVarint_zero_eq_encodeVarint (tag * 8) htag,
        paddedVarint_zero_eq_encodeVarint v.toNat (by have := v.isLt; omega)]
    have hvw : BitVec.ofNat 64 v.toNat = v.setWidth 64 := by
      apply BitVec.eq_of_toNat_eq; have := v.isLt; simp [BitVec.toNat_setWidth]
    rw [hvw]

private theorem e2e_msgField_eq_lenField (tag : Nat) (body : HwBytes)
    (hlen : body.length < 2 ^ 64) (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    DY.Libsignal.Composed.Refinement.msgField tag body =
      CryptoVerification.E2E.lenField tag body := by
  unfold DY.Libsignal.Composed.Refinement.msgField DY.Libsignal.Refinement.encodeField
    CryptoVerification.E2E.lenField CryptoVerification.LibsignalProtoCodec.encodeKey
  dsimp [CryptoVerification.LibsignalProtoCodec.WireType.toNat]
  rw [paddedVarint_zero_eq_encodeVarint (tag * 8 + 2) htag,
      paddedVarint_zero_eq_encodeVarint body.length hlen]

private theorem pbFields_u32FieldList_eq_e2e (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    pbFields (u32FieldList tag v) = CryptoVerification.E2E.uint32Field tag v := by
  have h1 : pbFields (u32FieldList tag v) = DY.Libsignal.Composed.Refinement.u32Field tag v := by
    unfold u32FieldList DY.Libsignal.Composed.Refinement.u32Field; split <;> simp [pbFields]
  rw [h1, e2e_u32Field_eq tag v htag]

private theorem pbFields_bytesFieldList_eq_e2e (tag : Nat) (b : HwBytes)
    (hlen : (CryptoVerification.E2E.bytesField tag b).length < 2 ^ 64)
    (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    pbFields (bytesFieldList tag b) = CryptoVerification.E2E.bytesField tag b := by
  have h1 : pbFields (bytesFieldList tag b) =
      DY.Libsignal.Composed.Refinement.bytesField tag b := by
    unfold bytesFieldList DY.Libsignal.Composed.Refinement.bytesField; split <;> simp [pbFields]
  rw [h1]
  unfold DY.Libsignal.Composed.Refinement.bytesField CryptoVerification.E2E.bytesField
  split_ifs with hb
  · rfl
  · unfold CryptoVerification.E2E.bytesField at hlen
    simp only [hb, ↓reduceIte] at hlen
    exact e2e_msgField_eq_lenField tag b (Nat.lt_of_le_of_lt (lenField_payload_le tag b) hlen) htag

private theorem pbFields_optMsgFieldList_eq_e2e (tag : Nat) (opt : Option HwBytes)
    (hlen : (CryptoVerification.E2E.msgField tag opt).length < 2 ^ 64)
    (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    pbFields (optMsgFieldList tag opt) = CryptoVerification.E2E.msgField tag opt := by
  cases opt with
  | none => rfl
  | some b =>
    dsimp only [optMsgFieldList, CryptoVerification.E2E.msgField] at hlen ⊢
    have h1 : pbFields [(tag, .bytes b)] = DY.Libsignal.Composed.Refinement.msgField tag b := by
      simp [pbFields, DY.Libsignal.Composed.Refinement.msgField]
    rw [h1, e2e_msgField_eq_lenField tag b
      (Nat.lt_of_le_of_lt (lenField_payload_le tag b) hlen) htag]

private theorem pbFields_receiverChains_eq_e2e (cs : List ReceiverChain)
    (hlen : ((cs.map fun c =>
      CryptoVerification.E2E.lenField 7 (encReceiverChain c)).flatten).length < 2 ^ 64) :
    pbFields (cs.map fun c => (7, PbValue.bytes (encReceiverChain c))) =
      (cs.map fun c => CryptoVerification.E2E.lenField 7 (encReceiverChain c)).flatten := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append] at hlen ⊢
    have hc_len : (encReceiverChain c).length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (lenField_payload_le 7 (encReceiverChain c)) (by omega)
    have hcons : pbFields ((7, PbValue.bytes (encReceiverChain c)) ::
        rest.map fun c => (7, PbValue.bytes (encReceiverChain c))) =
        DY.Libsignal.Composed.Refinement.msgField 7 (encReceiverChain c) ++
          pbFields (rest.map fun c => (7, PbValue.bytes (encReceiverChain c))) := rfl
    rw [hcons, e2e_msgField_eq_lenField 7 (encReceiverChain c) hc_len, ih (by omega)]

private def topFieldsX (x : RecordExtras) (st : SessionState Bytes) : List (Nat × PbValue) :=
  u32FieldList 1 st.sessionVersion ++
  bytesFieldList 2 st.localIdentity.serialize ++
  bytesFieldList 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++
  bytesFieldList 4 (HMAC.keyToBytes32 st.rootKey) ++
  u32FieldList 5 st.previousCounter ++
  optMsgFieldList 6 (st.senderChain.map encSenderChain) ++
  (st.receiverChains.map fun c => (7, PbValue.bytes (encReceiverChain c))) ++
  optMsgFieldList 9 (if st.pendingPreKey then some (encPendingPreKeyX x.pending) else none) ++
  u32FieldList 10 x.remoteRegistrationId ++
  u32FieldList 11 x.localRegistrationId ++
  bytesFieldList 13 x.aliceBaseKey ++
  optMsgFieldList 14 (if st.pendingPreKey then x.kyber.map encPendingKyberX else none) ++
  bytesFieldList 15 st.pqRatchetState

private theorem pbOk_topFieldsX (x : RecordExtras) (st : SessionState Bytes) :
    ∀ p ∈ topFieldsX x st, PbOk p := by
  unfold topFieldsX
  repeat apply pbOk_append
  · exact pbOk_u32FieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_optMsgFieldList _ _
  · intro p hp; simp only [List.mem_map] at hp; rcases hp with ⟨_, _, rfl⟩; exact trivial
  · exact pbOk_optMsgFieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_optMsgFieldList _ _
  · exact pbOk_bytesFieldList _ _

private theorem pbFields_topFieldsX_eq (x : RecordExtras) (st : SessionState Bytes)
    (hlen : (encStateUnderExtras x st).length < 2 ^ 64) :
    pbFields (topFieldsX x st) = encStateUnderExtras x st := by
  unfold topFieldsX encStateUnderExtras
  unfold encStateUnderExtras at hlen
  simp only [List.length_append] at hlen
  simp only [pbFields_append]
  rw [pbFields_u32FieldList_eq_e2e 1,
      pbFields_bytesFieldList_eq_e2e 2 _ (by omega),
      pbFields_bytesFieldList_eq_e2e 3 _ (by omega),
      pbFields_bytesFieldList_eq_e2e 4 _ (by omega),
      pbFields_u32FieldList_eq_e2e 5,
      pbFields_optMsgFieldList_eq_e2e 6 _ (by omega),
      pbFields_receiverChains_eq_e2e _ (by omega),
      pbFields_optMsgFieldList_eq_e2e 9 _ (by omega),
      pbFields_u32FieldList_eq_e2e 10,
      pbFields_u32FieldList_eq_e2e 11,
      pbFields_bytesFieldList_eq_e2e 13 _ (by omega),
      pbFields_optMsgFieldList_eq_e2e 14 _ (by omega),
      pbFields_bytesFieldList_eq_e2e 15 _ (by omega)]

private def sessionFieldsRec (s : DY.Libsignal.Rust.SessionRec) : List (Nat × PbValue) :=
  u32FieldList 1 s.sessionVersion ++
  bytesFieldList 2 s.localIdentityPublic ++
  bytesFieldList 3 s.remoteIdentityPublic ++
  bytesFieldList 4 s.rootKey ++
  u32FieldList 5 s.previousCounter ++
  optMsgFieldList 6 (s.senderChain.map DY.Libsignal.Composed.Refinement.chainBytes) ++
  (s.receiverChains.map fun c => (7, PbValue.bytes (DY.Libsignal.Composed.Refinement.chainBytes c))) ++
  optMsgFieldList 9 (s.pendingPreKey.map fun p => p.1 ++ p.2) ++
  u32FieldList 10 s.remoteRegistrationId ++
  u32FieldList 11 s.localRegistrationId ++
  bytesFieldList 13 s.aliceBaseKey ++
  optMsgFieldList 14 (s.pendingKyberPreKey.map fun p => p.1 ++ p.2) ++
  bytesFieldList 15 s.pqRatchetState

private theorem pbOk_sessionFieldsRec (s : DY.Libsignal.Rust.SessionRec) :
    ∀ p ∈ sessionFieldsRec s, PbOk p := by
  unfold sessionFieldsRec
  repeat apply pbOk_append
  · exact pbOk_u32FieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_optMsgFieldList _ _
  · intro p hp; simp only [List.mem_map] at hp; rcases hp with ⟨_, _, rfl⟩; exact trivial
  · exact pbOk_optMsgFieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_u32FieldList _ _
  · exact pbOk_bytesFieldList _ _
  · exact pbOk_optMsgFieldList _ _
  · exact pbOk_bytesFieldList _ _

private theorem pbFields_sessionFieldsRec (s : DY.Libsignal.Rust.SessionRec) :
    pbFields (sessionFieldsRec s) = DY.Libsignal.Composed.Refinement.sessionBytes s := by
  have hb (tag : Nat) (b : HwBytes) :
      pbFields (bytesFieldList tag b) = DY.Libsignal.Composed.Refinement.bytesField tag b := by
    unfold bytesFieldList DY.Libsignal.Composed.Refinement.bytesField; split <;> simp [pbFields]
  have hu (tag : Nat) (v : BitVec 32) :
      pbFields (u32FieldList tag v) = DY.Libsignal.Composed.Refinement.u32Field tag v := by
    unfold u32FieldList DY.Libsignal.Composed.Refinement.u32Field; split <;> simp [pbFields]
  have hm7 (cs : List DY.Libsignal.Rust.ChainRec) :
      pbFields (cs.map fun c => (7, PbValue.bytes (DY.Libsignal.Composed.Refinement.chainBytes c))) =
        cs.flatMap (DY.Libsignal.Composed.Refinement.msgField 7 ∘
          DY.Libsignal.Composed.Refinement.chainBytes) := by
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, pbFields, List.flatMap_cons,
        DY.Libsignal.Composed.Refinement.msgField, Function.comp_apply]
      congr 1
  unfold sessionFieldsRec DY.Libsignal.Composed.Refinement.sessionBytes
  simp only [pbFields_append, hu, hb, hm7]
  cases s.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
    simp [optMsgFieldList, pbFields, DY.Libsignal.Composed.Refinement.msgField]

private theorem filter13_bytesFieldList_ne {tag : Nat} (h : (tag == 13) = false) (b : HwBytes) :
    (bytesFieldList tag b).filter (fun p => p.1 == 13) = [] := by
  unfold bytesFieldList; split <;> simp [h]

private theorem filter13_bytesFieldList_self (b : HwBytes) :
    (bytesFieldList 13 b).filter (fun p => p.1 == 13) = bytesFieldList 13 b := by
  unfold bytesFieldList; split <;> simp

private theorem filter13_u32FieldList_ne {tag : Nat} (h : (tag == 13) = false) (v : BitVec 32) :
    (u32FieldList tag v).filter (fun p => p.1 == 13) = [] := by
  unfold u32FieldList; split <;> simp [h]

private theorem filter13_optMsgFieldList_ne {tag : Nat} (h : (tag == 13) = false)
    (o : Option HwBytes) :
    (optMsgFieldList tag o).filter (fun p => p.1 == 13) = [] := by
  cases o <;> simp [optMsgFieldList, h]

private theorem filter13_map7 {α : Type} (f : α → HwBytes) (l : List α) :
    (l.map fun c => (7, PbValue.bytes (f c))).filter (fun p => p.1 == 13) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem filter13_topFieldsX (x : RecordExtras) (st : SessionState Bytes) :
    (topFieldsX x st).filter (fun p => p.1 == 13) = bytesFieldList 13 x.aliceBaseKey := by
  unfold topFieldsX
  simp [List.filter_append, filter13_u32FieldList_ne, filter13_bytesFieldList_ne,
    filter13_optMsgFieldList_ne, filter13_map7, filter13_bytesFieldList_self]

private theorem filter13_sessionFieldsRec (s : DY.Libsignal.Rust.SessionRec) :
    (sessionFieldsRec s).filter (fun p => p.1 == 13) = bytesFieldList 13 s.aliceBaseKey := by
  unfold sessionFieldsRec
  simp [List.filter_append, filter13_u32FieldList_ne, filter13_bytesFieldList_ne,
    filter13_optMsgFieldList_ne, filter13_map7, filter13_bytesFieldList_self]

/-- Any `RecordRec` with `previous = []` whose `recordBytes` equals `chevalSessionBytes` has
`current.aliceBaseKey` beginning with `[0x05#8, 0x01#8]` (proved without reducing `spqrV1Init`). -/
theorem chevalSessionBytes_recordBytes_aliceBaseKey_take2
    {rr : DY.Libsignal.Rust.RecordRec}
    (hrec : chevalSessionBytes = DY.Libsignal.Composed.Refinement.recordBytes rr)
    (hprev : rr.previous = []) :
    rr.current.aliceBaseKey.take 2 = [0x05#8, 0x01#8] := by
  have hSome := initiateState_W0_isSome
  have hlt : chevalSessionBytes.length < 2 ^ 64 :=
    Nat.lt_trans chevalSessionBytes_lt (by decide)
  unfold chevalSessionBytes at hrec hlt
  cases hInit : initiateState X0 W0 .A emptyParty.me b0 t0 with
  | none => simp [hInit] at hSome
  | some xg =>
    rcases xg with ⟨x, g⟩
    simp only [hInit] at hrec hlt
    have hpb_lhs : pbFields (optMsgFieldList 1 (some (encStateUnderExtras (x) g.session))) =
        encodeRecordUnderExtras (fun _ => x) g :=
      pbFields_optMsgFieldList_eq_e2e 1 (some (encStateUnderExtras x g.session)) hlt
    have hpb_rhs : pbFields (optMsgFieldList 1
        (some (DY.Libsignal.Composed.Refinement.sessionBytes rr.current))) =
        DY.Libsignal.Composed.Refinement.recordBytes rr := by
      unfold DY.Libsignal.Composed.Refinement.recordBytes
        DY.Libsignal.Composed.Refinement.sessionBytes
      simp [hprev, optMsgFieldList, pbFields, DY.Libsignal.Composed.Refinement.msgField]
    have htop1 := pbFields_inj
      (pbOk_optMsgFieldList 1 _) (pbOk_optMsgFieldList 1 _)
      (hpb_lhs.trans (hrec.trans hpb_rhs.symm))
    simp only [optMsgFieldList, List.cons.injEq, Prod.mk.injEq, PbValue.bytes.injEq,
      true_and, and_true] at htop1
    have hlen_body : (encStateUnderExtras x g.session).length < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (lenField_payload_le 1 (encStateUnderExtras x g.session)) hlt
    have htop2 := pbFields_inj (pbOk_topFieldsX x g.session) (pbOk_sessionFieldsRec rr.current)
      ((pbFields_topFieldsX_eq x g.session hlen_body).trans
        (htop1.trans (pbFields_sessionFieldsRec rr.current).symm))
    have hfilt := congrArg (List.filter (fun p => p.1 == 13)) htop2
    rw [filter13_topFieldsX, filter13_sessionFieldsRec] at hfilt
    have hbk := bytesFieldList_inj hfilt
    rw [← hbk]
    exact initiateState_aliceBaseKey hInit

end Symbolic.Proofs.Tests.Refinement.Cli.Cheval26
