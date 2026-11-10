/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridge
public import Symbolic.Proofs.Refinement.LemmasPure
public import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureA

/-!
# Canonical Session Record Injectivity

Proves that `slots_RecordCanonical_Q slots_NonEmptyV1Q` uniquely determines the decoded
`Session (List (BitVec 8))` from its serialized record bytes across acknowledged and pending
PQXDH sessions (`recordCanonical_Q_inj`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.RecordX
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (PbValue encodeField paddedVarint readVarint readVarint_paddedVarint)
open DY.Libsignal.TripleRatchet.Refinement
open Swarm.Phase0WholeFunctionBridge
  (paddedVarint_zero_eq_encodeVarint msgField_eq_lenField u32Field_eq_uint32Field
    bytesField_eq_record_bytesField senderChainToChainRec receiverChainToChainRec)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.TR.Pure (slots_RecordCanonical_Q slots_NonEmptyV1Q)
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoinsCliPure (sessionToRecordRecPending)

/-! ## Protobuf Field-List Injectivity -/

private theorem readVarint_encodeField_varint_sr (tag : Nat) (n : Nat) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.varint n) ++ rest) =
      some (tag * 8, paddedVarint n 0 ++ rest) := by
  rw [encodeField, List.append_assoc, readVarint_paddedVarint]

private theorem readVarint_encodeField_bytes_sr (tag : Nat) (b : HwBytes) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.bytes b) ++ rest) =
      some (tag * 8 + 2, paddedVarint b.length 0 ++ (b ++ rest)) := by
  rw [encodeField, List.append_assoc, List.append_assoc, readVarint_paddedVarint]

private theorem pbFields_inj_sr {l₁ l₂ : List (Nat × PbValue)}
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
        have hr := readVarint_encodeField_varint_sr t₂ n₂ (pbFields rest₂)
        change [] = encodeField t₂ 0 0 (.varint n₂) ++ pbFields rest₂ at h
        rw [← h] at hr; nomatch hr
      | bytes b₂ =>
        have hr := readVarint_encodeField_bytes_sr t₂ b₂ (pbFields rest₂)
        change [] = encodeField t₂ 0 0 (.bytes b₂) ++ pbFields rest₂ at h
        rw [← h] at hr; nomatch hr
      | unknown _ _ => exact False.elim hok
  | cons p₁ rest₁ ih =>
    cases l₂ with
    | nil =>
      obtain ⟨t₁, v₁⟩ := p₁
      have hok := h₁ (t₁, v₁) (by simp)
      cases v₁ with
      | varint n₁ =>
        have hr := readVarint_encodeField_varint_sr t₁ n₁ (pbFields rest₁)
        change encodeField t₁ 0 0 (.varint n₁) ++ pbFields rest₁ = [] at h
        rw [h] at hr; nomatch hr
      | bytes b₁ =>
        have hr := readVarint_encodeField_bytes_sr t₁ b₁ (pbFields rest₁)
        change encodeField t₁ 0 0 (.bytes b₁) ++ pbFields rest₁ = [] at h
        rw [h] at hr; nomatch hr
      | unknown _ _ => exact False.elim hok
    | cons p₂ rest₂ =>
      obtain ⟨t₁, v₁⟩ := p₁
      obtain ⟨t₂, v₂⟩ := p₂
      have hok₁ := h₁ (t₁, v₁) (by simp)
      have hok₂ := h₂ (t₂, v₂) (by simp)
      change encodeField t₁ 0 0 v₁ ++ pbFields rest₁ =
        encodeField t₂ 0 0 v₂ ++ pbFields rest₂ at h
      cases v₁ with
      | unknown _ _ => exact False.elim hok₁
      | varint n₁ =>
        have hr₁ := readVarint_encodeField_varint_sr t₁ n₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => exact False.elim hok₂
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes_sr t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk; omega
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint_sr t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint n₁ (pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint n₂ (pbFields rest₂)
          rw [hrest'] at hrp₁; rw [hrp₁] at hrp₂
          injection hrp₂ with hp'; injection hp' with hn hr
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
            (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr
          subst ht; subst hn; subst hrest_eq; rfl
      | bytes b₁ =>
        have hr₁ := readVarint_encodeField_bytes_sr t₁ b₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => exact False.elim hok₂
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint_sr t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂
          injection hr₂ with hp; injection hp with hk; omega
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes_sr t₂ b₂ (pbFields rest₂)
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
          subst ht; subst hb; subst hrest_eq; rfl

private def optU32FieldList (tag : Nat) : Option (BitVec 32) → List (Nat × PbValue)
  | none => []
  | some v => [(tag, .varint v.toNat)]

private def u32FieldList_sr (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0#32 then [] else [(tag, .varint v.toNat)]

private def int32FieldList_sr (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0#32 then [] else [(tag, .varint (v.signExtend 64).toNat)]

private def bytesFieldList_sr (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private theorem pbOk_optU32 (tag : Nat) (ov : Option (BitVec 32)) :
    ∀ x ∈ optU32FieldList tag ov, PbOk x := by cases ov <;> simp [optU32FieldList, PbOk]

private theorem pbOk_u32 (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList_sr tag v, PbOk x := by unfold u32FieldList_sr; split_ifs <;> simp [PbOk]

private theorem pbOk_int32 (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ int32FieldList_sr tag v, PbOk x := by unfold int32FieldList_sr; split_ifs <;> simp [PbOk]

private theorem pbOk_bytes (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList_sr tag b, PbOk x := by unfold bytesFieldList_sr; split_ifs <;> simp [PbOk]

private theorem filter_tag_optU32 (tag t : Nat) (ov : Option (BitVec 32)) :
    (optU32FieldList tag ov).filter (fun x => decide (x.1 = t)) =
      if tag = t then optU32FieldList tag ov else [] := by
  cases ov <;> by_cases h : tag = t <;> simp [optU32FieldList, h]

private theorem filter_tag_u32 (tag t : Nat) (v : BitVec 32) :
    (u32FieldList_sr tag v).filter (fun x => decide (x.1 = t)) =
      if tag = t then u32FieldList_sr tag v else [] := by
  unfold u32FieldList_sr; by_cases hv : v = 0#32 <;> by_cases h : tag = t <;> simp [hv, h]

private theorem filter_tag_int32 (tag t : Nat) (v : BitVec 32) :
    (int32FieldList_sr tag v).filter (fun x => decide (x.1 = t)) =
      if tag = t then int32FieldList_sr tag v else [] := by
  unfold int32FieldList_sr; by_cases hv : v = 0#32 <;> by_cases h : tag = t <;> simp [hv, h]

private theorem filter_tag_bytes (tag t : Nat) (b : HwBytes) :
    (bytesFieldList_sr tag b).filter (fun x => decide (x.1 = t)) =
      if tag = t then bytesFieldList_sr tag b else [] := by
  unfold bytesFieldList_sr; by_cases hb : b = [] <;> by_cases h : tag = t <;> simp [hb, h]

private theorem pbFields_optU32FieldList (tag : Nat) (ov : Option (BitVec 32))
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    pbFields (optU32FieldList tag ov) = optUint32Field tag ov := by
  cases ov with
  | none => rfl
  | some v =>
    unfold optU32FieldList optUint32Field pbFields
    simp only [List.flatMap_cons, List.flatMap_nil]
    change encodeField tag 0 0 (.varint v.toNat) ++ [] = _
    rw [List.append_nil]; unfold encodeField encodeKey; dsimp [WireType.toNat]
    rw [paddedVarint_zero_eq_encodeVarint (tag * 8) htag,
        paddedVarint_zero_eq_encodeVarint v.toNat (by have := v.isLt; omega)]
    have hvw : BitVec.ofNat 64 v.toNat = v.setWidth 64 := by
      apply BitVec.eq_of_toNat_eq; have := v.isLt; simp [BitVec.toNat_setWidth]
    rw [hvw]

private theorem pbFields_u32FieldList_sr (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    pbFields (u32FieldList_sr tag v) = CryptoVerification.E2E.Record.uint32Field tag v := by
  rw [← u32Field_eq_uint32Field tag v htag]
  unfold u32FieldList_sr DY.Libsignal.Composed.Refinement.u32Field
  by_cases hv : v = 0#32
  · subst hv; rfl
  · simp [hv, pbFields]

private theorem pbFields_int32FieldList_sr (tag : Nat) (v : BitVec 32)
    (htag : tag * 8 < 2 ^ 64 := by decide) :
    pbFields (int32FieldList_sr tag v) = CryptoVerification.E2E.Record.int32Field tag v := by
  unfold int32FieldList_sr CryptoVerification.E2E.Record.int32Field
  by_cases hv : v = 0#32
  · subst hv; rfl
  · have hv0 : v ≠ 0 := hv
    simp only [hv, hv0, ↓reduceIte, pbFields, List.flatMap_cons, List.flatMap_nil]
    change encodeField tag 0 0 (.varint (v.signExtend 64).toNat) ++ [] = _
    rw [List.append_nil]; unfold encodeField encodeKey; dsimp [WireType.toNat]
    rw [paddedVarint_zero_eq_encodeVarint (tag * 8) htag,
        paddedVarint_zero_eq_encodeVarint (v.signExtend 64).toNat (v.signExtend 64).isLt]
    simp

private theorem pbFields_bytesFieldList_sr (tag : Nat) (b : HwBytes)
    (hlen : b.length < 2 ^ 64) (htag : tag * 8 + 2 < 2 ^ 64 := by decide) :
    pbFields (bytesFieldList_sr tag b) = CryptoVerification.E2E.Record.bytesField tag b := by
  rw [← bytesField_eq_record_bytesField tag b hlen htag]
  unfold bytesFieldList_sr DY.Libsignal.Composed.Refinement.bytesField
  split <;> simp [pbFields]

private theorem signExtend64_toNat_eq (v : BitVec 32) :
    (v.signExtend 64).toNat =
      if 2 * v.toNat < 2 ^ 32 then v.toNat else v.toNat + (2 ^ 64 - 2 ^ 32) := by
  have hd : (v.signExtend 64).toNat =
      ((if 2 * v.toNat < 2 ^ 32 then (v.toNat : Int) else (v.toNat : Int) - (2 ^ 32 : Nat)) %
        (2 ^ 64 : Int)).toNat := rfl
  rw [hd]; have hlt := v.isLt; split_ifs with h
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega
  · have heq : (v.toNat : Int) - (2 ^ 32 : Nat) =
        ((v.toNat + (2 ^ 64 - 2 ^ 32) : Nat) : Int) - (2 ^ 64 : Int) := by omega
    rw [heq, Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]; omega

private theorem signExtend64_toNat_inj {v₁ v₂ : BitVec 32}
    (h : (v₁.signExtend 64).toNat = (v₂.signExtend 64).toNat) : v₁ = v₂ := by
  rw [signExtend64_toNat_eq, signExtend64_toNat_eq] at h
  have := v₁.isLt; have := v₂.isLt
  apply BitVec.eq_of_toNat_eq; split_ifs at h <;> omega

/-! ## Key, Chain, and Pending Pre-Key Field Injectivity -/

theorem publicKey_serialize_injective {pk₁ pk₂ : PublicKey}
    (h : pk₁.serialize = pk₂.serialize) : pk₁ = pk₂ := by
  cases pk₁ with | mk b₁ => cases pk₂ with | mk b₂ =>
  simp [PublicKey.serialize] at h; exact congrArg PublicKey.mk (Subtype.ext h)

theorem identityKey_serialize_injective {ik₁ ik₂ : IdentityKey}
    (h : ik₁.serialize = ik₂.serialize) : ik₁ = ik₂ := by
  cases ik₁ with | mk pk₁ => cases ik₂ with | mk pk₂ =>
  exact congrArg IdentityKey.mk (publicKey_serialize_injective h)

private theorem remoteIdentity_getD_injective {r₁ r₂ : Option IdentityKey}
    (h : (r₁.map IdentityKey.serialize).getD [] = (r₂.map IdentityKey.serialize).getD []) :
    r₁ = r₂ := by
  cases r₁ with
  | none =>
    cases r₂ with
    | none => rfl
    | some _ => simp [IdentityKey.serialize, PublicKey.serialize] at h
  | some ik₁ =>
    cases r₂ with
    | none => simp [IdentityKey.serialize, PublicKey.serialize] at h
    | some ik₂ =>
      simp only [Option.map_some, Option.getD_some] at h
      exact congrArg some (identityKey_serialize_injective h)

private theorem keyToBytes32_injective {k₁ k₂ : BitVec 256}
    (h : CryptoGames.HMAC.keyToBytes32 k₁ = CryptoGames.HMAC.keyToBytes32 k₂) : k₁ = k₂ := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hj : i / 8 < 32 := by omega
  have hr : i % 8 < 8 := by omega
  have hbyte := congrArg (fun (l : List (BitVec 8)) => l[i / 8]?.map (fun b => b.getLsbD (i % 8))) h
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem?_ofFn, hj, ↓reduceDIte,
    Option.map_some, Option.some.injEq, BitVec.getLsbD_extractLsb', hr, decide_true,
    Bool.true_and, Nat.div_add_mod] at hbyte
  exact hbyte

private theorem senderChainToChainRec_injective {sc₁ sc₂ : SenderChain}
    (h : senderChainToChainRec sc₁ = senderChainToChainRec sc₂) : sc₁ = sc₂ := by
  rcases sc₁ with ⟨⟨pub₁, ⟨priv₁⟩⟩, ⟨ck₁, idx₁⟩⟩
  rcases sc₂ with ⟨⟨pub₂, ⟨priv₂⟩⟩, ⟨ck₂, idx₂⟩⟩
  have hpub : pub₁ = pub₂ := publicKey_serialize_injective (congrArg (·.senderRatchetKey) h)
  have hpriv : priv₁ = priv₂ := Subtype.ext (congrArg (·.senderRatchetKeyPrivate) h)
  have hck := congrArg (·.chainKey) h; dsimp [senderChainToChainRec] at hck
  injection hck with hpair; injection hpair with hidx hkey
  have hkey' := keyToBytes32_injective hkey
  subst hpub; subst hpriv; subst hidx; subst hkey'; rfl

private theorem receiverChainToChainRec_injective {rc₁ rc₂ : ReceiverChain}
    (h : receiverChainToChainRec rc₁ = receiverChainToChainRec rc₂) : rc₁ = rc₂ := by
  rcases rc₁ with ⟨rk₁, ck₁, mks₁⟩; rcases rc₂ with ⟨rk₂, ck₂, mks₂⟩
  have hrk : rk₁ = rk₂ := publicKey_serialize_injective (congrArg (·.senderRatchetKey) h)
  have hck_eq : ck₁ = ck₂ := by
    have hck := congrArg (·.chainKey) h; dsimp [receiverChainToChainRec] at hck
    cases ck₁ with
    | none => cases ck₂ <;> simp at hck; rfl
    | some c₁ =>
      cases ck₂ with
      | none => simp at hck
      | some c₂ =>
        rcases c₁ with ⟨k₁, i₁⟩; rcases c₂ with ⟨k₂, i₂⟩
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hck
        rw [hck.1, keyToBytes32_injective hck.2]
  have hmks_eq : mks₁ = mks₂ := by
    have hmks := congrArg (·.messageKeys) h; dsimp [receiverChainToChainRec] at hmks
    apply (List.map_injective_iff.mpr ?_) hmks
    intro a b hab; cases a; cases b; simp only [Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩; rfl
  subst hrk; subst hck_eq; subst hmks_eq; rfl

private theorem encPendingPreKey_injective {p₁ p₂ : PendingPreKey}
    (hts₁ : p₁.timestamp = 0#64) (hts₂ : p₂.timestamp = 0#64)
    (h : encPendingPreKey p₁ = encPendingPreKey p₂) : p₁ = p₂ := by
  let l₁ := optU32FieldList 1 p₁.preKeyId ++
    bytesFieldList_sr 2 p₁.baseKey.serialize ++ int32FieldList_sr 3 p₁.signedPreKeyId
  let l₂ := optU32FieldList 1 p₂.preKeyId ++
    bytesFieldList_sr 2 p₂.baseKey.serialize ++ int32FieldList_sr 3 p₂.signedPreKeyId
  have hlen₁ : p₁.baseKey.serialize.length < 2 ^ 64 := by simp [PublicKey.serialize]
  have hlen₂ : p₂.baseKey.serialize.length < 2 ^ 64 := by simp [PublicKey.serialize]
  have henc₁ : encPendingPreKey p₁ = pbFields l₁ := by
    unfold encPendingPreKey l₁
    rw [hts₁, show CryptoVerification.E2E.Record.uint64Field 4 0#64 = [] from rfl, List.append_nil]
    simp only [pbFields, List.flatMap_append]
    change optUint32Field 1 p₁.preKeyId ++
        CryptoVerification.E2E.Record.bytesField 2 p₁.baseKey.serialize ++
        CryptoVerification.E2E.Record.int32Field 3 p₁.signedPreKeyId =
      pbFields (optU32FieldList 1 p₁.preKeyId) ++
        pbFields (bytesFieldList_sr 2 p₁.baseKey.serialize) ++
        pbFields (int32FieldList_sr 3 p₁.signedPreKeyId)
    rw [pbFields_optU32FieldList 1, pbFields_bytesFieldList_sr 2 _ hlen₁,
        pbFields_int32FieldList_sr 3]
  have henc₂ : encPendingPreKey p₂ = pbFields l₂ := by
    unfold encPendingPreKey l₂
    rw [hts₂, show CryptoVerification.E2E.Record.uint64Field 4 0#64 = [] from rfl, List.append_nil]
    simp only [pbFields, List.flatMap_append]
    change optUint32Field 1 p₂.preKeyId ++
        CryptoVerification.E2E.Record.bytesField 2 p₂.baseKey.serialize ++
        CryptoVerification.E2E.Record.int32Field 3 p₂.signedPreKeyId =
      pbFields (optU32FieldList 1 p₂.preKeyId) ++
        pbFields (bytesFieldList_sr 2 p₂.baseKey.serialize) ++
        pbFields (int32FieldList_sr 3 p₂.signedPreKeyId)
    rw [pbFields_optU32FieldList 1, pbFields_bytesFieldList_sr 2 _ hlen₂,
        pbFields_int32FieldList_sr 3]
  have hok₁ : ∀ x ∈ l₁, PbOk x := by
    intro x hx; simp only [l₁, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact pbOk_optU32 _ _ x hx
    · exact pbOk_bytes _ _ x hx
    · exact pbOk_int32 _ _ x hx
  have hok₂ : ∀ x ∈ l₂, PbOk x := by
    intro x hx; simp only [l₂, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact pbOk_optU32 _ _ x hx
    · exact pbOk_bytes _ _ x hx
    · exact pbOk_int32 _ _ x hx
  have hl : l₁ = l₂ := pbFields_inj_sr hok₁ hok₂ (henc₁.symm.trans (h.trans henc₂))
  have hf1 : optU32FieldList 1 p₁.preKeyId = optU32FieldList 1 p₂.preKeyId := by
    have h1 := congrArg (List.filter (fun x => decide (x.1 = 1))) hl
    simp only [l₁, l₂, List.filter_append, filter_tag_optU32, filter_tag_bytes, filter_tag_int32,
      ↓reduceIte, Nat.reduceEqDiff, List.append_nil] at h1; exact h1
  have hpk : p₁.preKeyId = p₂.preKeyId := by
    rcases hp₁ : p₁.preKeyId with _ | v₁ <;> rcases hp₂ : p₂.preKeyId with _ | v₂
    · rfl
    · simp [hp₁, hp₂, optU32FieldList] at hf1
    · simp [hp₁, hp₂, optU32FieldList] at hf1
    · simp only [hp₁, hp₂, optU32FieldList, List.cons.injEq, Prod.mk.injEq,
        PbValue.varint.injEq, true_and, and_true] at hf1
      exact congrArg some (BitVec.eq_of_toNat_eq hf1)
  have hf2 : bytesFieldList_sr 2 p₁.baseKey.serialize = bytesFieldList_sr 2 p₂.baseKey.serialize := by
    have h2 := congrArg (List.filter (fun x => decide (x.1 = 2))) hl
    simp only [l₁, l₂, List.filter_append, filter_tag_optU32, filter_tag_bytes, filter_tag_int32,
      ↓reduceIte, Nat.reduceEqDiff, List.append_nil, List.nil_append] at h2; exact h2
  have hbk : p₁.baseKey = p₂.baseKey := by
    have hb₁ : p₁.baseKey.serialize ≠ [] := by simp [PublicKey.serialize]
    have hb₂ : p₂.baseKey.serialize ≠ [] := by simp [PublicKey.serialize]
    simp only [bytesFieldList_sr, hb₁, hb₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq,
      PbValue.bytes.injEq, true_and, and_true] at hf2
    exact publicKey_serialize_injective hf2
  have hf3 : int32FieldList_sr 3 p₁.signedPreKeyId = int32FieldList_sr 3 p₂.signedPreKeyId := by
    have h3 := congrArg (List.filter (fun x => decide (x.1 = 3))) hl
    simp only [l₁, l₂, List.filter_append, filter_tag_optU32, filter_tag_bytes, filter_tag_int32,
      ↓reduceIte, Nat.reduceEqDiff, List.append_nil, List.nil_append] at h3; exact h3
  have hspk : p₁.signedPreKeyId = p₂.signedPreKeyId := by
    unfold int32FieldList_sr at hf3
    by_cases hs₁ : p₁.signedPreKeyId = 0#32 <;> by_cases hs₂ : p₂.signedPreKeyId = 0#32
    · rw [hs₁, hs₂]
    · simp [hs₁, hs₂] at hf3
    · simp [hs₁, hs₂] at hf3
    · simp only [hs₁, hs₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq,
        PbValue.varint.injEq, true_and, and_true] at hf3
      exact signExtend64_toNat_inj hf3
  rcases p₁ with ⟨pk₁, spk₁, bk₁, ts₁⟩; rcases p₂ with ⟨pk₂, spk₂, bk₂, ts₂⟩
  dsimp at hpk hspk hbk hts₁ hts₂
  subst hpk; subst hspk; subst hbk; rw [hts₁, hts₂]

private theorem encPendingKyber_injective {k₁ k₂ : PendingKyberPreKey}
    (hlen₁ : k₁.ciphertext.length < 2 ^ 64) (hlen₂ : k₂.ciphertext.length < 2 ^ 64)
    (h : encPendingKyber k₁ = encPendingKyber k₂) : k₁ = k₂ := by
  let l₁ := u32FieldList_sr 1 k₁.preKeyId ++ bytesFieldList_sr 2 k₁.ciphertext
  let l₂ := u32FieldList_sr 1 k₂.preKeyId ++ bytesFieldList_sr 2 k₂.ciphertext
  have henc₁ : encPendingKyber k₁ = pbFields l₁ := by
    unfold encPendingKyber l₁; simp only [pbFields, List.flatMap_append]
    change CryptoVerification.E2E.Record.uint32Field 1 k₁.preKeyId ++
        CryptoVerification.E2E.Record.bytesField 2 k₁.ciphertext =
      pbFields (u32FieldList_sr 1 k₁.preKeyId) ++ pbFields (bytesFieldList_sr 2 k₁.ciphertext)
    rw [pbFields_u32FieldList_sr 1, pbFields_bytesFieldList_sr 2 _ hlen₁]
  have henc₂ : encPendingKyber k₂ = pbFields l₂ := by
    unfold encPendingKyber l₂; simp only [pbFields, List.flatMap_append]
    change CryptoVerification.E2E.Record.uint32Field 1 k₂.preKeyId ++
        CryptoVerification.E2E.Record.bytesField 2 k₂.ciphertext =
      pbFields (u32FieldList_sr 1 k₂.preKeyId) ++ pbFields (bytesFieldList_sr 2 k₂.ciphertext)
    rw [pbFields_u32FieldList_sr 1, pbFields_bytesFieldList_sr 2 _ hlen₂]
  have hok₁ : ∀ x ∈ l₁, PbOk x := by
    intro x hx; simp only [l₁, List.mem_append] at hx
    rcases hx with hx | hx; · exact pbOk_u32 _ _ x hx
    exact pbOk_bytes _ _ x hx
  have hok₂ : ∀ x ∈ l₂, PbOk x := by
    intro x hx; simp only [l₂, List.mem_append] at hx
    rcases hx with hx | hx; · exact pbOk_u32 _ _ x hx
    exact pbOk_bytes _ _ x hx
  have hl : l₁ = l₂ := pbFields_inj_sr hok₁ hok₂ (henc₁.symm.trans (h.trans henc₂))
  have hf1 : u32FieldList_sr 1 k₁.preKeyId = u32FieldList_sr 1 k₂.preKeyId := by
    have h1 := congrArg (List.filter (fun x => decide (x.1 = 1))) hl
    simp only [l₁, l₂, List.filter_append, filter_tag_u32, filter_tag_bytes,
      ↓reduceIte, Nat.reduceEqDiff, List.append_nil] at h1; exact h1
  have hpk : k₁.preKeyId = k₂.preKeyId := by
    unfold u32FieldList_sr at hf1
    by_cases hp₁ : k₁.preKeyId = 0#32 <;> by_cases hp₂ : k₂.preKeyId = 0#32
    · rw [hp₁, hp₂]
    · simp [hp₁, hp₂] at hf1
    · simp [hp₁, hp₂] at hf1
    · simp only [hp₁, hp₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq,
        PbValue.varint.injEq, true_and, and_true] at hf1
      exact BitVec.eq_of_toNat_eq hf1
  have hf2 : bytesFieldList_sr 2 k₁.ciphertext = bytesFieldList_sr 2 k₂.ciphertext := by
    have h2 := congrArg (List.filter (fun x => decide (x.1 = 2))) hl
    simp only [l₁, l₂, List.filter_append, filter_tag_u32, filter_tag_bytes,
      ↓reduceIte, Nat.reduceEqDiff, List.nil_append] at h2; exact h2
  have hct : k₁.ciphertext = k₂.ciphertext := by
    unfold bytesFieldList_sr at hf2
    by_cases hc₁ : k₁.ciphertext = [] <;> by_cases hc₂ : k₂.ciphertext = [] <;> simp_all
  rcases k₁ with ⟨pk₁, ct₁⟩; rcases k₂ with ⟨pk₂, ct₂⟩
  dsimp at hpk hct; subst hpk; subst hct; rfl

/-! ## Session Uniqueness -/

theorem normPending_sessionToRecordRecPending (s : Session (List (BitVec 8))) :
    TR.normPending (sessionToRecordRecPending s) = sessionToRecordRecPending s := by
  unfold TR.normPending sessionToRecordRecPending
  cases hp : s.pendingPreKey <;> cases hk : s.pendingKyberPreKey <;>
    simp [TR.normPendingS]

/-- Any two sessions satisfying `slots_RecordCanonical_Q slots_NonEmptyV1Q` on the same serialized
record bytes `bs` are equal. -/
theorem recordCanonical_Q_inj {bs : List (BitVec 8)}
    {s₁ s₂ : Session (List (BitVec 8))}
    (h₁ : slots_RecordCanonical_Q slots_NonEmptyV1Q bs s₁)
    (h₂ : slots_RecordCanonical_Q slots_NonEmptyV1Q bs s₂) :
    s₁ = s₂ := by
  have hb₁ : bs = DY.Libsignal.Composed.Refinement.recordBytes (sessionToRecordRecPending s₁) :=
    h₁.1.trans (TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q h₁).symm
  have hb₂ : bs = DY.Libsignal.Composed.Refinement.recordBytes (sessionToRecordRecPending s₂) :=
    h₂.1.trans (TR.SendRetCoinsCliPure.recordBytes_sessionToRecordRecPending_of_canonical_Q h₂).symm
  have hnorm : TR.normPending (sessionToRecordRecPending s₁) =
      TR.normPending (sessionToRecordRecPending s₂) :=
    TR.recordBytes_injective (hb₁.symm.trans hb₂)
  rw [normPending_sessionToRecordRecPending, normPending_sessionToRecordRecPending] at hnorm
  have hcur := congrArg (·.current) hnorm
  obtain ⟨_, ⟨⟨_, _, hrepr₁⟩, sx₁, hsx₁, hsp₁⟩, _⟩ := h₁
  obtain ⟨_, ⟨⟨_, _, hrepr₂⟩, sx₂, hsx₂, hsp₂⟩, _⟩ := h₂
  injection hsx₁ with hsx₁'; subst hsx₁'
  injection hsx₂ with hsx₂'; subst hsx₂'
  have hwf₁ : s₁.Wf := (hrepr₁ s₁ rfl).2.2.1
  have hwf₂ : s₂.Wf := (hrepr₂ s₂ rfl).2.2.1
  have hppk : s₁.pendingPreKey = s₂.pendingPreKey := by
    have hp := congrArg (·.pendingPreKey) hcur
    dsimp [sessionToRecordRecPending] at hp
    cases hp₁ : s₁.pendingPreKey with
    | none => cases hp₂ : s₂.pendingPreKey <;> simp [hp₁, hp₂] at hp; rfl
    | some p₁ =>
      cases hp₂ : s₂.pendingPreKey with
      | none => simp [hp₁, hp₂] at hp
      | some p₂ =>
        simp only [hp₁, hp₂, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true] at hp
        exact congrArg some (encPendingPreKey_injective (hsp₁.2.1 p₁ hp₁) (hsp₂.2.1 p₂ hp₂) hp)
  have hpkp : s₁.pendingKyberPreKey = s₂.pendingKyberPreKey := by
    have hk := congrArg (·.pendingKyberPreKey) hcur
    dsimp [sessionToRecordRecPending] at hk
    cases hk₁ : s₁.pendingKyberPreKey with
    | none => cases hk₂ : s₂.pendingKyberPreKey <;> simp [hk₁, hk₂] at hk; rfl
    | some k₁ =>
      cases hk₂ : s₂.pendingKyberPreKey with
      | none => simp [hk₁, hk₂] at hk
      | some k₂ =>
        simp only [hk₁, hk₂, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true] at hk
        have hl₁ : k₁.ciphertext.length < 2 ^ 64 := by have := hsp₁.2.2.1 k₁ hk₁; omega
        have hl₂ : k₂.ciphertext.length < 2 ^ 64 := by have := hsp₂.2.2.1 k₂ hk₂; omega
        exact congrArg some (encPendingKyber_injective hl₁ hl₂ hk)
  have hsc : s₁.state.senderChain = s₂.state.senderChain := by
    have hs := congrArg (·.senderChain) hcur
    dsimp [sessionToRecordRecPending, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec] at hs
    rcases hsc₁ : s₁.state.senderChain with _ | c₁ <;>
      rcases hsc₂ : s₂.state.senderChain with _ | c₂
    · rfl
    · simp [hsc₁, hsc₂] at hs
    · simp [hsc₁, hsc₂] at hs
    · simp only [hsc₁, hsc₂, Option.map_some, Option.some.injEq] at hs
      exact congrArg some (senderChainToChainRec_injective hs)
  have hrc : s₁.state.receiverChains = s₂.state.receiverChains := by
    have hr := congrArg (·.receiverChains) hcur
    dsimp [sessionToRecordRecPending, Swarm.Phase0WholeFunctionBridge.sessionToSessionRec] at hr
    exact (List.map_injective_iff.mpr (fun _ _ => receiverChainToChainRec_injective)) hr
  have hver : s₁.state.sessionVersion = s₂.state.sessionVersion := congrArg (·.sessionVersion) hcur
  have hloc : s₁.state.localIdentity = s₂.state.localIdentity :=
    identityKey_serialize_injective (congrArg (·.localIdentityPublic) hcur)
  have hrem : s₁.state.remoteIdentity = s₂.state.remoteIdentity :=
    remoteIdentity_getD_injective (congrArg (·.remoteIdentityPublic) hcur)
  have hrk : s₁.state.rootKey = s₂.state.rootKey :=
    keyToBytes32_injective (congrArg (·.rootKey) hcur)
  have hpct : s₁.state.previousCounter = s₂.state.previousCounter :=
    congrArg (·.previousCounter) hcur
  have hpq : s₁.state.pqRatchetState = s₂.state.pqRatchetState :=
    congrArg (·.pqRatchetState) hcur
  have hrreg : s₁.remoteRegistrationId = s₂.remoteRegistrationId :=
    congrArg (·.remoteRegistrationId) hcur
  have hlreg : s₁.localRegistrationId = s₂.localRegistrationId :=
    congrArg (·.localRegistrationId) hcur
  have habk : s₁.aliceBaseKey = s₂.aliceBaseKey := congrArg (·.aliceBaseKey) hcur
  have hflag : s₁.state.pendingPreKey = s₂.state.pendingPreKey := by
    change s₁.state.pendingPreKey = s₂.state.pendingPreKey
    rw [hwf₁, hwf₂, hppk]
  rcases s₁ with ⟨⟨ver₁, loc₁, rem₁, rk₁, pct₁, sc₁, rc₁, flag₁, pq₁⟩,
    ppk₁, pkp₁, lreg₁, rreg₁, abk₁⟩
  rcases s₂ with ⟨⟨ver₂, loc₂, rem₂, rk₂, pct₂, sc₂, rc₂, flag₂, pq₂⟩,
    ppk₂, pkp₂, lreg₂, rreg₂, abk₂⟩
  dsimp at hver hloc hrem hrk hpct hsc hrc hflag hpq hppk hpkp hlreg hrreg habk
  subst hver; subst hloc; subst hrem; subst hrk; subst hpct; subst hsc; subst hrc
  subst hflag; subst hpq; subst hppk; subst hpkp; subst hlreg; subst hrreg; subst habk
  rfl

end Symbolic.Swarm.CREF.Cli.Slots
