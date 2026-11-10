/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Refinement.EncodeWithCovered
import Symbolic.Proofs.Swarm.CREF.Prelude
import VCVio.EvalDist.ProbabilityNotation

/-!
# Session-Record Encoding Injectivity Modulo Pending Pre-Key Normalization

Proves `recordBytes_injective` (equal `recordBytes` encodings imply equal `normPending` records,
where `normPending` normalizes each pending pre-key pair `p` to `(p.1 ++ p.2, [])`) and derives
`keyInRecord_of_recordBytes_eq` transferring `KeyInRecord` across equal `recordBytes`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

section RecordBytes

open DY.Libsignal.Refinement (PbValue encodeField readVarint paddedVarint readVarint_paddedVarint)

/-- Normalizes each pending pre-key pair `p` of `s` to `(p.1 ++ p.2, [])`. -/
def normPendingS (s : SessionRec) : SessionRec :=
  { s with pendingPreKey := s.pendingPreKey.map fun p => (p.1 ++ p.2, [])
           pendingKyberPreKey := s.pendingKyberPreKey.map fun p => (p.1 ++ p.2, []) }

/-- `normPendingS` on the current session of a record. -/
def normPending (rec : RecordRec) : RecordRec := { rec with current := normPendingS rec.current }

private def pbFields (l : List (Nat × PbValue)) : HwBytes :=
  l.flatMap (fun p => encodeField p.1 0 0 p.2)

private def PbOk (p : Nat × PbValue) : Prop :=
  match p.2 with
  | .varint _ | .bytes _ => True
  | .unknown _ _ => False

private theorem readVarint_encodeField_varint (tag : Nat) (n : Nat) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.varint n) ++ rest) =
      some (tag * 8, paddedVarint n 0 ++ rest) := by
  rw [encodeField, List.append_assoc, readVarint_paddedVarint]

private theorem readVarint_encodeField_bytes (tag : Nat) (b : HwBytes) (rest : HwBytes) :
    readVarint (encodeField tag 0 0 (.bytes b) ++ rest) =
      some (tag * 8 + 2, paddedVarint b.length 0 ++ (b ++ rest)) := by
  rw [encodeField, List.append_assoc, List.append_assoc, readVarint_paddedVarint]

private theorem encodeField_append_ne_nil {t : Nat} {v : PbValue} (rest : HwBytes)
    (hok : PbOk (t, v)) : encodeField t 0 0 v ++ rest ≠ [] := by
  intro h
  cases v with
  | varint n => have hr := readVarint_encodeField_varint t n rest; rw [h] at hr; nomatch hr
  | bytes b => have hr := readVarint_encodeField_bytes t b rest; rw [h] at hr; nomatch hr
  | unknown _ _ => exact hok

private theorem pbFields_inj {l₁ l₂ : List (Nat × PbValue)}
    (h₁ : ∀ x ∈ l₁, PbOk x) (h₂ : ∀ x ∈ l₂, PbOk x) (h : pbFields l₁ = pbFields l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons p₂ rest₂ =>
      exact absurd h.symm (encodeField_append_ne_nil (pbFields rest₂) (h₂ p₂ (by simp)))
  | cons p₁ rest₁ ih =>
    cases l₂ with
    | nil =>
      exact absurd h (encodeField_append_ne_nil (pbFields rest₁) (h₁ p₁ (by simp)))
    | cons p₂ rest₂ =>
      obtain ⟨t₁, v₁⟩ := p₁; obtain ⟨t₂, v₂⟩ := p₂
      have hok₁ := h₁ (t₁, v₁) (by simp); have hok₂ := h₂ (t₂, v₂) (by simp)
      change encodeField t₁ 0 0 v₁ ++ pbFields rest₁ =
        encodeField t₂ 0 0 v₂ ++ pbFields rest₂ at h
      cases v₁ with
      | unknown _ _ => contradiction
      | varint n₁ =>
        have hr₁ := readVarint_encodeField_varint t₁ n₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => contradiction
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂; injection hr₂ with hp; injection hp with hk; omega
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂; injection hr₂ with hp; injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint n₁ (pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint n₂ (pbFields rest₂)
          rw [hrest'] at hrp₁; rw [hrp₁] at hrp₂; injection hrp₂ with hp'; injection hp' with hn hr
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr
          subst t₁; subst n₁; subst rest₁; rfl
      | bytes b₁ =>
        have hr₁ := readVarint_encodeField_bytes t₁ b₁ (pbFields rest₁)
        cases v₂ with
        | unknown _ _ => contradiction
        | varint n₂ =>
          have hr₂ := readVarint_encodeField_varint t₂ n₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂; injection hr₂ with hp; injection hp with hk; omega
        | bytes b₂ =>
          have hr₂ := readVarint_encodeField_bytes t₂ b₂ (pbFields rest₂)
          rw [h] at hr₁; rw [hr₁] at hr₂; injection hr₂ with hp; injection hp with hk hrest'
          have ht : t₁ = t₂ := by omega
          have hrp₁ := readVarint_paddedVarint b₁.length (b₁ ++ pbFields rest₁)
          have hrp₂ := readVarint_paddedVarint b₂.length (b₂ ++ pbFields rest₂)
          rw [hrest'] at hrp₁; rw [hrp₁] at hrp₂; injection hrp₂ with hp'; injection hp' with hlen happ
          obtain ⟨hb, hr⟩ := List.append_inj happ hlen
          have hrest_eq := ih (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
                              (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr
          subst t₁; subst b₁; subst rest₁; rfl

private theorem pbFields_append (l₁ l₂ : List (Nat × PbValue)) :
    pbFields (l₁ ++ l₂) = pbFields l₁ ++ pbFields l₂ := by simp [pbFields, List.flatMap_append]

private def bytesFieldList (tag : Nat) (b : HwBytes) : List (Nat × PbValue) :=
  if b = [] then [] else [(tag, .bytes b)]

private def u32FieldList (tag : Nat) (v : BitVec 32) : List (Nat × PbValue) :=
  if v = 0 then [] else [(tag, .varint v.toNat)]

private theorem pbFields_bytesFieldList (tag : Nat) (b : HwBytes) :
    pbFields (bytesFieldList tag b) = bytesField tag b := by
  unfold bytesFieldList bytesField; split <;> simp [pbFields]

private theorem pbFields_u32FieldList (tag : Nat) (v : BitVec 32) :
    pbFields (u32FieldList tag v) = u32Field tag v := by
  unfold u32FieldList u32Field; split <;> simp [pbFields]

private theorem bytesFieldList_inj {tag₁ tag₂ : Nat} {b₁ b₂ : HwBytes}
    (h : bytesFieldList tag₁ b₁ = bytesFieldList tag₂ b₂) : b₁ = b₂ := by
  unfold bytesFieldList at h
  by_cases h₁ : b₁ = [] <;> by_cases h₂ : b₂ = [] <;> simp_all

private theorem u32FieldList_inj {tag₁ tag₂ : Nat} {v₁ v₂ : BitVec 32}
    (h : u32FieldList tag₁ v₁ = u32FieldList tag₂ v₂) : v₁ = v₂ := by
  unfold u32FieldList at h
  by_cases h₁ : v₁ = 0 <;> by_cases h₂ : v₂ = 0
  · rw [h₁, h₂]
  · simp [h₁] at h; contradiction
  · simp [h₂] at h; contradiction
  · simp only [h₁, h₂, ↓reduceIte, List.cons.injEq, Prod.mk.injEq, PbValue.varint.injEq, and_true] at h
    exact BitVec.eq_of_toNat_eq h.2

private theorem pbOk_bytesFieldList (tag : Nat) (b : HwBytes) :
    ∀ x ∈ bytesFieldList tag b, PbOk x := by
  intro x hx; unfold bytesFieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; trivial

private theorem pbOk_u32FieldList (tag : Nat) (v : BitVec 32) :
    ∀ x ∈ u32FieldList tag v, PbOk x := by
  intro x hx; unfold u32FieldList at hx; split at hx
  · cases hx
  · simp only [List.mem_singleton] at hx; subst hx; trivial

private theorem pbOk_append {l₁ l₂ : List (Nat × PbValue)}
    (h₁ : ∀ x ∈ l₁, PbOk x) (h₂ : ∀ x ∈ l₂, PbOk x) : ∀ x ∈ l₁ ++ l₂, PbOk x := by
  intro x hx; rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

private theorem list_map_inj {α β : Type} {f : α → β} (h : ∀ x y, f x = f y → x = y)
    {l₁ l₂ : List α} (heq : l₁.map f = l₂.map f) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> first | rfl | contradiction
  | cons x xs ih =>
    cases l₂ with
    | nil => contradiction
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at heq
      rw [h x y heq.1, ih heq.2]

private theorem filter_bytesFieldList_ne {tag t : Nat} (h : (tag == t) = false) (b : HwBytes) :
    (bytesFieldList tag b).filter (fun p => p.1 == t) = [] := by
  unfold bytesFieldList; split <;> simp [h]

private theorem filter_bytesFieldList_self (tag : Nat) (b : HwBytes) :
    (bytesFieldList tag b).filter (fun p => p.1 == tag) = bytesFieldList tag b := by
  unfold bytesFieldList; split <;> simp

private theorem filter_u32FieldList_ne {tag t : Nat} (h : (tag == t) = false) (v : BitVec 32) :
    (u32FieldList tag v).filter (fun p => p.1 == t) = [] := by
  unfold u32FieldList; split <;> simp [h]

private theorem filter_u32FieldList_self (tag : Nat) (v : BitVec 32) :
    (u32FieldList tag v).filter (fun p => p.1 == tag) = u32FieldList tag v := by
  unfold u32FieldList; split <;> simp

private theorem filter_option_bytes_ne {α : Type} {tag t : Nat} (h : (tag == t) = false)
    (f : α → HwBytes) (o : Option α) :
    ((o.map fun x => [(tag, PbValue.bytes (f x))]).getD []).filter (fun p => p.1 == t) = [] := by
  cases o <;> simp [h]

private theorem filter_option_bytes_self {α : Type} (tag : Nat) (f : α → HwBytes) (o : Option α) :
    ((o.map fun x => [(tag, PbValue.bytes (f x))]).getD []).filter (fun p => p.1 == tag) =
    (o.map fun x => [(tag, PbValue.bytes (f x))]).getD [] := by
  cases o <;> simp

private theorem filter_map_bytes_ne {α : Type} {tag t : Nat} (h : (tag == t) = false)
    (f : α → HwBytes) (l : List α) :
    (l.map fun x => (tag, PbValue.bytes (f x))).filter (fun p => p.1 == t) = [] := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [h, ih]

private theorem filter_map_bytes_self {α : Type} (tag : Nat) (f : α → HwBytes) (l : List α) :
    (l.map fun x => (tag, PbValue.bytes (f x))).filter (fun p => p.1 == tag) =
    l.map fun x => (tag, PbValue.bytes (f x)) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [ih]

private theorem option_bytes_inj {α : Type} {tag : Nat} {f : α → HwBytes}
    (hf : ∀ x y, f x = f y → x = y) {o₁ o₂ : Option α}
    (h : (o₁.map fun x => [(tag, PbValue.bytes (f x))]).getD [] =
         (o₂.map fun x => [(tag, PbValue.bytes (f x))]).getD []) : o₁ = o₂ := by
  cases o₁ with
  | none => cases o₂ <;> first | rfl | cases h
  | some x =>
    cases o₂ with
    | none => cases h
    | some y =>
      simp only [Option.map_some, Option.getD_some, List.cons.injEq, Prod.mk.injEq,
        PbValue.bytes.injEq, and_true] at h
      rw [hf x y h.2]

private def chainKeyFields (k : BitVec 32 × List (BitVec 8)) : List (Nat × PbValue) :=
  u32FieldList 1 k.1 ++ bytesFieldList 2 k.2

private theorem pbFields_chainKeyFields (k : BitVec 32 × List (BitVec 8)) :
    pbFields (chainKeyFields k) = u32Field 1 k.1 ++ bytesField 2 k.2 := by
  simp [chainKeyFields, pbFields_append, pbFields_u32FieldList, pbFields_bytesFieldList]

private theorem pbOk_chainKeyFields (k : BitVec 32 × List (BitVec 8)) :
    ∀ x ∈ chainKeyFields k, PbOk x :=
  pbOk_append (pbOk_u32FieldList 1 k.1) (pbOk_bytesFieldList 2 k.2)

private theorem chainKey_injective {k₁ k₂ : BitVec 32 × List (BitVec 8)}
    (h : u32Field 1 k₁.1 ++ bytesField 2 k₁.2 = u32Field 1 k₂.1 ++ bytesField 2 k₂.2) :
    k₁ = k₂ := by
  have h1 : pbFields (chainKeyFields k₁) = pbFields (chainKeyFields k₂) := by
    rw [pbFields_chainKeyFields, pbFields_chainKeyFields, h]
  have h2 := pbFields_inj (pbOk_chainKeyFields k₁) (pbOk_chainKeyFields k₂) h1
  have hf1 := congrArg (List.filter (fun p => p.1 == 1)) h2
  have hf2 := congrArg (List.filter (fun p => p.1 == 2)) h2
  simp [chainKeyFields, List.filter_append, filter_u32FieldList_ne, filter_u32FieldList_self,
    filter_bytesFieldList_ne, filter_bytesFieldList_self] at hf1 hf2
  exact Prod.ext (u32FieldList_inj hf1) (bytesFieldList_inj hf2)

private def msgKeyFields (k : BitVec 32 × List (BitVec 8)) : List (Nat × PbValue) :=
  u32FieldList 1 k.1 ++ bytesFieldList 5 k.2

private theorem pbFields_msgKeyFields (k : BitVec 32 × List (BitVec 8)) :
    pbFields (msgKeyFields k) = u32Field 1 k.1 ++ bytesField 5 k.2 := by
  simp [msgKeyFields, pbFields_append, pbFields_u32FieldList, pbFields_bytesFieldList]

private theorem pbOk_msgKeyFields (k : BitVec 32 × List (BitVec 8)) :
    ∀ x ∈ msgKeyFields k, PbOk x :=
  pbOk_append (pbOk_u32FieldList 1 k.1) (pbOk_bytesFieldList 5 k.2)

private theorem msgKey_injective {k₁ k₂ : BitVec 32 × List (BitVec 8)}
    (h : u32Field 1 k₁.1 ++ bytesField 5 k₁.2 = u32Field 1 k₂.1 ++ bytesField 5 k₂.2) :
    k₁ = k₂ := by
  have h1 : pbFields (msgKeyFields k₁) = pbFields (msgKeyFields k₂) := by
    rw [pbFields_msgKeyFields, pbFields_msgKeyFields, h]
  have h2 := pbFields_inj (pbOk_msgKeyFields k₁) (pbOk_msgKeyFields k₂) h1
  have hf1 := congrArg (List.filter (fun p => p.1 == 1)) h2
  have hf5 := congrArg (List.filter (fun p => p.1 == 5)) h2
  simp [msgKeyFields, List.filter_append, filter_u32FieldList_ne, filter_u32FieldList_self,
    filter_bytesFieldList_ne, filter_bytesFieldList_self] at hf1 hf5
  exact Prod.ext (u32FieldList_inj hf1) (bytesFieldList_inj hf5)

private theorem pbFields_map_msgField4 (l : List (BitVec 32 × List (BitVec 8))) :
    pbFields (l.map fun k => (4, PbValue.bytes (u32Field 1 k.1 ++ bytesField 5 k.2))) =
    l.flatMap fun k => msgField 4 (u32Field 1 k.1 ++ bytesField 5 k.2) := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, pbFields, List.flatMap_cons, msgField]; congr 1

private def chainFields (c : ChainRec) : List (Nat × PbValue) :=
  bytesFieldList 1 c.senderRatchetKey ++
  bytesFieldList 2 c.senderRatchetKeyPrivate ++
  ((c.chainKey.map fun k => [(3, PbValue.bytes (u32Field 1 k.1 ++ bytesField 2 k.2))]).getD []) ++
  c.messageKeys.map fun k => (4, PbValue.bytes (u32Field 1 k.1 ++ bytesField 5 k.2))

private theorem pbFields_chainFields (c : ChainRec) : pbFields (chainFields c) = chainBytes c := by
  unfold chainFields chainBytes
  repeat rw [pbFields_append]
  rw [pbFields_bytesFieldList, pbFields_bytesFieldList]
  congr 1; congr 1
  · cases c.chainKey <;> simp [pbFields, msgField]
  · exact pbFields_map_msgField4 c.messageKeys

private theorem pbOk_chainFields (c : ChainRec) : ∀ x ∈ chainFields c, PbOk x := by
  unfold chainFields; repeat apply pbOk_append
  · exact pbOk_bytesFieldList 1 c.senderRatchetKey
  · exact pbOk_bytesFieldList 2 c.senderRatchetKeyPrivate
  · cases c.chainKey with
    | none => simp
    | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
  · intro x hx; rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; trivial

private theorem chainBytes_injective {c₁ c₂ : ChainRec}
    (h : chainBytes c₁ = chainBytes c₂) : c₁ = c₂ := by
  have h1 : pbFields (chainFields c₁) = pbFields (chainFields c₂) := by
    rw [pbFields_chainFields, pbFields_chainFields, h]
  have h2 := pbFields_inj (pbOk_chainFields c₁) (pbOk_chainFields c₂) h1
  have hf1 := congrArg (List.filter (fun p => p.1 == 1)) h2
  have hf2 := congrArg (List.filter (fun p => p.1 == 2)) h2
  have hf3 := congrArg (List.filter (fun p => p.1 == 3)) h2
  have hf4 := congrArg (List.filter (fun p => p.1 == 4)) h2
  simp [chainFields, List.filter_append, filter_bytesFieldList_ne, filter_bytesFieldList_self,
    filter_option_bytes_ne, filter_option_bytes_self,
    filter_map_bytes_ne, filter_map_bytes_self] at hf1 hf2 hf3 hf4
  have heq3 := option_bytes_inj (fun _ _ => chainKey_injective) hf3
  have heq4 := list_map_inj (f := fun k => (4, PbValue.bytes (u32Field 1 k.1 ++ bytesField 5 k.2)))
    (fun _ _ hxy => msgKey_injective (by simpa using hxy)) hf4
  cases c₁; cases c₂; simp only [ChainRec.mk.injEq]
  exact ⟨bytesFieldList_inj hf1, bytesFieldList_inj hf2, heq3, heq4⟩

private def sessionBytes (s : SessionRec) : HwBytes :=
  u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
  bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
  u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
  s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
  ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
  u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId ++
  bytesField 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++
  bytesField 15 s.pqRatchetState

private theorem pbFields_map_msgField7 (l : List ChainRec) :
    pbFields (l.map fun c => (7, PbValue.bytes (chainBytes c))) =
    l.flatMap (msgField 7 ∘ chainBytes) := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    simp only [List.map_cons, pbFields, List.flatMap_cons, msgField, Function.comp_apply]; congr 1

private def sessionFields (s : SessionRec) : List (Nat × PbValue) :=
  u32FieldList 1 s.sessionVersion ++
  bytesFieldList 2 s.localIdentityPublic ++
  bytesFieldList 3 s.remoteIdentityPublic ++
  bytesFieldList 4 s.rootKey ++
  u32FieldList 5 s.previousCounter ++
  ((s.senderChain.map (fun c => [(6, PbValue.bytes (chainBytes c))])).getD []) ++
  s.receiverChains.map (fun c => (7, PbValue.bytes (chainBytes c))) ++
  ((s.pendingPreKey.map (fun p => [(9, PbValue.bytes (p.1 ++ p.2))])).getD []) ++
  u32FieldList 10 s.remoteRegistrationId ++
  u32FieldList 11 s.localRegistrationId ++
  bytesFieldList 13 s.aliceBaseKey ++
  ((s.pendingKyberPreKey.map (fun p => [(14, PbValue.bytes (p.1 ++ p.2))])).getD []) ++
  bytesFieldList 15 s.pqRatchetState

private theorem pbFields_sessionFields (s : SessionRec) :
    pbFields (sessionFields s) = sessionBytes s := by
  unfold sessionFields sessionBytes
  repeat rw [pbFields_append]
  rw [pbFields_u32FieldList, pbFields_bytesFieldList, pbFields_bytesFieldList,
      pbFields_bytesFieldList, pbFields_u32FieldList, pbFields_map_msgField7,
      pbFields_u32FieldList, pbFields_u32FieldList, pbFields_bytesFieldList, pbFields_bytesFieldList]
  cases s.senderChain <;> cases s.pendingPreKey <;> cases s.pendingKyberPreKey <;>
    simp [pbFields, msgField]

private theorem pbOk_sessionFields (s : SessionRec) : ∀ x ∈ sessionFields s, PbOk x := by
  unfold sessionFields; repeat apply pbOk_append
  · exact pbOk_u32FieldList 1 s.sessionVersion
  · exact pbOk_bytesFieldList 2 s.localIdentityPublic
  · exact pbOk_bytesFieldList 3 s.remoteIdentityPublic
  · exact pbOk_bytesFieldList 4 s.rootKey
  · exact pbOk_u32FieldList 5 s.previousCounter
  · cases s.senderChain with
    | none => simp
    | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
  · intro x hx; rcases List.mem_map.mp hx with ⟨_, _, rfl⟩; trivial
  · cases s.pendingPreKey with
    | none => simp
    | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
  · exact pbOk_u32FieldList 10 s.remoteRegistrationId
  · exact pbOk_u32FieldList 11 s.localRegistrationId
  · exact pbOk_bytesFieldList 13 s.aliceBaseKey
  · cases s.pendingKyberPreKey with
    | none => simp
    | some _ => intro x hx; simp only [Option.map_some, Option.getD_some, List.mem_singleton] at hx; subst hx; trivial
  · exact pbOk_bytesFieldList 15 s.pqRatchetState

private theorem option_bytes_map_eq {α : Type} {tag : Nat} {f : α → HwBytes} {o₁ o₂ : Option α}
    (h : (o₁.map fun x => [(tag, PbValue.bytes (f x))]).getD [] =
         (o₂.map fun x => [(tag, PbValue.bytes (f x))]).getD []) : o₁.map f = o₂.map f := by
  cases o₁ with
  | none => cases o₂ <;> first | rfl | cases h
  | some x =>
    cases o₂ with
    | none => cases h
    | some y =>
      simp only [Option.map_some, Option.getD_some, List.cons.injEq, Prod.mk.injEq,
        PbValue.bytes.injEq, and_true, true_and] at h
      simp only [Option.map_some, h]

private theorem pending_norm_eq {o₁ o₂ : Option (List (BitVec 8) × List (BitVec 8))}
    (h : o₁.map (fun p => p.1 ++ p.2) = o₂.map (fun p => p.1 ++ p.2)) :
    o₁.map (fun p => (p.1 ++ p.2, ([] : List (BitVec 8)))) =
    o₂.map (fun p => (p.1 ++ p.2, ([] : List (BitVec 8)))) := by
  have := congrArg (Option.map fun b => (b, ([] : List (BitVec 8)))) h
  simpa [Option.map_map, Function.comp_def] using this

private theorem sessionBytes_injective {s₁ s₂ : SessionRec}
    (h : sessionBytes s₁ = sessionBytes s₂) : normPendingS s₁ = normPendingS s₂ := by
  have h1 : pbFields (sessionFields s₁) = pbFields (sessionFields s₂) := by
    rw [pbFields_sessionFields, pbFields_sessionFields, h]
  have h2 := pbFields_inj (pbOk_sessionFields s₁) (pbOk_sessionFields s₂) h1
  have hf1 := congrArg (List.filter (fun p => p.1 == 1)) h2
  have hf2 := congrArg (List.filter (fun p => p.1 == 2)) h2
  have hf3 := congrArg (List.filter (fun p => p.1 == 3)) h2
  have hf4 := congrArg (List.filter (fun p => p.1 == 4)) h2
  have hf5 := congrArg (List.filter (fun p => p.1 == 5)) h2
  have hf6 := congrArg (List.filter (fun p => p.1 == 6)) h2
  have hf7 := congrArg (List.filter (fun p => p.1 == 7)) h2
  have hf9 := congrArg (List.filter (fun p => p.1 == 9)) h2
  have hf10 := congrArg (List.filter (fun p => p.1 == 10)) h2
  have hf11 := congrArg (List.filter (fun p => p.1 == 11)) h2
  have hf13 := congrArg (List.filter (fun p => p.1 == 13)) h2
  have hf14 := congrArg (List.filter (fun p => p.1 == 14)) h2
  have hf15 := congrArg (List.filter (fun p => p.1 == 15)) h2
  simp [sessionFields, List.filter_append,
    filter_u32FieldList_ne, filter_u32FieldList_self,
    filter_bytesFieldList_ne, filter_bytesFieldList_self,
    filter_option_bytes_ne, filter_option_bytes_self,
    filter_map_bytes_ne, filter_map_bytes_self] at hf1 hf2 hf3 hf4 hf5 hf6 hf7 hf9 hf10 hf11 hf13 hf14 hf15
  have heq6 := option_bytes_inj (fun _ _ => chainBytes_injective) hf6
  have heq7 := list_map_inj (f := fun c => (7, PbValue.bytes (chainBytes c)))
    (fun _ _ hxy => chainBytes_injective (by simpa using hxy)) hf7
  have heq9 := pending_norm_eq (option_bytes_map_eq hf9)
  have heq14 := pending_norm_eq (option_bytes_map_eq hf14)
  cases s₁; cases s₂; simp only [normPendingS, SessionRec.mk.injEq]
  exact ⟨u32FieldList_inj hf1, bytesFieldList_inj hf2, bytesFieldList_inj hf3,
    bytesFieldList_inj hf4, u32FieldList_inj hf5, heq6, heq7, heq9, heq14,
    u32FieldList_inj hf10, u32FieldList_inj hf11, bytesFieldList_inj hf13, bytesFieldList_inj hf15⟩

private def recordFields (rec : RecordRec) : List (Nat × PbValue) :=
  (1, PbValue.bytes (sessionBytes rec.current)) :: rec.previous.map (fun p => (2, PbValue.bytes p))

private theorem pbFields_recordFields (rec : RecordRec) :
    pbFields (recordFields rec) = recordBytes rec := by
  unfold recordFields recordBytes sessionBytes
  simp only [pbFields, List.flatMap_cons, msgField]
  congr 1
  induction rec.previous with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.flatMap_cons, msgField]; congr 1

private theorem pbOk_recordFields (rec : RecordRec) : ∀ x ∈ recordFields rec, PbOk x := by
  intro x hx; simp only [recordFields, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨_, _, rfl⟩ <;> trivial

/-- `recordBytes` is injective up to `normPending`. -/
theorem recordBytes_injective {r₁ r₂ : RecordRec} (h : recordBytes r₁ = recordBytes r₂) :
    normPending r₁ = normPending r₂ := by
  have h1 : pbFields (recordFields r₁) = pbFields (recordFields r₂) := by
    rw [pbFields_recordFields, pbFields_recordFields, h]
  have h2 := pbFields_inj (pbOk_recordFields r₁) (pbOk_recordFields r₂) h1
  simp only [recordFields, List.cons.injEq, Prod.mk.injEq, PbValue.bytes.injEq] at h2
  have hcurr := sessionBytes_injective h2.1.2
  have hprev := list_map_inj (f := fun p => (2, PbValue.bytes p))
    (fun _ _ hxy => by simpa using hxy) h2.2
  cases r₁; cases r₂; simp only [normPending, RecordRec.mk.injEq]; exact ⟨hcurr, hprev⟩

theorem keyInRecord_normPending (rec : RecordRec) (k : HwBytes) :
    KeyInRecord (normPending rec) k ↔ KeyInRecord rec k := Iff.rfl

/-- `KeyInRecord` transfers along equal `recordBytes`. -/
theorem keyInRecord_of_recordBytes_eq {r₁ r₂ : RecordRec} {k : HwBytes}
    (h : recordBytes r₁ = recordBytes r₂) (hk : KeyInRecord r₁ k) : KeyInRecord r₂ k := by
  have hn := recordBytes_injective h
  rw [← keyInRecord_normPending] at hk ⊢
  rw [← hn]; exact hk

end RecordBytes

end Symbolic.Swarm.CREF.TR
