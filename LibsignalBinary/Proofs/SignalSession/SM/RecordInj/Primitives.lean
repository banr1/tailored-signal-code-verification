/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalE2E.State
import LibsignalBinary.Proofs.ProtoCodecRoundTrip

/-!
# Prefix-Cancellation Primitives and Key Serialization Injectivity

Varint and field-tag lookahead (`peekTag`, `TagGe`), `ChainEq` field-peeling combinators
(`peel_uint32`, `peel_bytes`, `peel_msg`, `peel_repeated`), and fixed-width key serialization
injectivity.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.SM.RecordInj

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## Varint and Key Prefix Cancellation -/

theorem encodeVarint_append_inj {v₁ v₂ : BitVec 64} {r₁ r₂ : Bytes}
    (h : encodeVarint v₁ ++ r₁ = encodeVarint v₂ ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  have hdec := congrArg decodeVarint h
  rw [decodeVarint_encodeVarint, decodeVarint_encodeVarint] at hdec
  simpa using hdec

theorem encodeVarint_nat_append_inj {n₁ n₂ : ℕ} {r₁ r₂ : Bytes}
    (h₁ : n₁ < 2 ^ 64) (h₂ : n₂ < 2 ^ 64)
    (h : encodeVarint (BitVec.ofNat 64 n₁) ++ r₁ = encodeVarint (BitVec.ofNat 64 n₂) ++ r₂) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  obtain ⟨hv, hr⟩ := encodeVarint_append_inj h
  have hnat := congrArg BitVec.toNat hv
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hnat
  exact ⟨hnat, hr⟩

theorem uint32_setWidth64_inj {v₁ v₂ : BitVec 32}
    (h : v₁.setWidth 64 = v₂.setWidth 64) : v₁ = v₂ := by
  apply BitVec.eq_of_toNat_eq
  have hv := congrArg BitVec.toNat h
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth] at hv
  have := v₁.isLt
  have := v₂.isLt
  omega

theorem encodeKey_append_inj {tag : ℕ} {wt : WireType} {r₁ r₂ : Bytes}
    (h : encodeKey tag wt ++ r₁ = encodeKey tag wt ++ r₂) :
    r₁ = r₂ :=
  (encodeVarint_append_inj h).2

/-- Next protobuf field number at the front of `bs`, if a valid field key starts `bs`. -/
def peekTag (bs : Bytes) : Option ℕ :=
  (decodeKey bs).map (·.1.1)

theorem peekTag_encodeKey (tag : ℕ) (wt : WireType) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) :
    peekTag (encodeKey tag wt ++ rest) = some tag := by
  simp [peekTag, decodeKey_encodeKey tag wt rest h1 h2]

/-! ## Lower Bounds on Next Field Tag (`TagGe`) -/

/-- Either `peekTag bs` is `none` (e.g. end of buffer) or its tag is `≥ T`. -/
def TagGe (T : ℕ) (bs : Bytes) : Prop :=
  ∀ t, peekTag bs = some t → T ≤ t

theorem tagGe_nil (T : ℕ) : TagGe T [] := by
  intro _ h
  cases h

theorem peekTag_ne_of_tagGe {tag T : ℕ} {bs : Bytes}
    (hlt : tag < T) (hbs : TagGe T bs) : peekTag bs ≠ some tag := by
  intro h
  have := hbs tag h
  omega

theorem tagGe_lenField {T tag : ℕ} (b rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) :
    TagGe T (lenField tag b ++ rest) := by
  intro t ht
  simp only [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ h1 h2,
    Option.some.injEq] at ht
  omega

theorem tagGe_bytesField {T tag : ℕ} (v rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (bytesField tag v ++ rest) := by
  unfold bytesField
  split_ifs
  · simpa using hrest
  · exact tagGe_lenField v rest h1 h2 hle

theorem tagGe_uint32Field {T tag : ℕ} (v : BitVec 32) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (uint32Field tag v ++ rest) := by
  unfold uint32Field
  split_ifs
  · simpa using hrest
  · intro t ht
    simp only [List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2, Option.some.injEq] at ht
    omega

theorem tagGe_msgField {T tag : ℕ} (ov : Option Bytes) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (msgField tag ov ++ rest) := by
  cases ov with
  | none => simpa [msgField] using hrest
  | some body => exact tagGe_lenField body rest h1 h2 hle

theorem tagGe_flatten_lenField {α : Type} {T tag : ℕ} (enc : α → Bytes) (xs : List α)
    (rest : Bytes) (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T ((xs.map fun x => lenField tag (enc x)).flatten ++ rest) := by
  cases xs with
  | nil => simpa using hrest
  | cons x xs =>
    simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    exact tagGe_lenField (enc x) _ h1 h2 hle

/-! ## Length Bounds and Low-Level Field Prefix Cancellation -/

theorem length_le_lenField (tag : ℕ) (b : Bytes) :
    b.length ≤ (lenField tag b).length := by
  simp [lenField]
  omega

theorem length_le_bytesField (tag : ℕ) (v : Bytes) :
    v.length ≤ (bytesField tag v).length := by
  unfold bytesField
  split_ifs with hv
  · simp [hv]
  · exact length_le_lenField tag v

theorem length_le_flatten_lenField {α : Type} (tag : ℕ) (enc : α → Bytes) (xs : List α)
    {x : α} (hx : x ∈ xs) :
    (enc x).length ≤ ((xs.map fun y => lenField tag (enc y)).flatten).length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    rcases List.mem_cons.mp hx with rfl | hmem
    · have := length_le_lenField tag (enc x)
      omega
    · have := ih hmem
      omega

theorem lenField_append_inj {tag : ℕ} {b₁ b₂ r₁ r₂ : Bytes}
    (h₁ : b₁.length < 2 ^ 64) (h₂ : b₂.length < 2 ^ 64)
    (h : lenField tag b₁ ++ r₁ = lenField tag b₂ ++ r₂) :
    b₁ = b₂ ∧ r₁ = r₂ := by
  simp only [lenField, List.append_assoc] at h
  have h1 := encodeKey_append_inj h
  obtain ⟨hlen, hbr⟩ := encodeVarint_nat_append_inj h₁ h₂ h1
  exact List.append_inj hbr hlen

theorem bytesField_append_inj {tag : ℕ} {v₁ v₂ r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (h₁ : v₁.length < 2 ^ 64) (h₂ : v₂.length < 2 ^ 64)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : bytesField tag v₁ ++ r₁ = bytesField tag v₂ ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  unfold bytesField at h
  by_cases hv₁ : v₁ = [] <;> by_cases hv₂ : v₂ = []
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exact ⟨hv₁.trans hv₂.symm, h⟩
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₁
    rw [h]
    simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at h
    exfalso
    apply hr₂
    rw [← h]
    simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
  · simp only [hv₁, hv₂, ↓reduceIte] at h
    exact lenField_append_inj h₁ h₂ h

theorem uint32Field_append_inj {tag : ℕ} {v₁ v₂ : BitVec 32} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : uint32Field tag v₁ ++ r₁ = uint32Field tag v₂ ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  unfold uint32Field at h
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
    exact ⟨uint32_setWidth64_inj hw, hr⟩

theorem msgField_append_inj {tag : ℕ} {ov₁ ov₂ : Option Bytes} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (h₁ : ∀ b, ov₁ = some b → b.length < 2 ^ 64)
    (h₂ : ∀ b, ov₂ = some b → b.length < 2 ^ 64)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : msgField tag ov₁ ++ r₁ = msgField tag ov₂ ++ r₂) :
    ov₁ = ov₂ ∧ r₁ = r₂ := by
  cases ov₁ with
  | none =>
    cases ov₂ with
    | none => exact ⟨rfl, by simpa [msgField] using h⟩
    | some b₂ =>
      simp only [msgField, List.nil_append] at h
      exfalso
      apply hr₁
      rw [h]
      simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
  | some b₁ =>
    cases ov₂ with
    | none =>
      simp only [msgField, List.nil_append] at h
      exfalso
      apply hr₂
      rw [← h]
      simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
    | some b₂ =>
      simp only [msgField] at h
      obtain ⟨hb, hr⟩ := lenField_append_inj (h₁ b₁ rfl) (h₂ b₂ rfl) h
      exact ⟨congrArg some hb, hr⟩

theorem flatten_lenField_append_inj {α : Type} {tag : ℕ} (enc : α → Bytes)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hinj : ∀ x y, (enc x).length < 2 ^ 64 → enc x = enc y → x = y)
    {xs₁ xs₂ : List α} {r₁ r₂ : Bytes}
    (hlen₁ : ∀ x ∈ xs₁, (enc x).length < 2 ^ 64)
    (hlen₂ : ∀ y ∈ xs₂, (enc y).length < 2 ^ 64)
    (hr₁ : peekTag r₁ ≠ some tag) (hr₂ : peekTag r₂ ≠ some tag)
    (h : (xs₁.map fun x => lenField tag (enc x)).flatten ++ r₁ =
         (xs₂.map fun y => lenField tag (enc y)).flatten ++ r₂) :
    xs₁ = xs₂ ∧ r₁ = r₂ := by
  induction xs₁ generalizing xs₂ with
  | nil =>
    cases xs₂ with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons y ys =>
      simp only [List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, List.append_assoc] at h
      exfalso
      apply hr₁
      rw [h]
      simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
  | cons x xs ih =>
    cases xs₂ with
    | nil =>
      simp only [List.map_nil, List.flatten_nil, List.nil_append, List.map_cons,
        List.flatten_cons, List.append_assoc] at h
      exfalso
      apply hr₂
      rw [← h]
      simp [lenField, List.append_assoc, peekTag_encodeKey tag .lengthDelimited _ htag1 htag2]
    | cons y ys =>
      simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
      have hxlen : (enc x).length < 2 ^ 64 := hlen₁ x List.mem_cons_self
      have hylen : (enc y).length < 2 ^ 64 := hlen₂ y List.mem_cons_self
      obtain ⟨henc, htail⟩ := lenField_append_inj hxlen hylen h
      obtain ⟨hxs, hr⟩ := ih
        (fun a ha => hlen₁ a (List.mem_cons_of_mem x ha))
        (fun b hb => hlen₂ b (List.mem_cons_of_mem y hb))
        htail
      exact ⟨congrArg₂ List.cons (hinj x y hxlen henc) hxs, hr⟩

/-! ## High-Level `ChainEq` Field Peeling Combinators -/

/-- Equal byte streams of length `< 2 ^ 64` (threads both equality and the varint length bound). -/
def ChainEq (bs₁ bs₂ : Bytes) : Prop :=
  bs₁ = bs₂ ∧ bs₁.length < 2 ^ 64

theorem peel_uint32 {tag : ℕ} {v₁ v₂ : BitVec 32} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (uint32Field tag v₁ ++ r₁) (uint32Field tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  obtain ⟨hv, hr⟩ := uint32Field_append_inj htag1 htag2
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  rw [List.length_append] at hlen
  exact ⟨hv, hr, by omega⟩

theorem peel_bytes {tag : ℕ} {v₁ v₂ r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (bytesField tag v₁ ++ r₁) (bytesField tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen₁⟩ := hc
  have hlen₂ : (bytesField tag v₂ ++ r₂).length < 2 ^ 64 := heq ▸ hlen₁
  rw [List.length_append] at hlen₁ hlen₂
  have hb₁ := length_le_bytesField tag v₁
  have hb₂ := length_le_bytesField tag v₂
  obtain ⟨hv, hr⟩ := bytesField_append_inj htag1 htag2 (by omega) (by omega)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  exact ⟨hv, hr, by omega⟩

theorem peel_msg {α : Type} {tag : ℕ} (enc : α → Bytes)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hinj : ∀ x y, (enc x).length < 2 ^ 64 → enc x = enc y → x = y)
    {o₁ o₂ : Option α} {r₁ r₂ : Bytes}
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (msgField tag (o₁.map enc) ++ r₁) (msgField tag (o₂.map enc) ++ r₂)) :
    o₁ = o₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen₁⟩ := hc
  have hlen₂ : (msgField tag (o₂.map enc) ++ r₂).length < 2 ^ 64 := heq ▸ hlen₁
  rw [List.length_append] at hlen₁ hlen₂
  have hb₁ : ∀ b, o₁.map enc = some b → b.length < 2 ^ 64 := by
    intro b hb
    rw [hb, msgField] at hlen₁
    have := length_le_lenField tag b
    omega
  have hb₂ : ∀ b, o₂.map enc = some b → b.length < 2 ^ 64 := by
    intro b hb
    rw [hb, msgField] at hlen₂
    have := length_le_lenField tag b
    omega
  obtain ⟨hov, hr⟩ := msgField_append_inj htag1 htag2 hb₁ hb₂
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  refine ⟨?_, hr, by omega⟩
  cases o₁ with
  | none =>
    cases o₂ with
    | none => rfl
    | some y => cases hov
  | some x =>
    cases o₂ with
    | none => cases hov
    | some y =>
      simp only [Option.map_some, Option.some.injEq] at hov
      exact congrArg some (hinj x y (hb₁ (enc x) rfl) hov)

theorem peel_repeated {α : Type} {tag : ℕ} (enc : α → Bytes)
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hinj : ∀ x y, (enc x).length < 2 ^ 64 → enc x = enc y → x = y)
    {xs₁ xs₂ : List α} {r₁ r₂ : Bytes}
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq ((xs₁.map fun x => lenField tag (enc x)).flatten ++ r₁)
                  ((xs₂.map fun y => lenField tag (enc y)).flatten ++ r₂)) :
    xs₁ = xs₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen₁⟩ := hc
  have hlen₂ : ((xs₂.map fun y => lenField tag (enc y)).flatten ++ r₂).length < 2 ^ 64 :=
    heq ▸ hlen₁
  rw [List.length_append] at hlen₁ hlen₂
  have hx₁ : ∀ x ∈ xs₁, (enc x).length < 2 ^ 64 := by
    intro x hx
    have := length_le_flatten_lenField tag enc xs₁ hx
    omega
  have hx₂ : ∀ y ∈ xs₂, (enc y).length < 2 ^ 64 := by
    intro y hy
    have := length_le_flatten_lenField tag enc xs₂ hy
    omega
  obtain ⟨hxs, hr⟩ := flatten_lenField_append_inj enc htag1 htag2 hinj hx₁ hx₂
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁)
    (peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂) heq
  exact ⟨hxs, hr, by omega⟩

/-! ## Fixed-Width Key Serialization Injectivity -/

theorem publicKey_serialize_inj {k₁ k₂ : PublicKey}
    (h : k₁.serialize = k₂.serialize) : k₁ = k₂ := by
  cases k₁ with | mk b₁ =>
  cases k₂ with | mk b₂ =>
  simp only [PublicKey.serialize, List.cons.injEq, true_and] at h
  exact congrArg PublicKey.mk (List.Vector.eq b₁ b₂ h)

theorem identityKey_serialize_inj {k₁ k₂ : IdentityKey}
    (h : k₁.serialize = k₂.serialize) : k₁ = k₂ := by
  cases k₁ with | mk p₁ =>
  cases k₂ with | mk p₂ =>
  exact congrArg IdentityKey.mk (publicKey_serialize_inj h)

theorem privateKey_toList_inj {k₁ k₂ : PrivateKey}
    (h : k₁.bytes.toList = k₂.bytes.toList) : k₁ = k₂ := by
  cases k₁ with | mk b₁ =>
  cases k₂ with | mk b₂ =>
  exact congrArg PrivateKey.mk (List.Vector.eq b₁ b₂ h)

theorem keyToBytes32_inj {k₁ k₂ : BitVec 256}
    (h : HMAC.keyToBytes32 k₁ = HMAC.keyToBytes32 k₂) : k₁ = k₂ := by
  have hf := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hbyte := congrArg (·.getLsbD (b % 8)) (congrFun hf ⟨b / 8, by omega⟩)
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega, decide_true,
    Bool.true_and] at hbyte
  simpa [show 8 * (b / 8) + b % 8 = b by omega] using hbyte

end CryptoVerification.SignalSession.SM.RecordInj
