/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.PqDir
import all Init.Data.Repr
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip
import LibsignalBinary.Proofs.SignalSession.SM.RecordInj.Fields

/-!
# Pure Model `CliRun` Satisfying `CliSpecPqxdh`

**Checked by Lean.**

Defines `pqModelRun X W : CliRun` and proves `cliSpecPq_pqModelRun X W : CliSpecPqxdh (pqModelRun X W) X W`
for every `(X : UnreachedPqxdhPrimitives) (W : PEParams)`:
1. The five witness predicates (`InitWitness`, `SendWitness`, `RecvWhisperWitness`,
   `RecvPrekeyWitness`, `RecvOtherWitness`) partition `CliSpecPqxdh` inputs by `(i.argv.head?, i.stdin.head?)`.
2. Within each branch, `pqxdhExpectedOutcome` is independent of the witness via
   `PreKeyMessageFields.bytes_inj`, path-prefix separation of `PublicBundle.files` and `encodeDir`,
   and `SM.RecordInj` protobuf peeling on `encStateUnderExtras` (including `pendingPreKey = false`
   extras erasure).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession.SM.RecordInj

/-! ## 1. Low-level list, integer, and fixed-width key injectivity -/

private theorem snoc_inj {α : Type} {xs₁ xs₂ : List α} {a₁ a₂ : α}
    (h : xs₁ ++ [a₁] = xs₂ ++ [a₂]) : xs₁ = xs₂ ∧ a₁ = a₂ := by
  have hlen : xs₁.length = xs₂.length := by
    have hl := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hl
    omega
  obtain ⟨hxs, ha⟩ := List.append_inj h hlen
  exact ⟨hxs, List.singleton_inj.mp ha⟩

private theorem le32_inj {a b : BitVec 32} (h : le32 a = le32 b) : a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [le32, List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  have e0 := congrArg BitVec.toNat h0
  have e1 := congrArg BitVec.toNat h1
  have e2 := congrArg BitVec.toNat h2
  have e3 := congrArg BitVec.toNat h3
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.reducePow] at e0 e1 e2 e3 ha hb
  omega

private theorem djbKey_inj {a b : List.Vector (BitVec 8) 32} (h : djbKey a = djbKey b) : a = b := by
  simp only [djbKey, List.cons.injEq, true_and] at h
  exact List.Vector.eq a b h

private theorem kyberKey_inj {a b : List.Vector (BitVec 8) 1568}
    (h : kyberKey a = kyberKey b) : a = b := by
  simp only [kyberKey, List.cons.injEq, true_and] at h
  exact List.Vector.eq a b h

private theorem digitChar_val (d : ℕ) (hd : d < 10) : d.digitChar.toNat - 48 = d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | d + 10 => omega

private theorem toDigitsCore_append :
    ∀ (fuel n : ℕ) (ds : List Char),
      Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds
  | 0, _, ds => by simp [Nat.toDigitsCore]
  | fuel + 1, n, ds => by
    simp only [Nat.toDigitsCore]
    split
    · simp
    · rw [toDigitsCore_append fuel (n / 10) (_ :: ds),
          toDigitsCore_append fuel (n / 10) [_]]
      simp

private def parseDec : List Char → ℕ :=
  List.foldl (fun acc c => 10 * acc + (c.toNat - 48)) 0

private theorem parseDec_toDigitsCore :
    ∀ (fuel n : ℕ), n < fuel → parseDec (Nat.toDigitsCore 10 fuel n []) = n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, h => by
    unfold parseDec
    simp only [Nat.toDigitsCore]
    have hd : (n % 10).digitChar.toNat - 48 = n % 10 := digitChar_val (n % 10) (by omega)
    split
    · next hdiv =>
      simp only [List.foldl_cons, List.foldl_nil, hd]
      omega
    · next hdiv =>
      rw [toDigitsCore_append fuel (n / 10) [_], List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ih := parseDec_toDigitsCore fuel (n / 10) (by omega)
      unfold parseDec at ih
      rw [ih, hd]
      omega

private theorem toString_nat_inj {n m : ℕ} (h : toString n = toString m) : n = m := by
  have hl : (toString n).toList = (toString m).toList := congrArg String.toList h
  rw [Nat.toString_eq_ofList_toDigits, Nat.toString_eq_ofList_toDigits,
      String.toList_ofList, String.toList_ofList] at hl
  have hp := congrArg parseDec hl
  unfold Nat.toDigits at hp
  rw [parseDec_toDigitsCore (n + 1) n (Nat.lt_succ_self n),
      parseDec_toDigitsCore (m + 1) m (Nat.lt_succ_self m)] at hp
  exact hp

private theorem bv32_toString_inj {a b : BitVec 32} (h : toString a.toNat = toString b.toNat) :
    a = b :=
  BitVec.eq_of_toNat_eq (toString_nat_inj h)

private theorem string_append_left_inj (pre : String) {s₁ s₂ : String}
    (h : pre ++ s₁ = pre ++ s₂) : s₁ = s₂ := by
  have hl := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at hl
  exact String.ext (List.append_cancel_left hl)

private theorem string_append_right_inj (suf : String) {s₁ s₂ : String}
    (h : s₁ ++ suf = s₂ ++ suf) : s₁ = s₂ := by
  have hl := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at hl
  exact String.ext (List.append_cancel_right hl)

/-! ## 2. `Prost.varint` and `PreKeyMessageFields.bytes` injectivity -/

private theorem prost_varint_append_inj :
    ∀ {n₁ n₂ : ℕ} {r₁ r₂ : List (BitVec 8)},
      Prost.varint n₁ ++ r₁ = Prost.varint n₂ ++ r₂ → n₁ = n₂ ∧ r₁ = r₂ := by
  intro n₁
  induction n₁ using Prost.varint.induct with
  | case1 n₁ h₁ =>
    intro n₂ r₁ r₂ heq
    conv at heq => lhs; arg 1; rw [Prost.varint.eq_def]
    conv at heq => rhs; arg 1; rw [Prost.varint.eq_def]
    by_cases h₂ : n₂ < 128
    · simp only [h₁, h₂, ↓reduceDIte, List.cons_append, List.nil_append, List.cons.injEq] at heq
      have hb := congrArg BitVec.toNat heq.1
      simp only [BitVec.toNat_ofNat] at hb
      exact ⟨by omega, heq.2⟩
    · simp only [h₁, h₂, ↓reduceDIte, List.cons_append, List.nil_append, List.cons.injEq] at heq
      have hb := congrArg BitVec.toNat heq.1
      simp only [BitVec.toNat_ofNat] at hb
      omega
  | case2 n₁ h₁ ih =>
    intro n₂ r₁ r₂ heq
    conv at heq => lhs; arg 1; rw [Prost.varint.eq_def]
    conv at heq => rhs; arg 1; rw [Prost.varint.eq_def]
    by_cases h₂ : n₂ < 128
    · simp only [h₁, h₂, ↓reduceDIte, List.cons_append, List.nil_append, List.cons.injEq] at heq
      have hb := congrArg BitVec.toNat heq.1
      simp only [BitVec.toNat_ofNat] at hb
      omega
    · simp only [h₁, h₂, ↓reduceDIte, List.cons_append, List.cons.injEq] at heq
      have hb := congrArg BitVec.toNat heq.1
      simp only [BitVec.toNat_ofNat] at hb
      obtain ⟨hdiv, hr⟩ := ih heq.2
      exact ⟨by omega, hr⟩

private theorem prost_key_append_inj {tag wt : ℕ} {r₁ r₂ : List (BitVec 8)}
    (h : Prost.key tag wt ++ r₁ = Prost.key tag wt ++ r₂) : r₁ = r₂ :=
  (prost_varint_append_inj h).2

private theorem prost_bytesField_some_append_inj {tag : ℕ} {b₁ b₂ r₁ r₂ : List (BitVec 8)}
    (h : Prost.bytesField tag (some b₁) ++ r₁ = Prost.bytesField tag (some b₂) ++ r₂) :
    b₁ = b₂ ∧ r₁ = r₂ := by
  simp only [Prost.bytesField, List.append_assoc] at h
  obtain ⟨hlen, hbr⟩ := prost_varint_append_inj (prost_key_append_inj h)
  exact List.append_inj hbr hlen

private theorem prost_uint32Field_some_append_inj {tag : ℕ} {v₁ v₂ : BitVec 32}
    {r₁ r₂ : List (BitVec 8)}
    (h : Prost.uint32Field tag (some v₁) ++ r₁ = Prost.uint32Field tag (some v₂) ++ r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  simp only [Prost.uint32Field, List.append_assoc] at h
  obtain ⟨hv, hr⟩ := prost_varint_append_inj (prost_key_append_inj h)
  exact ⟨BitVec.eq_of_toNat_eq hv, hr⟩

private theorem prost_optOpk_peel {o₁ o₂ : Option (BitVec 32)}
    {b₁ b₂ r₁ r₂ : List (BitVec 8)}
    (h : Prost.uint32Field 1 o₁ ++ (Prost.bytesField 2 (some b₁) ++ r₁) =
         Prost.uint32Field 1 o₂ ++ (Prost.bytesField 2 (some b₂) ++ r₂)) :
    o₁ = o₂ ∧
      Prost.bytesField 2 (some b₁) ++ r₁ = Prost.bytesField 2 (some b₂) ++ r₂ := by
  have hk1 : Prost.key 1 0 = [0x08#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  have hk2 : Prost.key 2 2 = [0x12#8] := by rw [Prost.key, Prost.varint.eq_def]; decide
  cases o₁ with
  | none =>
    cases o₂ with
    | none => exact ⟨rfl, by simpa [Prost.uint32Field] using h⟩
    | some v₂ =>
      simp only [Prost.uint32Field, Prost.bytesField, hk1, hk2, List.nil_append,
        List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (by decide)
  | some v₁ =>
    cases o₂ with
    | none =>
      simp only [Prost.uint32Field, Prost.bytesField, hk1, hk2, List.nil_append,
        List.cons_append, List.cons.injEq] at h
      exact absurd h.1 (by decide)
    | some v₂ =>
      obtain ⟨hv, hr⟩ := prost_uint32Field_some_append_inj h
      exact ⟨congrArg some hv, hr⟩

/-- `PreKeyMessageFields.bytes` is injective on all `PreKeyMessageFields`. -/
theorem PreKeyMessageFields.bytes_inj {m₁ m₂ : PreKeyMessageFields} (h : m₁.bytes = m₂.bytes) : m₁ = m₂ := by
  unfold PreKeyMessageFields.bytes ProtoPreKeySignalMessage.encode at h
  simp only [List.cons.injEq, true_and] at h
  have h0 : Prost.uint32Field 1 m₁.opkId ++
      (Prost.bytesField 2 (some (djbKey m₁.baseKey)) ++
        (Prost.bytesField 3 (some (djbKey m₁.idPub)) ++
          (Prost.bytesField 4 (some m₁.inner) ++
            (Prost.uint32Field 5 (some m₁.regId) ++
              (Prost.uint32Field 6 (some m₁.spkId) ++
                (Prost.uint32Field 7 (some m₁.kpkId) ++
                  (Prost.bytesField 8 (some (kyberKey m₁.kyberCt)) ++ []))))))) =
    Prost.uint32Field 1 m₂.opkId ++
      (Prost.bytesField 2 (some (djbKey m₂.baseKey)) ++
        (Prost.bytesField 3 (some (djbKey m₂.idPub)) ++
          (Prost.bytesField 4 (some m₂.inner) ++
            (Prost.uint32Field 5 (some m₂.regId) ++
              (Prost.uint32Field 6 (some m₂.spkId) ++
                (Prost.uint32Field 7 (some m₂.kpkId) ++
                  (Prost.bytesField 8 (some (kyberKey m₂.kyberCt)) ++ []))))))) := by
    simpa only [List.append_assoc, List.append_nil] using h
  obtain ⟨hopk, h1⟩ := prost_optOpk_peel h0
  obtain ⟨hbk, h2⟩ := prost_bytesField_some_append_inj h1
  obtain ⟨hid, h3⟩ := prost_bytesField_some_append_inj h2
  obtain ⟨hinner, h4⟩ := prost_bytesField_some_append_inj h3
  obtain ⟨hreg, h5⟩ := prost_uint32Field_some_append_inj h4
  obtain ⟨hspk, h6⟩ := prost_uint32Field_some_append_inj h5
  obtain ⟨hkpk, h7⟩ := prost_uint32Field_some_append_inj h6
  obtain ⟨hct, _⟩ := prost_bytesField_some_append_inj h7
  cases m₁; cases m₂
  simp only at hopk hbk hid hinner hreg hspk hkpk hct
  cases hopk
  cases djbKey_inj hbk
  cases djbKey_inj hid
  cases hinner
  cases hreg
  cases hspk
  cases hkpk
  cases kyberKey_inj hct
  rfl

/-! ## 3. `PublicBundle` and `encodeDir` record / section injectivity -/

private theorem bundleE_of_publicBundleOf_files_eq {b₁ b₂ : PreKeyBundleFields}
    (h : (publicBundleOf b₁).files bundleDir = (publicBundleOf b₂).files bundleDir) :
    b₁ = b₂ := by
  unfold PublicBundle.files publicBundleOf at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq, Prod.mk.injEq, true_and] at h
  rcases h with ⟨h1, hreg, hspk, hkpk, hopk⟩
  obtain ⟨hspk12, hspkSig⟩ := List.append_inj hspk (by simp [le32, djbKey])
  obtain ⟨hspkId, hspkPub⟩ := List.append_inj hspk12 (by simp [le32])
  obtain ⟨hkpk12, hkpkSig⟩ := List.append_inj hkpk (by simp [le32, kyberKey])
  obtain ⟨hkpkId, hkpkPub⟩ := List.append_inj hkpk12 (by simp [le32])
  have hopkEq : b₁.opk = b₂.opk := by
    cases ho₁ : b₁.opk with
    | none =>
      cases ho₂ : b₂.opk with
      | none => rfl
      | some p₂ => simp [ho₁, ho₂] at hopk
    | some p₁ =>
      cases ho₂ : b₂.opk with
      | none => simp [ho₁, ho₂] at hopk
      | some p₂ =>
        obtain ⟨i₁, k₁⟩ := p₁
        obtain ⟨i₂, k₂⟩ := p₂
        simp only [ho₁, ho₂, Option.map_some, List.cons.injEq, Prod.mk.injEq, true_and,
          and_true] at hopk
        obtain ⟨hi, hk⟩ := List.append_inj hopk (by simp [le32])
        exact congrArg some (Prod.ext (le32_inj hi) (djbKey_inj hk))
  cases b₁; cases b₂
  simp only at h1 hreg hspkId hspkPub hspkSig hkpkId hkpkPub hkpkSig hopkEq
  cases djbKey_inj h1
  cases le32_inj hreg
  cases le32_inj hspkId
  cases djbKey_inj hspkPub
  cases List.Vector.eq _ _ hspkSig
  cases le32_inj hkpkId
  cases kyberKey_inj hkpkPub
  cases List.Vector.eq _ _ hkpkSig
  cases hopkEq
  rfl

private theorem signedRecordBytes_inj {C : Crypto} {i₁ i₂ : BitVec 32} {k₁ k₂ : PqSignedKey}
    (h : signedRecordBytes C i₁ k₁ = signedRecordBytes C i₂ k₂) : i₁ = i₂ ∧ k₁ = k₂ := by
  have hd := congrArg RecordCodecs.SignedPreKeyRecordStructure.decode h
  unfold signedRecordBytes at hd
  rw [RecordCodecs.SignedPreKeyRecordStructure.decode_encode _
        (by simp [djbKey]) (by simp) (by simp),
      RecordCodecs.SignedPreKeyRecordStructure.decode_encode _
        (by simp [djbKey]) (by simp) (by simp)] at hd
  simp only [Option.some.injEq, RecordCodecs.SignedPreKeyRecordStructure.mk.injEq] at hd
  rcases hd with ⟨hi, _, hpriv, hsig, hts⟩
  cases k₁; cases k₂
  simp only at hpriv hsig hts
  exact ⟨hi, by cases List.Vector.eq _ _ hpriv; cases List.Vector.eq _ _ hsig; cases hts; rfl⟩

private theorem kyberRecordBytes_inj {i₁ i₂ : BitVec 32} {k₁ k₂ : PqKyberKey}
    (h : kyberRecordBytes i₁ k₁ = kyberRecordBytes i₂ k₂) : i₁ = i₂ ∧ k₁ = k₂ := by
  have hd := congrArg RecordCodecs.SignedPreKeyRecordStructure.decode h
  unfold kyberRecordBytes at hd
  rw [RecordCodecs.SignedPreKeyRecordStructure.decode_encode _
        (by simp [kyberKey]) (by simp) (by simp),
      RecordCodecs.SignedPreKeyRecordStructure.decode_encode _
        (by simp [kyberKey]) (by simp) (by simp)] at hd
  simp only [Option.some.injEq, RecordCodecs.SignedPreKeyRecordStructure.mk.injEq,
    List.cons.injEq, true_and] at hd
  rcases hd with ⟨hi, hpub, hsec, hsig, hts⟩
  cases k₁; cases k₂
  simp only at hpub hsec hsig hts
  refine ⟨hi, ?_⟩
  cases kyberKey_inj hpub
  cases List.Vector.eq _ _ hsec
  cases List.Vector.eq _ _ hsig
  cases hts
  rfl

private theorem kyberRecordBytes_ne_nil (i : BitVec 32) (k : PqKyberKey) :
    kyberRecordBytes i k ≠ [] := by
  intro h
  have hd := congrArg RecordCodecs.SignedPreKeyRecordStructure.decode h
  unfold kyberRecordBytes at hd
  rw [RecordCodecs.SignedPreKeyRecordStructure.decode_encode _
        (by simp [kyberKey]) (by simp) (by simp)] at hd
  have hemp : RecordCodecs.SignedPreKeyRecordStructure.decode [] =
      some RecordCodecs.SignedPreKeyRecordStructure.empty := rfl
  rw [hemp] at hd
  simp only [Option.some.injEq, RecordCodecs.SignedPreKeyRecordStructure.empty,
    RecordCodecs.SignedPreKeyRecordStructure.mk.injEq] at hd
  have hl := congrArg List.length hd.2.2.2.1
  simp at hl

private theorem oneTimeRecordBytes_inj {C : Crypto} {i₁ i₂ : BitVec 32}
    {sk₁ sk₂ : List.Vector (BitVec 8) 32}
    (h : oneTimeRecordBytes C i₁ sk₁ = oneTimeRecordBytes C i₂ sk₂) : i₁ = i₂ ∧ sk₁ = sk₂ := by
  have hd := congrArg RecordCodecs.PreKeyRecordStructure.decode h
  unfold oneTimeRecordBytes at hd
  rw [RecordCodecs.PreKeyRecordStructure.decode_encode _ (by simp [djbKey]) (by simp),
      RecordCodecs.PreKeyRecordStructure.decode_encode _ (by simp [djbKey]) (by simp)] at hd
  simp only [Option.some.injEq, RecordCodecs.PreKeyRecordStructure.mk.injEq] at hd
  exact ⟨hd.1, List.Vector.eq _ _ hd.2.2⟩

private theorem oneTimeRecordBytes_ne_nil (C : Crypto) (i : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) : oneTimeRecordBytes C i sk ≠ [] := by
  intro h
  have hd := congrArg RecordCodecs.PreKeyRecordStructure.decode h
  unfold oneTimeRecordBytes at hd
  rw [RecordCodecs.PreKeyRecordStructure.decode_encode _ (by simp [djbKey]) (by simp)] at hd
  have hemp : RecordCodecs.PreKeyRecordStructure.decode [] =
      some RecordCodecs.PreKeyRecordStructure.empty := rfl
  rw [hemp] at hd
  simp only [Option.some.injEq, RecordCodecs.PreKeyRecordStructure.empty,
    RecordCodecs.PreKeyRecordStructure.mk.injEq] at hd
  have hl := congrArg List.length hd.2.2
  simp at hl

private theorem baseKeysBytes_inj :
    ∀ {s₁ s₂ : List (BitVec 32 × List.Vector (BitVec 8) 32)},
      baseKeysBytes s₁ = baseKeysBytes s₂ → s₁ = s₂
  | [], [], _ => rfl
  | [], (a, b) :: tl, h => by
    have hl := congrArg List.length h
    simp [baseKeysBytes, le32, djbKey] at hl
  | (a, b) :: tl, [], h => by
    have hl := congrArg List.length h
    simp [baseKeysBytes, le32, djbKey] at hl
  | (a₁, b₁) :: tl₁, (a₂, b₂) :: tl₂, h => by
    unfold baseKeysBytes at h
    simp only [List.map_cons, List.flatten_cons] at h
    obtain ⟨hhd, htl⟩ := List.append_inj h (by simp [le32, djbKey])
    obtain ⟨ha, hb⟩ := List.append_inj hhd (by simp [le32])
    exact congrArg₂ List.cons (Prod.ext (le32_inj ha) (djbKey_inj hb)) (baseKeysBytes_inj htl)

private theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} (h : l₁.map f = l₂.map f) : l₁ = l₂ :=
  List.map_injective_iff.mpr hf h

private abbrev DirEntry := String × List (BitVec 8)

private theorem addrE_other_text_inj {p₁ p₂ : Party}
    (h : (partyAddress p₁.other).text = (partyAddress p₂.other).text) : p₁ = p₂ := by
  cases p₁ <;> cases p₂
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

private theorem pqMe_ext {a b : LocalIdentity} (h1 : a.idPriv = b.idPriv) (h2 : a.regId = b.regId) :
    a = b := by
  cases a; cases b; cases h1; cases h2; rfl

/-- Disjoint character-prefix tag for `encodeDir` (tags 0–8) and `bundle/` (tag 9). -/
private def dirSecTagChars : List Char → ℕ
  | 'a' :: _ => 0
  | 'i' :: 'd' :: 'e' :: 'n' :: 't' :: 'i' :: 't' :: 'y' :: _ => 1
  | 'r' :: _ => 2
  | 'i' :: 'd' :: 'e' :: 'n' :: 't' :: 'i' :: 't' :: 'i' :: _ => 3
  | 's' :: 'e' :: _ => 4
  | 's' :: 'i' :: _ => 5
  | 'o' :: 'n' :: 'e' :: '-' :: 't' :: 'i' :: 'm' :: 'e' :: '-' :: 'p' :: _ => 6
  | 'o' :: 'n' :: 'e' :: '-' :: 't' :: 'i' :: 'm' :: 'e' :: '-' :: 'k' :: _ => 7
  | 'l' :: _ => 8
  | 'b' :: _ => 9
  | _ => 10

private def dirSecTag (p : String) : ℕ := dirSecTagChars p.toList

private theorem dirSecTag_address : dirSecTag addressFile = 0 := rfl
private theorem dirSecTag_idkp : dirSecTag identityKeyPairFile = 1 := rfl
private theorem dirSecTag_regId : dirSecTag registrationIdFile = 2 := rfl

private theorem dirSecTag_identity (s : String) : dirSecTag (identityFile s) = 3 := by
  unfold dirSecTag identityFile; rw [String.toList_append]; rfl

private theorem dirSecTag_session (a : Address) : dirSecTag (sessionFile a) = 4 := by
  unfold dirSecTag sessionFile; rw [String.toList_append]; rfl

private theorem dirSecTag_signed (i : BitVec 32) : dirSecTag (signedPreKeyFile i) = 5 := by
  unfold dirSecTag signedPreKeyFile; rw [String.toList_append]; rfl

private theorem dirSecTag_oneTime (i : BitVec 32) : dirSecTag (oneTimePreKeyFile i) = 6 := by
  unfold dirSecTag oneTimePreKeyFile; rw [String.toList_append]; rfl

private theorem dirSecTag_kyberOneTime (i : BitVec 32) :
    dirSecTag (oneTimeKyberPreKeyFile i) = 7 := by
  unfold dirSecTag oneTimeKyberPreKeyFile; rw [String.toList_append]; rfl

private theorem dirSecTag_lastResort (i : BitVec 32) :
    dirSecTag (lastResortKyberPreKeyFile i) = 8 := by
  unfold dirSecTag lastResortKyberPreKeyFile; rw [String.toList_append]; rfl

private theorem dirSecTag_baseKeys (i : BitVec 32) : dirSecTag (baseKeysFile i) = 8 := by
  unfold dirSecTag baseKeysFile; rw [String.append_assoc, String.toList_append]; rfl

private theorem dirSecTag_bundle_aux (suf : String) : dirSecTag (bundleDir ++ suf) = 9 := by
  unfold dirSecTag bundleDir; rw [String.toList_append]; rfl

private theorem dirSecTag_bundle_files (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, dirSecTag f.1 = 9 := by
  intro f hf
  unfold PublicBundle.files at hf
  cases ho : b.oneTime with
  | none =>
    simp only [ho, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> exact dirSecTag_bundle_aux _
  | some p =>
    obtain ⟨id, key⟩ := p
    simp only [ho, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl <;> exact dirSecTag_bundle_aux _

private theorem dirSecTag_encodeDir_lt_9 (W : PEParams) (st : PqParty) :
    ∀ f ∈ encodeDir W st, dirSecTag f.1 < 9 := by
  intro f hf
  unfold encodeDir at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | h | h | h | h
  · rw [dirSecTag_address]; omega
  · rw [dirSecTag_idkp]; omega
  · rw [dirSecTag_regId]; omega
  · cases hp : st.peerId <;> simp only [hp, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h; rw [dirSecTag_identity]; omega
  · cases hs : st.session with
    | none => simp [hs] at h
    | some xg =>
      obtain ⟨x, g⟩ := xg
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; rw [dirSecTag_session]; omega
  · obtain ⟨⟨i, k⟩, _, rfl⟩ := h; rw [dirSecTag_signed]; omega
  · obtain ⟨⟨i, k⟩, _, rfl⟩ := h; rw [dirSecTag_oneTime]; omega
  · obtain ⟨⟨i, k⟩, _, rfl⟩ := h; rw [dirSecTag_kyberOneTime]; omega
  · obtain ⟨l, ⟨⟨i, k, seen⟩, _, rfl⟩, hl⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [dirSecTag_lastResort]; omega
    · rw [dirSecTag_baseKeys]; omega

private theorem split_encodeDir_bundle {W : PEParams} {st₁ st₂ : PqParty} {b₁ b₂ : PreKeyBundleFields}
    (h : encodeDir W st₁ ++ (publicBundleOf b₁).files bundleDir =
         encodeDir W st₂ ++ (publicBundleOf b₂).files bundleDir) :
    encodeDir W st₁ = encodeDir W st₂ ∧ b₁ = b₂ := by
  have hf_lt := congrArg (List.filter fun f => decide (dirSecTag f.1 < 9)) h
  have hf_eq := congrArg (List.filter fun f => decide (dirSecTag f.1 = 9)) h
  have hd₁ : (encodeDir W st₁).filter (fun f => decide (dirSecTag f.1 < 9)) = encodeDir W st₁ :=
    List.filter_eq_self.mpr fun f hf => decide_eq_true (dirSecTag_encodeDir_lt_9 W st₁ f hf)
  have hd₂ : (encodeDir W st₂).filter (fun f => decide (dirSecTag f.1 < 9)) = encodeDir W st₂ :=
    List.filter_eq_self.mpr fun f hf => decide_eq_true (dirSecTag_encodeDir_lt_9 W st₂ f hf)
  have hb₁_lt : ((publicBundleOf b₁).files bundleDir).filter
      (fun f => decide (dirSecTag f.1 < 9)) = [] :=
    List.filter_eq_nil_iff.mpr fun f hf => by
      simp only [decide_eq_true_eq]; rw [dirSecTag_bundle_files _ f hf]; omega
  have hb₂_lt : ((publicBundleOf b₂).files bundleDir).filter
      (fun f => decide (dirSecTag f.1 < 9)) = [] :=
    List.filter_eq_nil_iff.mpr fun f hf => by
      simp only [decide_eq_true_eq]; rw [dirSecTag_bundle_files _ f hf]; omega
  have hd₁_9 : (encodeDir W st₁).filter (fun f => decide (dirSecTag f.1 = 9)) = [] :=
    List.filter_eq_nil_iff.mpr fun f hf => by
      simp only [decide_eq_true_eq]; have := dirSecTag_encodeDir_lt_9 W st₁ f hf; omega
  have hd₂_9 : (encodeDir W st₂).filter (fun f => decide (dirSecTag f.1 = 9)) = [] :=
    List.filter_eq_nil_iff.mpr fun f hf => by
      simp only [decide_eq_true_eq]; have := dirSecTag_encodeDir_lt_9 W st₂ f hf; omega
  have hb₁_9 : ((publicBundleOf b₁).files bundleDir).filter
      (fun f => decide (dirSecTag f.1 = 9)) = (publicBundleOf b₁).files bundleDir :=
    List.filter_eq_self.mpr fun f hf => decide_eq_true (dirSecTag_bundle_files _ f hf)
  have hb₂_9 : ((publicBundleOf b₂).files bundleDir).filter
      (fun f => decide (dirSecTag f.1 = 9)) = (publicBundleOf b₂).files bundleDir :=
    List.filter_eq_self.mpr fun f hf => decide_eq_true (dirSecTag_bundle_files _ f hf)
  simp only [List.filter_append, hd₁, hd₂, hb₁_lt, hb₂_lt, List.append_nil] at hf_lt
  simp only [List.filter_append, hd₁_9, hd₂_9, hb₁_9, hb₂_9, List.nil_append] at hf_eq
  exact ⟨hf_lt, bundleE_of_publicBundleOf_files_eq hf_eq⟩

private theorem filter_sec_nil {l : List DirEntry} {k : ℕ} (h : ∀ f ∈ l, dirSecTag f.1 ≠ k) :
    l.filter (fun f => decide (dirSecTag f.1 = k)) = [] :=
  List.filter_eq_nil_iff.mpr fun f hf => by simp only [decide_eq_true_eq]; exact h f hf

private theorem filter_sec_self {l : List DirEntry} {k : ℕ} (h : ∀ f ∈ l, dirSecTag f.1 = k) :
    l.filter (fun f => decide (dirSecTag f.1 = k)) = l :=
  List.filter_eq_self.mpr fun f hf => decide_eq_true (h f hf)

private theorem filter_tagged7 {l₀ l₃ l₄ l₅ l₆ l₇ l₈ : List DirEntry}
    (h₀ : ∀ f ∈ l₀, dirSecTag f.1 < 3)
    (h₃ : ∀ f ∈ l₃, dirSecTag f.1 = 3)
    (h₄ : ∀ f ∈ l₄, dirSecTag f.1 = 4)
    (h₅ : ∀ f ∈ l₅, dirSecTag f.1 = 5)
    (h₆ : ∀ f ∈ l₆, dirSecTag f.1 = 6)
    (h₇ : ∀ f ∈ l₇, dirSecTag f.1 = 7)
    (h₈ : ∀ f ∈ l₈, dirSecTag f.1 = 8) :
    let tot := l₀ ++ l₃ ++ l₄ ++ l₅ ++ l₆ ++ l₇ ++ l₈
    tot.filter (fun f => decide (dirSecTag f.1 = 3)) = l₃ ∧
    tot.filter (fun f => decide (dirSecTag f.1 = 4)) = l₄ ∧
    tot.filter (fun f => decide (dirSecTag f.1 = 5)) = l₅ ∧
    tot.filter (fun f => decide (dirSecTag f.1 = 6)) = l₆ ∧
    tot.filter (fun f => decide (dirSecTag f.1 = 7)) = l₇ ∧
    tot.filter (fun f => decide (dirSecTag f.1 = 8)) = l₈ := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.filter_append,
      filter_sec_nil (k := 3) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_self h₃,
      filter_sec_nil (k := 3) (fun f hf => by rw [h₄ f hf]; omega),
      filter_sec_nil (k := 3) (fun f hf => by rw [h₅ f hf]; omega),
      filter_sec_nil (k := 3) (fun f hf => by rw [h₆ f hf]; omega),
      filter_sec_nil (k := 3) (fun f hf => by rw [h₇ f hf]; omega),
      filter_sec_nil (k := 3) (fun f hf => by rw [h₈ f hf]; omega),
      List.nil_append, List.append_nil]
  · simp only [List.filter_append,
      filter_sec_nil (k := 4) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_nil (k := 4) (fun f hf => by rw [h₃ f hf]; omega),
      filter_sec_self h₄,
      filter_sec_nil (k := 4) (fun f hf => by rw [h₅ f hf]; omega),
      filter_sec_nil (k := 4) (fun f hf => by rw [h₆ f hf]; omega),
      filter_sec_nil (k := 4) (fun f hf => by rw [h₇ f hf]; omega),
      filter_sec_nil (k := 4) (fun f hf => by rw [h₈ f hf]; omega),
      List.nil_append, List.append_nil]
  · simp only [List.filter_append,
      filter_sec_nil (k := 5) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_nil (k := 5) (fun f hf => by rw [h₃ f hf]; omega),
      filter_sec_nil (k := 5) (fun f hf => by rw [h₄ f hf]; omega),
      filter_sec_self h₅,
      filter_sec_nil (k := 5) (fun f hf => by rw [h₆ f hf]; omega),
      filter_sec_nil (k := 5) (fun f hf => by rw [h₇ f hf]; omega),
      filter_sec_nil (k := 5) (fun f hf => by rw [h₈ f hf]; omega),
      List.nil_append, List.append_nil]
  · simp only [List.filter_append,
      filter_sec_nil (k := 6) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_nil (k := 6) (fun f hf => by rw [h₃ f hf]; omega),
      filter_sec_nil (k := 6) (fun f hf => by rw [h₄ f hf]; omega),
      filter_sec_nil (k := 6) (fun f hf => by rw [h₅ f hf]; omega),
      filter_sec_self h₆,
      filter_sec_nil (k := 6) (fun f hf => by rw [h₇ f hf]; omega),
      filter_sec_nil (k := 6) (fun f hf => by rw [h₈ f hf]; omega),
      List.nil_append, List.append_nil]
  · simp only [List.filter_append,
      filter_sec_nil (k := 7) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_nil (k := 7) (fun f hf => by rw [h₃ f hf]; omega),
      filter_sec_nil (k := 7) (fun f hf => by rw [h₄ f hf]; omega),
      filter_sec_nil (k := 7) (fun f hf => by rw [h₅ f hf]; omega),
      filter_sec_nil (k := 7) (fun f hf => by rw [h₆ f hf]; omega),
      filter_sec_self h₇,
      filter_sec_nil (k := 7) (fun f hf => by rw [h₈ f hf]; omega),
      List.nil_append, List.append_nil]
  · simp only [List.filter_append,
      filter_sec_nil (k := 8) (fun f hf => by have := h₀ f hf; omega),
      filter_sec_nil (k := 8) (fun f hf => by rw [h₃ f hf]; omega),
      filter_sec_nil (k := 8) (fun f hf => by rw [h₄ f hf]; omega),
      filter_sec_nil (k := 8) (fun f hf => by rw [h₅ f hf]; omega),
      filter_sec_nil (k := 8) (fun f hf => by rw [h₆ f hf]; omega),
      filter_sec_nil (k := 8) (fun f hf => by rw [h₇ f hf]; omega),
      filter_sec_self h₈,
      List.nil_append]

private theorem encodeDir_filters (W : PEParams) (st : PqParty) :
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 3)) =
      (match st.peerId with
       | some k => [(identityFile (partyAddressName st.party.other), k.serialize)]
       | none => []) ∧
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 4)) =
      (match st.session with
       | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)]
       | none => []) ∧
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 5)) =
      (st.signed.map fun (i, k) => (signedPreKeyFile i, signedRecordBytes W.C i k)) ∧
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 6)) =
      (st.oneTime.map fun (i, k) =>
        (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W.C i sk | none => [])) ∧
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 7)) =
      (st.kyberOneTime.map fun (i, k) =>
        (oneTimeKyberPreKeyFile i, match k with | some ky => kyberRecordBytes i ky | none => [])) ∧
    (encodeDir W st).filter (fun f => decide (dirSecTag f.1 = 8)) =
      ((st.kyberLastResort.map fun (i, ky, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i ky),
         (baseKeysFile i, baseKeysBytes seen)]).flatten) := by
  unfold encodeDir
  refine filter_tagged7 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · rw [dirSecTag_address]; omega
    · rw [dirSecTag_idkp]; omega
    · rw [dirSecTag_regId]; omega
  · intro f hf
    cases hp : st.peerId <;> simp only [hp, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf; exact dirSecTag_identity _
  · intro f hf
    cases hs : st.session with
    | none => simp [hs] at hf
    | some xg =>
      obtain ⟨x, g⟩ := xg
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; exact dirSecTag_session _
  · intro f hf
    obtain ⟨⟨i, k⟩, _, rfl⟩ := List.mem_map.mp hf
    exact dirSecTag_signed _
  · intro f hf
    obtain ⟨⟨i, k⟩, _, rfl⟩ := List.mem_map.mp hf
    exact dirSecTag_oneTime _
  · intro f hf
    obtain ⟨⟨i, k⟩, _, rfl⟩ := List.mem_map.mp hf
    exact dirSecTag_kyberOneTime _
  · intro f hf
    obtain ⟨pair, hpair, hfp⟩ := List.mem_flatten.mp hf
    obtain ⟨⟨i, ky, seen⟩, _, rfl⟩ := List.mem_map.mp hpair
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfp
    rcases hfp with rfl | rfl
    · exact dirSecTag_lastResort _
    · exact dirSecTag_baseKeys _

private theorem lr_flatten_inj :
    ∀ {l₁ l₂ : List (BitVec 32 × PqKyberKey × List (BitVec 32 × List.Vector (BitVec 8) 32))},
      (l₁.map fun (i, ky, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i ky),
         (baseKeysFile i, baseKeysBytes seen)]).flatten =
      (l₂.map fun (i, ky, seen) =>
        [(lastResortKyberPreKeyFile i, kyberRecordBytes i ky),
         (baseKeysFile i, baseKeysBytes seen)]).flatten →
      l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (i₁, ky₁, s₁) :: t₁, (i₂, ky₂, s₂) :: t₂, h => by
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append,
      List.cons.injEq, Prod.mk.injEq] at h
    rcases h with ⟨⟨_, hky⟩, ⟨_, hs⟩, htl⟩
    obtain ⟨hi, hkyEq⟩ := kyberRecordBytes_inj hky
    have hsEq := baseKeysBytes_inj hs
    exact congrArg₂ List.cons (by subst hi hkyEq hsEq; rfl) (lr_flatten_inj htl)

private theorem encodeDir_nonSession_inj {W : PEParams} {st₁ st₂ : PqParty}
    (h : encodeDir W st₁ = encodeDir W st₂) :
    st₁.me = st₂.me ∧
    st₁.peerId = st₂.peerId ∧
    st₁.signed = st₂.signed ∧
    st₁.oneTime = st₂.oneTime ∧
    st₁.kyberOneTime = st₂.kyberOneTime ∧
    st₁.kyberLastResort = st₂.kyberLastResort ∧
    (match st₁.session with
     | some (x, g) => [(sessionFile (partyAddress st₁.party.other), encodeRecordUnderExtras (fun _ => x) g)]
     | none => []) =
    (match st₂.session with
     | some (x, g) => [(sessionFile (partyAddress st₂.party.other), encodeRecordUnderExtras (fun _ => x) g)]
     | none => []) := by
  have sec := fun k => congrArg (List.filter fun f => decide (dirSecTag f.1 = k)) h
  obtain ⟨f3₁, f4₁, f5₁, f6₁, f7₁, f8₁⟩ := encodeDir_filters W st₁
  obtain ⟨f3₂, f4₂, f5₂, f6₂, f7₂, f8₂⟩ := encodeDir_filters W st₂
  have hhead :
      RecordCodecs.IdentityKeyPairStructure.encode
        ⟨djbKey (keyPairOf W.C st₁.me.idPriv).publicKey.bytes, st₁.me.idPriv.toList⟩ =
      RecordCodecs.IdentityKeyPairStructure.encode
        ⟨djbKey (keyPairOf W.C st₂.me.idPriv).publicKey.bytes, st₂.me.idPriv.toList⟩ ∧
      le32 st₁.me.regId = le32 st₂.me.regId := by
    have hh := h
    unfold encodeDir at hh
    simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq, true_and] at hh
    exact ⟨hh.2.1, hh.2.2.1⟩
  have hme : st₁.me = st₂.me := by
    have hd := congrArg RecordCodecs.IdentityKeyPairStructure.decode hhead.1
    rw [RecordCodecs.IdentityKeyPairStructure.decode_encode _ (by simp [djbKey]) (by simp),
        RecordCodecs.IdentityKeyPairStructure.decode_encode _ (by simp [djbKey]) (by simp)] at hd
    simp only [Option.some.injEq, RecordCodecs.IdentityKeyPairStructure.mk.injEq] at hd
    exact pqMe_ext (List.Vector.eq _ _ hd.2) (le32_inj hhead.2)
  have s3 := (f3₁.symm.trans (sec 3)).trans f3₂
  have hpeer : st₁.peerId = st₂.peerId := by
    cases hp₁ : st₁.peerId with
    | none =>
      cases hp₂ : st₂.peerId with
      | none => rfl
      | some ik₂ => simp [hp₁, hp₂] at s3
    | some ik₁ =>
      cases hp₂ : st₂.peerId with
      | none => simp [hp₁, hp₂] at s3
      | some ik₂ =>
        simp only [hp₁, hp₂, List.cons.injEq, Prod.mk.injEq, and_true] at s3
        exact congrArg some (identityKey_serialize_inj s3.2)
  have hsess := (f4₁.symm.trans (sec 4)).trans f4₂
  have s5 := (f5₁.symm.trans (sec 5)).trans f5₂
  have hsigned : st₁.signed = st₂.signed := by
    refine map_inj_of_inj (fun ⟨i₁, k₁⟩ ⟨i₂, k₂⟩ heq => ?_) s5
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hi, hk⟩ := signedRecordBytes_inj heq.2
    exact Prod.ext hi hk
  have s6 := (f6₁.symm.trans (sec 6)).trans f6₂
  have honeTime : st₁.oneTime = st₂.oneTime := by
    refine map_inj_of_inj (fun ⟨i₁, o₁⟩ ⟨i₂, o₂⟩ heq => ?_) s6
    simp only [Prod.mk.injEq] at heq
    have hi : i₁ = i₂ := bv32_toString_inj (string_append_left_inj "one-time-pre-keys/" heq.1)
    subst hi
    refine Prod.ext rfl ?_
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some sk₂ => exact absurd heq.2.symm (oneTimeRecordBytes_ne_nil W.C i₁ sk₂)
    | some sk₁ =>
      cases o₂ with
      | none => exact absurd heq.2 (oneTimeRecordBytes_ne_nil W.C i₁ sk₁)
      | some sk₂ => exact congrArg some (oneTimeRecordBytes_inj heq.2).2
  have s7 := (f7₁.symm.trans (sec 7)).trans f7₂
  have hkyberOT : st₁.kyberOneTime = st₂.kyberOneTime := by
    refine map_inj_of_inj (fun ⟨i₁, o₁⟩ ⟨i₂, o₂⟩ heq => ?_) s7
    simp only [Prod.mk.injEq] at heq
    have hi : i₁ = i₂ :=
      bv32_toString_inj (string_append_left_inj "one-time-kyber-pre-keys/" heq.1)
    subst hi
    refine Prod.ext rfl ?_
    cases o₁ with
    | none =>
      cases o₂ with
      | none => rfl
      | some k₂ => exact absurd heq.2.symm (kyberRecordBytes_ne_nil i₁ k₂)
    | some k₁ =>
      cases o₂ with
      | none => exact absurd heq.2 (kyberRecordBytes_ne_nil i₁ k₁)
      | some k₂ => exact congrArg some (kyberRecordBytes_inj heq.2).2
  have s8 := (f8₁.symm.trans (sec 8)).trans f8₂
  exact ⟨hme, hpeer, hsigned, honeTime, hkyberOT, lr_flatten_inj s8, hsess⟩

private theorem pqParty_eq_of_encodeDir_eq_noSession {W : PEParams} {st₁ st₂ : PqParty}
    (hp : st₁.party = st₂.party) (hs₁ : st₁.session = none) (hs₂ : st₂.session = none)
    (h : encodeDir W st₁ = encodeDir W st₂) : st₁ = st₂ := by
  obtain ⟨hme, hpeer, hsig, hot, hkot, hklr, _⟩ := encodeDir_nonSession_inj h
  cases st₁; cases st₂
  cases hp; cases hme; cases hpeer; cases hs₁; cases hs₂; cases hsig; cases hot; cases hkot
  cases hklr
  rfl

/-! ## 4. `encStateUnderExtras` / `encodeRecordUnderExtras` peeling and `pendingPreKey = false` congruence -/

private theorem signExtend32_64_inj {v₁ v₂ : BitVec 32}
    (h : v₁.signExtend 64 = v₂.signExtend 64) : v₁ = v₂ := by
  apply BitVec.eq_of_toInt_eq
  have hi := congrArg BitVec.toInt h
  rwa [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_signExtend_of_le (by omega)] at hi

private theorem tagGe_optUint32FieldX {T tag : ℕ} (ov : Option (BitVec 32)) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (optUint32FieldX tag ov ++ rest) := by
  cases ov with
  | none => simpa [optUint32FieldX] using hrest
  | some v =>
    intro t ht
    simp only [optUint32FieldX, List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2,
      Option.some.injEq] at ht
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

private theorem tagGe_uint64FieldX {T tag : ℕ} (v : BitVec 64) (rest : Bytes)
    (h1 : 1 ≤ tag) (h2 : tag < 2 ^ 28) (hle : T ≤ tag) (hrest : TagGe T rest) :
    TagGe T (uint64FieldX tag v ++ rest) := by
  unfold uint64FieldX
  split_ifs
  · simpa using hrest
  · intro t ht
    simp only [List.append_assoc, peekTag_encodeKey tag .varint _ h1 h2, Option.some.injEq] at ht
    omega

private theorem peel_optUint32FieldX {tag : ℕ} {o₁ o₂ : Option (BitVec 32)} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (optUint32FieldX tag o₁ ++ r₁) (optUint32FieldX tag o₂ ++ r₂)) :
    o₁ = o₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  have hn₁ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁
  have hn₂ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂
  cases o₁ with
  | none =>
    cases o₂ with
    | none => exact ⟨rfl, by simpa [optUint32FieldX] using heq, by simpa [optUint32FieldX] using hlen⟩
    | some v₂ =>
      simp only [optUint32FieldX, List.nil_append, List.append_assoc] at heq
      exfalso; apply hn₁; rw [heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
  | some v₁ =>
    cases o₂ with
    | none =>
      simp only [optUint32FieldX, List.nil_append, List.append_assoc] at heq
      exfalso; apply hn₂; rw [← heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
    | some v₂ =>
      simp only [optUint32FieldX, List.append_assoc] at heq hlen
      obtain ⟨hw, hr⟩ := encodeVarint_append_inj (encodeKey_append_inj heq)
      rw [List.length_append, List.length_append] at hlen
      exact ⟨congrArg some (uint32_setWidth64_inj hw), hr, by omega⟩

private theorem peel_int32FieldX {tag : ℕ} {v₁ v₂ : BitVec 32} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (int32FieldX tag v₁ ++ r₁) (int32FieldX tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  have hn₁ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁
  have hn₂ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂
  unfold int32FieldX at heq hlen
  by_cases hv₁ : v₁ = 0 <;> by_cases hv₂ : v₂ = 0
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at heq hlen
    exact ⟨hv₁.trans hv₂.symm, heq, hlen⟩
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append, List.append_assoc] at heq
    exfalso; apply hn₁; rw [heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append, List.append_assoc] at heq
    exfalso; apply hn₂; rw [← heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
  · simp only [hv₁, hv₂, ↓reduceIte, List.append_assoc] at heq hlen
    obtain ⟨hw, hr⟩ := encodeVarint_append_inj (encodeKey_append_inj heq)
    rw [List.length_append, List.length_append] at hlen
    exact ⟨signExtend32_64_inj hw, hr, by omega⟩

private theorem peel_uint64FieldX {tag : ℕ} {v₁ v₂ : BitVec 64} {r₁ r₂ : Bytes}
    (htag1 : 1 ≤ tag) (htag2 : tag < 2 ^ 28)
    (hr₁ : TagGe (tag + 1) r₁) (hr₂ : TagGe (tag + 1) r₂)
    (hc : ChainEq (uint64FieldX tag v₁ ++ r₁) (uint64FieldX tag v₂ ++ r₂)) :
    v₁ = v₂ ∧ ChainEq r₁ r₂ := by
  obtain ⟨heq, hlen⟩ := hc
  have hn₁ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₁
  have hn₂ := peekTag_ne_of_tagGe (Nat.lt_succ_self tag) hr₂
  unfold uint64FieldX at heq hlen
  by_cases hv₁ : v₁ = 0 <;> by_cases hv₂ : v₂ = 0
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append] at heq hlen
    exact ⟨hv₁.trans hv₂.symm, heq, hlen⟩
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append, List.append_assoc] at heq
    exfalso; apply hn₁; rw [heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
  · simp only [hv₁, hv₂, ↓reduceIte, List.nil_append, List.append_assoc] at heq
    exfalso; apply hn₂; rw [← heq]; exact peekTag_encodeKey tag .varint _ htag1 htag2
  · simp only [hv₁, hv₂, ↓reduceIte, List.append_assoc] at heq hlen
    obtain ⟨hw, hr⟩ := encodeVarint_append_inj (encodeKey_append_inj heq)
    rw [List.length_append, List.length_append] at hlen
    exact ⟨hw, hr, by omega⟩

private theorem encPendingPreKeyX_inj (p₁ p₂ : PendingPreKey)
    (hlen : (encPendingPreKeyX p₁).length < 2 ^ 64)
    (h : encPendingPreKeyX p₁ = encPendingPreKeyX p₂) : p₁ = p₂ := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encPendingPreKeyX, List.append_assoc] at hc0
  have g4 : ∀ p : PendingPreKey, TagGe 4 (uint64FieldX 4 p.timestamp ++ []) := fun p =>
    tagGe_uint64FieldX _ _ (by omega) (by omega) (by omega) (tagGe_nil _)
  have g3 : ∀ p : PendingPreKey,
      TagGe 3 (int32FieldX 3 p.signedPreKeyId ++ (uint64FieldX 4 p.timestamp ++ [])) := fun p =>
    tagGe_int32FieldX _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (g4 p t ht))
  have g2 : ∀ p : PendingPreKey,
      TagGe 2 (bytesField 2 p.baseKey.serialize ++
        (int32FieldX 3 p.signedPreKeyId ++ (uint64FieldX 4 p.timestamp ++ []))) := fun p =>
    tagGe_bytesField _ _ (by omega) (by omega) (by omega)
      (fun t ht => Nat.le_trans (by omega) (g3 p t ht))
  obtain ⟨hf1, hc1⟩ := peel_optUint32FieldX (by omega) (by omega) (g2 p₁) (g2 p₂) hc0
  obtain ⟨hf2, hc2⟩ := peel_bytes (by omega) (by omega) (g3 p₁) (g3 p₂) hc1
  obtain ⟨hf3, hc3⟩ := peel_int32FieldX (by omega) (by omega) (g4 p₁) (g4 p₂) hc2
  obtain ⟨hf4, _⟩ := peel_uint64FieldX (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc3
  cases p₁; cases p₂
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
  cases p₁; cases p₂
  cases hf1
  cases hf2
  rfl

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

private theorem stateXTail_tagGe (x : RecordExtras) (st : SessionState Bytes) :
    let t15 := bytesField 15 st.pqRatchetState ++ []
    let t14 := msgField 14 (if st.pendingPreKey then x.kyber.map encPendingKyberX else none) ++ t15
    let t13 := bytesField 13 x.aliceBaseKey ++ t14
    let t11 := uint32Field 11 x.localRegistrationId ++ t13
    let t10 := uint32Field 10 x.remoteRegistrationId ++ t11
    let t9 := msgField 9 (if st.pendingPreKey then some (encPendingPreKeyX x.pending) else none) ++ t10
    let t7 := (st.receiverChains.map fun c => lenField 7 (encReceiverChain c)).flatten ++ t9
    let t6 := msgField 6 (st.senderChain.map encSenderChain) ++ t7
    let t5 := uint32Field 5 st.previousCounter ++ t6
    let t4 := bytesField 4 (HMAC.keyToBytes32 st.rootKey) ++ t5
    let t3 := bytesField 3 ((st.remoteIdentity.map IdentityKey.serialize).getD []) ++ t4
    let t2 := bytesField 2 st.localIdentity.serialize ++ t3
    TagGe 2 t2 ∧ TagGe 3 t3 ∧ TagGe 4 t4 ∧ TagGe 5 t5 ∧ TagGe 6 t6 ∧ TagGe 7 t7 ∧
      TagGe 8 t9 ∧ TagGe 10 t10 ∧ TagGe 11 t11 ∧ TagGe 12 t13 ∧ TagGe 14 t14 ∧ TagGe 15 t15 := by
  intro t15 t14 t13 t11 t10 t9 t7 t6 t5 t4 t3 t2
  have h15 : TagGe 15 t15 := tagGe_bytesField _ _ (by omega) (by omega) (by omega) (tagGe_nil _)
  have h14 : TagGe 14 t14 := tagGe_msgField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h15 t ht))
  have h12 : TagGe 12 t13 := tagGe_bytesField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h14 t ht))
  have h11 : TagGe 11 t11 := tagGe_uint32Field _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h12 t ht))
  have h10 : TagGe 10 t10 := tagGe_uint32Field _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h11 t ht))
  have h8 : TagGe 8 t9 := tagGe_msgField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h10 t ht))
  have h7 : TagGe 7 t7 := tagGe_flatten_lenField _ _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h8 t ht))
  have h6 : TagGe 6 t6 := tagGe_msgField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h7 t ht))
  have h5 : TagGe 5 t5 := tagGe_uint32Field _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h6 t ht))
  have h4 : TagGe 4 t4 := tagGe_bytesField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h5 t ht))
  have h3 : TagGe 3 t3 := tagGe_bytesField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h4 t ht))
  have h2 : TagGe 2 t2 := tagGe_bytesField _ _ (by omega) (by omega) (by omega)
    (fun t ht => Nat.le_trans (by omega) (h3 t ht))
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h14, h15⟩

/-- Non-pending fields of `RecordExtras` (the only fields `encStateUnderExtras` writes when
`pendingPreKey = false`). -/
private def ExtrasSteadyEq (x₁ x₂ : RecordExtras) : Prop :=
  x₁.remoteRegistrationId = x₂.remoteRegistrationId ∧
  x₁.localRegistrationId = x₂.localRegistrationId ∧
  x₁.aliceBaseKey = x₂.aliceBaseKey

private theorem encStateX_congr_of_pending_false {x₁ x₂ : RecordExtras} {st : SessionState Bytes}
    (hp : st.pendingPreKey = false) (hx : ExtrasSteadyEq x₁ x₂) :
    encStateUnderExtras x₁ st = encStateUnderExtras x₂ st := by
  rcases hx with ⟨hr, hl, ha⟩
  simp [encStateUnderExtras, hp, hr, hl, ha]

private theorem encodeRecordX_congr_of_pending_false {x₁ x₂ : RecordExtras}
    {g₁ g₂ : GhostState Bytes}
    (hs : g₁.session = g₂.session) (hp : g₁.session.pendingPreKey = false)
    (hx : ExtrasSteadyEq x₁ x₂) :
    encodeRecordUnderExtras (fun _ => x₁) g₁ = encodeRecordUnderExtras (fun _ => x₂) g₂ := by
  unfold encodeRecordUnderExtras
  rw [← hs, encStateX_congr_of_pending_false hp hx]

private theorem encStateX_peel {x₁ x₂ : RecordExtras} {st₁ st₂ : SessionState Bytes}
    (hlen : (encStateUnderExtras x₁ st₁).length < 2 ^ 64)
    (h : encStateUnderExtras x₁ st₁ = encStateUnderExtras x₂ st₂) :
    st₁ = st₂ ∧ ExtrasSteadyEq x₁ x₂ ∧ (st₁.pendingPreKey = true → x₁ = x₂) := by
  have hc0 := chainEq_of_eq_lt hlen h
  simp only [encStateUnderExtras, List.append_assoc] at hc0
  obtain ⟨g2, g3, g4, g5, g6, g7, g8, g10, g11, g12, g14, g15⟩ := stateXTail_tagGe x₁ st₁
  obtain ⟨g2', g3', g4', g5', g6', g7', g8', g10', g11', g12', g14', g15'⟩ :=
    stateXTail_tagGe x₂ st₂
  obtain ⟨hf1, hc1⟩ := peel_uint32 (by omega) (by omega) g2 g2' hc0
  obtain ⟨hf2, hc2⟩ := peel_bytes (by omega) (by omega) g3 g3' hc1
  obtain ⟨hf3, hc3⟩ := peel_bytes (by omega) (by omega) g4 g4' hc2
  obtain ⟨hf4, hc4⟩ := peel_bytes (by omega) (by omega) g5 g5' hc3
  obtain ⟨hf5, hc5⟩ := peel_uint32 (by omega) (by omega) g6 g6' hc4
  obtain ⟨hf6, hc6⟩ := peel_msg encSenderChain (by omega) (by omega) encSenderChain_inj g7 g7' hc5
  obtain ⟨hf7, hc7⟩ := peel_repeated encReceiverChain (by omega) (by omega) encReceiverChain_inj
    g8 g8' hc6
  have hmap9 : ∀ (b : Bool) (p : PendingPreKey),
      (if b then some (encPendingPreKeyX p) else none) =
      (if b then some p else none).map encPendingPreKeyX := by
    intro b p; cases b <;> rfl
  rw [hmap9 st₁.pendingPreKey x₁.pending, hmap9 st₂.pendingPreKey x₂.pending] at hc7
  obtain ⟨hf9, hc8⟩ := peel_msg encPendingPreKeyX (by omega) (by omega) encPendingPreKeyX_inj
    g10 g10' hc7
  obtain ⟨hf10, hc9⟩ := peel_uint32 (by omega) (by omega) g11 g11' hc8
  obtain ⟨hf11, hc10⟩ := peel_uint32 (by omega) (by omega) g12 g12' hc9
  obtain ⟨hf13, hc11⟩ := peel_bytes (by omega) (by omega) g14 g14' hc10
  have hmap14 : ∀ (b : Bool) (ok : Option PendingKyberPreKey),
      (if b then ok.map encPendingKyberX else none) =
      (if b then ok else none).map encPendingKyberX := by
    intro b ok; cases b <;> rfl
  rw [hmap14 st₁.pendingPreKey x₁.kyber, hmap14 st₂.pendingPreKey x₂.kyber] at hc11
  obtain ⟨hf14, hc12⟩ := peel_msg encPendingKyberX (by omega) (by omega) encPendingKyberX_inj
    g15 g15' hc11
  obtain ⟨hf15, _⟩ := peel_bytes (by omega) (by omega) (tagGe_nil _) (tagGe_nil _) hc12
  have hpendBool : st₁.pendingPreKey = st₂.pendingPreKey := by
    cases hp₁ : st₁.pendingPreKey <;> cases hp₂ : st₂.pendingPreKey <;>
      simp [hp₁, hp₂] at hf9 ⊢
  have hst : st₁ = st₂ := by
    cases st₁; cases st₂
    cases hf1
    cases identityKey_serialize_inj hf2
    cases remoteIdentity_opt_inj hf3
    cases keyToBytes32_inj hf4
    cases hf5
    cases hf6
    cases hf7
    cases hpendBool
    cases hf15
    rfl
  refine ⟨hst, ⟨hf10, hf11, hf13⟩, fun hp => ?_⟩
  have hp₂ : st₂.pendingPreKey = true := hpendBool ▸ hp
  simp only [hp, hp₂, ↓reduceIte, Option.some.injEq] at hf9 hf14
  cases x₁; cases x₂
  simp only at hf9 hf14 hf10 hf11 hf13
  subst hf9 hf14 hf10 hf11 hf13
  rfl

private theorem encodeRecordX_peel {x₁ x₂ : RecordExtras} {g₁ g₂ : GhostState Bytes}
    (h₁ : (encodeRecordUnderExtras (fun _ => x₁) g₁).length < 2 ^ 64)
    (h₂ : (encodeRecordUnderExtras (fun _ => x₂) g₂).length < 2 ^ 64)
    (h : encodeRecordUnderExtras (fun _ => x₁) g₁ = encodeRecordUnderExtras (fun _ => x₂) g₂) :
    g₁.session = g₂.session ∧ ExtrasSteadyEq x₁ x₂ ∧
      (g₁.session.pendingPreKey = true → x₁ = x₂) := by
  have hs₁ : (encStateUnderExtras x₁ g₁.session).length < 2 ^ 64 := by
    have := length_le_lenField 1 (encStateUnderExtras x₁ g₁.session)
    simp only [encodeRecordUnderExtras, msgField] at h₁
    omega
  have hs₂ : (encStateUnderExtras x₂ g₂.session).length < 2 ^ 64 := by
    have := length_le_lenField 1 (encStateUnderExtras x₂ g₂.session)
    simp only [encodeRecordUnderExtras, msgField] at h₂
    omega
  have hrec : lenField 1 (encStateUnderExtras x₁ g₁.session) ++ [] =
      lenField 1 (encStateUnderExtras x₂ g₂.session) ++ [] := by
    simpa [encodeRecordUnderExtras, msgField] using h
  exact encStateX_peel hs₁ (lenField_append_inj hs₁ hs₂ hrec).1

/-! ## 5. Preservation of `pendingPreKey = false` under `messageEncrypt` and `tryDecryptFromRecord` -/

private theorem mut_exec_bind {σ α β : Type} (m : Mut σ α) (f : α → Mut σ β) (s : σ) :
    Mut.exec (m >>= f) s =
      match Mut.exec m s with
      | (.ok a, s') => Mut.exec (f a) s'
      | (.error e, s') => (.error e, s') := by
  unfold Mut.exec ExceptT.run StateT.run
  change (match m s with | (r, s') => ExceptT.bindCont f r s') = _
  cases m s with
  | mk r s' => cases r <;> rfl

private theorem mut_exec_get {σ : Type} (s : σ) :
    Mut.exec (get : Mut σ σ) s = (.ok s, s) := rfl

private theorem mut_exec_pure {σ α : Type} (a : α) (s : σ) :
    Mut.exec (pure a : Mut σ α) s = (.ok a, s) := rfl

private theorem mut_exec_throw {σ α : Type} (e : SignalProtocolError) (s : σ) :
    Mut.exec (throw e : Mut σ α) s = (.error e, s) := rfl

private theorem mut_exec_modify {σ : Type} (f : σ → σ) (s : σ) :
    Mut.exec (modify f : Mut σ Unit) s = (.ok (), f s) := rfl

private theorem mut_exec_takePq {PQ : Type} [Inhabited PQ] (s : SessionState PQ) :
    Mut.exec SessionState.takePqRatchetState s =
      (.ok s.pqRatchetState, { s with pqRatchetState := default }) := rfl

private theorem mut_exec_takeRatchet {PQ : Type} (s : SessionState PQ) :
    Mut.exec SessionState.takeRatchetState s =
      (.ok ⟨s.rootKey, s.senderChain, s.receiverChains, s.previousCounter, maxForwardJumps⟩,
        { s with receiverChains := [] }) := rfl

private theorem messageEncrypt_pendingPreKey {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (codec : SignalMessageProtoCodec) (spqr : Spqr PQ PQC)
    (addrs : Option (List (BitVec 8))) (m : List (BitVec 8)) (r : PQC)
    (st s : SessionState PQ) (msg : SignalMessage)
    (h : SessionState.messageEncrypt C codec spqr addrs m r st = (.ok msg, s)) :
    s.pendingPreKey = st.pendingPreKey := by
  unfold SessionState.messageEncrypt at h
  split at h
  · simp at h
  · rename_i session taken hfs
    have hp1 : taken.pendingPreKey = st.pendingPreKey := by
      unfold OutgoingTripleRatchet.fromSessionState at hfs
      simp only [mut_exec_bind, mut_exec_get] at hfs
      cases hsc : st.senderChain with
      | none => simp [hsc, mut_exec_throw] at hfs
      | some sc =>
        simp only [hsc, mut_exec_bind, mut_exec_takePq, mut_exec_get] at hfs
        split at hfs
        · simp [mut_exec_throw] at hfs
        · cases hrem : st.remoteIdentity with
          | none => simp [hrem, mut_exec_throw] at hfs
          | some remote =>
            simp only [hrem, mut_exec_pure, Prod.mk.injEq] at hfs
            rw [← hfs.2]
    split at h
    · simp at h
    · simp only [Prod.mk.injEq] at h
      rw [← h.2]
      exact hp1

private theorem tryDecryptFromRecord_pendingPreKey_false {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto) (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8)))
    (msg : SignalMessage) (ty : MessageType) (rc : BitVec 256)
    (st s : SessionState PQ) (pt : List (BitVec 8))
    (h : SessionState.tryDecryptFromRecord C spqr expected msg ty rc st = (.ok pt, s)) :
    s.pendingPreKey = false := by
  unfold SessionState.tryDecryptFromRecord at h
  split at h
  · simp at h
  · cases hex : Mut.exec (SessionState.tryDecryptWithState C spqr expected msg ty rc) st with
    | mk r updated =>
      rw [hex] at h
      cases r with
      | error e => simp at h
      | ok ptext =>
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState at hex
        simp only [mut_exec_bind, mut_exec_takeRatchet, mut_exec_takePq, mut_exec_get] at hex
        cases hrem : st.remoteIdentity with
        | none => simp [hrem, mut_exec_throw] at hex
        | some remote =>
          simp only [hrem, mut_exec_pure] at hex
          cases hdec : Mut.exec (TripleRatchet.decrypt C spqr expected msg ty rc)
              ⟨⟨st.rootKey, st.senderChain, st.receiverChains, st.previousCounter, maxForwardJumps⟩,
                st.pqRatchetState, st.localIdentity, remote⟩ with
          | mk r2 session' =>
            rw [hdec] at hex
            cases r2 with
            | error e => simp [liftE, mut_exec_throw] at hex
            | ok pt2 =>
              simp only [liftE, mut_exec_pure, mut_exec_modify, Prod.mk.injEq] at hex
              rw [← hex.2]
              rfl

/-! ## 6. Witness-independence of `pqxdhExpectedOutcome` across equivalent `PqxdhPartyInSpecDomain` directory encodings -/

private theorem encodeDir_update_eq {W : PEParams} {st₁ st₂ : PqParty}
    (hp : st₁.party = st₂.party) (henc : encodeDir W st₁ = encodeDir W st₂)
    (k : IdentityKey) {x₁ x₂ : RecordExtras} {g₁ g₂ : GhostState Bytes}
    (hrec : encodeRecordUnderExtras (fun _ => x₁) g₁ = encodeRecordUnderExtras (fun _ => x₂) g₂) :
    encodeDir W { st₁ with peerId := some k, session := some (x₁, g₁) } =
    encodeDir W { st₂ with peerId := some k, session := some (x₂, g₂) } := by
  obtain ⟨hme, _, hsig, hot, hkot, hklr, _⟩ := encodeDir_nonSession_inj henc
  unfold encodeDir
  dsimp only
  rw [hp, hme, hsig, hot, hkot, hklr, hrec]

private theorem pqObserve_update_eq {W : PEParams} {i : Inputs} {st₁ st₂ : PqParty}
    (hp : st₁.party = st₂.party) (henc : encodeDir W st₁ = encodeDir W st₂)
    (k : IdentityKey) {x₁ x₂ : RecordExtras} {g₁ g₂ : GhostState Bytes} (out : List (BitVec 8))
    (hrec : encodeRecordUnderExtras (fun _ => x₁) g₁ = encodeRecordUnderExtras (fun _ => x₂) g₂) :
    pqxdhExpectedOutcome W i (some (some ({ st₁ with peerId := some k, session := some (x₁, g₁) }, out))) =
    pqxdhExpectedOutcome W i (some (some ({ st₂ with peerId := some k, session := some (x₂, g₂) }, out))) := by
  simp only [pqxdhExpectedOutcome, Option.map_some, encodeDir_update_eq hp henc k hrec]

private theorem trusts_congr {W : PEParams} {st₁ st₂ : PqParty}
    (henc : encodeDir W st₁ = encodeDir W st₂) (k : IdentityKey) :
    st₁.trusts k = st₂.trusts k := by
  obtain ⟨_, hpeer, _, _, _, _, _⟩ := encodeDir_nonSession_inj henc
  unfold PqParty.trusts
  rw [hpeer]

private theorem pqSend_observe_congr {W : PEParams} {i : Inputs} {st₁ st₂ : PqParty}
    (hparty : st₁.party = st₂.party) (hwf₁ : PqxdhPartyInSpecDomain W st₁) (hwf₂ : PqxdhPartyInSpecDomain W st₂)
    (henc : encodeDir W st₁ = encodeDir W st₂) (m r : List (BitVec 8)) :
    pqxdhExpectedOutcome W i (pqSendModel W st₁ m r) = pqxdhExpectedOutcome W i (pqSendModel W st₂ m r) := by
  obtain ⟨_, _, _, _, _, _, hsess⟩ := encodeDir_nonSession_inj henc
  unfold pqSendModel
  cases hs₁ : st₁.session with
  | none =>
    cases hs₂ : st₂.session with
    | none => rfl
    | some xg₂ => simp [hs₁, hs₂] at hsess
  | some xg₁ =>
    cases hs₂ : st₂.session with
    | none => simp [hs₁, hs₂] at hsess
    | some xg₂ =>
      obtain ⟨x₁, g₁⟩ := xg₁
      obtain ⟨x₂, g₂⟩ := xg₂
      simp only [hs₁, hs₂, List.cons.injEq, Prod.mk.injEq, and_true] at hsess
      have hl₁ : (encodeRecordUnderExtras (fun _ => x₁) g₁).length < 2 ^ 64 := by
        have := (hwf₁.1 x₁ g₁ hs₁).2.2; omega
      have hl₂ : (encodeRecordUnderExtras (fun _ => x₂) g₂).length < 2 ^ 64 := by
        have := (hwf₂.1 x₂ g₂ hs₂).2.2; omega
      obtain ⟨hgs, hxSteady, hxPend⟩ := encodeRecordX_peel hl₁ hl₂ hsess.2
      have hgp : g₁.party = g₂.party :=
        (hwf₁.1 x₁ g₁ hs₁).2.1.trans (hparty.trans (hwf₂.1 x₂ g₂ hs₂).2.1.symm)
      dsimp only
      rw [← hgp, ← hgs]
      cases hme : SessionState.messageEncrypt W.C protoSignalCodec (pqxdhSpqrSession W)
          ((pqxdhSessionParams W).sendAddrs g₁.party) m r g₁.session with
      | mk res s =>
        cases res with
        | error e => cases e <;> rfl
        | ok msg =>
          dsimp only
          cases g₁.session.remoteIdentity with
          | none => rfl
          | some k =>
            dsimp only
            rw [trusts_congr henc k]
            split
            · rfl
            · have hsPend : s.pendingPreKey = g₁.session.pendingPreKey :=
                messageEncrypt_pendingPreKey _ _ _ _ _ _ _ _ _ hme
              cases hp : g₁.session.pendingPreKey
              · exact pqObserve_update_eq hparty henc k _
                  (encodeRecordX_congr_of_pending_false rfl (hsPend.trans hp) hxSteady)
              · have hxEq := hxPend hp
                subst hxEq
                exact pqObserve_update_eq hparty henc k _ rfl

private theorem pqDecryptWith_observe_congr {W : PEParams} {i : Inputs} {st₁ st₂ : PqParty}
    (hparty : st₁.party = st₂.party) (henc : encodeDir W st₁ = encodeDir W st₂)
    {x₁ x₂ : RecordExtras} {g₁ g₂ : GhostState Bytes}
    (hgp : g₁.party = g₂.party) (hgs : g₁.session = g₂.session) (hx : ExtrasSteadyEq x₁ x₂)
    (msg : SignalMessage) (ty : MessageType) (rc : BitVec 256) :
    pqxdhExpectedOutcome W i (pqxdhSessionDecryptModel W st₁ x₁ g₁ msg ty rc) =
    pqxdhExpectedOutcome W i (pqxdhSessionDecryptModel W st₂ x₂ g₂ msg ty rc) := by
  unfold pqxdhSessionDecryptModel
  rw [← hgp, ← hgs]
  cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) ((pqxdhSessionParams W).expectedAddrs g₁.party)
      msg ty rc g₁.session with
  | mk res s =>
    cases res with
    | error e => cases e <;> rfl
    | ok pt =>
      dsimp only
      cases s.remoteIdentity with
      | none => rfl
      | some k =>
        dsimp only
        rw [trusts_congr henc k]
        split
        · rfl
        · have hsFalse : s.pendingPreKey = false :=
            tryDecryptFromRecord_pendingPreKey_false _ _ _ _ _ _ _ _ _ hdec
          exact pqObserve_update_eq hparty henc k pt
            (encodeRecordX_congr_of_pending_false rfl hsFalse hx)

private theorem pqRecvWhisper_observe_congr {W : PEParams} {i : Inputs} {st₁ st₂ : PqParty}
    (hparty : st₁.party = st₂.party) (hwf₁ : PqxdhPartyInSpecDomain W st₁) (hwf₂ : PqxdhPartyInSpecDomain W st₂)
    (henc : encodeDir W st₁ = encodeDir W st₂) (c : List (BitVec 8)) (rc : BitVec 256) :
    pqxdhExpectedOutcome W i (pqRecvWhisperModel W st₁ c rc) =
    pqxdhExpectedOutcome W i (pqRecvWhisperModel W st₂ c rc) := by
  obtain ⟨_, _, _, _, _, _, hsess⟩ := encodeDir_nonSession_inj henc
  unfold pqRecvWhisperModel
  cases hs₁ : st₁.session with
  | none =>
    cases hs₂ : st₂.session with
    | none => rfl
    | some xg₂ => simp [hs₁, hs₂] at hsess
  | some xg₁ =>
    cases hs₂ : st₂.session with
    | none => simp [hs₁, hs₂] at hsess
    | some xg₂ =>
      obtain ⟨x₁, g₁⟩ := xg₁
      obtain ⟨x₂, g₂⟩ := xg₂
      simp only [hs₁, hs₂, List.cons.injEq, Prod.mk.injEq, and_true] at hsess
      have hl₁ : (encodeRecordUnderExtras (fun _ => x₁) g₁).length < 2 ^ 64 := by
        have := (hwf₁.1 x₁ g₁ hs₁).2.2; omega
      have hl₂ : (encodeRecordUnderExtras (fun _ => x₂) g₂).length < 2 ^ 64 := by
        have := (hwf₂.1 x₂ g₂ hs₂).2.2; omega
      obtain ⟨hgs, hxSteady, _⟩ := encodeRecordX_peel hl₁ hl₂ hsess.2
      have hgp : g₁.party = g₂.party :=
        (hwf₁.1 x₁ g₁ hs₁).2.1.trans (hparty.trans (hwf₂.1 x₂ g₂ hs₂).2.1.symm)
      dsimp only
      cases SignalMessage.tryFrom protoSignalCodec c with
      | error _ => rfl
      | ok msg => exact pqDecryptWith_observe_congr hparty henc hgp hgs hxSteady msg .whisper rc

private theorem pqRecvPrekey_observe_congr {X : UnreachedPqxdhPrimitives} {W : PEParams} {i : Inputs}
    {st₁ st₂ : PqParty} (hparty : st₁.party = st₂.party) (hwf₁ : PqxdhPartyInSpecDomain W st₁) (hwf₂ : PqxdhPartyInSpecDomain W st₂)
    (henc : encodeDir W st₁ = encodeDir W st₂) (m : PreKeyMessageFields) (rc : BitVec 256) :
    pqxdhExpectedOutcome W i (pqRecvPrekeyModel X W st₁ m rc) =
    pqxdhExpectedOutcome W i (pqRecvPrekeyModel X W st₂ m rc) := by
  obtain ⟨_, _, _, _, _, _, hsess⟩ := encodeDir_nonSession_inj henc
  cases hs₁ : st₁.session with
  | none =>
    cases hs₂ : st₂.session with
    | none =>
      have hst : st₁ = st₂ := pqParty_eq_of_encodeDir_eq_noSession hparty hs₁ hs₂ henc
      rw [hst]
    | some xg₂ => simp [hs₁, hs₂] at hsess
  | some xg₁ =>
    cases hs₂ : st₂.session with
    | none => simp [hs₁, hs₂] at hsess
    | some xg₂ =>
      obtain ⟨x₁, g₁⟩ := xg₁
      obtain ⟨x₂, g₂⟩ := xg₂
      simp only [hs₁, hs₂, List.cons.injEq, Prod.mk.injEq, and_true] at hsess
      have hl₁ : (encodeRecordUnderExtras (fun _ => x₁) g₁).length < 2 ^ 64 := by
        have := (hwf₁.1 x₁ g₁ hs₁).2.2; omega
      have hl₂ : (encodeRecordUnderExtras (fun _ => x₂) g₂).length < 2 ^ 64 := by
        have := (hwf₂.1 x₂ g₂ hs₂).2.2; omega
      obtain ⟨hgs, hxSteady, _⟩ := encodeRecordX_peel hl₁ hl₂ hsess.2
      have hgp : g₁.party = g₂.party :=
        (hwf₁.1 x₁ g₁ hs₁).2.1.trans (hparty.trans (hwf₂.1 x₂ g₂ hs₂).2.1.symm)
      unfold pqRecvPrekeyModel
      cases SignalMessage.tryFrom protoSignalCodec m.inner with
      | error _ => rfl
      | ok inner =>
        dsimp only
        rw [trusts_congr henc ⟨⟨m.idPub⟩⟩]
        split
        · rfl
        · rw [hs₁, hs₂]
          dsimp only
          have hmiff : PqSessionMatches x₁ g₁ m ↔ PqSessionMatches x₂ g₂ m := by
            unfold PqSessionMatches
            rw [hxSteady.2.2, hgs]
          by_cases hm : PqSessionMatches x₁ g₁ m
          · have hm₂ : PqSessionMatches x₂ g₂ m := hmiff.mp hm
            simp only [hm, hm₂, ↓reduceIte]
            rw [← hgs, ← hgp]
            split
            · rfl
            · cases hdec : SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs g₁.party) inner .preKey rc g₁.session with
              | mk res s =>
                cases res with
                | error e => cases e <;> rfl
                | ok pt =>
                  have hsFalse : s.pendingPreKey = false :=
                    tryDecryptFromRecord_pendingPreKey_false _ _ _ _ _ _ _ _ _ hdec
                  exact pqObserve_update_eq hparty henc ⟨⟨m.idPub⟩⟩ pt
                    (encodeRecordX_congr_of_pending_false rfl hsFalse hxSteady)
          · have hm₂ : ¬ PqSessionMatches x₂ g₂ m := fun h => hm (hmiff.mpr h)
            simp [hm, hm₂]

/-! ## 7. Witness predicates, `pqModelRun`, and `cliSpecPq_pqModelRun` -/

/-- `(st, b, t)` witnesses an `init` input `i` in `CliSpecPqxdh`'s domain. -/
def InitWitness (W : PEParams) (i : Inputs)
    (p : PqParty × PreKeyBundleFields × List.Vector (BitVec 8) initiateTapeLen) : Prop :=
  PqxdhPartyInSpecDomain W p.1 ∧ p.1.session = none ∧ pqInitInputs W p.1 p.2.1 p.2.2 = i

/-- `(st, m, r)` witnesses a `send` input `i` in `CliSpecPqxdh`'s domain. -/
def SendWitness (W : PEParams) (i : Inputs)
    (p : PqParty × List (BitVec 8) × List.Vector (BitVec 8) 64) : Prop :=
  PqxdhPartyInSpecDomain W p.1 ∧ p.2.1.length < 2 ^ 32 ∧ pqSendInputs W p.1 p.2.1 p.2.2 = i

/-- `(st, c, rc)` witnesses a `recv` whisper (`2 ‖ c`) input `i` in `CliSpecPqxdh`'s domain. -/
def RecvWhisperWitness (W : PEParams) (i : Inputs)
    (p : PqParty × List (BitVec 8) × BitVec 256) : Prop :=
  PqxdhPartyInSpecDomain W p.1 ∧ p.2.1.length < 2 ^ 32 ∧ pqRecvInputs W p.1 (wireWhisper :: p.2.1) p.2.2 = i

/-- `(st, m, rc)` witnesses a `recv` pre-key (`3 ‖ m.bytes`) input `i` in `CliSpecPqxdh`'s domain. -/
def RecvPrekeyWitness (W : PEParams) (i : Inputs)
    (p : PqParty × PreKeyMessageFields × BitVec 256) : Prop :=
  PqxdhPartyInSpecDomain W p.1 ∧ p.2.1.inner.length + 2048 < 2 ^ 32 ∧
    (∀ x g, p.1.session = some (x, g) → PqSessionMatches x g p.2.1) ∧
    pqRecvInputs W p.1 (wirePrekey :: p.2.1.bytes) p.2.2 = i

/-- `(st, c, rc)` witnesses a `recv` non-whisper / non-prekey input `i` in `CliSpecPqxdh`'s domain. -/
def RecvOtherWitness (W : PEParams) (i : Inputs)
    (p : PqParty × List (BitVec 8) × BitVec 256) : Prop :=
  PqxdhPartyInSpecDomain W p.1 ∧ p.2.1.length < 2 ^ 32 ∧
    p.2.1.head? ≠ some wireWhisper ∧ p.2.1.head? ≠ some wirePrekey ∧
    pqRecvInputs W p.1 p.2.1 p.2.2 = i

open Classical in
/-- Pure PQXDH directory model run: answers every input in `CliSpecPqxdh`'s domain with the
model's outcome, and `none` elsewhere. -/
noncomputable def pqModelRun (X : UnreachedPqxdhPrimitives) (W : PEParams) : CliRun := fun i =>
  if h1 : ∃ p, InitWitness W i p then
    some (pqxdhExpectedOutcome W i
      (pqInitModel X W (Classical.choose h1).1 (Classical.choose h1).2.1 (Classical.choose h1).2.2))
  else if h2 : ∃ p, SendWitness W i p then
    if i.stdin.length > stdinCapBytes then
      some (.exited 2 [] (filesOf i.files))
    else if i.stdin.length > maxPlaintextBytes then
      some (.exited 1 [] (filesOf i.files))
    else
      some (pqxdhExpectedOutcome W i
        (pqSendModel W (Classical.choose h2).1 (Classical.choose h2).2.1
          (Classical.choose h2).2.2.toList))
  else if h3 : ∃ p, RecvWhisperWitness W i p then
    if i.stdin.length > stdinCapBytes then
      some (.exited 2 [] (filesOf i.files))
    else
      some (pqxdhExpectedOutcome W i
        (pqRecvWhisperModel W (Classical.choose h3).1 (Classical.choose h3).2.1
          (Classical.choose h3).2.2))
  else if h4 : ∃ p, RecvPrekeyWitness W i p then
    if i.stdin.length > stdinCapBytes then
      some (.exited 2 [] (filesOf i.files))
    else
      some (pqxdhExpectedOutcome W i
        (pqRecvPrekeyModel X W (Classical.choose h4).1 (Classical.choose h4).2.1
          (Classical.choose h4).2.2))
  else if _h5 : ∃ p, RecvOtherWitness W i p then
    if i.stdin.length > stdinCapBytes then
      some (.exited 2 [] (filesOf i.files))
    else
      some (.exited 1 [] (filesOf i.files))
  else none

private theorem initWitness_argv {W : PEParams} {i : Inputs} {p} (h : InitWitness W i p) :
    i.argv.head? = some "init" := by
  rw [← h.2.2]; rfl

private theorem sendWitness_argv {W : PEParams} {i : Inputs} {p} (h : SendWitness W i p) :
    i.argv.head? = some "send" := by
  rw [← h.2.2]; rfl

private theorem recvWhisperWitness_key {W : PEParams} {i : Inputs} {p}
    (h : RecvWhisperWitness W i p) :
    i.argv.head? = some "recv" ∧ i.stdin.head? = some wireWhisper := by
  rw [← h.2.2]; exact ⟨rfl, rfl⟩

private theorem recvPrekeyWitness_key {W : PEParams} {i : Inputs} {p}
    (h : RecvPrekeyWitness W i p) :
    i.argv.head? = some "recv" ∧ i.stdin.head? = some wirePrekey := by
  rw [← h.2.2.2]; exact ⟨rfl, rfl⟩

private theorem party_eq_of_pqInputs {W : PEParams} {st₁ st₂ : PqParty} {cmd₁ cmd₂ : Cmd}
    {e₁ e₂ : List DirEntry} {c₁ c₂ s₁ s₂ : List (BitVec 8)}
    (hp₁ : cmd₁.argv[1]? = some (partyAddress st₁.party.other).text)
    (hp₂ : cmd₂.argv[1]? = some (partyAddress st₂.party.other).text)
    (h : pqInputs W st₁ cmd₁ e₁ c₁ s₁ = pqInputs W st₂ cmd₂ e₂ c₂ s₂) :
    st₁.party = st₂.party := by
  have ha : cmd₁.argv[1]? = cmd₂.argv[1]? := congrArg (fun x : Inputs => x.argv[1]?) h
  rw [hp₁, hp₂, Option.some.injEq] at ha
  exact addrE_other_text_inj ha

/-- Satisfiability of `CliSpecPqxdh` for every `(X : UnreachedPqxdhPrimitives) (W : PEParams)`. -/
theorem cliSpecPq_pqModelRun (X : UnreachedPqxdhPrimitives) (W : PEParams) :
    CliSpecPqxdh (pqModelRun X W) X W := by
  intro st hwf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- init
    intro b t hsess
    set i := pqInitInputs W st b t
    have hex : ∃ p, InitWitness W i p := ⟨(st, b, t), hwf, hsess, rfl⟩
    simp only [pqModelRun, hex, ↓reduceDIte]
    set p := Classical.choose hex
    obtain ⟨_, hsess', heq⟩ : InitWitness W i p := Classical.choose_spec hex
    have hparty : p.1.party = st.party := party_eq_of_pqInputs rfl rfl heq
    have hfiles : (pqInitInputs W p.1 p.2.1 p.2.2).files = (pqInitInputs W st b t).files :=
      congrArg Inputs.files heq
    simp only [pqInitInputs, pqInputs] at hfiles
    obtain ⟨hdirb, ht⟩ := snoc_inj hfiles
    simp only [Prod.mk.injEq, true_and] at ht
    obtain ⟨hdir, hb⟩ := split_encodeDir_bundle hdirb
    have hst : p.1 = st := pqParty_eq_of_encodeDir_eq_noSession hparty hsess' hsess hdir
    have htEq : p.2.2 = t := List.Vector.eq _ _ ht
    rw [hst, hb, htEq]
  · -- send
    intro m r hlen
    set i := pqSendInputs W st m r
    have hex : ∃ p, SendWitness W i p := ⟨(st, m, r), hwf, hlen, rfl⟩
    have hno1 : ¬ ∃ p, InitWitness W i p := by
      rintro ⟨p, hp⟩; have := initWitness_argv hp; simp [i, pqSendInputs, pqInputs, Cmd.argv] at this
    simp only [pqModelRun, hno1, hex, ↓reduceDIte]
    have hlenEq : i.stdin = m := rfl
    rw [hlenEq]
    by_cases hc : m.length > stdinCapBytes
    · simp only [hc, ↓reduceIte]
    · by_cases hm : m.length > maxPlaintextBytes
      · simp only [hc, hm, ↓reduceIte]
      · simp only [hc, hm, ↓reduceIte]
        set p := Classical.choose hex
        obtain ⟨hwf', _, heq⟩ : SendWitness W i p := Classical.choose_spec hex
        have hparty : p.1.party = st.party := party_eq_of_pqInputs rfl rfl heq
        have hfiles : (pqSendInputs W p.1 p.2.1 p.2.2).files = (pqSendInputs W st m r).files :=
          congrArg Inputs.files heq
        have hstdin : (pqSendInputs W p.1 p.2.1 p.2.2).stdin = (pqSendInputs W st m r).stdin :=
          congrArg Inputs.stdin heq
        simp only [pqSendInputs, pqInputs, List.append_nil] at hfiles
        simp only [pqSendInputs, pqInputs] at hstdin
        obtain ⟨hdir, hr⟩ := snoc_inj hfiles
        simp only [Prod.mk.injEq, true_and] at hr
        rw [hstdin, hr]
        exact congrArg some (pqSend_observe_congr hparty hwf' hwf hdir m r.toList)
  · -- recv whisper
    intro c rc hlen
    set i := pqRecvInputs W st (wireWhisper :: c) rc
    have hex : ∃ p, RecvWhisperWitness W i p := ⟨(st, c, rc), hwf, hlen, rfl⟩
    have hno1 : ¬ ∃ p, InitWitness W i p := by
      rintro ⟨p, hp⟩; have := initWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    have hno2 : ¬ ∃ p, SendWitness W i p := by
      rintro ⟨p, hp⟩; have := sendWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    simp only [pqModelRun, hno1, hno2, hex, ↓reduceDIte]
    have hlenEq : i.stdin = wireWhisper :: c := rfl
    rw [hlenEq]
    by_cases hc : (wireWhisper :: c).length > stdinCapBytes
    · simp only [hc, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
      set p := Classical.choose hex
      obtain ⟨hwf', _, heq⟩ : RecvWhisperWitness W i p := Classical.choose_spec hex
      have hparty : p.1.party = st.party := party_eq_of_pqInputs rfl rfl heq
      have hfiles : (pqRecvInputs W p.1 (wireWhisper :: p.2.1) p.2.2).files =
          (pqRecvInputs W st (wireWhisper :: c) rc).files := congrArg Inputs.files heq
      have hstdin : (pqRecvInputs W p.1 (wireWhisper :: p.2.1) p.2.2).stdin =
          (pqRecvInputs W st (wireWhisper :: c) rc).stdin := congrArg Inputs.stdin heq
      simp only [pqRecvInputs, pqInputs, List.append_nil] at hfiles
      simp only [pqRecvInputs, pqInputs, List.cons.injEq, true_and] at hstdin
      obtain ⟨hdir, hrc⟩ := snoc_inj hfiles
      simp only [Prod.mk.injEq, true_and] at hrc
      rw [hstdin, keyToBytes32_inj hrc]
      exact congrArg some (pqRecvWhisper_observe_congr hparty hwf' hwf hdir c rc)
  · -- recv prekey
    intro m rc hlen hmatch
    set i := pqRecvInputs W st (wirePrekey :: m.bytes) rc
    have hex : ∃ p, RecvPrekeyWitness W i p := ⟨(st, m, rc), hwf, hlen, hmatch, rfl⟩
    have hno1 : ¬ ∃ p, InitWitness W i p := by
      rintro ⟨p, hp⟩; have := initWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    have hno2 : ¬ ∃ p, SendWitness W i p := by
      rintro ⟨p, hp⟩; have := sendWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    have hno3 : ¬ ∃ p, RecvWhisperWitness W i p := by
      rintro ⟨p, hp⟩
      have hk := (recvWhisperWitness_key hp).2
      simp [i, pqRecvInputs, pqInputs, wirePrekey, wireWhisper] at hk
    simp only [pqModelRun, hno1, hno2, hno3, hex, ↓reduceDIte]
    have hlenEq : i.stdin = wirePrekey :: m.bytes := rfl
    rw [hlenEq]
    by_cases hc : (wirePrekey :: m.bytes).length > stdinCapBytes
    · simp only [hc, ↓reduceIte]
    · simp only [hc, ↓reduceIte]
      set p := Classical.choose hex
      obtain ⟨hwf', _, _, heq⟩ : RecvPrekeyWitness W i p := Classical.choose_spec hex
      have hparty : p.1.party = st.party := party_eq_of_pqInputs rfl rfl heq
      have hfiles : (pqRecvInputs W p.1 (wirePrekey :: p.2.1.bytes) p.2.2).files =
          (pqRecvInputs W st (wirePrekey :: m.bytes) rc).files := congrArg Inputs.files heq
      have hstdin : (pqRecvInputs W p.1 (wirePrekey :: p.2.1.bytes) p.2.2).stdin =
          (pqRecvInputs W st (wirePrekey :: m.bytes) rc).stdin := congrArg Inputs.stdin heq
      simp only [pqRecvInputs, pqInputs, List.append_nil] at hfiles
      simp only [pqRecvInputs, pqInputs, List.cons.injEq, true_and] at hstdin
      obtain ⟨hdir, hrc⟩ := snoc_inj hfiles
      simp only [Prod.mk.injEq, true_and] at hrc
      rw [PreKeyMessageFields.bytes_inj hstdin, keyToBytes32_inj hrc]
      exact congrArg some (pqRecvPrekey_observe_congr hparty hwf' hwf hdir m rc)
  · -- recv other
    intro c rc hlen hnw hnp
    set i := pqRecvInputs W st c rc
    have hex : ∃ p, RecvOtherWitness W i p := ⟨(st, c, rc), hwf, hlen, hnw, hnp, rfl⟩
    have hno1 : ¬ ∃ p, InitWitness W i p := by
      rintro ⟨p, hp⟩; have := initWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    have hno2 : ¬ ∃ p, SendWitness W i p := by
      rintro ⟨p, hp⟩; have := sendWitness_argv hp; simp [i, pqRecvInputs, pqInputs, Cmd.argv] at this
    have hno3 : ¬ ∃ p, RecvWhisperWitness W i p := by
      rintro ⟨p, hp⟩; exact hnw (recvWhisperWitness_key hp).2
    have hno4 : ¬ ∃ p, RecvPrekeyWitness W i p := by
      rintro ⟨p, hp⟩; exact hnp (recvPrekeyWitness_key hp).2
    simp only [pqModelRun, hno1, hno2, hno3, hno4, hex, ↓reduceDIte]
    rfl

#print axioms cliSpecPq_pqModelRun

end CryptoVerification.SignalSession
