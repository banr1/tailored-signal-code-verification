/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsAuthPrf
public import Computational.Specifications.Assumptions.KemCorrect
public import Computational.Proofs.CryptoGames.AEAD.EffSaltProofDefs
/-!
# Effective 32-byte HKDF salt of `deriveMsgKeys` (DEV-LS25)

For salts of at most 32 bytes, `deriveMsgKeysRef` depends only on `effectiveHkdfSaltBytes` because
HMAC zero-pads its key to 64 bytes. Under `WellFormedPrimitivesδ`, every SPQR salt has at most 32
bytes, so `deriveMsgKeys` agrees with `deriveMsgKeysEff`.
-/

@[expose] public section
set_option autoImplicit false
namespace SignalPqxdh.Security
open SignalPqxdh

/-- The salt (if any) has at most 32 bytes. -/
def SaltOK (s? : Option Bytes) : Prop := ∀ s ∈ s?, s.length ≤ 32

theorem fitBytesRef_append_zeros (N : Nat) (k : Bytes) (n : Nat) (h : k.length + n ≤ N) :
    fitBytesRef N (k ++ List.replicate n 0) = fitBytesRef N k := by
  unfold fitBytesRef
  rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega)]
  simp only [List.length_append, List.length_replicate, List.append_assoc,
    List.replicate_append_replicate]
  congr 2
  omega

/-- HMAC zero-pads a key of at most 64 bytes, so appending zeros below 64 bytes is invisible. -/
theorem hmacSha256Ref_append_zeros (P : Primitives) (k m : Bytes) (n : Nat)
    (h : k.length + n ≤ 64) :
    hmacSha256Ref P (k ++ List.replicate n 0) m = hmacSha256Ref P k m := by
  have h1 : ¬ (k ++ List.replicate n 0).length > 64 := by simp; omega
  have h2 : ¬ k.length > 64 := by omega
  simp only [hmacSha256Ref, h1, h2, ↓reduceIte, fitBytesRef_append_zeros 64 k n h]

theorem saltKeyB_toList_some {s : Bytes} (h : s.length ≤ 32) :
    (effectiveHkdfSaltBytes (some s)).toList = s ++ List.replicate (32 - s.length) 0 := by
  simp only [effectiveHkdfSaltBytes, CryptoGames.effectiveHkdfSalt, Option.map_some, Option.getD_some]
  exact CryptoGames.fit32_toList_of_length_le h

theorem saltKeyB_toList_none : (effectiveHkdfSaltBytes none).toList = List.replicate 32 0 := by
  simp [effectiveHkdfSaltBytes, CryptoGames.effectiveHkdfSalt]

theorem hkdfExtractRef_saltKeyB (P : Primitives) (s? : Option Bytes) (h : SaltOK s?)
    (ikm : Bytes) :
    hkdfExtractRef P (some (effectiveHkdfSaltBytes s?).toList) ikm = hkdfExtractRef P s? ikm := by
  cases s? with
  | none => simp only [hkdfExtractRef, saltKeyB_toList_none]
  | some s =>
    have hs : s.length ≤ 32 := h s rfl
    simp only [hkdfExtractRef, saltKeyB_toList_some hs]
    exact hmacSha256Ref_append_zeros P s ikm _ (by omega)

theorem deriveMsgKeysRef_saltKeyB (P : Primitives) (seed : Bytes) (s? : Option Bytes)
    (h : SaltOK s?) :
    deriveMsgKeysRef P seed (some (effectiveHkdfSaltBytes s?).toList) = deriveMsgKeysRef P seed s? := by
  simp only [deriveMsgKeysRef, hkdfExtractRef_saltKeyB P s? h]

/-- `deriveMsgKeys` at a salt of at most 32 bytes is `deriveMsgKeys` at its effective salt. -/
theorem deriveMsgKeys_saltKeyB {P : Primitives} (hWF : WellFormedPrimitivesδ P) (seed : Bytes)
    (s? : Option Bytes) (h : SaltOK s?) :
    P.deriveMsgKeys seed (some (effectiveHkdfSaltBytes s?).toList) = P.deriveMsgKeys seed s? := by
  rw [hWF.deriveMsgKeys_eq_ref, hWF.deriveMsgKeys_eq_ref, deriveMsgKeysRef_saltKeyB P seed s? h]

theorem saltOK_of_spqrInitRecv {P : Primitives} (hWF : WellFormedPrimitivesδ P)
    {k m st : Bytes} {s? : Option Bytes} (h : P.spqrInitRecv k m = some (st, s?)) :
    SaltOK s? := by
  intro s hs
  cases hs
  exact hWF.spqrInitRecv_salt_len k m st s h

theorem saltOK_of_spqrInitSend {P : Primitives} (hWF : WellFormedPrimitivesδ P)
    {k c st m : Bytes} {s? : Option Bytes} (h : P.spqrInitSend k c = some (st, s?, m)) :
    SaltOK s? := by
  obtain ⟨stB, hR⟩ := hWF.spqr_corr k c st s? m h
  exact saltOK_of_spqrInitRecv hWF hR

/-- `deriveMsgKeys` at the 32-byte effective salt: the real `PrfMsgKeys` oracle answer. -/
def deriveMsgKeysEff (P : Primitives) (seed : Bytes) (s? : Option Bytes) : MessageKeys :=
  P.deriveMsgKeys seed (some (effectiveHkdfSaltBytes s?).toList)

theorem deriveMsgKeysEff_congr (P : Primitives) (seed : Bytes) {s₁ s₂ : Option Bytes}
    (h : sameSaltKey s₁ s₂ = true) : deriveMsgKeysEff P seed s₁ = deriveMsgKeysEff P seed s₂ := by
  have hk : effectiveHkdfSaltBytes s₁ = effectiveHkdfSaltBytes s₂ := beq_iff_eq.mp h
  simp only [deriveMsgKeysEff, hk]

theorem deriveMsgKeysEff_eq {P : Primitives} (hWF : WellFormedPrimitivesδ P) (seed : Bytes)
    {s? : Option Bytes} (h : SaltOK s?) : deriveMsgKeysEff P seed s? = P.deriveMsgKeys seed s? :=
  deriveMsgKeys_saltKeyB hWF seed s? h

theorem mkSaltKeyMatch_of_sid_ne {S : Setup} {k : SessionId S × Option Bytes} {sid : SessionId S}
    (h : k.1 ≠ sid) (s? : Option Bytes) : mkSaltKeyMatch k sid s? = false := by
  simp [mkSaltKeyMatch, h]

theorem mkSaltKeyMatch_sameSaltKey {S : Setup} {k : SessionId S × Option Bytes}
    {sid : SessionId S} {s? : Option Bytes} (h : mkSaltKeyMatch k sid s? = true) :
    k.1 = sid ∧ sameSaltKey k.2 s? = true := by
  simp only [mkSaltKeyMatch, Bool.and_eq_true, beq_iff_eq] at h
  exact h

end SignalPqxdh.Security
