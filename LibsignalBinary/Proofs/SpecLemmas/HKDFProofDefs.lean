/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import Mathlib.Data.Vector.Basic

/-!
# HKDF Helper Definitions and Salt-Padding Lemmas

Defines `hkdfExtractRaw` on arbitrary-length optional salts and proves `hmacWith_append_zeros` and
`hkdfExtractRaw_eq_saltKey` (`effectiveHkdfSalt` reduction for salts of at most `32` bytes).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.HKDFProofDefs

open CryptoGames (fit32 effectiveHkdfSalt)
open CryptoGames.HMAC (ShaState hmacWith)
open CryptoGames.HKDF (hkdfExtract)

theorem fit32_toList_of_length_le {α : Type} [OfNat α 0] {s : List α} (h : s.length ≤ 32) :
    (fit32 s).toList = s ++ List.replicate (32 - s.length) 0 := by
  simp [fit32, List.Vector.toList, List.take_of_length_le h]

/-- HKDF-Extract on a salt of any length (`Hkdf::new(Option<&[u8]>, ikm)`). -/
def hkdfExtractRaw (F : ShaState → List (BitVec 8) → ShaState) (salt? : Option (List (BitVec 8)))
    (ikm : List (BitVec 8)) : List (BitVec 8) :=
  hmacWith F (salt?.getD (List.replicate 32 0)) ikm

/-- HMAC zero-pads a key of at most 64 bytes, so appending zeros below 64 bytes is invisible. -/
theorem hmacWith_append_zeros (F : ShaState → List (BitVec 8) → ShaState) (k m : List (BitVec 8))
    (n : ℕ) (h : k.length + n ≤ 64) : hmacWith F (k ++ List.replicate n 0) m = hmacWith F k m := by
  have h1 : ¬ 64 < (k ++ List.replicate n 0).length := by simp; omega
  have h2 : ¬ 64 < k.length := by omega
  have hk : k ++ List.replicate n 0 ++ List.replicate (64 - (k ++ List.replicate n 0).length) 0 =
      k ++ List.replicate (64 - k.length) 0 := by
    rw [List.append_assoc, List.replicate_append_replicate]; congr 2; simp; omega
  simp only [hmacWith, h1, h2, ite_false, hk]

/-- Effective salt (DEV-LS25, checked): on salts of at most 32 bytes, HKDF-Extract depends only
on `effectiveHkdfSalt salt?`, the salt zero-padded to 32 bytes (`none` = 32 zero bytes). -/
theorem hkdfExtractRaw_eq_saltKey (F : ShaState → List (BitVec 8) → ShaState)
    (salt? : Option (List (BitVec 8))) (h : ∀ s ∈ salt?, s.length ≤ 32) (ikm : List (BitVec 8)) :
    hkdfExtractRaw F salt? ikm = hkdfExtract F (some (effectiveHkdfSalt salt?)) ikm := by
  cases salt? with
  | none => rfl
  | some s =>
    have hs : s.length ≤ 32 := h s rfl
    simp only [hkdfExtractRaw, hkdfExtract, effectiveHkdfSalt, Option.map_some, Option.getD_some,
      fit32_toList_of_length_le hs]
    exact (hmacWith_append_zeros F s ikm _ (by omega)).symm

end LibsignalBinary.Proofs.SpecLemmas.HKDFProofDefs

-- AUTO-BRIDGE BEGIN
namespace CryptoGames
export LibsignalBinary.Proofs.SpecLemmas.HKDFProofDefs (fit32_toList_of_length_le)
end CryptoGames
namespace CryptoGames.HKDF
export LibsignalBinary.Proofs.SpecLemmas.HKDFProofDefs (hkdfExtractRaw hmacWith_append_zeros hkdfExtractRaw_eq_saltKey)
end CryptoGames.HKDF
-- AUTO-BRIDGE END
