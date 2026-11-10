/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCLazy
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.Bday
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.Hop1
import LibsignalBinary.Proofs.CryptoGames.AEAD.CBCProof.Hop2

/-!
# One-time IND-CPA security of AES-256-CBC (PKCS#7) from a PRF

**Checked by Lean.** No theorem of `Computational/Theorems/` unfolds a definition of this file, and
Lean's kernel checks every proof in it: you do not need to read it to trust those theorems.

Proves one-time IND-CPA security of CBC-mode encryption from PRF security of the block function via
a PRF game hop (`cbc_branch_false_eq`) and a birthday bound (`cbcLazy_close`) against a lazily
sampled random function (`CBCLazy.lean`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames
namespace CBC

/-- The real IND-CPA branch equals the real PRF branch of `cbcRed`. -/
theorem cbc_branch_false_eq {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    𝒟[(cbcScheme E encode).branch false A] = 𝒟[(blockPRF E).branch false (cbcRed encode A)] := by
  exact Hop1.cbc_branch_false_eq E encode A

/-- CBC with a lazy random function and a uniform IV is within `n(n−1)/2 · 2⁻¹²⁸` of uniform. -/
theorem cbcLazy_close {n : ℕ} (P : List.Vector Block n)
    (F : List.Vector Block n → ProbComp Bool) :
    𝒟[cbcLazy P >>= F].boolDist 𝒟[$ᵗ (List.Vector Block n) >>= F] ≤
      ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  exact Bday.cbcLazy_close P F

/-- If `cbcLazy (encode m)` is `ε`-close to uniform for every `m`, then the ideal PRF branch of
`cbcRed` is `ε`-close to the ideal IND-CPA branch. -/
theorem cbc_branch_true_le {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) (ε : ℝ≥0∞)
    (h : ∀ (m : M) (F : List.Vector Block n → ProbComp Bool),
      𝒟[cbcLazy (encode m) >>= F].boolDist 𝒟[$ᵗ (List.Vector Block n) >>= F] ≤ ε) :
    𝒟[(blockPRF E).branch true (cbcRed encode A)].boolDist
      𝒟[(cbcScheme E encode).branch true A] ≤ ε := by
  exact Hop2.cbc_branch_true_le E encode A ε h

/-- One-time IND-CPA security of CBC from a PRF for any deterministic block encoding. -/
theorem cbc_indcpa {M : Type} {n : ℕ} (E : AesKey → Block → Block)
    (encode : M → List.Vector Block n)
    (A : CipherScheme.INDCPAAdversary M (List.Vector Block n)) :
    (cbcScheme E encode).indcpaAdvantage A ≤
      (blockPRF E).prfAdvantage (cbcRed encode A) + ((n * (n - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
  rw [CipherScheme.indcpaAdvantage_eq_boolDist, MACScheme.prfAdvantage_eq_boolDist]
  have hbday := cbc_branch_true_le E encode A _ fun m F => cbcLazy_close (encode m) F
  rw [Measure.boolDist_comm] at hbday
  calc 𝒟[(cbcScheme E encode).branch true A].boolDist 𝒟[(cbcScheme E encode).branch false A]
      ≤ 𝒟[(cbcScheme E encode).branch true A].boolDist
            𝒟[(blockPRF E).branch true (cbcRed encode A)] +
          𝒟[(blockPRF E).branch true (cbcRed encode A)].boolDist
            𝒟[(cbcScheme E encode).branch false A] := Measure.boolDist_triangle _ _ _
    _ ≤ _ := by
      rw [cbc_branch_false_eq, add_comm]
      exact add_le_add le_rfl hbday

/-- One-time IND-CPA security of AES-256-CBC with PKCS#7 padding on `ℓ`-byte plaintexts. -/
theorem specCbc_indcpa (E : AesKey → Block → Block) (ℓ : ℕ)
    (A : CipherScheme.INDCPAAdversary (Plain ℓ) (List.Vector Block (nBlocks ℓ))) :
    (cbcPkcs7EncryptOnly E ℓ).indcpaAdvantage A ≤
      (blockPRF E).prfAdvantage (cbcRed pkcs7Blocks A) +
        ((nBlocks ℓ * (nBlocks ℓ - 1) / 2 : ℕ) : ℝ≥0∞) / 2 ^ 128 :=
  cbc_indcpa E pkcs7Blocks A

end CBC
end CryptoGames
