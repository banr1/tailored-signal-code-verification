/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Lazy
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.CKA.DDHDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# Correctness of the Abstract DH-Ratchet CKA

**Checked by Lean.**

Proves correctness (`dhScheme_agreesFrom`, `dhScheme_correct`) of the Diffie–Hellman CKA scheme
`dhScheme D` for any commuting DH function `D` (DEV-CKA10), as used by the session security proof
while keeping CKA security as a standalone assumption (DEV-LS30).

**DEV-CKA8 (formalization): the cyclic group in module notation.** VCVio models cyclic-group DDH
with exponents in a field `F` acting on an `F`-module `G` via a bijective generator map `x ↦ x • g`,
whereas `dhScheme D` abstracts commuting scalar multiplication directly.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory CryptoGames.Lazy CryptoGames.CKA.DDH

namespace CryptoGames.CKA

open DHFun DDH

variable {Sc Pt : Type}

theorem dhScheme_agreesFrom [Zero Pt] (D : DHFun Sc Pt) (hD : D.Commutes) (y : Sc)
    (rs : List Sc) : (dhScheme D).AgreesFrom (.pub (D.dh y D.base)) (.exp y) rs := by
  induction rs generalizing y with
  | nil => trivial
  | cons r rs ih => exact ⟨hD r y, ih r⟩

/-- `dhScheme D` is a correct CKA scheme whenever `D` commutes. -/
theorem dhScheme_correct [Zero Pt] (D : DHFun Sc Pt) (hD : D.Commutes) : (dhScheme D).Correct :=
  fun x₀ rs => dhScheme_agreesFrom D hD x₀ rs

end CryptoGames.CKA
