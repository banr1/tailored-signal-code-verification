/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.Model

/-!
# Pure Cryptographic Packaging for Extern Interpretations

Packages an `ExternInterpretation` and AES-CBC block cipher operations into
`CryptoGames.LibsignalSession.Crypto` and proves basic projection lemmas.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.libsignal.Hooks2

open CryptoGames
open CryptoGames.CBC (AesKey Block)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement
open DY.Libsignal.Composed.Refinement (vec32)

theorem vec32_toList_of_length_32' (b : List (BitVec 8)) (hb : b.length = 32) :
    (vec32 b).toList = b := by
  simp only [vec32, List.Vector.toList, List.take_append_of_le_length (by omega : 32 ≤ b.length)]
  rw [← hb, List.take_length]

/-- Packages `interpretation` and AES-CBC block cipher operations `E` and `D` into
`CryptoGames.LibsignalSession.Crypto`. -/
def cryptoOf' (interpretation : ExternInterpretation)
    (E D : AesKey → Block → Block := fun _ b => b) :
    Crypto where
  F := sha256CompressFunction interpretation
  E := E
  D := D
  X := fun sec pub =>
    vec32 ((interpretation x25519AgreementSymbol [sec.toList, pub.toList]).getD [])
  pubKey := fun sec =>
    vec32 ((interpretation x25519PublicKeySymbol [sec.toList]).getD [])

@[scoped simp]
theorem cryptoOf'_F (interpretation : ExternInterpretation) (E D : AesKey → Block → Block) :
    (cryptoOf' interpretation E D).F = sha256CompressFunction interpretation := rfl

theorem cryptoOf'_X_toList_of_some (interpretation : ExternInterpretation)
    (E D : AesKey → Block → Block)
    (sec pub : List.Vector (BitVec 8) 32) (shared : List (BitVec 8)) (h32 : shared.length = 32)
    (h : interpretation x25519AgreementSymbol [sec.toList, pub.toList] = some shared) :
    ((cryptoOf' interpretation E D).X sec pub).toList = shared := by
  dsimp [cryptoOf']
  rw [h, Option.getD_some]
  exact vec32_toList_of_length_32' shared h32

theorem cryptoOf'_pubKey_toList_of_some (interpretation : ExternInterpretation)
    (E D : AesKey → Block → Block)
    (sec : List.Vector (BitVec 8) 32) (pub : List (BitVec 8)) (h32 : pub.length = 32)
    (h : interpretation x25519PublicKeySymbol [sec.toList] = some pub) :
    ((cryptoOf' interpretation E D).pubKey sec).toList = pub := by
  dsimp [cryptoOf']
  rw [h, Option.getD_some]
  exact vec32_toList_of_length_32' pub h32

end Proofs.libsignal.Hooks2
