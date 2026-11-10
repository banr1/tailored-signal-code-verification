/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.CKA.Defs
public import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# CKA party state for Diffie–Hellman ratchets (ACD19 §4.1.2)

**Trusted: definitions used by the statement.** The theorems of `Computational/Theorems/` use every
definition in this file: read them. The theorems here are checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines the party state `State` of the Diffie–Hellman continuous-key-agreement (CKA) scheme of
ACD19 §4.1.2, shared by the module-based scheme (`Computational/Proofs/CryptoGames/CKA/DDHProofDefs.lean`,
DEV-CKA9) and libsignal's abstract-DH instantiation (`CKA/LibsignalCKA.lean`). A party holds either
the peer's latest public element (`pub h`) or its own latest secret exponent (`exp x`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.CKA.DDH

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- DDH-CKA party state (ACD19 §4.1.2): a peer public element `pub h` or a secret exponent `exp x`. -/
inductive State (F G : Type) where
  | pub (h : G)
  | exp (x : F)

section Reduction

variable [SampleableType F] [SampleableType G] (g : G) (tStar : ℕ)

local notation "GameM" => StateT (GameState (State F G) G) ProbComp

end Reduction

end CryptoGames.CKA.DDH
