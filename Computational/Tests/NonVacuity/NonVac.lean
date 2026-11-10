/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalSessionProofDefs
import LibsignalBinary.Proofs.ConsumeMessageKey.NonVacProofs.StateWitness

/-!
# Satisfiability of the `consume_message_key` Specification

Proves `ConsumeMessageKeySpecSatisfiable F img` for every loaded image `img` and SHA-256
compression function `F`. Exhibits allocator hooks satisfying `AllocHooks` and
`AllocSucceedsWithRoom` (failing only when no unmapped block fits) together with an entry state
with 1 MiB of unmapped address space that satisfies `consumeMessageKeySpec`'s precondition on a
store-loop call (`counter > index + 1`, `message_keys` capacity `0`, model result `Ok`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Every loaded image `img` admits trace-preserving allocator hooks (`AllocWitness`) and a
disjoint 16 KiB read-write arena plus 1 MiB unmapped region (`StateWitness`) that satisfy
`ConsumeMessageKeySpecSatisfiable F img`. -/
theorem cmkSpec_nonvacuous_ok (F : ShaState → List (BitVec 8) → ShaState) (img : Obj.Image) :
    ConsumeMessageKeySpecSatisfiable F img := by
  exact NonVacuityWitness.cmkNonVacStmt_proof F img

end CryptoVerification.LibsignalSession
