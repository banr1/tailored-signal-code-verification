/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.Defs
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym

/-!
# Relocatable `[LibsignalPlacement]` Specifications for `spqr::chain_from` (Block `323`)

Relocatable `withLsCallInv` contracts `ChainFromPbPlacedOkX` (Block `364`) and `ChainFromPlacedOkX` (Block `323`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.ChainFrom

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.Placed

/-- Relocatable `<spqr::chain::Chain>::from_pb` (Block `364`) meets
`withLsCallInv lsmpl (chainFromPbSpecX A)` on `Rust.withPanics ext`. -/
def ChainFromPbPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
    (lsmpl.base 364)
    (withLsCallInv lsmpl (chainFromPbSpecX A))

/-- Relocatable `spqr::chain_from` (Block `323`) meets `withLsCallInv lsmpl (chainFromSpecX hkdf A)`
on `Rust.withPanics ext`. -/
def ChainFromPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
    (blkPl_323).base
    (withLsCallInv lsmpl (chainFromSpecX hkdf A))

end CryptoVerification.SpqrV1.Top.ChainFrom
