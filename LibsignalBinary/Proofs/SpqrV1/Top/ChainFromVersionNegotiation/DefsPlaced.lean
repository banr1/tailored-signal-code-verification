/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.TopLeafCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternal

/-!
# Relocatable Specifications for `spqr::chain_from_version_negotiation` (Block `328`)

Relocatable `withLsCallInv` contract `ChainFromVersionNegotiationPlacedOkX` for Block `328`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.Placed

/-- Relocatable callee-contract predicate for `spqr::chain_from_version_negotiation` (Block `328`). -/
def ChainFromVersionNegotiationPlacedOkX [LibsignalPlacement] (hkdf : HkdfFn) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_328).rebase (blkPl_328).base (Rust.withPanics ext))
    (blkPl_328).base
    (withLsCallInv lsmpl (chainFromVersionNegotiationSpecX hkdf A))

end CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
