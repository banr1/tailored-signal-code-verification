/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecode

/-!
# Budget-Threaded `IdentityKey::decode` Proof

Relocatable `[LibsignalPlacement]` proof of `IdentityKey::decode` (Block `18`, `0` heap
allocations) over `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecodeBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement blkPC_211 blkPl_211)
open CryptoVerification.LibsignalTripleRatchet (pkTryFromPlacedSpec)
open CryptoVerification.RecordCodecs.Placed (blkPl_18 lsProg_18)
open LibsignalBinary.Heap (AllocCostModel RustCliAllocBudget)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (identityKeyDecodePlacedSpec)

/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedSpec A`, given the
relocatable `PublicKey::try_from` contract (Block `211`). -/
theorem identityKey_decode_placed_ok_of_pkTryFrom [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {H : LibsignalHooks}
    (hpk : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H)
      (blkPl_211).base pkTryFromPlacedSpec) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok_of_pkTryFrom
    (A := A.repAlloc) hpk

/-- Relocatable `IdentityKey::decode` (Block `18`) meets `identityKeyDecodePlacedSpec A` for any
hooks `H`. -/
theorem identityKey_decode_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} (H : LibsignalHooks) :
    subroutine_ok (lsProg_18 H) (blkPl_18).base (identityKeyDecodePlacedSpec A) :=
  CryptoVerification.RecordCodecsBinary.IdentityKeyDecode.identityKey_decode_placed_ok
    (A := A.repAlloc) H

end LibsignalBinary.Proofs.RecordCodecs.IdentityKeyDecodeBudget
