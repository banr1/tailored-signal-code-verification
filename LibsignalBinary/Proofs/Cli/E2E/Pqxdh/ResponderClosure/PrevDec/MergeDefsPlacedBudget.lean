/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym

/-!
# Budget-Threaded Relocatable Handshake `bytes::merge [local#5]` Definitions

Budget-threaded (`RustCliAllocBudget M`) relocatable specifications (`bytesMerge3PlacedSpec`,
`bytesMerge3ProtoPlacedSpec`) and contract propositions (`BytesMerge6PlacedOkExt`,
`BytesMerge6ProtoPlacedOkExt`) for `prost::encoding::bytes::merge [local#5]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (BytesMergeProtoGhost)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget (
  bytesMerge3ProtoRawSpec bytesMerge3RawSpec
)

/-- Relocatable `[LibsignalPlacement]` budget-threaded spec of
`prost::encoding::bytes::merge [local#5]` using `mergeBytes` on `lsProg_518 ext`. -/
abbrev bytesMerge3PlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeGhost × M.σ) :=
  withLsCl lsmpl (bytesMerge3RawSpec A lim)

/-- Relocatable `[LibsignalPlacement]` budget-threaded spec of
`prost::encoding::bytes::merge [local#5]` using `LibsignalSpqrV1.Proto.mergeBytes` on `lsProg_518 ext`. -/
abbrev bytesMerge3ProtoPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Spec (BytesMergeProtoGhost × M.σ) :=
  withLsCl lsmpl (bytesMerge3ProtoRawSpec A lim)

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3PlacedSpec A lim`. -/
def BytesMerge6PlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3PlacedSpec A lim)

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]`
(Block `508`, `(blkPl_507).base = lsmpl.base 507`) against `bytesMerge3ProtoPlacedSpec A lim`. -/
def BytesMerge6ProtoPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 507)
    (bytesMerge3ProtoPlacedSpec A lim)

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsPlacedBudget
