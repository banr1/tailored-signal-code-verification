/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlaced
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget

/-!
# Budget-Threaded Relocatable Callee Specifications for `message::merge<Chain>`

Relocatable (`[LibsignalPlacement]`) allocator-budget (`RustCliAllocBudget M`) contracts and
`Chain3CalleePlacedKit` bundle for `prost::encoding::message::merge<Chain> [local#4]` on
`lsProg_516`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost)
open CryptoVerification.CliHandshake.Placed (lsProg_516)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsBudget (
  bytesMerge3RawSpec decodeVarint2SpecX
)

/-- Budget-threaded relocatable contract for
`prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#5]` (Block `514`). -/
abbrev bytesMerge3PlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (BytesMergeGhost × M.σ) :=
  withLsCl lsmpl (bytesMerge3RawSpec A lim)

/-- Budget-threaded callee contract bundle for `message::merge<Chain>` on `lsProg_516`,
grouping `decode_varint [local#4]` (Block `515`), `bytes::merge [local#5]` (Block `514`), and
`RawVec<Chain>::grow_one` (Block `43`). -/
structure Chain3CalleePlacedKit [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop where
  dv : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 515)
      (withLsCl lsmpl (decodeVarint2SpecX A lim))
  bm : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 514)
      (bytesMerge3PlacedSpec A lim)
  grow : ∀ (ext : String → Option (State → State)),
    subroutine_ok (lsProg_516 ext) (lsmpl.base 43)
      (withLsCl lsmpl (growOneChainSpecX M A lim))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlacedBudget
