/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget

/-!
# Budget-Threaded Relocatable Leaf Callee Contracts for Inlined `SessionStructure::decode`

Budget-threaded (`RustCliAllocBudget M`) relocatable callee contract propositions
(`SkipField6PlacedOkExtX` on Block `510` and `GrowOneMessageKeyPlacedOkExtX` on Block `519`) on
`lsProg_518 ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget (skipField3Spec)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (growOneChainSpecX)

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`prost::encoding::skip_field::<&mut &[u8]> [local#5]`
(Block `510`, `(blkPl_510).base = lsmpl.base 510`) on `lsProg_518 ext`. -/
def SkipField6PlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 510)
    (withLsCl lsmpl (skipField3Spec A lim))

/-- Relocatable `[LibsignalPlacement]` budget-threaded contract for
`<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::chain::MessageKey>>::grow_one`
(Block `519`, `(blkPl_519).base = lsmpl.base 519`) on `lsProg_518 ext`. -/
def GrowOneMessageKeyPlacedOkExtX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_518 ext) (lsmpl.base 519)
    (withLsCl lsmpl (growOneChainSpecX M A lim))

abbrev subroutine_ok_skipField3_or_placed :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget.subroutine_ok_skipField3_or_placed
abbrev subroutine_ok_skipField3_imp_placed :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget.subroutine_ok_skipField3_imp_placed
abbrev skipField3SpecAt_reaches_outcome_placed_eq :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget.skipField3SpecAt_reaches_outcome_placed_eq
abbrev subroutine_ok_skipField3Spec_of_at_depth_placed :=
  @LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget.subroutine_ok_skipField3Spec_of_at_depth_placed

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsPlacedBudget
