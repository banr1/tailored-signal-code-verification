/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget

/-!
# Budget-Threaded Code-Loaded `[LibsignalPlacement]` Callee Contracts for `spqr::decode_state` (Block `325`)

Bundles budget-threaded code-loaded callee contracts (`DecodeStateCalleeContractsClPlaced` and
`DecodeStateCalleeContractsClPlacedX`) for Block `325`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge (OptInnerStatePolyBound)
open CryptoVerification.SpqrV1.Top.DecodeState
  (V1InnerHeapPred optProtoInnerStateAt optProtoInnerStateCapOkAt)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (bytesMerge3RawBudgetSpec skipField3BudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (growOneStrideFullSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (chainParamsMergeSpec epochDirectionMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
  (dropOptProtoInnerStatePlacedSpec dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Obj.lookup

/-- Budget-threaded code-loaded bundle of relocatable callee contracts used by `spqr::decode_state`
(Block `325`). Every cross-block callee carries `withLsCodeLoaded lsmpl` or `withLsCl lsmpl`. -/
structure DecodeStateCalleeContractsClPlaced [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  of_drop_inner : ∀ a opt,
    CryptoVerification.SpqrV1.Drop.optProtoInnerStateAt A.repAlloc a opt ⊢
      optProtoInnerStateAt H_inner A.repAlloc a opt
  of_cap_inner : ∀ a remLen opt,
    OptInnerStatePolyBound remLen opt →
    CryptoVerification.SpqrV1.Prost.MessageMerge.optProtoInnerStateCapAt A.repAlloc a remLen opt ⊢
      optProtoInnerStateCapOkAt H_inner A.repAlloc a remLen opt
  dealloc : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim)
  memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "memcpy") (withVmPreserved (libcMemcpySpec hookStack))
  session_memcpy : ∀ (hookStack : Nat), allocHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
      (lsρ "memcpy") (withVmPreserved (sessionMemcpySpec hookStack))
  decodeErrorFrom : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 261) (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim))
  decodeErrorPush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 257) (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim))
  decodeVarint2 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 291) (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim))
  skipField3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 263) (withLsCodeLoaded lsmpl (skipField3BudgetSpec M A lim))
  chainParamsMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 294) (withLsCodeLoaded lsmpl (chainParamsMergeSpec A lim))
  growOneChainEpoch : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 356) (withLsCodeLoaded lsmpl (growOneStrideFullSpec M A lim 112 8))
  dropOptProtoInnerState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 267) (withLsCl lsmpl (dropOptProtoInnerStatePlacedSpec H_inner A lim))
  dropProtoPqRatchetState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 270) (withLsCl lsmpl (dropProtoPqRatchetStatePlacedSpec H_inner A lim))

/-- Full budget-threaded code-loaded relocatable callee contracts for `spqr::decode_state`
(Block `325`), extending `DecodeStateCalleeContractsClPlaced` with `withLsCodeRoLoaded lsmpl`
contracts for callees that invoke `bytes::merge [local#3]` (`bytesMerge3`, `epochDirectionMerge`,
`v1StateMerge`). -/
structure DecodeStateCalleeContractsClPlacedX [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContractsClPlaced H_inner A lim ext where
  bytesMerge3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim))
  epochDirectionMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim))
  v1StateMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsClPlacedBudget
