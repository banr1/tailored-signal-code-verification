/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4KBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.DecodeStateCodeSym
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget

/-!
# Budget-Threaded Relocatable `[LibsignalPlacement]` Specifications for `spqr::decode_state` (Block `325`)

Defines budget-threaded relocatable callee contract bundles and top-level specifications
(`spqrDecodeStatePlacedSpecOfEnv` and `spqrDecodeStatePlacedSpec`) for Block `325`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget

open Arm64 Arm64.Obj ProofLib SepProp
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open CryptoVerification.SpqrV1.Top.DecodeState.Placed (blkPC_325 blkPl_325)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec withLsCodeRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (OptInnerStatePolyBound v1StateJumpTablesPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost DropOptProtoInnerStateGhost DropProtoPqRatchetStateGhost
   V1InnerHeapPred decodeStateResultAt decodeStateStackX dropOptProtoInnerStateStack
   optProtoInnerStateAt optProtoInnerStateCapOkAt protoPqRatchetStateAt)
open CryptoVerification.LibsignalSpqrV1 (spqrDecodeState)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustCliDeallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (bytesMerge3RawBudgetSpec skipField3BudgetSpec)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneBudget
  (growOneStrideFullSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateDefsBudget
  (v1StateMergePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsBudget
  (DecodeStateEnv chainParamsMergeSpec epochDirectionMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Obj.lookup

/-- Budget-threaded relocatable contract for
`core::ptr::drop_glue::<Option<spqr::proto::pq_ratchet::v1_state::InnerState>>` (Block `267`). -/
def dropOptProtoInnerStatePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropOptProtoInnerStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      optProtoInnerStateAt H_inner A.repAlloc x.a x.st ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a 224 ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp dropOptProtoInnerStateStack

/-- Budget-threaded relocatable contract for
`core::ptr::drop_glue::<spqr::proto::pq_ratchet::PqRatchetState>` (Block `270`). -/
def dropProtoPqRatchetStatePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropProtoPqRatchetStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.a ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      protoPqRatchetStateAt H_inner A.repAlloc x.a x.st ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool lim st s ∗ stackAt s.sp dropOptProtoInnerStateStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ FreeOnlyEvs evs⌝ ∗
      memRegion x.a 352 ∗
      v1StateJumpTablesPlacedAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp dropOptProtoInnerStateStack

/-- Envelope-parameterized budget-threaded relocatable specification of `spqr::decode_state`
(Block `325`). -/
def spqrDecodeStatePlacedSpecOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop) :
    Spec (DecodeStateGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.outPtr ∧
      s.readReg64 .x0 = x.st.v ∧
      x.st.bytes.length < 2 ^ 32 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      memRegion x.outPtr 352 ∗
      A.pool lim st s ∗ stackAt s.sp decodeStateStackX
  post := fun (x, st) s0 sf =>
    (∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      A.pool lim (M.stepEvents evs st) sf) ∗
      v1StateJumpTablesPlacedAt ∗
      x.st.at A.repAlloc ∗
      decodeStateResultAt H_inner A.repAlloc x.outPtr (spqrDecodeState x.st.bytes) ∗
      stackAt s0.sp decodeStateStackX

def spqrDecodeStatePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeStateGhost × M.σ) :=
  spqrDecodeStatePlacedSpecOfEnv H_inner A lim DecodeStateEnv DecodeStateEnv

abbrev decodeStatePlacedSpecX [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DecodeStateGhost × M.σ) :=
  spqrDecodeStatePlacedSpec H_inner A lim

/-- Budget-threaded bundle of relocatable callee contracts used by `spqr::decode_state` (Block `325`). -/
structure DecodeStateCalleeContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
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
    (lsmpl.base 261) (decodeErrorFromBudgetSpec M A lim)
  decodeErrorPush : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 257) (decodeErrorPushBudgetSpec M A lim)
  decodeVarint2 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 291) (decodeVarint2Spec A lim)
  skipField3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 263) (skipField3BudgetSpec M A lim)
  chainParamsMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 294) (chainParamsMergeSpec A lim)
  growOneChainEpoch : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 356) (growOneStrideFullSpec M A lim 112 8)
  dropOptProtoInnerState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 267) (dropOptProtoInnerStatePlacedSpec H_inner A lim)
  dropProtoPqRatchetState : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 270) (dropProtoPqRatchetStatePlacedSpec H_inner A lim)

/-- Full budget-threaded relocatable callee contracts for `spqr::decode_state` (Block `325`). -/
structure DecodeStateCalleeContractsPlacedX [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop extends
    DecodeStateCalleeContractsPlaced H_inner A lim ext where
  bytesMerge3 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 290) (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec M A lim))
  epochDirectionMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 299) (withLsCodeRoLoaded lsmpl (epochDirectionMergeSpec A lim))
  v1StateMerge : subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (lsmpl.base 298) (withLsCodeRoLoaded lsmpl (v1StateMergePlacedSpec A lim))

def DecodeStatePlacedOkOfEnv [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (PreEnv PostEnv : DecodeStateGhost → List AllocEvent → Prop)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (blkPl_325).base
    (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpecOfEnv H_inner A lim PreEnv PostEnv))

def DecodeStatePlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_325).rebase (blkPl_325).base (Rust.withPanics ext))
    (blkPl_325).base
    (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec H_inner A lim))

abbrev DecodeStatePlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (H_inner : V1InnerHeapPred) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  DecodeStatePlacedOk H_inner A lim ext

end LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget
