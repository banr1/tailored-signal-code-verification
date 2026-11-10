/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymD
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded Minimal Stage-2 Contracts for `SessionRecord::deserialize`

Defines `Stage2ContractsMinPlaced M A lim H` (combining `AllocContractsPlaced M A lim H` with
`VmPreserved`-preserving `memcpy` at `extHookStack`), conversion bridges to `SerContractsXPlaced`,
and parametric-envelope `recordDeserializeOpenEnvSpec` wrappers on block `46`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg
  lsmpl withLsCodeLoaded withLsCl
  lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym lsRustNoAllocShimSym lsMemcpySym
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack withLsCodeRoLoaded
  ls_hook_ok_of_caller ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.E2E.Record.Placed (lsProg_46 blkPl_46)
open Symbolic.Swarm.TRREF.B3Defs (NonEmptyV1Q)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliDeallocBudgetExternSpecWithStack
  rustCliReallocBudgetExternSpecWithStack
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyBudgetSpec sessionMemmoveBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (session2ShimBudgetSpecX)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.AdaptersBudget (Stage2ContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DoReserveExtBudget (
  allocContractsPlaced_of_stage2ContractsPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (SerContractsXPlaced)
open LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget (
  RecordDeserializeEnv recordDeserializeOpenEnvSpec_Q recordDeserializeOpenSpec_Q
)

/-! ## 1. Minimal `[LibsignalPlacement]` Stage-2 Contract Bundle (`Stage2ContractsMinPlaced`) -/

/-- Minimal relocatable budget-threaded `[LibsignalPlacement]` contract bundle for
`SessionRecord::deserialize` (and `SessionRecord::serialize`):
`AllocContractsPlaced M A lim H` (`alloc`, `dealloc`, `realloc`, `shim`, `memmove` at
`extHookStack`) plus `VmPreserved`-preserving owned-source `memcpy` at `extHookStack`. -/
structure Stage2ContractsMinPlaced [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : AllocContractsPlaced M A lim H
  memcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))

/-- Construct `Stage2ContractsMinPlaced M A lim H` from block-0 `withLsCodeLoaded` contracts. -/
theorem Stage2ContractsMinPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocBudgetSpecWithStack M A lim false extHookStack)))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustCliDeallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocBudgetExternSpecWithStack M A lim extHookStack)))
    (hshim : subroutine_ok blk0Prog (lsρ lsRustNoAllocShimSym)
      (withLsCodeLoaded lsmpl session2ShimBudgetSpecX))
    (hmemcpy : subroutine_ok blk0Prog (lsρ lsMemcpySym)
      (withLsCodeLoaded lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (hmemmove : subroutine_ok blk0Prog (lsρ "memmove")
      (withLsCodeLoaded lsmpl (sessionMemmoveBudgetSpec extHookStack))) :
    Stage2ContractsMinPlaced M A lim H where
  alloc := AllocContractsPlaced.of_block0 halloc hdealloc hrealloc hshim hmemmove
  memcpy := ls_subroutine_ok_cl_of_callee (j := 0) hmemcpy

/-- Construct `Stage2ContractsMinPlaced M A lim H` from `HookSat H` single-step budget hooks. -/
theorem Stage2ContractsMinPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (hmemcpy : HookSat H lsMemcpySym (sessionMemcpyBudgetSpec extHookStack))
    (hmemmove : HookSat H "memmove" (sessionMemmoveBudgetSpec extHookStack)) :
    Stage2ContractsMinPlaced M A lim H where
  alloc := AllocContractsPlaced.of_hooks halloc hdealloc hrealloc hshim hmemmove
  memcpy := ls_subroutine_ok_cl_of_plain_prog (ls_hook_ok_of_caller hmemcpy)

/-- Forget the unused fields of `Stage2ContractsPlaced A lim H`. -/
theorem stage2ContractsMinPlaced_of_stage2ContractsPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsPlaced A lim H) :
    Stage2ContractsMinPlaced M A lim H where
  alloc := allocContractsPlaced_of_stage2ContractsPlaced hC
  memcpy := hC.memcpy

abbrev Stage2ContractsMinPlaced.of_stage2 := @stage2ContractsMinPlaced_of_stage2ContractsPlaced

/-- Project `SerContractsXPlaced M A lim H` from `Stage2ContractsMinPlaced M A lim H`. -/
theorem serContractsXPlaced_of_stage2ContractsMinPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : Stage2ContractsMinPlaced M A lim H) :
    SerContractsXPlaced M A lim H :=
  ⟨hC.alloc, hC.memcpy⟩

abbrev Stage2ContractsMinPlaced.toSerContractsXPlaced :=
  @serContractsXPlaced_of_stage2ContractsMinPlaced

/-- Construct `Stage2ContractsMinPlaced M A lim H` from `SerContractsXPlaced M A lim H`. -/
theorem Stage2ContractsMinPlaced.of_serContractsXPlaced [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    Stage2ContractsMinPlaced M A lim H :=
  ⟨hC.alloc, hC.memcpy⟩

/-! ## 2. Parametric-Envelope `recordDeserializeOpenEnvSpec` & Block-`46` Bundle Projections -/

/-- Parametric-envelope budget-threaded `recordDeserializeOpenSpec` (`onPanic = ⌜False⌝`,
`onOom = ⌜False⌝`), matching `LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget.recordDeserializeOpenSpec`
at `Env := fun bs _ => RecordDeserializeEnv bs`. -/
def recordDeserializeOpenEnvSpec
    (Env : List (BitVec 8) → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) × M.σ) where
  pre := fun (x, st) s =>
    let (_, bs, _, sess) := x
    ⌜FitsEnv M lim st (Env bs sess)⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeOpenSpec (A.atState lim st s)).pre x s
  post := fun (x, st) s0 sf =>
    let (_, bs, _, sess) := x
    ∃∗ evs : List AllocEvent,
      ⌜Env bs sess evs⌝ ∗
      (CryptoVerification.E2E.Bin.recordDeserializeOpenSpec
        (A.atState lim (M.stepEvents evs st) sf)).post x s0 sf

/-- Canonical-envelope (`RecordDeserializeEnv`) budget-threaded `recordDeserializeOpenSpec`. -/
abbrev recordDeserializeOpenSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) × M.σ) :=
  recordDeserializeOpenEnvSpec (fun bs _ => RecordDeserializeEnv bs) M A lim

/-- `recordDeserializeOpenSpecX` is definitionally equal to
`LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget.recordDeserializeOpenSpec`. -/
theorem recordDeserializeOpenSpecX_eq_specsCommon (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    recordDeserializeOpenSpecX M A lim =
      LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget.recordDeserializeOpenSpec M A lim :=
  rfl

/-- Unpack `Stage2ContractsMinPlaced M A lim H` into its `(alloc, memcpy)` premises for any
callee contract. -/
theorem lift_placed_ok_of_stage2Min [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks} {P : Prop}
    (hStage2 : Stage2ContractsMinPlaced M A lim H)
    (hCallee :
      AllocContractsPlaced M A lim H →
      (∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
        subroutine_ok callerProg (lsρ lsMemcpySym)
          (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) →
      P) :
    P :=
  hCallee hStage2.alloc hStage2.memcpy

/-- Block-`46` `recordDeserializeOpenEnvSpec` from `Stage2ContractsMinPlaced M A lim H` and its
`(alloc, memcpy)` callee contract. -/
theorem recordDeserializeEnv_placed_ok_of_stage2Min_of_alloc [LibsignalPlacement]
    {Env : List (BitVec 8) → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced M A lim H)
    (hCallee :
      AllocContractsPlaced M A lim H →
      (∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
        subroutine_ok callerProg (lsρ lsMemcpySym)
          (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) →
      subroutine_ok (lsProg_46 H) (blkPl_46).base
        (withLsCodeRoLoaded lsmpl (recordDeserializeOpenEnvSpec Env M A lim))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (withLsCodeRoLoaded lsmpl (recordDeserializeOpenEnvSpec Env M A lim)) :=
  lift_placed_ok_of_stage2Min hStage2 hCallee

/-- Block-`46` `SpecsCommonBudget.recordDeserializeOpenSpec` from
`Stage2ContractsMinPlaced M A lim H` and its `(alloc, memcpy)` callee contract. -/
theorem recordDeserialize_placed_ok_of_stage2Min_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced M A lim H)
    (hCallee :
      AllocContractsPlaced M A lim H →
      (∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
        subroutine_ok callerProg (lsρ lsMemcpySym)
          (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) →
      subroutine_ok (lsProg_46 H) (blkPl_46).base
        (withLsCodeRoLoaded lsmpl
          (LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget.recordDeserializeOpenSpec M A lim))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.E2E.Bin.SpecsCommonBudget.recordDeserializeOpenSpec M A lim)) :=
  lift_placed_ok_of_stage2Min hStage2 hCallee

/-- Block-`46` `recordDeserializeOpenEnvSpec_Q` from `Stage2ContractsMinPlaced M A lim H` and its
`(alloc, memcpy)` callee contract. -/
theorem recordDeserializeOpenEnvQ_placed_ok_of_stage2Min_of_alloc [LibsignalPlacement]
    {Q : List (BitVec 8) → Prop}
    {Env : List (BitVec 8) → Session (List (BitVec 8)) → List AllocEvent → Prop}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced M A lim H)
    (hCallee :
      AllocContractsPlaced M A lim H →
      (∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
        subroutine_ok callerProg (lsρ lsMemcpySym)
          (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) →
      subroutine_ok (lsProg_46 H) (blkPl_46).base
        (withLsCodeRoLoaded lsmpl (recordDeserializeOpenEnvSpec_Q Q Env M A lim))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (withLsCodeRoLoaded lsmpl (recordDeserializeOpenEnvSpec_Q Q Env M A lim)) :=
  lift_placed_ok_of_stage2Min hStage2 hCallee

/-- Block-`46` `recordDeserializeOpenSpec_Q NonEmptyV1Q` from
`Stage2ContractsMinPlaced M A lim H` and its `(alloc, memcpy)` callee contract. -/
theorem recordDeserializeOpenQ_placed_ok_of_stage2Min_of_alloc [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hStage2 : Stage2ContractsMinPlaced M A lim H)
    (hCallee :
      AllocContractsPlaced M A lim H →
      (∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
        subroutine_ok callerProg (lsρ lsMemcpySym)
          (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) →
      subroutine_ok (lsProg_46 H) (blkPl_46).base
        (withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q M A lim))) :
    subroutine_ok (lsProg_46 H) (blkPl_46).base
      (withLsCodeRoLoaded lsmpl (recordDeserializeOpenSpec_Q NonEmptyV1Q M A lim)) :=
  lift_placed_ok_of_stage2Min hStage2 hCallee

end LibsignalBinary.Proofs.SessionRecordMin.DeserializeBudget
