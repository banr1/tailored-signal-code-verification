/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.Existing
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded `[LibsignalPlacement]` `SessionFiles::store_session::{closure#0}`

Allocation-budget (`RustCliAllocBudget M`) proof of `SessionFiles::store_session::{closure#0}`
(Block `570`) at `SerializeEnvX`, transferred onto any caller block program at residual stack
`stk - cliInitiateFrame`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsmpl withLsCodeLoaded)
open CryptoVerification.E2E.Record.Placed (lsProg_52)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (subroutine_ok_rocl_of_withLsCodeRoLoaded withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (DirGhost)
open CryptoVerification.SignalSession.Cli.Placed (lsProg_542 lsProg_570 lsProg_594)
open CryptoVerification.SignalSession.Cli.RunProofs (cliInitiateFrame cliInitiateNeed)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (cliAddrTextStk cliDirPutStk stk_sub_ge_base)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
  (SerContractsXPlaced SerializeEnvX serializeCanonSpecX serializeStackX)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
  (RunHooksPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (addrTextSpecPlaced dirPutSpecPlaced sessStorePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueXPlacedBudget
  (serializeCanonX_placed_ok_of_serContractsX)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePoll.LayoutBudget
  (CliStorePollEnv addrTextCellsSpec cliStorePollInnerSpec dirPutCellsSpec serializeCellsSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget
  (sessStorePollInner_placed_ok sessStorePoll_placed_of_inner)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollXPlacedBudget
  (serialize_cells_placed_okX sessStorePoll_placed_caller_ok_of_depsX
   sessStorePoll_placed_ok_of_depsX)

section Placed

/-! ## 1. Extended `SessionRecord::serialize` (`serializeCanonSpecX`) on Block `52` -/

theorem serializeCanon_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_52 H) (lsmpl.base 52)
      (withLsCodeLoaded lsmpl (serializeCanonSpecX M A lim)) :=
  serializeCanonX_placed_ok_of_serContractsX hC

/-! ## 2. Cell-Oriented Callee Wrappers -/

theorem addrText_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {prog : Program} {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok prog (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 594)
      (withLsCodeRoLoaded lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget.addrText_cells_placed_ok
    hAddr hle hhi

theorem addrText_cells_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {prog : Program} {addrStk calleeStk : Nat}
    (hAddr : subroutine_ok prog (lsmpl.base 594) (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hle : addrStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 594)
      (withLsRoCl lsmpl (addrTextCellsSpec A lim AddrEnv calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (addrText_cells_placed_ok hAddr hle hhi)

theorem serialize_cells_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {calleeStk : Nat}
    (hSer : subroutine_ok prog (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hle : serializeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCellsSpec A lim SerializeEnvX calleeStk)) :=
  serialize_cells_placed_okX hSer hle hhi

theorem serialize_cells_rocl_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {prog : Program} {calleeStk : Nat}
    (hSer : subroutine_ok prog (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hle : serializeStackX ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 52)
      (withLsRoCl lsmpl (serializeCellsSpec A lim SerializeEnvX calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (serialize_cells_placed_ok_x hSer hle hhi)

theorem dirPut_cells_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {putStk calleeStk : Nat}
    (hPut : subroutine_ok prog (lsmpl.base 542) (dirPutSpecPlaced A lim PutEnv putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 542)
      (withLsCodeRoLoaded lsmpl (dirPutCellsSpec A lim PutEnv calleeStk)) :=
  LibsignalBinary.Proofs.SignalSession.Cli.Store.StorePollPlacedBudget.dirPut_cells_placed_ok
    hPut hle hhi

theorem dirPut_cells_rocl_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {putStk calleeStk : Nat}
    (hPut : subroutine_ok prog (lsmpl.base 542) (dirPutSpecPlaced A lim PutEnv putStk))
    (hle : putStk ≤ calleeStk) (hhi : calleeStk ≤ 2 ^ 64) :
    subroutine_ok prog (lsmpl.base 542)
      (withLsRoCl lsmpl (dirPutCellsSpec A lim PutEnv calleeStk)) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (dirPut_cells_placed_ok hPut hle hhi)

/-! ## 3. Block `570` (`lsProg_570 H`) Inner, Outer, & CLI Instantiations -/

theorem sessStorePollInner_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrStk putStk : Nat}
    (hAddr : subroutine_ok (lsProg_570 H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hSer : subroutine_ok (lsProg_570 H) (lsmpl.base 52)
      (withLsCodeRoLoaded lsmpl (serializeCanonSpecX M A lim)))
    (hPut : subroutine_ok (lsProg_570 H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hhi : max (max addrStk serializeStackX) (max putStk extHookStack) ≤ 2 ^ 64) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (withLsCodeRoLoaded lsmpl
        (cliStorePollInnerSpec A lim AddrEnv SerializeEnvX PutEnv
          (max (max addrStk serializeStackX) (max putStk extHookStack)))) :=
  sessStorePollInner_placed_ok
    (addrText_cells_placed_ok hAddr (by omega) hhi)
    (serialize_cells_placed_ok_x hSer (by omega) hhi)
    (dirPut_cells_placed_ok hPut (by omega) hhi)

theorem sessStorePoll_of_inner_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {prog : Program} {entry : BitVec 64} {calleeStk stk : Nat}
    (hInner : calleeStk ≤ 2 ^ 64 →
      subroutine_ok prog entry
        (withLsCodeRoLoaded lsmpl
          (cliStorePollInnerSpec A lim AddrEnv SerializeEnvX PutEnv calleeStk)))
    (hstk : 0xd0 + calleeStk ≤ stk) :
    subroutine_ok prog entry
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnvX PutEnv) stk) :=
  sessStorePoll_placed_of_inner hInner hstk

/-- Block-570 `SessionFiles::store_session::{closure#0}` contract from `RunHooksPlaced`,
polymorphic in `addrStk`, `putStk`, and `stk`. -/
theorem sessStorePoll_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {W : CliHooks} {H : LibsignalHooks}
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {addrProg putProg : Program} {addrBlk putBlk : Nat}
    [IsLsBlockProg addrProg addrBlk H] [IsLsBlockProg putProg putBlk H]
    {addrStk putStk stk : Nat}
    (hh : RunHooksPlaced W A lim H)
    (hAddr : subroutine_ok addrProg (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv addrStk))
    (hPut : subroutine_ok putProg (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv putStk))
    (hstk : 0xd0 + max (max addrStk serializeStackX) (max putStk extHookStack) ≤ stk)
    (hAddrBlk : addrBlk < 619 := by decide)
    (hAddrUnmut : (addrBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_570 H) (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim (CliStorePollEnv AddrEnv SerializeEnvX PutEnv) stk) :=
  sessStorePoll_placed_ok_of_depsX hh.alloc hAddr (serializeCanon_placed_ok_x hh.ser) hPut hstk
    hAddrBlk hAddrUnmut (by decide) (by decide) hPutBlk hPutUnmut

/-- CLI instantiation of `SessionFiles::store_session::{closure#0}` (Block `570`) transferred onto
any caller block program `prog` (e.g. `initProgPlaced W`) at residual stack
`stk - cliInitiateFrame`. -/
theorem sessStorePoll_cli_placed_ok [LibsignalPlacement] {prog : Program} {i : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {W : CliHooks} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    {AddrEnv : AddrGhost → List AllocEvent → Prop}
    {PutEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (B : RunBudgets)
    (hh : RunHooksPlaced W A lim H)
    (hAddr : subroutine_ok (lsProg_594 H) (lsmpl.base 594)
      (addrTextSpecPlaced A lim AddrEnv cliAddrTextStk))
    (hPut : subroutine_ok (lsProg_542 H) (lsmpl.base 542)
      (dirPutSpecPlaced A lim PutEnv cliDirPutStk))
    (hi : i < 619 := by decide)
    {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    subroutine_ok prog (lsmpl.base 570)
      (sessStorePollSpecPlaced A lim
        (CliStorePollEnv AddrEnv SerializeEnvX PutEnv) (stk - cliInitiateFrame)) := by
  have h1 := stk_sub_ge_base hstk
  have hext : 0xd0 + max (max cliAddrTextStk serializeStackX)
      (max cliDirPutStk extHookStack) ≤ 516880 := by decide
  exact sessStorePoll_placed_caller_ok_of_depsX hh.alloc hAddr
    (serializeCanon_placed_ok_x hh.ser) hPut (by omega) hi

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.StorePollCliPlacedBudget
