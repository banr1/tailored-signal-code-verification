/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `FdsGe3Closed`-Threaded Relocatable `<IdentityFiles as IdentityKeyStore>::save_identity::{closure#0}`

Proves `withFdsGe3Closed (idSavePollSpecPlaced …)` on Block `565` (`lsProg_565 H`) under
`[LibsignalPlacement]` over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsBlackBoxU8Sym lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (extHookStack publicKeySerializeStackX)
open CryptoVerification.LibsignalTripleRatchet.Getters (publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession.Cli (DirGhost IdPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_565 blkPl_565 lsProg_565)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
  (ls_transfer_withFdsGe3Closed_lscro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsFsPlaced dirGetSpecPlaced dirPutStrSpecPlaced idSavePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (CliIdSavePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudgetFd
  (publicKeySerialize_lscro_of_fs)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudgetFd
  (idSavePoll_placed_ok_of_deps_core_fd idSavePoll_placed_ok_of_deps_core_gen_fd)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (identityKeyDecodePlacedBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudgetFd
  (identityKey_decode_placed_ok_fd ls_transfer_withFdsGe3Closed_cl_to_lscro
   publicKeyEq_placed_ok_of_bb_fd)

section Placed

theorem idSavePoll_placed_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {getProg putProg decProg eqProg : Program} {getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hFitGet : ∀ F0 x st0, FitsEnv M lim st0 (SaveEnv F0 x) →
      FitsEnv M lim st0 (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hSaveErr : ∀ F0 x evsGet,
      x.peers.get rd F0 x.call.call.addr.val.name = .error () →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      SaveEnv F0 x evsGet)
    (hFitSer : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsGet ++ evsFree) st0) PublicKeySerializeEnv)
    (hFitPut : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents ((evsGet ++ evsFree) ++ publicKeySerializeEvents) st0)
        (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveOk : ∀ F0 x bs evsGet evsFree evsPut,
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv F0 x ((evsGet ++ evsFree) ++ publicKeySerializeEvents ++ evsPut))
    (hstk : 208 + max (max (max getStk putStk) (max 96 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)) := by
  have hSer := publicKeySerialize_lscro_of_fs
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hFs (by decide)
  have hGet' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hEq (by decide) hEqBlk hEqUnmut
  exact idSavePoll_placed_ok_of_deps_core_gen_fd hFs hSer hGet' hPut' hDec' hEq'
    hFitGet hSaveErr hFitSer hFitPut hSaveOk hstk

/-- Block `565` (`save_identity::{closure#0}`) meets two-sided
`withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk)`
given `AllocContractsFsPlaced`, `withFdsGe3Closed (dirGetSpecPlaced …)` (block `589`),
`withFdsGe3Closed (dirPutStrSpecPlaced …)` (block `543`),
`IdentityKey::decode` (block `18`), and `<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idSavePoll_placed_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {getProg putProg decProg eqProg : Program} {getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hstk : 208 + max (max (max getStk putStk) (max 96 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk)) := by
  have hSer := publicKeySerialize_lscro_of_fs
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hFs (by decide)
  have hGet' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_withFdsGe3Closed_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_withFdsGe3Closed_cl_to_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_withFdsGe3Closed_cl_to_lscro
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hEq (by decide) hEqBlk hEqUnmut
  exact idSavePoll_placed_ok_of_deps_core_fd hFs hSer hGet' hPut' hDec' hEq' hstk

/-- Convenience specialization discharging `IdentityKey::decode` via
`identityKey_decode_placed_ok_fd` and `<PublicKey as PartialEq>::eq` via
`publicKeyEq_placed_ok_of_bb_fd`. -/
theorem idSavePoll_placed_ok_of_get_put_bb_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {getProg putProg : Program} {getBlk putBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 208 + max (max (max getStk putStk) (max 96 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk)) :=
  idSavePoll_placed_ok_of_deps_fd hFs hGet hPut
    (identityKey_decode_placed_ok_fd H)
    (publicKeyEq_placed_ok_of_bb_fd h_bb) hstk hGetBlk hGetUnmut hPutBlk hPutUnmut

theorem idSavePoll_placed_caller_ok_of_deps_gen_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {SaveEnv : FsFiles → IdPollGhost → List AllocEvent → Prop}
    {callerProg getProg putProg decProg eqProg : Program}
    {callerBlk getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hFitGet : ∀ F0 x st0, FitsEnv M lim st0 (SaveEnv F0 x) →
      FitsEnv M lim st0 (GetEnv F0 x.peers x.call.call.addr.name.bytes))
    (hSaveErr : ∀ F0 x evsGet,
      x.peers.get rd F0 x.call.call.addr.val.name = .error () →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      SaveEnv F0 x evsGet)
    (hFitSer : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents (evsGet ++ evsFree) st0) PublicKeySerializeEnv)
    (hFitPut : ∀ F0 x bs st0 evsGet evsFree,
      FitsEnv M lim st0 (SaveEnv F0 x) →
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      FitsEnv M lim (M.stepEvents ((evsGet ++ evsFree) ++ publicKeySerializeEvents) st0)
        (PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize))
    (hSaveOk : ∀ F0 x bs evsGet evsFree evsPut,
      x.peers.get rd F0 x.call.call.addr.val.name = .ok bs →
      GetEnv F0 x.peers x.call.call.addr.name.bytes evsGet →
      FreeOnlyEvs evsFree →
      PutStrEnv x.peers x.call.call.addr.name.bytes x.call.call.key.serialize evsPut →
      SaveEnv F0 x ((evsGet ++ evsFree) ++ publicKeySerializeEvents ++ evsPut))
    (hstk : 208 + max (max (max getStk putStk) (max 96 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 565)
      (withFdsGe3Closed (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 565)
    (idSavePoll_placed_ok_of_deps_gen_fd hFs hGet hPut hDec hEq
      hFitGet hSaveErr hFitSer hFitPut hSaveOk hstk
      hGetBlk hGetUnmut hPutBlk hPutUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

theorem idSavePoll_placed_caller_ok_of_deps_fd [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {callerProg getProg putProg decProg eqProg : Program}
    {callerBlk getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg callerProg callerBlk H]
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hFs : AllocContractsFsPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (withFdsGe3Closed (dirGetSpecPlaced rd pathOk A lim GetEnv getStk)))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (withFdsGe3Closed (dirPutStrSpecPlaced A lim PutStrEnv putStk)))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (withFdsGe3Closed (identityKeyDecodePlacedBudgetSpec A)))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withFdsGe3Closed (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec))))
    (hstk : 208 + max (max (max getStk putStk) (max 96 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hCallerBlk : callerBlk < 619 := by decide)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hDecBlk : decBlk < 619 := by decide)
    (hDecUnmut : (decBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hEqBlk : eqBlk < 619 := by decide)
    (hEqUnmut : (eqBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg (lsmpl.base 565)
      (withFdsGe3Closed
        (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk)) :=
  ls_transfer_withFdsGe3Closed_lscro (callerProg := callerProg) (j := 565)
    (idSavePoll_placed_ok_of_deps_fd hFs hGet hPut hDec hEq hstk
      hGetBlk hGetUnmut hPutBlk hPutUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudgetFd
