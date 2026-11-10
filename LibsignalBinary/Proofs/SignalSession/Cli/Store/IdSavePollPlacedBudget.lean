/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `<IdentityFiles as IdentityKeyStore>::save_identity::{closure#0}`

Proves budget-threaded `idSavePollSpecPlaced` on Block `565` (`lsProg_565 H`) under
`[LibsignalPlacement]` in both generic-envelope and canonical `CliIdSavePollEnv` forms.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement libsignalMutatedBlocks lsBlackBoxU8Sym lsmpl
   withLsCodeLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchet (extHookStack publicKeySerializeStackX)
open CryptoVerification.LibsignalTripleRatchet.Getters (publicKeyEqSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.SignalSession.Cli (DirGhost IdPollGhost ReadRule)
open CryptoVerification.SignalSession.Cli.Placed (blkPC_565 blkPl_565 lsProg_565)
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
  (ls_transfer_cl_to_lscro ls_transfer_lscro)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (AllocContractsXCliPlaced dirGetSpecPlaced dirPutStrSpecPlaced idSavePollSpecPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.BranchesPlacedBudget
  (publicKeySerialize_lscro_of_cli)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
  (CliIdSavePollEnv CliIdSaveTailEnv idSavePoll_placed_ok_of_deps_core
   idSavePoll_placed_ok_of_deps_core_gen)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (identityKeyDecodePlacedBudgetSpec identityKey_decode_placed_ok publicKeyEq_placed_ok_of_bb)

export LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePoll.SymPlacedBudget
  (CliIdSaveTailEnv CliIdSavePollEnv)
export LibsignalBinary.Proofs.SignalSession.Cli.Store.IdTrustPollPlacedBudget
  (publicKeyEq_placed_ok_of_bb identityKeyDecodePlacedBudgetSpec identityKey_decode_placed_ok)

section Placed

theorem idSavePoll_placed_ok_of_deps_gen [LibsignalPlacement] {M : AllocCostModel}
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
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
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
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
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
      (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk) := by
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hC (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idSavePoll_placed_ok_of_deps_core_gen hC hSer hGet' hPut' hDec' hEq'
    hFitGet hSaveErr hFitSer hFitPut hSaveOk hstk

/-- Block `565` (`save_identity::{closure#0}`) meets
`idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk`
given `AllocContractsXCliPlaced`, `Dir::get` (block `589`), `Dir::put::<&str>` (block `543`),
`IdentityKey::decode` (block `18`), and `<PublicKey as PartialEq>::eq` (block `212`). -/
theorem idSavePoll_placed_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {getProg putProg decProg eqProg : Program} {getBlk putBlk decBlk eqBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    [IsLsBlockProg decProg decBlk H]
    [IsLsBlockProg eqProg eqBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
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
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk) := by
  have hSer := publicKeySerialize_lscro_of_cli
    (callerProg := (blkPC_565).rebase (blkPl_565).base H) hC (by decide)
  have hGet' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hGet (by decide) hGetBlk hGetUnmut
  have hPut' := ls_transfer_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hPut (by decide) hPutBlk hPutUnmut
  have hDec' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hDec (by decide) hDecBlk hDecUnmut
  have hEq' := ls_transfer_cl_to_lscro (callerProg := (blkPC_565).rebase (blkPl_565).base H)
    hEq (by decide) hEqBlk hEqUnmut
  exact idSavePoll_placed_ok_of_deps_core hC hSer hGet' hPut' hDec' hEq' hstk

/-- Convenience specialization discharging `IdentityKey::decode` via
`identityKey_decode_placed_ok` and `<PublicKey as PartialEq>::eq` via
`publicKeyEq_placed_ok_of_bb`. -/
theorem idSavePoll_placed_ok_of_get_put_bb [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {GetEnv : FsFiles → DirGhost → List (BitVec 8) → List AllocEvent → Prop}
    {PutStrEnv : DirGhost → List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {getProg putProg : Program} {getBlk putBlk : Nat}
    [IsLsBlockProg getProg getBlk H]
    [IsLsBlockProg putProg putBlk H]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {getStk putStk stk : Nat}
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
      (max publicKeySerializeStackX extHookStack) ≤ stk)
    (hGetBlk : getBlk < 619 := by decide)
    (hGetUnmut : (getBlk ∈ libsignalMutatedBlocks) = false := by decide)
    (hPutBlk : putBlk < 619 := by decide)
    (hPutUnmut : (putBlk ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (lsProg_565 H) (lsmpl.base 565)
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk) :=
  idSavePoll_placed_ok_of_deps hC hGet hPut
    (identityKey_decode_placed_ok H)
    (publicKeyEq_placed_ok_of_bb h_bb) hstk hGetBlk hGetUnmut hPutBlk hPutUnmut

theorem idSavePoll_placed_caller_ok_of_deps_gen [LibsignalPlacement] {M : AllocCostModel}
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
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
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
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
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
      (idSavePollSpecPlaced rd pathOk A lim SaveEnv stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 565)
    (idSavePoll_placed_ok_of_deps_gen hC hGet hPut hDec hEq
      hFitGet hSaveErr hFitSer hFitPut hSaveOk hstk
      hGetBlk hGetUnmut hPutBlk hPutUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

theorem idSavePoll_placed_caller_ok_of_deps [LibsignalPlacement] {M : AllocCostModel}
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
    (hC : AllocContractsXCliPlaced A lim H)
    (hGet : subroutine_ok getProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A lim GetEnv getStk))
    (hPut : subroutine_ok putProg (lsmpl.base 543)
      (dirPutStrSpecPlaced A lim PutStrEnv putStk))
    (hDec : subroutine_ok decProg (lsmpl.base 18)
      (identityKeyDecodePlacedBudgetSpec A))
    (hEq : subroutine_ok eqProg (lsmpl.base 212)
      (withLsCodeLoaded lsmpl (withVmPreserved publicKeyEqSpec)))
    (hstk : 0xd0 + max (max (max getStk putStk) (max 0x60 64))
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
      (idSavePollSpecPlaced rd pathOk A lim (CliIdSavePollEnv rd GetEnv PutStrEnv) stk) :=
  ls_transfer_lscro (callerProg := callerProg) (j := 565)
    (idSavePoll_placed_ok_of_deps hC hGet hPut hDec hEq hstk
      hGetBlk hGetUnmut hPutBlk hPutUnmut hDecBlk hDecUnmut hEqBlk hEqUnmut) hCallerBlk

end Placed

end LibsignalBinary.Proofs.SignalSession.Cli.Store.IdSavePollPlacedBudget
