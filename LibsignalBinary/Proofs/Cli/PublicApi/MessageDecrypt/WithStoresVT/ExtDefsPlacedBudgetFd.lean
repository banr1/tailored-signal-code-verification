/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudgetFd
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget

/-!
# File-Descriptor-Threaded `WithStoresVT` Foundations (`ExtDefsPlacedBudgetFd`)

Extends `ExtDefsPlacedBudget` on `lsProg_463 H` with `FdsGe3Closed` contracts for `load_session`
and pre-cutoff `memcpy`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (IsLsBlockProg LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitLoadPollPlacedSpecSE)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv kitLoadShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (FdsGe3Closed withFdsGe3Closed)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudgetFd (DecFsCtxPlacedFd)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
  (DecHypsExtPlaced)

/-- Filesystem invariant carrier with `FdsGe3Closed` for `decrypt_signal` on `lsProg_463 H`. -/
abbrev DecFsCtxExtPlacedFd [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  DecFsCtxPlacedFd kit ikit H s0 s

/-- `FdsGe3Closed`-preserving `load_session` shim, poll, and future-drop contracts. -/
structure SessionLoadPlacedOkSEFds [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  loadShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadShimOff)
      (withLsRoCl lsmpl (kitLoadShimSpec M A lim kit true))
  loadPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadPollOff)
      (withLsRoCl lsmpl (kitLoadPollPlacedSpecSE M A lim kit kitEnv Scope encRecord true))
  loadFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadFutDropOff)
      (withLsRoCl lsmpl (futDropBudgetSpec kit.fdsOk true))

theorem SessionLoadPlacedOkSEFds.of_kit [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (h : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H true) :
    SessionLoadPlacedOkSEFds A lim kit kitEnv Scope encRecord H where
  loadShim := h.loadShim
  loadPoll := h.loadPoll
  loadFutDrop := h.loadFutDrop

/-- `PublicApiDecHooksPlaced` extended with `FdsGe3Closed`-preserving `memcpy` for `SegDispatch`. -/
structure PublicApiDecHooksPlacedFd [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  base : PublicApiDecHooksPlaced A lim H
  memcpyFds : HookSat H "memcpy" (withFdsGe3Closed sessionMemcpyRegionBudgetSpec)

/-- File-descriptor-threaded relocatable hypothesis bundle for `MessageDecrypt` segments on `lsProg_463 H`. -/
structure DecHypsExtPlacedFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A.repAlloc 0#64) (ssEnv : SessionStoreBudgetEnv ss)
    (id : IdentityStoreSpec A.repAlloc 0#64) (idEnv : IdentityStoreBudgetEnv id)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  base : DecHypsExtPlaced C A lim parse S encRecord H ss ssEnv id idEnv st0 Scope
  hooksFd : PublicApiDecHooksPlacedFd A lim H
  loadFds : SessionLoadPlacedOkSEFds A lim ss ssEnv Scope encRecord H
  ikitFds : IdentityStoreKitPlacedOkI A lim id idEnv H true
  ss_fdsOk : ∀ fs, ss.fdsOk fs ↔ FdsGe3Closed fs
  id_fdsOk : ∀ fs, id.fdsOk fs ↔ FdsGe3Closed fs

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudgetFd
