/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridgePlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# File-Descriptor-Threaded Inner Store-Kit Specification for `decrypt_signal` (Placed)

`withFdsGe3Closed`-threaded variants of `withStoresDecPlacedSpecVTP` and `InnerDecryptPlacedOk`
(and their `withLsFrozen`-guarded counterparts) on Block `463`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudgetFd

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord)
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityStoreSpec SessionStoreSpec withEnvPre)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (withFdsGe3Closed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced withStoresDecFrozenPlacedSpecVTP withStoresDecPlacedSpecVTP)

def withStoresDecPlacedSpecVTPFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  withFdsGe3Closed
    (withStoresDecPlacedSpecVTP C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope)

/-- `withFdsGe3Closed`-threaded inner store-kit hypothesis on Block `463` (`lsProg_463 H`). -/
def InnerDecryptPlacedOkFd [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    FilesOkPeer scopeIn F0 peer.val →
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok (lsProg_463 H) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTPFd P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

def withStoresDecFrozenPlacedSpecVTPFd [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  withFdsGe3Closed
    (withStoresDecFrozenPlacedSpecVTP C A lim ctl parse S tdEnv encRecord
      kit kitEnv ikit ikitEnv st0 ist0 Scope)

/-- `withLsFrozen`-guarded `withFdsGe3Closed` inner store-kit hypothesis on Block `463` (`lsProg_463 H`). -/
def InnerDecryptFrozenPlacedOkFd [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    FilesOkPeer scopeIn F0 peer.val →
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok (lsProg_463 H) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecFrozenPlacedSpecVTPFd P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudgetFd
