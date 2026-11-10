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
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.Spec
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridgePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Inner Store-Kit Specification for `decrypt_signal` (Placed)

Budget-pool counterparts of `withStoresDecPlacedSpecVTP`, `InnerDecryptPlacedOk`, and
`InnerDecryptFrozenPlacedOk` on Block `463` (`signal_session_ratchet::decrypt_signal`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding lsLogOff withLsCodeRoLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.CliRatchet.DecPlaced
open CryptoVerification.LibsignalSpqrV1 hiding Bytes
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
  (cliIdentityStoreSpecPlaced cliSessionStoreSpecPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (withStoresDecPlacedSpecVX)

noncomputable abbrev cliAnswers :=
  @CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1CliAnswers
abbrev cliStep :=
  @CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1CliStep
abbrev cliFinal :=
  @CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas.w1CliFinal
abbrev decNeedAux :=
  @CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.decNeedAux
noncomputable abbrev decKeyAux :=
  @CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.decKeyAux
noncomputable abbrev decDefAux :=
  @CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.decDefAux
abbrev decDefAux_eq_model :=
  @CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas.decDefAux_eq_model

/-- Budget-threaded tight store-kit contract for `decrypt_signal` under `[LibsignalPlacement]`,
threading `tokenInitPlacedAt` and `Slots.DistinctSid`. -/
def withStoresDecPlacedSpecVTP [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  let base := withStoresDecPlacedSpecVX
    C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope (fun _ _ => False)
  { base with
    pre := fun xs s =>
      ⌜Slots.DistinctSid parse xs.1.loc.name.bytes xs.1.rem.name.bytes⌝ ∗
        tokenInitPlacedAt ∗ base.pre xs s
    post := fun xs s0 sf =>
      tokenInitPlacedAt ∗ base.post xs s0 sf }

noncomputable abbrev decSessKitPlaced [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    SessionStoreSpec A 0#64 :=
  cliSessionStoreSpecPlaced A cliIo.rd F0 cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

noncomputable abbrev decIdKitPlaced [LibsignalPlacement] (A : RustAlloc)
    (F0 : FsFiles) (peer : AddrGhost) (B : RunBudgets) :
    IdentityStoreSpec A 0#64 :=
  cliIdentityStoreSpecPlaced A cliIo.rd F0 cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

/-- Budget-threaded inner store-kit hypothesis on Block `463` (`lsProg_463 H`) at
`decSessKitPlaced A.repAlloc` and `decIdKitPlaced A.repAlloc`. -/
def InnerDecryptPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok (lsProg_463 H) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecPlacedSpecVTP P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv E2E.Record.encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

def withStoresDecFrozenPlacedSpecVTP [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec (DecryptGhost × M.σ) :=
  CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
    (withStoresDecPlacedSpecVTP C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope)

/-- `withLsFrozen`-guarded variant of `InnerDecryptPlacedOk` on Block `463` (`lsProg_463 H`). -/
def InnerDecryptFrozenPlacedOk [LibsignalPlacement] {M : AllocCostModel}
    (P : PEParams) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : LibsignalHooks) (B : RunBudgets)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (kitEnv : ∀ F0 peer, SessionStoreBudgetEnv (decSessKitPlaced A.repAlloc F0 peer B))
    (ikitEnv : ∀ F0 peer, IdentityStoreBudgetEnv (decIdKitPlaced A.repAlloc F0 peer B)) : Prop :=
  ∀ (F0 : FsFiles) (peer : AddrGhost),
    Slots.FilesOkPeer Slots.scopeIn F0 peer.val →
    let kit := decSessKitPlaced A.repAlloc F0 peer B
    let ikit := decIdKitPlaced A.repAlloc F0 peer B
    subroutine_ok (lsProg_463 H) (lsmpl.base 463)
      (withEnvPre
        (withStoresDecFrozenPlacedSpecVTP P.C A lim 0#64 uuidTryParse
          (pqxdhSpqrModel P) tdEnv E2E.Record.encodeRecord
          kit (kitEnv F0 peer) ikit (ikitEnv F0 peer)
          StoresGhost.opened.sessions StoresGhost.opened.identity Slots.scopeKit)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
