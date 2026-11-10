/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Separation-Logic and Store-Kit Bridges for `encrypt`

`[LibsignalPlacement]` counterparts of `cliSessionStoreSpec`, `cliIdentityStoreSpec`, stack budget
bounds, and `storesAt` entry/exit framing for `signal_session_ratchet::encrypt`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification

/-! ## Relocatable CLI store kits -/

/-- Relocatable `[LibsignalPlacement]` counterpart of `cliSessionStoreSpec` with placed vtable, shim, poll, and drop offsets. -/
def cliSessionStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (peer : AddrGhost) (loadShimStk loadPollStk storeShimStk storePollStk : Nat) :
    SessionStoreSpec A 0#64 :=
  { cliSessionStoreSpec A 0#64 rd F0 pathOk Scope peer
      loadShimStk loadPollStk storeShimStk storePollStk with
    ss_vt := lsρ cliSessionVtSym
    id_vt := lsρ cliIdentityVtSym
    loadShimOff := lsmpl.base 604
    storeShimOff := lsmpl.base 605
    loadFutVtOff := lsρ sessLoadFutVtSym
    storeFutVtOff := lsρ sessStoreFutVtSym
    loadPollOff := lsmpl.base 569
    storePollOff := lsmpl.base 570
    loadFutDropOff := lsDropOffPlaced
    storeFutDropOff := lsDropOffPlaced
    loadFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    storeFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

/-- Relocatable `[LibsignalPlacement]` counterpart of `cliIdentityStoreSpec` with placed vtable, shim, poll, and drop offsets. -/
def cliIdentityStoreSpecPlaced [LibsignalPlacement] (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (trustShimStk trustPollStk saveShimStk savePollStk : Nat) :
    IdentityStoreSpec A 0#64 :=
  { cliIdentityStoreSpec A 0#64 rd F0 pathOk peer
      trustShimStk trustPollStk saveShimStk savePollStk with
    id_vt := lsρ cliIdentityVtSym
    trustShimOff := lsmpl.base 601
    trustFutVtOff := lsρ idTrustFutVtSym
    trustPollOff := lsmpl.base 566
    trustFutDropOff := lsDropOffPlaced
    saveShimOff := lsmpl.base 600
    saveFutVtOff := lsρ idSaveFutVtSym
    savePollOff := lsmpl.base 565
    saveFutDropOff := lsDropOffPlaced
    trustFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero
    saveFutDrop_ne_zero := fun _ => lsDropOffPlaced_ne_zero }

noncomputable abbrev w1SessKitPlaced [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) : SessionStoreSpec E2E.HooksE.A0 0#64 :=
  cliSessionStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F cliWrOk Slots.scopeKit peer
    SessKit.loadShimNeed (SessKit.loadPollNeed B.readFile)
    SessKit.storeShimNeed SessKit.storePollNeedX

noncomputable abbrev w1IdKitPlaced [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) : IdentityStoreSpec E2E.HooksE.A0 0#64 :=
  cliIdentityStoreSpecPlaced E2E.HooksE.A0 cliIo.rd F cliWrOk peer
    IdKit.trustShimNeed (IdKit.trustPollNeed B.readFile)
    IdKit.saveShimNeed (IdKit.savePollNeed B.readFile)

theorem w1_innerStack_le_need_placed [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) :
    withStoresEncStackV (w1SessKitPlaced B F peer) (w1IdKitPlaced B F peer) ≤ w1EncryptNeed B :=
  w1_innerStack_le_need B default F peer

/-! ## Entry and exit `storesAt` framing -/

theorem storesAt_opened_to_kits_placed [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (B : RunBudgets) (F : FsFiles) (peer : AddrGhost) (a : BitVec 64)
    (hsub : ∀ r, Scope r → Slots.scopeIn r)
    (hok : Slots.FilesOkPeer Scope F peer.val) :
    storesAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      (w1SessKitPlaced B F peer).storeAt (a + 0xf0#64) StoresGhost.opened.sessions ∗
        (w1IdKitPlaced B F peer).identityAt a StoresGhost.opened.identity ∗
        w1UnusedDirsAt E2E.HooksE.A0 a StoresGhost.opened :=
  storesAt_opened_to_kits B default F peer a hsub hok

theorem kits_to_storesAt_placed [LibsignalPlacement]
    (B : RunBudgets) (F : FsFiles) (peer : AddrGhost)
    (a : BitVec 64) (sess : DirGhost) (idg : IdGhost) :
    (w1SessKitPlaced B F peer).storeAt (a + 0xf0#64) sess ∗
      (w1IdKitPlaced B F peer).identityAt a idg ∗
      w1UnusedDirsAt E2E.HooksE.A0 a StoresGhost.opened ⊢
      storesAt E2E.HooksE.A0 a (mkCliStores sess idg) :=
  kits_to_storesAt B default F peer a sess idg

/-! ## Store-relation and final-state equalities -/

theorem w1SessKitPlaced_callsRel_eq [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) (st0 : DirGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (w1SessKitPlaced B F peer).callsRel st0 ans cs ↔
      (w1SessKit B default F peer).callsRel st0 ans cs := by
  induction cs generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, ih] <;> rfl

theorem w1SessKitPlaced_storeFinal_eq [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) (st0 : DirGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (w1SessKitPlaced B F peer).storeFinal st0 ans cs =
      (w1SessKit B default F peer).storeFinal st0 ans cs := by
  induction cs generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> exact ih _

theorem w1IdKitPlaced_idCallsRel_eq [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) (ist0 : IdGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (w1IdKitPlaced B F peer).idCallsRel ist0 ans cs ↔
      (w1IdKit B default F peer).idCallsRel ist0 ans cs := by
  induction cs generalizing ist0 with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> simp only [IdentityStoreSpec.idCallsRel] <;>
      first | exact ih _ | exact and_congr_right fun _ => ih _

theorem w1IdKitPlaced_idFinal_eq [LibsignalPlacement] (B : RunBudgets) (F : FsFiles)
    (peer : AddrGhost) (ist0 : IdGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8)))) :
    (w1IdKitPlaced B F peer).idFinal ist0 ans cs =
      (w1IdKit B default F peer).idFinal ist0 ans cs := by
  induction cs generalizing ist0 with
  | nil => rfl
  | cons c cs ih => cases c <;> exact ih _

end CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas
