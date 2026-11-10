/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem SessionOnlyKitPlacedOkSE.loadShim_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.loadShimOff)
      (StoreKit.withLsRoCl lsmpl (kitLoadShimSpec kit)) :=
  h.loadShim (callerBlk := 463) (by decide)

theorem SessionOnlyKitPlacedOkSE.loadPoll_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.loadPollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitLoadPollPlacedSpecSE kit Scope encRecord)) :=
  h.loadPoll (callerBlk := 463) (by decide)

theorem SessionOnlyKitPlacedOkSE.loadFutDrop_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.loadFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec) :=
  h.loadFutDrop (callerBlk := 463) (by decide)

theorem SessionOnlyKitPlacedOkSE.storeShim_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.storeShimOff)
      (StoreKit.withLsRoCl lsmpl (kitStoreShimSpec kit)) :=
  h.storeShim (callerBlk := 463) (by decide)

theorem SessionOnlyKitPlacedOkSE.storePoll_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.storePollOff)
      (StoreKit.withLsRoCl lsmpl (StoreKit.kitStorePollPlacedSpecE kit encRecord)) :=
  h.storePoll (callerBlk := 463) (by decide)

theorem SessionOnlyKitPlacedOkSE.storeFutDrop_463 [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    (h : StoreKit.SessionOnlyKitPlacedOkSE kit Scope encRecord H) :
    subroutine_ok (lsProg_463 H) (0#64 + kit.storeFutDropOff)
      (StoreKit.withLsRoCl lsmpl futDropSpec) :=
  h.storeFutDrop (callerBlk := 463) (by decide)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
