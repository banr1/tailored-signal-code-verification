/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SegmentProofs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegRegionNonePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegLoadPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegWritePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegPostNonePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegTrustPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegRegionSomePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegStorePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegPostSomePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegUntrustedPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegErrTeardownPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordJoin
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordSplit

/-!
# Relocatable CLI `MessageDecrypt` Segment Proofs Bundle

Packages the twelve relocatable (`[LibsignalPlacement]`) `MessageDecrypt` segment proofs on
`lsProg_463` into `DecSegsVPlaced`.
-/

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
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced segLoadVPlaced_ok segDispatchVPlaced_ok segRegionSomeVPlaced_ok segRegionNoneVPlaced_ok segPostSomeVPlaced_ok segPostNoneVPlaced_ok segTrustVPlaced_ok segUntrustedVPlaced_ok segSaveVPlaced_ok segStoreVPlaced_ok segErrTeardownVPlaced_ok segWriteVPlaced_ok recordSplit_placed_ok recordJoin_placed_ok DecSegsVPlaced decSegsVPlaced_of_seams decSegsVPlaced_ok

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
variable {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {Scope : SessionRecord (List (BitVec 8)) → Prop}


open CryptoVerification

variable [LibsignalPlacement] {H : LibsignalHooks}
  {kitPlaced : SessionStoreSpec A 0#64} {ikitPlaced : IdentityStoreSpec A 0#64}
  {st0Placed : kitPlaced.StoreState} {ist0Placed : ikitPlaced.IdState}

theorem segLoadVPlaced_ok :
    SegLoadSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegLoad.segLoadVPlaced_ok

theorem segDispatchVPlaced_ok :
    SegDispatchSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch.segDispatchVPlaced_ok

theorem segRegionSomeVPlaced_ok :
    SegRegionSomeSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionSome.segRegionSomeVPlaced_ok

theorem segRegionNoneVPlaced_ok :
    SegRegionNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegRegionNone.segRegionNoneVPlaced_ok

theorem segPostSomeVPlaced_ok :
    SegPostSomeSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostSome.segPostSomeVPlaced_ok

theorem segPostNoneVPlaced_ok :
    SegPostNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegPostNone.segPostNoneVPlaced_ok

theorem segTrustVPlaced_ok :
    SegTrustSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegTrust.segTrustVPlaced_ok

theorem segUntrustedVPlaced_ok :
    SegUntrustedSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.segUntrustedVPlaced_ok

theorem segSaveVPlaced_ok :
    SegSaveSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegSave.segSaveVPlaced_ok

theorem segStoreVPlaced_ok :
    SegStoreSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegStore.segStoreVPlaced_ok

theorem segErrTeardownVPlaced_ok :
    SegErrTeardownSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown.segErrTeardownVPlaced_ok

theorem segWriteVPlaced_ok :
    SegWriteSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegWrite.segWriteVPlaced_ok

theorem recordSplit_placed_ok : RecordSplit :=
  CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordSplit.recordSplit_placed_ok

theorem recordJoin_placed_ok : RecordJoin :=
  CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.RecordJoin.recordJoin_placed_ok

/-- Bundle of the twelve relocatable `MessageDecrypt` segment specifications parameterized by `kit`, `ikit`, `st0`, `ist0`, and `Scope`. -/
structure DecSegsVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  load : SegLoadSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  dispatch : SegDispatchSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  regionSome : SegRegionSomeSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  regionNone : SegRegionNoneSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  postSome : SegPostSomeSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  postNone : SegPostNoneSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  trust : SegTrustSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  untrusted : SegUntrustedSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  save : SegSaveSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  store : SegStoreSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  errTeardown : SegErrTeardownSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope
  write : SegWriteSpecVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope

theorem decSegsVPlaced_of_seams {parse : UuidParser}
    (hLoad : SegLoadSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hDispatch : SegDispatchSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hRegionSome : SegRegionSomeSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hRegionNone : SegRegionNoneSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hPostSome : SegPostSomeSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hPostNone : SegPostNoneSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hTrust : SegTrustSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hUntrusted : SegUntrustedSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hSave : SegSaveSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hStore : SegStoreSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hErrTeardown : SegErrTeardownSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope)
    (hWrite : SegWriteSpecVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope) :
    DecSegsVPlaced C A ctl parse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  ⟨hLoad, hDispatch, hRegionSome, hRegionNone, hPostSome, hPostNone, hTrust, hUntrusted,
    hSave, hStore, hErrTeardown, hWrite⟩

theorem decSegsVPlaced_ok :
    DecSegsVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  decSegsVPlaced_of_seams segLoadVPlaced_ok segDispatchVPlaced_ok segRegionSomeVPlaced_ok
    segRegionNoneVPlaced_ok segPostSomeVPlaced_ok segPostNoneVPlaced_ok segTrustVPlaced_ok
    segUntrustedVPlaced_ok segSaveVPlaced_ok segStoreVPlaced_ok segErrTeardownVPlaced_ok
    segWriteVPlaced_ok


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
