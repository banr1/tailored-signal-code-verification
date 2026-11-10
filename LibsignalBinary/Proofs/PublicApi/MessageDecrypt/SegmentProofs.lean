/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordJoin
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.RecordSplit
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegDispatch
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegErrTeardown
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegLoad
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostNone
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegPostSome
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionNone
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegRegionSome
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegSave
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStore
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegTrust
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegWrite

/-!
# `MessageDecrypt` Segment Proofs and Bundles

Exports the twelve store-kit-parameterized segment proofs (`segLoadV_ok` through `segWriteV_ok`),
the `recordSplit_ok` and `recordJoin_ok` separation-logic bridges, and the relocatable
`[LibsignalPlacement]` segment bundle `DecSegsVPlaced` (`decSegsV_placed_ok`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}
  {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
  {st0 : kit.StoreState} {ist0 : ikit.IdState}
  {Scope : SessionRecord (List (BitVec 8)) → Prop}

/-! ## Store-kit-parameterized (`V`) segments -/

theorem segLoadV_ok : SegLoadSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegLoad.segLoadV_ok

theorem segDispatchV_ok : SegDispatchSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegDispatch.segDispatchV_ok

theorem segRegionSomeV_ok : SegRegionSomeSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegRegionSome.segRegionSomeV_ok

theorem segRegionNoneV_ok : SegRegionNoneSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegRegionNone.segRegionNoneV_ok

theorem segPostSomeV_ok : SegPostSomeSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegPostSome.segPostSomeV_ok

theorem segPostNoneV_ok : SegPostNoneSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegPostNone.segPostNoneV_ok

theorem segTrustV_ok : SegTrustSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegTrust.segTrustV_ok

theorem segUntrustedV_ok : SegUntrustedSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegUntrusted.segUntrustedV_ok

theorem segSaveV_ok : SegSaveSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegSave.segSaveV_ok

theorem segStoreV_ok : SegStoreSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegStore.segStoreV_ok

theorem segErrTeardownV_ok : SegErrTeardownSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegErrTeardown.segErrTeardownV_ok_pf

theorem segWriteV_ok : SegWriteSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope :=
  Pf.SegWrite.segWriteV_ok

/-! ## Bridges -/

/-- Pure separation-logic bridge splitting a loaded `SessionRecord` with a current session into its `previous_sessions` header and `sessionStateAt`. -/
theorem recordSplit_ok : RecordSplit := by
  exact Pf.RecordSplit.recordSplit_ok

/-- Pure separation-logic bridge reassembling `sessionRecordAt` after `AfterRecordDecrypt G G'` with cleared pending pre-key fields. -/
theorem recordJoin_ok : RecordJoin := by
  exact Pf.RecordJoin.recordJoin_ok

/-! ## Relocatable `[LibsignalPlacement]` Segments & Bundle -/

section Placed

open CryptoVerification CryptoVerification.LibsignalPublicApi.Placed

variable [LibsignalPlacement] {H : LibsignalHooks}
  {kitPlaced : SessionStoreSpec A 0#64} {ikitPlaced : IdentityStoreSpec A 0#64}
  {st0Placed : kitPlaced.StoreState} {ist0Placed : ikitPlaced.IdState}

theorem segLoadVPlaced_ok :
    SegLoadSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegLoad.segLoadVPlaced_ok

theorem segDispatchVPlaced_ok :
    SegDispatchSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegDispatch.segDispatchVPlaced_ok

theorem segRegionSomeVPlaced_ok :
    SegRegionSomeSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegRegionSome.segRegionSomeVPlaced_ok

theorem segRegionNoneVPlaced_ok :
    SegRegionNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegRegionNone.segRegionNoneVPlaced_ok

theorem segPostSomeVPlaced_ok :
    SegPostSomeSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegPostSome.segPostSomeVPlaced_ok

theorem segPostNoneVPlaced_ok :
    SegPostNoneSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegPostNone.segPostNoneVPlaced_ok

theorem segTrustVPlaced_ok :
    SegTrustSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegTrust.segTrustVPlaced_ok

theorem segUntrustedVPlaced_ok :
    SegUntrustedSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegUntrusted.segUntrustedVPlaced_ok

theorem segSaveVPlaced_ok :
    SegSaveSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegSave.segSaveVPlaced_ok

theorem segStoreVPlaced_ok :
    SegStoreSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegStore.segStoreVPlaced_ok

theorem segErrTeardownVPlaced_ok :
    SegErrTeardownSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegErrTeardown.segErrTeardownVPlaced_ok

theorem segWriteVPlaced_ok :
    SegWriteSpecVPlaced C A ctl uuidTryParse S encRecord H kitPlaced ikitPlaced st0Placed ist0Placed Scope :=
  Pf.SegWrite.segWriteVPlaced_ok

theorem recordSplit_placed_ok : RecordSplit :=
  Pf.RecordSplit.recordSplit_placed_ok

theorem recordJoin_placed_ok : RecordJoin :=
  Pf.RecordJoin.recordJoin_placed_ok

/-- The twelve `[LibsignalPlacement]` segment specifications parameterized by `kit`, `ikit`,
`st0`, `ist0`, and `Scope`. -/
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

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
