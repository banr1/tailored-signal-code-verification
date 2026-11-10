/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBodyPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSavePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStorePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `MessageEncrypt` Segment Proofs

Exports the nine relocatable `[LibsignalPlacement]` segment theorems on Block `464` (`lsProg_464 Hk`)
and bundles them into `encSegsV_placed_ok : EncSegsVPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

variable [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {H : LibsignalHooks}
  {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}

theorem segLoad_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegLoadSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegLoad.segLoad_placed_okV

theorem segFrom_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegFromSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegFrom.segFrom_placed_okV

theorem segIdentity_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegIdentitySpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegIdentity.segIdentity_placed_okV

theorem segSignal_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegSignalSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegSignal.segSignal_placed_okV

theorem segPreKey_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegPreKeySpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegPreKey.segPreKey_placed_okV

theorem segTrust_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegTrustSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegTrust.segTrust_placed_okV

theorem segSave_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegSaveSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegSave.segSave_placed_okV

theorem segApplyStore_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegApplyStoreSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegApplyStore.segApplyStore_placed_okV

theorem segFinish_placed_okV {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    SegFinishSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  Pf.SegFinish.segFinish_placed_okV

/-- Bundle of all nine relocatable `[LibsignalPlacement]` `MessageEncrypt` segments on `lsProg_464 H`. -/
theorem encSegsV_placed_ok {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} :
    EncSegsVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H :=
  ⟨segLoad_placed_okV, segFrom_placed_okV, segIdentity_placed_okV, segSignal_placed_okV,
   segPreKey_placed_okV, segTrust_placed_okV, segSave_placed_okV, segApplyStore_placed_okV,
   segFinish_placed_okV⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
