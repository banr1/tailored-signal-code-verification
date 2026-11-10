/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.CmDrop
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CalleeProofs.KyberMap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.EncModel
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStore
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegApplyStoreTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinish
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFinishTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentity
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSomeTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSave
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSaveTrap
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignal
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrust
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustTrap
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.SegmentProofs

/-!
# `MessageEncrypt` Segment, Callee, and Bridge Re-Exports

Collects the nine segment theorems (`segLoad` through `segFinish`), callee contracts (`kyberMap_ok`,
`cmDrop_ok`), and callee-bundle bridges (`otrEncryptOkQ_of_emptyRun`, `encCallees_ok`) for
`signal_session_ratchet::encrypt` in both normal and trap-at-RNG modes.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

variable {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)}

/- The segment packets are generic in the loaded record's scope `Scope` and the SPQR precondition
`Q` of `OTR::encrypt` (`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv`; only the statements that mention them take them). -/

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}

/-! ## Segments -/

/-- `segLoad` (`+0x000..+0x20c`, `+0x41c..+0x45c`, `+0x660..+0x680`): executes the prologue,
session-store load shim/poll/cleanup, and result dispatch, advancing to `CurStateV` on `Ok (some r)`
with a current session or exiting via T1/T2 on store error or missing session. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segLoad_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegLoad.segLoad_ok

/-- `segFrom` (`+0x20c..+0x2c8`): calls `OutgoingTripleRatchet::from_session_state`, advancing to
`OtrStateV` with the moved 200-byte ratchet at `sp + 0x288` on `Ok` or exiting via T1 `+0x49c` on
protocol error. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFrom_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.segFrom_ok

/-- `segIdentity` (`+0x2c8..+0x344`, panic `+0xfac..+0xfc4`): queries `remote_identity_key`,
advancing to `KeyStateV` with the 32-byte key at `sp + 0x350` on `Some k` or panicking via
`expect_failed` on `None`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segIdentity_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.segIdentity_ok

/-- `segSignal` (`+0x344..+0x41c`, error tail `+0xc14`): handles `pendingPreKey = none`, calling
`unacknowledged_pre_key_message_items` and `OTR::encrypt`, copying the `SignalMessage` to
`sp + 0x370` (`CmStateV` at `+0xa70`) on `Ok` or exiting via T5/T1 on error. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSignal_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok

/-- `segPreKey` (`+0x344..+0x390`, `+0x680..+0xa70`): handles `pendingPreKey = some items`,
checking session staleness (`duration_since` and `timeAdd`), mapping the optional Kyber payload,
calling `OTR::encrypt` and `PreKeySignalMessage::new`, and writing the 248-byte result to
`CmStateV` at `+0xa70`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segPreKey_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_ok_body

/-- `segTrust` (`+0xa70..+0xbd4`, `+0xc78..+0xd50`): runs the identity-store `is_trusted_identity`
shim/poll/cleanup (`Sending`), advancing to `SaveStateV` on `Ok true` or dropping the ciphertext
message and exiting on `Ok false` (`UntrustedIdentity`) or store error. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.segTrust_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.segTrust_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.segTrust_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segTrust_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.segTrust_ok

/-- `segSave` (`+0xbd4..+0xc14`, `+0xd50..+0xd9c`): runs the identity-store `save_identity`
shim/poll/cleanup, advancing to `ApplyStateV` on `Ok c` or exiting via `+0xe28` → T5/T1 on store
error. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave.segSave_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave.segSave_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave.segSave_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segSave_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSave.segSave_ok

/-- `segApplyStore` (`+0xd9c..+0xe88`, `+0xf2c..+0xf3c`): applies the updated outgoing ratchet back
to the session state and runs the session-store `store_session` shim/poll/cleanup, advancing to
`StoredStateV` on `Ok ()` or exiting via T5/T1 on store error. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.segApplyStore_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.segApplyStore_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.segApplyStore_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segApplyStore_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegApplyStore.segApplyStore_ok

/-- `segFinish` (`+0xe88..+0xfac`, T2 `+0x5f8..+0x660`): drops the in-frame `SessionRecord`, copies
the 248-byte `CiphertextMessage` to the return slot, and executes the epilogue to establish the
`withStoresEncSpecV` postcondition. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_okV_trap {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish.segFinish_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish.segFinish_okV

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_ok_trap : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish.segFinish_ok_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.segFinish_ok : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish.segFinish_ok

/-! ## Callees -/

/-- `kyberMap`: proves that the `Option::map` closure for `KyberPayload` satisfies `KyberMapOk_trap`
(allocating and copying the Kyber ciphertext box on `Some`, or panicking on OOM). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.kyberMap_ok_trap (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk_trap img C A abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_ok_trap h3 himg

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.kyberMap_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KyberMapOk img C A ctl abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.KyberMap.kyberMap_ok h3 himg

/-- `cmDrop`: proves that `drop_glue::<CiphertextMessage>` frees all owned heap buffers of either
`SignalMessage` or `PreKeySignalMessage` variant (`CmDropOk_trap`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmDrop_ok_trap (h3 : TripleRatchetHooks C A S (trTrapExterns C abs))
    (himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk_trap img C A abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok_trap h3 himg

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmDrop_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmDropOk img C A ctl abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.CmDrop.cmDrop_ok h3 himg

/-! ## Bridges -/

/-- Specializes `OtrEncryptOkQ` to the empty SPQR state `(· = [])` from `OtrEncryptEmptyRunStmt`
and `S.SendEmptyOk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptOkQ_of_emptyRun (hrun : CryptoVerification.Cli.LibsignalTripleRatchet.OtrEncryptEmptyRunStmt C A ctl S abs img)
    (h2 : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ (· = []) img C A ctl uuidTryParse S abs := by
  have h := hrun h2 hE himg
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) himg] at h

/-- Bundles `otrFrom_ok`, `otrApply_ok`, `remoteIdentityKeyOk`, `hEnc`, `unackItems`, `kyberMap`,
`preKeyMsgNew`, and `cmDrop` into `EncCallees_trap` (generic in `Q`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCallees_ok_of_callees_trap
    (h3 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CliEncHooks C A S (trTrapExterns C abs))
    (hEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ_trap Q img C A ctl uuidTryParse S abs)
    (hUnack : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.UnackItemsOk_trap img C A abs)
    (hPsm : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.PreKeyMsgNewOk_trap img C A abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_trap Q img C A ctl uuidTryParse S abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs_trap
    h3.alloc hEnc himg hUnack
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.kyberMap_ok_trap h3.toTripleRatchetHooks himg)
    hPsm
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmDrop_ok_trap h3.toTripleRatchetHooks himg)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCallees_ok (h3 : PublicApiHooks C A S encRecord abs)
    (hEnc : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrEncryptOkQ Q img C A ctl uuidTryParse S abs) (himg : Obj.Loads libsignalSessionImage img) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees Q img C A ctl uuidTryParse S abs := by
  exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.EncModel.encCallees_of_calleeProofs h3 hEnc himg
    (unackItems_ok h3 himg) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.kyberMap_ok h3 himg) (preKeyMsgNew_ok h3 himg) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmDrop_ok h3 himg)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
