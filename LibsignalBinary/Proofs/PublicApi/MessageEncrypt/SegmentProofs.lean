/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDrop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMap
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItems
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.EncModel
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegApplyStore
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinish
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentity
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegLoadDispatchSome
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyBody
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSave
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignal
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrust

/-!
# Top-Level Segment, Callee, and Bridge Theorems for `session_message_encrypt`

Re-exports the nine segment proofs (`segLoad_okV` through `segFinish_okV`), the four `MessageEncrypt`
callee proofs (`unackItems_ok`, `kyberMap_ok`, `preKeyMsgNew_ok`, `cmDrop_ok`), and the `OTR::encrypt`
and pure-model bridges assembled in `Assembly.lean`.
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

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}

/-! ## Segments -/

/-- Entry-to-`Cur` segment (`+0x000..+0x20c`, `+0x41c..+0x45c`, `+0x660..+0x680`): `load_session`
shim, poll, and dispatch. -/
theorem segLoad_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegLoadSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegLoad.segLoad_okV

theorem segLoad_ok : SegLoadSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegLoad.segLoad_ok

/-- `Cur`-to-`Otr` segment (`+0x20c..+0x2c8`): `OutgoingTripleRatchet::from_session_state` and
200-byte OTR relocation. -/
theorem segFrom_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegFromSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegFrom.segFrom_okV

theorem segFrom_ok : SegFromSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegFrom.segFrom_ok

/-- `Otr`-to-`Key` segment (`+0x2c8..+0x344`, `+0xfac..+0xfc4`): `remote_identity_key` lookup
and `expect` check. -/
theorem segIdentity_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegIdentitySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegIdentity.segIdentity_okV

theorem segIdentity_ok : SegIdentitySpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegIdentity.segIdentity_ok

/-- `Key`-to-`Cm` segment when `pendingPreKey = none` (`+0x344..+0x41c`): `OTR::encrypt` and
`SignalMessage` staging. -/
theorem segSignal_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegSignal.segSignal_okV

theorem segSignal_ok : SegSignalSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegSignal.segSignal_ok

/-- `Key`-to-`Cm` segment when `pendingPreKey = some items` (`+0x344..+0x390`, `+0x680..+0xa70`):
unacknowledged session expiry check, optional Kyber clone, `OTR::encrypt`, and
`PreKeySignalMessage::new`. -/
theorem segPreKey_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegPreKeySpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegPreKey.segPreKey_ok_body

theorem segPreKey_ok : SegPreKeySpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegPreKey.segPreKey_ok_body

/-- `Cm`-to-`Save` segment (`+0xa70..+0xbd4`, `+0xc78..+0xd40`): `is_trusted_identity` check
and `UntrustedIdentity` error path. -/
theorem segTrust_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegTrustSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegTrust.segTrust_okV

theorem segTrust_ok : SegTrustSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  Pf.SegTrust.segTrust_ok

/-- `Save`-to-`Apply` segment (`+0xbd4..+0xc14`, `+0xd50..+0xd9c`): `save_identity` call and
dispatch. -/
theorem segSave_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegSaveSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegSave.segSave_okV

theorem segSave_ok : SegSaveSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact Pf.SegSave.segSave_ok

/-- `Apply`-to-`Stored` segment (`+0xd9c..+0xe88`, `+0xf2c..+0xf3c`):
`OTR::apply_to_session_state` and `store_session`. -/
theorem segApplyStore_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegApplyStoreSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegApplyStore.segApplyStore_okV

theorem segApplyStore_ok : SegApplyStoreSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact Pf.SegApplyStore.segApplyStore_ok

/-- `Stored`-to-exit segment (`+0xe88..+0xfac`, `+0x5f8..+0x660`): `SessionRecord` drop,
248-byte `sret` copy, and epilogue. -/
theorem segFinish_okV {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} :
    SegFinishSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs :=
  Pf.SegFinish.segFinish_okV

theorem segFinish_ok : SegFinishSpec Scope Q img C A ctl uuidTryParse S encRecord abs := by
  exact Pf.SegFinish.segFinish_ok

/-! ## Callees -/

/-- `SessionState::unacknowledged_pre_key_message_items` (`0x1245c`) satisfies `unackItemsSpec`. -/
theorem unackItems_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : UnackItemsOk img C A ctl abs := by
  exact Pf.UnackItems.unackItems_ok h3 himg

/-- Closure helper `kyberMap` (`0x34254`) satisfies `kyberMapSpec`. -/
theorem kyberMap_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : KyberMapOk img C A ctl abs := by
  exact Pf.KyberMap.kyberMap_ok h3 himg

/-- `PreKeySignalMessage::new` (`0x15130`) satisfies `preKeyMsgNewSpec`. -/
theorem preKeyMsgNew_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : PreKeyMsgNewOk img C A ctl abs :=
  PreKeySignalMessageNew.Compose.preKeyMsgNew_ok h3 himg

/-- Drop glue for `CiphertextMessage` (`0x353b0`) satisfies `cmDropSpec`. -/
theorem cmDrop_ok (h3 : PublicApiHooks C A S encRecord abs)
    (himg : Obj.Loads libsignalSessionImage img) : CmDropOk img C A ctl abs := by
  exact Pf.CmDrop.cmDrop_ok h3 himg

/-! ## Bridges -/

/-- Lifts `OtrEncryptRunStmt` to `MessageEncrypt.OtrEncryptOk`. -/
theorem otrEncryptOk_of_run (hrun : OtrEncryptRunStmt C A ctl S abs img)
    (h2 : TripleRatchetHooks C A S abs) (hsend : SpqrSendOk C A ctl S abs img)
    (himg : Obj.Loads libsignalSessionImage img) : MessageEncrypt.OtrEncryptOk img C A ctl uuidTryParse S abs := by
  have h := hrun h2 hsend himg
  unfold MessageEncrypt.OtrEncryptOk
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) himg] at h

theorem otrEncryptOkQ_of_ok (Q : List (BitVec 8) → Prop)
    (h : MessageEncrypt.OtrEncryptOk img C A ctl uuidTryParse S abs) : OtrEncryptOkQ Q img C A ctl uuidTryParse S abs := by
  unfold OtrEncryptOkQ otrEncryptSpecQ
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hal => ?_
  have hp' : s0.mem ⊨ (⌜Q x.ot.pqrState⌝ ∗ (otrEncryptSpec C A ctl uuidTryParse S img).pre x s0) ∗ R :=
    hp
  rw [sepConj_assoc] at hp'
  exact (h.to_outcome x R s0 hpc hrun ((satisfies_pure_sepConj _ _ _).1 hp').2 hal).mono_outcome
    fun _ hout => hout

/-- Lifts `OtrEncryptRunStmt` under `SpqrSendOk` to `OtrEncryptOkQ Q` for arbitrary `Q`. -/
theorem otrEncryptOkQ_of_run (Q : List (BitVec 8) → Prop)
    (hrun : OtrEncryptRunStmt C A ctl S abs img) (h2 : TripleRatchetHooks C A S abs)
    (hsend : SpqrSendOk C A ctl S abs img) (himg : Obj.Loads libsignalSessionImage img) :
    OtrEncryptOkQ Q img C A ctl uuidTryParse S abs :=
  otrEncryptOkQ_of_ok Q (otrEncryptOk_of_run hrun h2 hsend himg)

/-- Lifts `OtrEncryptEmptyRunStmt` under `S.SendEmptyOk` to `OtrEncryptOkQ (· = [])`. -/
theorem otrEncryptOkQ_of_emptyRun (hrun : OtrEncryptEmptyRunStmt C A ctl S abs img)
    (h2 : TripleRatchetHooks C A S abs) (hE : S.SendEmptyOk) (himg : Obj.Loads libsignalSessionImage img) :
    OtrEncryptOkQ (· = []) img C A ctl uuidTryParse S abs := by
  have h := hrun h2 hE himg
  unfold OtrEncryptOkQ otrEncryptSpecQ
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) himg] at h

/-- Lifts `OtrEncryptV1RunStmt` to `OtrEncryptOkQT` for concrete `spqrV1`. -/
theorem otrEncryptOkQT_of_v1Run {K : LibsignalSpqrV1.MlKem}
    (hrun : LibsignalSpqrV1.OtrEncryptV1RunStmt C A ctl K abs img)
    (h2 : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hspqr : LibsignalSpqrV1.SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    OtrEncryptOkQT img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs := by
  have h := hrun h2 hspqr himg
  unfold OtrEncryptOkQT OtrEncryptOkQF otrEncryptSpecQF LibsignalSpqrV1.otrEncryptSpecT at *
  rwa [tripleRatchetProg_eq_tripleRatchetProgAt himg, entryOf_eq_tripleRatchetProgAt (C := C) (ctl := ctl)
    (abs := abs) himg] at h

/-- Pure agreement between `StepsThroughEncrypt` on `okAnswers r c` and `messageEncrypt`. -/
theorem encModelOk : EncModelOkStmt C S uuidTryParse := by
  exact Pf.EncModel.encModelOk

/-- Assembles `EncCallees Q` from `PublicApiHooks` and `OtrEncryptOkQ Q`. -/
theorem encCallees_ok (h3 : PublicApiHooks C A S encRecord abs)
    (hEnc : OtrEncryptOkQ Q img C A ctl uuidTryParse S abs) (himg : Obj.Loads libsignalSessionImage img) :
    EncCallees Q img C A ctl uuidTryParse S abs := by
  exact Pf.EncModel.encCallees_of_calleeProofs h3 hEnc himg
    (unackItems_ok h3 himg) (kyberMap_ok h3 himg) (preKeyMsgNew_ok h3 himg) (cmDrop_ok h3 himg)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
