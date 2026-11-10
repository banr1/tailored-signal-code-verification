/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts

/-!
# Pure Model Unfolding and Callee Bundle Construction for `MessageEncrypt`

Proves `encModelOk` (`EncModelOkStmt`), relating `StepsThroughEncrypt` and `okAnswers r c` to the
pure `messageEncrypt` output, RNG draw count, and updated session state, and assembles `EncCallees`
from the individual callee proofs (`encCallees_of_calleeProofs`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.EncModel

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

theorem encModelOk {C : Crypto} {S : SpqrModel} :
    EncModelOkStmt C S uuidTryParse := by
  rintro x r sess otr taken k m otr' c ⟨hcur, -, hfrom, hrem, hstep5⟩
  unfold EncEncryptStep at hstep5
  cases hp : sess.pendingPreKey with
  | none =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨sm, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp]⟩
  | some items =>
    rw [hp] at hstep5
    rcases hstep5 with ⟨ts, expiry, sm, hts, hexp, hlt, henc, rfl⟩
    exact ⟨by simp [EncryptGhost.model, messageEncrypt_eq_flat, encryptFlat, wrapFlat, okAnswers,
        storedRecord, hcur, hfrom, hrem, hp, hts, hexp, hlt, henc],
      by simp [EncryptGhost.draws, EncryptGhost.sendState, loadedSession, okAnswers, hcur, hfrom,
        hrem, hp, hts, hexp, hlt, Option.bind]⟩

theorem encCallees_of_calleeProofs_noSessionStore {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {abs : String → Option (State → State)}
    (h3 : PublicApiHooksNoSessionStore C A S abs)
    (hEnc : OtrEncryptOkQ Q img C A ctl uuidTryParse S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hUnack : UnackItemsOk img C A ctl abs)
    (hKyber : KyberMapOk img C A ctl abs)
    (hPsm : PreKeyMsgNewOk img C A ctl abs)
    (hCmDrop : CmDropOk img C A ctl abs) :
    EncCallees Q img C A ctl uuidTryParse S abs where
  otrFrom := OutgoingRatchet.otrFrom_ok himg h3.alloc (Glue.deserializeOk img.base C ctl abs)
    (Glue.remoteIdentityKeyOk img C A ctl abs himg)
    (Glue.dropSpeOk_of_tripleRatchetHooks himg h3.toTripleRatchetHooks)
  otrApply := OutgoingRatchet.otrApply_ok img C A S ctl abs h3.toTripleRatchetHooks
  remoteIk := Glue.remoteIdentityKeyOk img C A ctl abs himg
  otrEnc := hEnc
  unack := hUnack
  kyber := hKyber
  psmNew := hPsm
  cmDrop := hCmDrop
  dropSs := FromRecordCallees.drop_session_structure_local2_ok h3.alloc (Glue.drop_chain_ok_of_tripleRatchetHooks h3.toTripleRatchetHooks)

theorem encCallees_of_calleeProofs {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (h3 : PublicApiHooks C A S encRecord abs)
    (hEnc : OtrEncryptOkQ Q img C A ctl uuidTryParse S abs)
    (himg : Obj.Loads libsignalSessionImage img)
    (hUnack : UnackItemsOk img C A ctl abs)
    (hKyber : KyberMapOk img C A ctl abs)
    (hPsm : PreKeyMsgNewOk img C A ctl abs)
    (hCmDrop : CmDropOk img C A ctl abs) :
    EncCallees Q img C A ctl uuidTryParse S abs :=
  encCallees_of_calleeProofs_noSessionStore (PublicApiHooks.toNoSessionStore h3) hEnc himg hUnack hKyber hPsm hCmDrop

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.EncModel
