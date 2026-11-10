/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt

/-!
# `segPreKey` Encryption and `PreKeySignalMessage` Tail (`+0x8b4..+0xa70`)

Composes the `OTR::encrypt` call and error branch (`SegPreKeyTailEncrypt`) with the
`PreKeySignalMessage::new` call and 248-byte result copy (`SegPreKeyTailBuildMessage`) to reach
`CmState` at `+0xa70` from `PreKeyEncryptState` (`+0x8b4`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

abbrev preKeyEncryptScratch := preKeyEncryptScratch'
abbrev pollPreKeyEncrypt := pollE6c'
abbrev PreKeyEncryptState {A : RustAlloc} {img : Obj.Image} := @PreKeyEncryptState' A img

/-- From `PreKeyEncryptState` at `+0x8b4`, runs `OTR::encrypt` (exiting via
`tailPreKeyEncryptErr_ok` on `Err`), builds the `PreKeySignalMessage`, copies it to `sp + 0x370`,
and reaches `CmState` at `+0xa70`. -/
theorem segPreKey_tail_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  refine segExit_trans
    (segPreKey_encrypt_call_ok env x r sess otr taken pqCap pqPtr k items R s0 s
      hcur hscope hfrom hrem hpk hst)
    fun s2 hret => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact segExit_of_false
      (segPreKey_encrypt_err_ok env x r sess otr taken pqCap pqPtr k items e R s0 s2
        hcur hscope hfrom hrem hpk hres hret)
  · exact segPreKey_buildMessage_ok env x r sess otr taken pqCap pqPtr k items sm R s0 s2
      hcur hscope hfrom hrem hpk hres hret

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

