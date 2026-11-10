/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt

/-!
# `segPreKey` Tail Composition (`+0x8b4..+0xa70`)

Combines `segPreKey_encrypt_call_ok`, `segPreKey_encrypt_err_ok`, and `segPreKey_buildMessage_ok`
into `segPreKey_tail_ok` (and `segPreKey_tail_ok_trap`).
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

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState {A : RustAlloc} {img : Obj.Image} := @CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState' A img

/-- **E6c–E6e tail (`+0x8b4..+0xa70`):** from `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState` at `+0x8b4`, calls `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptSpecQ` at
`+0x8c4` (exiting via `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.tailPreKeyEncryptErr_ok` at `+0xc38` on `Err`), calls `preKeyMsgNewSpec` at `+0x98c`,
copies the `PreKeySignalMessage` into `sp + 0x370`, and reaches `CmState` at `+0xa70`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_tail_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans_trap
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_encrypt_call_ok_trap env x r sess otr taken pqCap pqPtr k items R s0 s
      hcur hscope hfrom hrem hpk hst)
    fun s2 hret => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false_trap
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_encrypt_err_ok_trap env x r sess otr taken pqCap pqPtr k items e R s0 s2
        hcur hscope hfrom hrem hpk hres hret)
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_buildMessage_ok_trap env x r sess otr taken pqCap pqPtr k items sm R s0 s2
      hcur hscope hfrom hrem hpk hres hret

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_tail_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.PreKeyEncryptState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_trans
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_encrypt_call_ok env x r sess otr taken pqCap pqPtr k items R s0 s
      hcur hscope hfrom hrem hpk hst)
    fun s2 hret => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_false
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_encrypt_err_ok env x r sess otr taken pqCap pqPtr k items e R s0 s2
        hcur hscope hfrom hrem hpk hres hret)
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_buildMessage_ok env x r sess otr taken pqCap pqPtr k items sm R s0 s2
      hcur hscope hfrom hrem hpk hres hret

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
