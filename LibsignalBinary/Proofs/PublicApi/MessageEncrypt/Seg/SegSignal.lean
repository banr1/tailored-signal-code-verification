/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalOk
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEncCall
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalErr

/-!
# `MessageEncrypt` `SignalMessage` Segment (`segSignal_ok`)

Assembles `KeyStateV → CmStateV` when `sess.pendingPreKey = none` (`+0x344..+0x41c`): calls
`unacknowledged_pre_key_message_items` (tag `2`), invokes `OTR::encrypt` without a local identity
address, routes `Err p` to `tailSignalEncryptErr_ok`, and copies `Ok sm` to `sp + 0x370`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

theorem segSignal_segExit_trans {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

/-- Steps from `KeyStateV` (`+0x344`) through the items getter and `OTR::encrypt` to
`SegSignalRetStateV` (`+0x3a4`). -/
theorem segSignal_to_ret {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') :=
  segSignal_segExit_trans (segSignal_to_ack env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs)
    fun sm h => segSignal_segExit_trans (segSignal_ack_to_enc env x r sess otr taken pqCap pqPtr k R0 s0 sm h)
      fun sn h' => segSignal_enc_to_ret_pf env x r sess otr taken pqCap pqPtr k R0 s0 sn h'

/-- Error branch from `SegSignalRetStateV` (`+0x3a4..+0x3c8` to `+0xc14`), exiting via
`tailSignalEncryptErr_ok`. -/
theorem segSignal_err_path {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) :=
  segSignal_err_path_pf env x r sess otr taken k R0 s0 s p herr hs

/-- Full `segSignal` segment proof (`KeyStateV → CmStateV`, `pendingPreKey = none`),
parameterized by `SessionStoreSpec` and `IdentityStoreSpec`. -/
theorem segSignal_okV {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs
  refine segSignal_segExit_trans (segSignal_to_ret env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs) ?_
  intro sm hret
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact SegFrom.SegExit.of_false
      (segSignal_err_path env x r sess otr taken k R0 s0 sm p hres hret)
  · exact segSignal_ok_path env x r sess otr taken k R0 s0 sm m hres hret

theorem segSignal_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegSignalSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  segSignal_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
