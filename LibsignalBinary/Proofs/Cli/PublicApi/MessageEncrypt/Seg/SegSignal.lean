/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalOk
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncCall
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalErr

/-!
# `segSignal` Non-PreKey Encryption Segment (`+0x344..+0x418`)

Assembles the unacknowledged-items check (`pendingPreKey = none`), `OTR::encrypt` call, protocol
error branch (`+0xc14`), and 120-byte `SignalMessage` copy into `segSignal_okV` and `segSignal_ok`
(plus trap-mode variants).
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

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

/-- **Key → Ret** (`+0x344..+0x3a0`): items getter (tag 2), set-up, `OTR::encrypt` call. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ret_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ack_trap env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs)
    fun sm h => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ack_to_enc_trap env x r sess otr taken pqCap pqPtr k R0 s0 sm h)
      fun sn h' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_to_ret_pf_trap env x r sess otr taken pqCap pqPtr k R0 s0 sn h'

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ret {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ack env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs)
    fun sm h => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ack_to_enc env x r sess otr taken pqCap pqPtr k R0 s0 sm h)
      fun sn h' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_enc_to_ret_pf env x r sess otr taken pqCap pqPtr k R0 s0 sn h'

/-- **The `Err` path** (`+0x3a4..+0x3c8 b.eq` → T5 `+0xc14` → T1): `Err(protocol p)`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path_pf_trap env x r sess otr taken k R0 s0 s p herr hs

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path_pf env x r sess otr taken k R0 s0 s p herr hs

/-- **segSignal** (Key → Cm, `pendingPreKey = none`, parameterized by session-store kit `kit`, `st0`,
`ikit`, and `ist0`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans_trap (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ret_trap env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs) ?_
  intro sm hret
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false_trap
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path_trap env x r sess otr taken k R0 s0 sm p hres hret)
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_path_trap env x r sess otr taken k R0 s0 sm m hres hret

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs := by
  intro env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_segExit_trans (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_to_ret env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs) ?_
  intro sm hret
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_false
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_err_path env x r sess otr taken k R0 s0 sm p hres hret)
  · exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_path env x r sess otr taken k R0 s0 sm m hres hret

/-- **segSignal** (Key → Cm, `pendingPreKey = none`, `E₀` store). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec_trap Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV_trap

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec Scope Q img C A ctl uuidTryParse S encRecord abs :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_okV

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
