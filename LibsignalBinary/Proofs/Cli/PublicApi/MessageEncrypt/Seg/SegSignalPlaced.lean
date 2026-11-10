/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalErrPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncCallPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `segSignal` Segment Assembly (`segSignal_placed_okV`)

Assembles `segSignal_placed_to_ack`, `segSignal_placed_ack_to_enc`,
`segSignal_placed_enc_to_ret_pf`, `segSignal_placed_err_path_pf`, and `segSignal_placed_ok_path`
into `segSignal_placed_okV` on Block `464` (`lsProg_464 Hk`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem segSignal_placed_segExit_trans [LibsignalPlacement]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s mid)
    (h2 : ∀ sm, mid sm → SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

/-- **Key → Ret** (`+0x344..+0x3a0`) under `[LibsignalPlacement]`: items getter (tag 2), set-up,
`OTR::encrypt` call. -/
theorem segSignal_placed_to_ret [LibsignalPlacement]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0
        s') :=
  segSignal_placed_segExit_trans (segSignal_placed_to_ack env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs)
    fun sm h => segSignal_placed_segExit_trans
      (segSignal_placed_ack_to_enc env x r sess otr taken pqCap pqPtr k R0 s0 sm h)
      fun sn h' => segSignal_placed_enc_to_ret_pf env x r sess otr taken pqCap pqPtr k R0 s0 sn h'

/-- **The `Err` path** (`+0x3a4..+0x3c8 b.eq` → T5 `+0xc14` → T1) under `[LibsignalPlacement]`:
`Err(protocol p)`. -/
theorem segSignal_placed_err_path [LibsignalPlacement]
    {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateVPlaced kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s (fun _ => False) :=
  segSignal_placed_err_path_pf env x r sess otr taken k R0 s0 s p herr hs

/-- **segSignal** (Key → Cm, `pendingPreKey = none`) under `[LibsignalPlacement]`, parameterized by
session-store kit `kit`, `st0`, `ikit`, and `ist0`. -/
theorem segSignal_placed_okV [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegSignalSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk := by
  intro env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs
  refine segSignal_placed_segExit_trans
    (segSignal_placed_to_ret env x r sess otr taken pqCap pqPtr k R0 s0 s hpk hs) ?_
  intro sm hret
  rcases hres : (segSignalRes C S x otr).1 with p | m
  · exact SegExitPlaced.of_false
      (segSignal_placed_err_path env x r sess otr taken k R0 s0 sm p hres hret)
  · exact segSignal_placed_ok_path env x r sess otr taken k R0 s0 sm m hres hret

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
