/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CommonPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CmDropPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncryptPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrSignalEncryptPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrStoreHookPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErrPlaced
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResultPlaced

/-!
# Relocatable (`[LibsignalPlacement]`) Shared Error and Result Tails

Exports `EncTailVPlaced` and the nine relocatable error/result tail theorems for
`session_message_encrypt_with_stores` on Block `198` (`lsProg_198 Hk`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

open Arm64 ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt

/-- Relocatable tail entry state on Block `198` (`lsProg_198 Hk`) under `[LibsignalPlacement]`. -/
abbrev EncTailVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState) :=
  Pf.TailCommon.EncTailVPlaced kit st0 ikit ist0

/-- Relocatable T2 writer + T3 (`+0x5f8..+0x660`). -/
theorem tailWriteResult_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  Pf.TailWriteResult.tailWriteResult_placed_ok env x R s0 s answers res w0 w1 w2 w3 bs H hm hst hs

/-- Relocatable T2 `Err` + writer + T3 (`+0x5b4..+0x660`). -/
theorem tailWriteErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x5b4#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  Pf.TailWriteErr.tailWriteErr_placed_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H hm hst hs

/-- Relocatable T1 from `+0x564` + T2 + T3 (`+0x564..+0x660`). -/
theorem tailFreePrevSessions_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  Pf.TailFreePrevSessions.tailFreePrevSessions_placed_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm hst hs

/-- Relocatable T1 from-error + T2 + T3 (`+0x49c..+0x660`). -/
theorem tailFromSessionStateErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  Pf.TailFromSessionStateErr.tailFromSessionStateErr_placed_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hst hs

/-- Relocatable T1 + T2 + T3 (`+0x46c..+0x660`). -/
theorem tailDropRecord_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0x46c#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  Pf.TailDropRecord.tailDropRecord_placed_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm hst hs

/-- Relocatable T5 signal (`+0xc14..+0xc20`, `+0xc6c..+0xc78`) + T1 + T2 + T3. -/
theorem tailSignalEncryptErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xc14#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0xb00 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  ProtocolErr.tailSignalEncryptErrPlaced hm hs fun s' hm' hs' =>
    tailDropRecord_placed_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- Relocatable T5 Kyber (`+0xc38..+0xc64`) + T1 + T2 + T3. -/
theorem tailPreKeyEncryptErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (kyPtr : BitVec 64) (kp : Option KyberPayload)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  ProtocolErr.tailPreKeyEncryptErrPlaced env.hooks.dealloc hm hs fun s' hm' hs' =>
    tailDropRecord_placed_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- Relocatable CM drop (`+0xd40..+0xd50`) + T1 + T2 + T3. -/
theorem tailCmDrop_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (m : CiphertextMessage)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  ProtocolErr.tailCmDropPlaced env.callees.cmDrop hm hs fun s' hm' hs' =>
    tailDropRecord_placed_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- Relocatable T5 store (`+0xc20..+0xc38`, stubs `+0xe28`/`+0xf2c`) + CM drop + T1 + T2 + T3. -/
theorem tailStoreHookErr_placed_ok [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (m : CiphertextMessage) (pcOff src : Nat)
    (hpc : (pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
      (pcOff, src) = (0xf2c, 0x9b0))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced kit st0 ikit ist0 C ctl uuidTryParse S x answers
      (encEntryPlaced + BitVec.ofNat 64 pcOff) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp src [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False) :=
  ProtocolErr.tailStoreHookErrPlaced hpc hm hs fun s' hm' hs' =>
    tailCmDrop_placed_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot m hm' hst hs'

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
