/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness

/-!
# Shared Seam Definitions for the `segPreKey` Tail (`+0x8b4` and `+0x8c8`)

Defines the intermediate states `PreKeyEncryptState'` (`+0x8b4`, after `kyberMap`) and
`PreKeyEncryptRetState` (`+0x8c8`, after `OTR::encrypt`) shared between `SegPreKeyTailEncrypt` and
`SegPreKeyTailBuildMessage`.
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

/-- Call scratch (`sp + 0x00 .. sp + 0x58`) at `+0x8b4`. -/
def preKeyEncryptScratch' (sp : BitVec 64) (regId spk pkVal : BitVec 32) : SepProp :=
  memRegion sp 0x14 ∗
  ((sp + 0x14#64) ↦₃₂ regId) ∗
  memRegion (sp + 0x18#64) 0xc ∗
  ((sp + 0x24#64) ↦₃₂ spk) ∗
  memRegion (sp + 0x28#64) 0xc ∗
  ((sp + 0x34#64) ↦₃₂ pkVal) ∗
  ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
  ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Poll and staging region (`sp + 0x46a .. sp + 0xb80`) at `+0x8b4`. -/
def pollE6c' (A : RustAlloc) (sp : BitVec 64) (kyBoxPtr : BitVec 64)
    (items : PendingPreKey) (kyber : Option PendingKyberPreKey) : SepProp :=
  memRegion (sp + 0x46a#64) 0x436 ∗
  optKyberAt A (sp + 0x8a0#64) kyBoxPtr
    (kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
  memRegion (sp + 0x8b8#64) 0x1fc ∗
  ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
  memRegion (sp + 0xad4#64) 0xac

/-- Seam state at `+0x8b4`, immediately after `kyberMap` returns. -/
def PreKeyEncryptState' {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  ∃ (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64),
    SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
    ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧
    expiry.lt x.now = false ∧
    optU32ValProp items.preKeyId pkVal ∧
    s.pc = encEntry img + 2228#64 ∧
    encMidMeta img x s0 s ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
    s.readReg64 .x20 = sp + 0x58#64 ∧
    s.readReg64 .x22 = sp + 0x8b8#64 ∧
    (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
    s.readReg64 .x25 = sp + 0x580#64 ∧
    s.readReg64 .x26 = sp + 0x9d0#64 ∧
    s.readReg64 .x27 = sp + 0xc0#64 ∧
    s.readReg64 .x28 = sp + 0x4a0#64 ∧
    x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
    x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      pollE6c' A sp kyBoxPtr items sess.pendingKyberPreKey ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

/-- Seam state at `+0x8c8`, immediately after `OTR::encrypt` returns. -/
def PreKeyEncryptRetState {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (items : PendingPreKey)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  let res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S parse
  ∃ (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal : BitVec 32) (kyBoxPtr pqCap' pqPtr' : BitVec 64),
    SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
    ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧
    expiry.lt x.now = false ∧
    optU32ValProp items.preKeyId pkVal ∧
    res.1 ≠ .error .panic ∧
    s.pc = encEntry img + 2248#64 ∧
    encMidMeta img x s0 s ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
    s.readReg64 .x20 = sp + 0x58#64 ∧
    s.readReg64 .x22 = sp + 0x8b8#64 ∧
    (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
    s.readReg64 .x25 = sp + 0x580#64 ∧
    s.readReg64 .x26 = sp + 0x9d0#64 ∧
    s.readReg64 .x28 = sp + 0x4a0#64 ∧
    x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
    x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
