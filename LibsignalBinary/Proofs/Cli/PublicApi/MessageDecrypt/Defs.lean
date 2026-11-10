/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.Defs

/-!
# CLI `MessageDecrypt` Seam States and Segment Specifications

Defines seam program counters, intermediate states, and the twelve segment specifications for
`signal_session_ratchet::decrypt_signal` on the CLI image, together with `_trap` hypotheses at
`trTrapProgAt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib CryptoVerification.RustHeap CryptoGames.LibsignalSession

open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoGames CryptoGames.LibsignalSessionApi

open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Seam program counters -/

/-- Entry PC `+0x0` of `libsignal_cli_ratchet::decrypt_signal`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName

/-- Seam PC `+0x8c` immediately after the `load_session` poll returns. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.loadPolledPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x8c#64

/-- Seam PC `+0x1fcc` when `remote_identity_key` returns `Some`, before copying the key and calling the trust shim. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.keyReadyPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fcc#64

/-- Seam PC `+0x2150` at the `save_identity` shim call when `is_trusted_identity` returns `Ok(true)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.saveCallPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2150#64

/-- Seam PC `+0x21b0` on the untrusted-identity branch when `is_trusted_identity` returns `Ok(false)`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.untrustedPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x21b0#64

/-- Trust-branch target PC (`+0x2150` if `t = true`, `+0x21b0` if `t = false`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.trustedPC (img : Obj.Image) (t : Bool) : BitVec 64 :=
  if t then CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.saveCallPC img else CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.untrustedPC img

/-- Seam PC `+0x2388` at the `store_session` shim call. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.storeCallPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2388#64

/-- Error-join PC: `+0x2294` when the plaintext `Vec` is still owned (`pt = true`), or `+0x22a8` otherwise. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.errJoinPC (img : Obj.Image) (pt : Bool) : BitVec 64 :=
  if pt then entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2294#64 else entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x22a8#64

/-- Seam PC `+0x24d4` at the final 48-byte result write to `[x27]`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.resultFinalPC (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x24d4#64

/-! ## Seam states and segment specifications -/

set_option linter.unusedVariables false in
/-- Seam state at `+0x8c` after the `load_session` shim and poll return. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.loadPolledPC img ∧ wsMeta img x s0 s ∧ wsStack ≤ s0.sp.toNat ∧
  s.readReg64 .x19 = sp + 0x5f0#64 ∧
  kit.loadRel st0 x.rem.val ans.loadSession ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
  (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
    (∃∗ box : BitVec 64, ⌜box ≠ 0#64⌝ ∗ ((sp + 0x2d0#64) ↦₆₄ box) ∗
      ((sp + 0x2d8#64) ↦₆₄ (img.base + kit.loadFutVtOff)) ∗
      A.live box kit.loadBoxSize 8 ∗
      kit.loadBoxAt box (s0.readReg64 .x3) x.remA 1#8) ∗
    loadPollOutAtS Scope A img.base (sp + 0x5f0#64) ans.loadSession ∗
    memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗ memRegion (sp + 0x4b0#64) 0x140 ∗
    memRegion (sp + 0x760#64) 0x6a0 ∗ memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
    decStoreExtra kit ikit st0 ist0 s0 ∗ R)

/-- Seam state at `+0x1a8` entering the record-decrypt region with `currentSession = some _`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img ∧ wsMeta img x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).pre (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

set_option linter.unusedVariables false in
/-- Precondition at `+0x1a8` when `currentSession = none` (`[sp + 0x138] = noneCap`, 336 uninitialized
session bytes). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.regionNonePre (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : DecryptGhost)
    (prevPtr : BitVec 64) (s : State) : SepProp :=
  ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab ∧ s.spAligned = true ∧ s.readReg64 .x27 = x.ret ∧
    s.readReg64 .x19 = x.remA ∧ s.readReg64 .x23 = s.sp + 0x5f0#64 ∧
    s.readReg64 .x24 = s.sp + 0xca0#64 ∧ rootStack ≤ s.sp.toNat⌝ ∗
  memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (s.sp + 0x140#64) 336 ∗
  memRegion (s.sp + 0x4b0#64) 0x950 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
  stackAt s.sp rootStack ∗ A.pool

/-- Seam state at `+0x1a8` when `load_session` returned `Ok(Some r)` with `r.currentSession = none`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img ∧ wsMeta img x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.regionNonePre A ctl img x prevPtr s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

/-- Seam state at `+0x1f50` exiting the record-decrypt region from `RegionSomeStateV`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img ∧ wsMeta img x s0 s ∧
  ∃ (s1 : State) (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevCap prevPtr : BitVec 64),
    s1.sp = s0.sp - 0xee0#64 ∧
    s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    (s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl parse S img).post (recGhostOf x prevPtr G ses.state) s1 s ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `+0x1f50` exiting the `currentSession = none` path from `RegionNoneStateV`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateV {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img ∧ wsMeta img x s0 s ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 = recordResultTag (.error (.invalidMessage .whisper .decryptionFailed)) ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
      recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
      memRegion (sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
      stackAt sp rootStack ∗ A.pool ∗
      wsRegionFrameV img kit ikit x s0 prevCap prevPtr ∗ decStoreExtra kit ikit st0 ist0 s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `+0x1fcc` with the remote identity key extracted for trust verification. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.keyReadyPC img ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0 ist0 s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `trustedPC img t` after `is_trusted_identity` returns `Ok(t)`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.trustedPC img t ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x19 = sp + 0x2a8#64 ∧ s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok t ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity) ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0 (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity) s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `+0x2388` after `save_identity` succeeds, ready to store the updated session. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.storeCallPC img ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey) (c : IdentityChange),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok true ∧
    ans.saveIdentity = .ok c ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
      x.rem.val k ans.saveIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity ++
      ikit.saveEvs x.rem.val k ans.saveIdentity) ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit st0
        (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
          x.rem.val k ans.saveIdentity) s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `errJoinPC img pt` on a non-panic protocol or store error. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.errJoinPC img pt ∧ wsMeta img x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 ≠ pendingTag ∧
  ∃ (ans : StoreAnswers (List (BitVec 8)) Unit) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))),
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ p, (x.model C S parse ans).1 ≠ .ok p) ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗
      (if pt then ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p
       else memRegion (sp + 0x290#64) 24) ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x580#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

set_option linter.unusedVariables false in
/-- Seam state at `+0x24d4` ready to write the 48-byte `Result` to `[x27]`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV (C : Crypto) {A : RustAlloc} (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.resultFinalPC img ∧ wsMeta img x s0 s ∧
  ∃ ans : StoreAnswers (List (BitVec 8)) Unit,
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x300#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C ans) ∗
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

set_option linter.unusedVariables false in
/-- Specification of `signal_session_ratchet::decrypt_signal` parameterized by `SessionStoreSpec`,
`IdentityStoreSpec`, initial states `st0` / `ist0`, and `Scope`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
            kit.callsRel st0 answers (x.model C S parse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2⌝ ∗
          kit.storeAt (s0.readReg64 .x3)
            (kit.storeFinal st0 answers (x.model C S parse answers).2) ∗
          ikit.identityAt (s0.readReg64 .x5)
            (ikit.idFinal ist0 answers (x.model C S parse answers).2) ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws C answers) ∗
          logOff img ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
        anyHeap }
    img

/-- Extracts `kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val` from `withStoresDecSpecV.pre`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV_pre_addrOk {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {img : Obj.Image} {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact hpre.2.1.2.2.2.2.2.2.2

/-- Common step relation from an entry seam state to an exit seam or subroutine outcome. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
  ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
    (Out s' ∨
      SubroutineOutcome (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope)
        x R s0 s')

/-- Segment `SegLoad` (`+0x0 → +0x8c`): prologue and `load_session` shim/poll. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 : State),
    DecFsCtx kit ikit C ctl abs s0 s0 →
    s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗ R) →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s0
      (fun s' => ∃ ans, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegDispatch` (`+0x8c → +0x1a8 / +0x24d4`): unpacks the `load_session` result. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegRegionSome` (`+0x1a8 → +0x1f50`): crosses the record-decrypt region under any
predicate `Q` satisfied by scoped post-quantum states (`ScopePq`). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionSomeSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (tripleRatchetProgAt img.base C ctl abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

/-- Segment `SegRegionNone` (`+0x1a8 → +0x1f50`): handles `r.currentSession = none`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegPostSome` (`+0x1f50 → +0x1fcc / +0x22a8`): post-decrypt dispatch and remote key lookup. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegPostNone` (`+0x1f50 → +0x22a8`): post-region error routing when `currentSession = none`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegTrust` (`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`): `is_trusted_identity` shim and poll. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans' t, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' t R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegUntrusted` (`+0x21b0 → +0x2294`): constructs `UntrustedIdentity` when `is_trusted_identity` returns `false`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans false R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegSave` (`+0x2150 → +0x2388 / +0x2294`): `save_identity` shim and poll. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans true R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans', CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegStore` (`+0x2388 → +0x24d4 / +0x2294`): `store_session` shim and poll. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    DecFsCtx kit ikit C ctl abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegErrTeardown` (`+0x2294 / +0x22a8 → +0x24d4`): drops owned buffers on error paths. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs →
  ∀ (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-- Segment `SegWrite` (`+0x24d4 → +0x2510`): writes the 48-byte return value and epilogue. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpecV (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsV img C A ctl parse S encRecord abs kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s (fun _ => False)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpec (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpecV img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

/-! ## Trap-program hook and hypothesis bundles (`trTrapProgAt`) -/

/-- Decrypt hook bundle (`TripleRatchetHooks` plus `stringClone`) at `ext`. -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap
    (C : Crypto) (A : RustAlloc) (S : SpqrModel)
    (ext : String → Option (State → State)) : Prop extends TripleRatchetHooks C A S ext where
  stringClone : HookSat ext stringCloneHookName (stringCloneSpec A)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_tripleRatchetHooks_trap
    {C : Crypto} {A : RustAlloc} {S : SpqrModel} {abs : String → Option (State → State)}
    (hH : TripleRatchetHooks C A S abs)
    (hSC : HookSat abs stringCloneHookName (stringCloneSpec A)) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap C A S (trTrapExterns C abs) where
  alloc :=
    { alloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.alloc
      dealloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.dealloc
      realloc := hookSat_trTrapExterns (by decide) (by decide) hH.alloc.realloc }
  allocZeroed := hookSat_trTrapExterns (by decide) (by decide) hH.allocZeroed
  aesEnc := hookSat_trTrapExterns (by decide) (by decide) hH.aesEnc
  aesDec := hookSat_trTrapExterns (by decide) (by decide) hH.aesDec
  formatInner := hookSat_trTrapExterns (by decide) (by decide) hH.formatInner
  fmtWrite := hookSat_trTrapExterns (by decide) (by decide) hH.fmtWrite
  stringClone := hookSat_trTrapExterns (by decide) (by decide) hSC

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_noStores_trap
    {C : Crypto} {A : RustAlloc} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : StoreKit.Identity.PublicApiHooksNoStores C A S abs) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap C A S (trTrapExterns C abs) :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap.of_tripleRatchetHooks_trap
    h.toTripleRatchetHooks h.stringClone

/-- Hypothesis bundle for `MessageDecrypt` segments on `trTrapProgAt img.base C abs`. -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (ss : SessionStoreSpec A img.base)
    (id : IdentityStoreSpec A img.base)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.CliDecHooks_trap C A S (trTrapExterns C abs)
  kit : SessionOnlyKitOkSE ss Scope encRecord (trTrapExterns C abs)
  ikit : StoreKit.Identity.IdentityStoreKitOkIE img id (trTrapExterns C abs)
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHyps_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs
    (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () RecordInScope

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecFsCtx_trap
    {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (C : Crypto) (abs : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (trTrapProgAt img.base C abs) s0 s

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (trTrapProgAt img.base C abs).CodeLoaded s.mem →
  ∃ s', Steps (trTrapProgAt img.base C abs) s s' ∧
    (Out s' ∨
      SubroutineOutcome (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope)
        x R s0 s')

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_of_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (hOut : ∀ s', Out s' → s'.status = .Running)
    (h : CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s Out := by
  intro hL
  obtain ⟨s', hsteps, hout⟩ := h ((trTrapProgAt_codeLoaded_iff img.base C ctl abs s.mem).mpr hL)
  rcases hout with hO | hSub
  · exact ⟨s', ProofLib.Variant.Steps.of_trapsOnly (trapsOnly_trTrap_kit img.base C ctl abs) hsteps
      (.of_running (hOut s' hO)), Or.inl hO⟩
  · exact ⟨s', ProofLib.Variant.Steps.of_trapsOnly (trapsOnly_trTrap_kit img.base C ctl abs) hsteps
      (ProofLib.Variant.SubroutineOutcome.outcomeStatus hSub), Or.inr hSub⟩

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecFsCtx_trap kit ikit C abs s0 s0 →
    s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.wsEntryPC img → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.withStoresDecSpecV C A ctl parse S encRecord img kit ikit st0 ist0 Scope).pre x s0 ∗ R) →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s0
      (fun s' => ∃ ans, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegLoadSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.LoadPolledStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegDispatchSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionSomeSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (trTrapProgAt img.base C abs) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img) (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img)
    ((CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpec C A ctl uuidTryParse S img).withVRegs.restrictPre (Q ·.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionSomeSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionSomeSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.RegionNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegRegionNoneSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr Getters.remoteIdentityKeyName)
    (Getters.remoteIdentityKeySpec A img) →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostSomeStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostSomeSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.PostNoneStateV ctl encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x false R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegPostNoneSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecFsCtx_trap kit ikit C abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.KeyReadyStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans' t, CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' t R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegTrustSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans false R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegUntrustedSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecFsCtx_trap kit ikit C abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.TrustedStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans true R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans', CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegSaveSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A (trTrapExterns C abs) →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecFsCtx_trap kit ikit C abs s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.StoreCallStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x ans R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s' ∨
        CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x true R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegStoreSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt img.base A (trTrapExterns C abs) →
  ∀ (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ErrJoinStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x pt R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegErrTeardownSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpecV_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecHypsV_trap img C A parse S encRecord abs kit ikit st0 Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 s : State),
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.ResultFinalStateV C ctl parse S encRecord img kit ikit st0 ist0 Scope x R s0 s →
    CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.DecSegV_trap img C A ctl parse S encRecord abs kit ikit st0 ist0 Scope x R s0 s (fun _ => False)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpec_trap
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.SegWriteSpecV_trap img C A ctl parse S encRecord abs (hookSessionStoreSpec A img.base) (hookIdentityStoreSpec A img.base) () () RecordInScope

end CryptoVerification.LibsignalPublicApi.MessageDecrypt
