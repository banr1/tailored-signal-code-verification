/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams

/-!
# Segment Specifications for `session_message_encrypt_with_stores`

Defines the nine seam-to-seam segment propositions (`SegLoadSpecV` through `SegFinishSpecV`), the
shared environment `EncEnv` parameterized by record scope `Scope` and SPQR invariant `Q`, and the
public-entry wrapper statement `EntryWrapStmt`.

| Specification | Transition | Offset range |
| --- | --- | --- |
| `SegLoadSpecV` | Entry → `Cur` | `+0x000..+0x20c`, `+0x41c..+0x45c`, `+0x660..+0x680` |
| `SegFromSpecV` | `Cur` → `Otr` | `+0x20c..+0x2c8` |
| `SegIdentitySpecV` | `Otr` → `Key` | `+0x2c8..+0x344` |
| `SegSignalSpecV` | `Key` → `Cm` (`pendingPreKey = none`) | `+0x344..+0x41c`, `+0xa70` |
| `SegPreKeySpecV` | `Key` → `Cm` (`pendingPreKey = some _`) | `+0x344..+0x390`, `+0x680..+0xa70` |
| `SegTrustSpecV` | `Cm` → `Save` | `+0xa70..+0xab0`, `+0xb7c..+0xbd4`, `+0xc78..+0xd50` |
| `SegSaveSpecV` | `Save` → `Apply` | `+0xbd4..+0xc14`, `+0xd50..+0xd9c` |
| `SegApplyStoreSpecV` | `Apply` → `Stored` | `+0xd9c..+0xe88`, `+0xf2c..+0xf3c` |
| `SegFinishSpecV` | `Stored` → outcome | `+0xe88..+0xf2c`, `+0xf3c..+0xfac`, `+0x5f8..+0x660` |
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (SessionOnlyKitOkS SessionOnlyVtablesOk)

/-- Encryption-side projection of `RecordInScope`, omitting the decrypt-only
`remoteIdentity ≠ some localIdentity` condition while preserving conjunct positions. -/
def RecordInScopeEnc (r : SessionRecord (List (BitVec 8))) : Prop :=
  ∀ s, r.currentSession = some s →
    True ∧ SeedsLen32 s.state ∧
      s.state.receiverChains.length < 2 ^ 32 ∧
      ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length < 2 ^ 32

theorem _root_.CryptoVerification.LibsignalPublicApi.RecordInScope.toEnc
    {r : SessionRecord (List (BitVec 8))} (h : RecordInScope r) :
    RecordInScopeEnc r :=
  fun s hs => ⟨trivial, (h s hs).2⟩

instance (r : SessionRecord (List (BitVec 8))) : Coe (RecordInScope r) (RecordInScopeEnc r) :=
  ⟨RecordInScope.toEnc⟩

/-- Shared segment environment bundling the loaded image, external hooks, store kit contracts
(`StoreKitOkS`), callee contracts (`EncCallees Q`), and scope bridges (`scopeIn`, `scopeQ`). -/
structure EncEnv {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : PublicApiHooksNoStores C A S abs
  kitOk : SessionOnlyKitOkS kit Scope C encRecord ctl abs
  ikitOk : IdentityStoreKitOkI img ikit C ctl abs
  callees : EncCallees Q img C A ctl parse S abs
  vtables : SessionOnlyVtablesOk img kit
  idVtables : IdentityVtablesOk img ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → Q s.state.pqRatchetState
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

/-- Deduces `Q otr.pqrState` from `Scope r` and `OutgoingTripleRatchet.fromSessionState`
success. -/
theorem EncEnv.q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- Segment-exit relation: execution from `s` reaches either a state satisfying `next` or an
outcome of `withStoresEncSpecV` from `s0`. -/
def SegExit {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
    ∃ sf, Steps (tripleRatchetProgAt img.base C ctl abs) s sf ∧
      (next sf ∨ SubroutineOutcome (withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord) x R s0 sf)

/-- Filesystem trace-quietness invariant carried from entry `s0` to `s` for both store kits. -/
abbrev EncFsCtx {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (C : Crypto) (ctl : BitVec 64) (abs : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (tripleRatchetProgAt img.base C ctl abs) s0 s

/-- `segLoad` (Entry → `Cur`): prologue, `load_session` shim/poll/drop/free, and result
dispatch. -/
def SegLoadSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (R : SepProp) (s0 : State),
      EncFsCtx kit ikit C ctl abs s0 s0 →
      s0.pc = encEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).pre x s0 ∗ R) →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s0
        (fun s => ∃ r g sess, CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s)

abbrev SegLoadSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegLoadSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segFrom` (`Cur` → `Otr`): `OTR::from_session_state` call and 200-byte OTR stack copy. -/
def SegFromSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
      (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ otr taken pqCap pqPtr,
          OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s')

abbrev SegFromSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegFromSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segIdentity` (`Otr` → `Key`): `remote_identity_key` lookup and `expect` unwrap. -/
def SegIdentitySpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ k,
          KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s')

abbrev SegIdentitySpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegIdentitySpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segSignal` (`Key` → `Cm`, `pendingPreKey = none`): pre-key items check and `OTR::encrypt`
producing a `SignalMessage`. -/
def SegSignalSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev SegSignalSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegSignalSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segPreKey` (`Key` → `Cm`, `pendingPreKey = some items`): expiry check, optional Kyber
clone, `OTR::encrypt`, and `PreKeySignalMessage::new`. -/
def SegPreKeySpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev SegPreKeySpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegPreKeySpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segTrust` (`Cm` → `Save`): `is_trusted_identity` shim/poll/drop/free and
`UntrustedIdentity` error path. -/
def SegTrustSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k
          m otr' pqCap' pqPtr' R s0 s')

abbrev SegTrustSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegTrustSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segSave` (`Save` → `Apply`): `save_identity` shim/poll/drop/free and dispatch. -/
def SegSaveSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ c, ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr
          taken k m otr' pqCap' pqPtr' c R s0 s')

abbrev SegSaveSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegSaveSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segApplyStore` (`Apply` → `Stored`): `OTR::apply_to_session_state` and
`store_session` shim/poll/drop/free. -/
def SegApplyStoreSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
        pqCap' pqPtr' c R s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken
          k m otr' c R s0 s')

abbrev SegApplyStoreSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegApplyStoreSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- `segFinish` (`Stored` → outcome): `SessionRecord` drop, 248-byte `sret` copy, and
epilogue. -/
def SegFinishSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' c R
        s0 s →
      SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s (fun _ => False)

abbrev SegFinishSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  SegFinishSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

theorem StepsThroughEncrypt.inScope {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto}
    {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (hin : ∀ r, Scope r → RecordInScopeEnc r)
    (h : StepsThroughEncrypt Scope C S uuidTryParse x r sess otr taken k m otr') :
    StepsThroughEncrypt RecordInScopeEnc C S uuidTryParse x r sess otr taken k m otr' :=
  ⟨h.1, hin r h.2.1, h.2.2⟩

/-- Pure postcondition agreement for the success path: given `StepsThroughEncrypt` and
`okAnswers r c`, `messageEncrypt` returns `Ok m` with RNG draw count `S.draws`. -/
def EncModelOkStmt (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) : Prop :=
  ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange),
    StepsThroughEncrypt RecordInScopeEnc C S uuidParse x r sess otr taken k m otr' →
    x.model C S uuidParse (okAnswers r c) =
        (.ok m, [.loadSession x.rem.val, .isTrustedIdentity x.rem.val k .sending,
          .saveIdentity x.rem.val k, .storeSession x.rem.val (storedRecord sess otr' taken)]) ∧
      x.draws S (okAnswers r c) = S.draws otr.pqrState x.rest

/-- Closure of `kit.RecOk` under `messageEncrypt` updates on records in `kit.ScopeAt Scope st0`. -/
def EncModelRecOk {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) : Prop :=
  ∀ (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (addr : AddrVal) (r' : SessionRecord (List (BitVec 8))),
    (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) →
    .storeSession addr r' ∈ (x.model C S uuidParse answers).2 →
    kit.RecOk r'

theorem recOk_of_encModelRecOk {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {st0 : kit.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel}
    (hmodel : EncModelOkStmt C S uuidTryParse)
    (hin : ∀ {rem} r, kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hrec : EncModelRecOk kit st0 Scope C S uuidTryParse)
    {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (h15 : StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr') :
    kit.RecOk (storedRecord sess otr' taken) := by
  have h15' := h15.inScope (fun r₀ hr₀ => hin r₀ hr₀)
  have hm := (hmodel x r sess otr taken k m otr' .newOrUnchanged h15').1
  apply hrec x (okAnswers r .newOrUnchanged) x.rem.val (storedRecord sess otr' taken)
  · intro r₀ hr₀
    cases hr₀
    exact h15.2.1
  · rw [hm]
    simp

/-- Bundle of all nine segment specifications for `session_message_encrypt_with_stores`. -/
structure EncSegsV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  load : SegLoadSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  fromS : SegFromSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  identity : SegIdentitySpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  signal : SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  preKey : SegPreKeySpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  trust : SegTrustSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  save : SegSaveSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  applyStore : SegApplyStoreSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  finish : SegFinishSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs

abbrev EncSegs (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  EncSegsV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- Wrapper specification lifting `withStoresEncSpec` (`0x3caf4`) to the public entry
`session_message_encrypt` (`0x430cc`). -/
def EntryWrapStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (encEntry img)
      (withStoresEncSpec C A ctl parse S encRecord img) →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img encryptEntryName)
      (encryptSpec C A ctl parse S encRecord img)

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
