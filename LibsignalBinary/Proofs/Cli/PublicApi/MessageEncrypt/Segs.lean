/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Callees
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.CliEncHooks
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitE
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seams

/-!
# `MessageEncrypt` Segment Specifications (`EncEnv`, `SegExit`, and `EncSegsV`)

Defines the per-segment environment `EncEnv`, exit relation `SegExit`, individual specifications for
the nine segments (`segLoad` through `segFinish`), and their bundle `EncSegsV` (along with trap-mode
twins) for `signal_session_ratchet::encrypt`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

open CryptoVerification.LibsignalPublicApi.MessageDecrypt (SessionOnlyKitOkS SessionOnlyVtablesOk)

/-- **The environment of every segment**: the image, the hook contracts, the in-image store code
at its rebased addresses (`StoreKitOkS Scope`: the load poll's `Ok(Some r)` gives `Scope r`), the
callees (`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees Q`: `OTR::encrypt` for OTRs whose SPQR state meets `Q`), and the two pure
facts tying `Scope` to the segments' needs: a record in `Scope` is in scope (`RecordInScopeEnc`), and its current session's SPQR state meets `Q` (what `from_session_state` hands
`OTR::encrypt`, `fromSessionState_pqrState`). -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv {A : RustAlloc} {img : Obj.Image}
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
  ikitOk : IdentityStoreKitOk ikit C ctl abs
  callees : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees Q img C A ctl parse S abs
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

/-- The `Q` of `OTR::encrypt`'s pre at segSignal / segPreKey: the OTR `from_session_state` made from
the loaded record's current session (the `KeyState` facts). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv.q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- **A segment's exit**: if the code is loaded, execution from `s` reaches a state meeting `next`
(the next seam) or an outcome of `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV` for the call `x` from `s0` (an error result
returned through T1/T2/T3, or a panic). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
    ∃ sf, Steps (tripleRatchetProgAt img.base C ctl abs) s sf ∧
      (next sf ∨ SubroutineOutcome (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord) x R s0 sf)

/-- **segLoad** (entry → Cur), parameterized by `kit`, `st0`, `ikit`, `ist0`:
prologue, load shim / poll / drop / free, dispatch on the answer.
`Err` → `ApplicationCallbackError` (T2), `Ok(None)` and no current session → `SessionNotFound`
(`String::clone`; T2 / T1); `Ok(Some r)` with a current session → Cur. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (R : SepProp) (s0 : State),
      EncFsCtx kit ikit C ctl abs s0 s0 →
      s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).pre x s0 ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s0
        (fun s => ∃ r g sess, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segFrom** (Cur → Otr): `OTR::from_session_state` (`+0x224`); `Err e` → `Err(protocol e)`
(T1 `+0x49c`); `Ok` → the OTR copied to `sp+0x288`, drop flag 1. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
      (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ otr taken pqCap pqPtr,
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segIdentity** (Otr → Key): `remote_identity_key` (`+0x2c8`); `None` → `.panic` (`expect_failed`); `Some k` → the key at `sp+0x350`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ k,
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segSignal** (Key → Cm, `pendingPreKey = none`): the items getter (tag 2), `OTR::encrypt`
without a local address (`+0x3a0`); `Err e` → T5 / T1 `Err(protocol e)`; `Ok` → the CM tagged
`ctSignalTag` at `sp+0x370`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segPreKey** (Key → Cm, `pendingPreKey = some items`): the items getter (`timeAdd` panic),
`items.timestamp() + MAX_UNACKNOWLEDGED_SESSION_AGE` (`timeAdd`, panic) and `< now` →
`SessionNotFound` (`String::clone`); the Kyber closure, `OTR::encrypt` with the local address
(`Err` → free the Kyber box, T5 / T1), `PreKeySignalMessage::new` (`Err` refuted by length bounds), the
248-byte CM copy. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segTrust** (Cm → Save): trust shim / poll (`Sending`), drop, free; `Err` → T5 (CM drop) →
`Err(store)`; `Ok false` → `UntrustedIdentity` (`String::clone`, CM drop `+0xd48`); `Ok true` →
Save. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k
          m otr' pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segSave** (Save → Apply): save shim / poll, drop, free; `Err` → T5 → `Err(store)`; `Ok c` →
Apply. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ c, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr
          taken k m otr' pqCap' pqPtr' c R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segApplyStore** (Apply → Stored): `OTR::apply_to_session_state` (`+0xde4`) on the taken
state, store shim / poll on the record `sp+0x110`, drop, free; store `Err` → T5 (CM drop) →
`Err(store)`; `Ok ()` → Stored. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtx kit ikit C ctl abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
        pqCap' pqPtr' c R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken
          k m otr' c R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segFinish** (Stored → outcome): the record drop (SS drop glue `+0xef4`, the empty
previous-sessions loop, buffer free), the CM copy to the sret (T2 `+0x5f8`), the epilogue
(`+0x63c..+0x660`). The outcome is `post` with `okAnswers r c` (`EncModelOkStmt`). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' c R
        s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s (fun _ => False)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpec (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- All nine segments (generic in `kit`, `st0`, `ikit`, `ist0`, `Scope`, `Q`). -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  load : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  fromS : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  identity : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  signal : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  preKey : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  trust : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  save : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  applyStore : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  finish : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs

/-- Trap-at-rng twin of `EncFsCtx`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (C : Crypto) (abs : String → Option (State → State)) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (trTrapProgAt img.base C abs) s0 s

structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CliEncHooks C A S (trTrapExterns C abs)
  kitOk : CryptoVerification.LibsignalPublicApi.MessageDecrypt.SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns C abs)
  ikitOk : CryptoVerification.LibsignalPublicApi.StoreKit.Identity.IdentityStoreKitOkIE img ikit (trTrapExterns C abs)
  callees : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncCallees_trap Q img C A ctl parse S abs
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
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

/-- The `Q` of `OTR::encrypt`'s pre at segSignal / segPreKey: the OTR `from_session_state` made from
the loaded record's current session (the `KeyState` facts). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap.q_otr {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- **A segment's exit**: if the code is loaded, execution from `s` reaches a state meeting `next`
(the next seam) or an outcome of `CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV` for the call `x` from `s0` (an error result
returned through T1/T2/T3, or a panic). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (trTrapProgAt img.base C abs).CodeLoaded s.mem →
    ∃ sf, Steps (trTrapProgAt img.base C abs) s sf ∧
      (next sf ∨ SubroutineOutcome (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord) x R s0 sf)

/-- **segLoad** (entry → Cur), parameterized by `kit`, `st0`, `ikit`, `ist0`:
prologue, load shim / poll / drop / free, dispatch on the answer.
`Err` → `ApplicationCallbackError` (T2), `Ok(None)` and no current session → `SessionNotFound`
(`String::clone`; T2 / T1); `Ok(Some r)` with a current session → Cur. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (R : SepProp) (s0 : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s0 →
      s0.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl parse S encRecord).pre x s0 ∗ R) →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s0
        (fun s => ∃ r g sess, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segFrom** (Cur → Otr): `OTR::from_session_state` (`+0x224`); `Err e` → `Err(protocol e)`
(T1 `+0x49c`); `Ok` → the OTR copied to `sp+0x288`, drop flag 1. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
      (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ otr taken pqCap pqPtr,
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segIdentity** (Otr → Key): `remote_identity_key` (`+0x2c8`); `None` → `.panic` (`expect_failed`); `Some k` → the key at `sp+0x350`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ k,
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segSignal** (Key → Cm, `pendingPreKey = none`): the items getter (tag 2), `OTR::encrypt`
without a local address (`+0x3a0`); `Err e` → T5 / T1 `Err(protocol e)`; `Ok` → the CM tagged
`ctSignalTag` at `sp+0x370`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segPreKey** (Key → Cm, `pendingPreKey = some items`): the items getter (`timeAdd` panic),
`items.timestamp() + MAX_UNACKNOWLEDGED_SESSION_AGE` (`timeAdd`, panic) and `< now` →
`SessionNotFound` (`String::clone`); the Kyber closure, `OTR::encrypt` with the local address
(`Err` → free the Kyber box, T5 / T1), `PreKeySignalMessage::new` (`Err` refuted by length bounds), the
248-byte CM copy. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segTrust** (Cm → Save): trust shim / poll (`Sending`), drop, free; `Err` → T5 (CM drop) →
`Err(store)`; `Ok false` → `UntrustedIdentity` (`String::clone`, CM drop `+0xd48`); `Ok true` →
Save. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k
          m otr' pqCap' pqPtr' R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segSave** (Save → Apply): save shim / poll, drop, free; `Err` → T5 → `Err(store)`; `Ok c` →
Apply. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => ∃ c, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr
          taken k m otr' pqCap' pqPtr' c R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segApplyStore** (Apply → Stored): `OTR::apply_to_session_state` (`+0xde4`) on the taken
state, store shim / poll on the record `sp+0x110`, drop, free; store `Err` → T5 (CM drop) →
`Err(store)`; `Ok ()` → Stored. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncFsCtx_trap kit ikit C abs s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
        pqCap' pqPtr' c R s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s
        (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken
          k m otr' c R s0 s')

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- **segFinish** (Stored → outcome): the record drop (SS drop glue `+0xef4`, the empty
previous-sessions loop, buffer free), the CM copy to the sret (T2 `+0x5f8`), the epilogue
(`+0x63c..+0x660`). The outcome is `post` with `okAnswers r c` (`EncModelOkStmt`). -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateV kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' c R
        s0 s →
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R s0 s (fun _ => False)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpec_trap (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV_trap (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope Q C ctl parse S encRecord abs

/-- All nine segments (generic in `kit`, `st0`, `ikit`, `ist0`, `Scope`, `Q`). -/
structure _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSegsV_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  load : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegLoadSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  fromS : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFromSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  identity : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegIdentitySpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  signal : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSignalSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  preKey : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegPreKeySpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  trust : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegTrustSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  save : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegSaveSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  applyStore : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegApplyStoreSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs
  finish : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegFinishSpecV_trap kit st0 ikit ist0 Scope Q C ctl parse S encRecord abs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
