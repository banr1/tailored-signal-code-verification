/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
public import LibsignalBinary.Proofs.Cli.Specifications.LibsignalPublicApi

/-!
# CLI `MessageEncrypt` Seam States and Top-Level Contract

Defines the seam PCs, common frame predicates, seam state invariants (`CurStateV` through
`StoredStateV`), and `withStoresEncSpecV` for `session_message_encrypt_with_stores` on the CLI image.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Seam PCs and Top-Level Contract -/

/-- Entry address of `session_message_encrypt_with_stores` on `img`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry (img : Obj.Image) : BitVec 64 := entryOf img CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName

/-- **Cur** (`+0x20c`): the load returned `Ok(Some r)` with a current session; next
`from_session_state` (`+0x224`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x20c#64

/-- **Otr** (`+0x2c8`): `bl remote_identity_key`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x2c8#64

/-- **Key** (`+0x344`): `bl unacknowledged_pre_key_message_items`. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.keyPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x344#64

/-- **Cm** (`+0xa70`): join of the SignalMessage (E5) and PreKey (E6e) branches; next the
`is_trusted_identity` shim. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xa70#64

/-- **Save** (`+0xbd4`): trusted; next the `save_identity` shim. -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.savePC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xbd4#64

/-- **Apply** (`+0xd9c`): saved; next the OTR copy and `apply_to_session_state` (`+0xde4`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.applyPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xd9c#64

/-- **Stored** (`+0xe88`): `store_session` answered `Ok(())`; next the record drop, the result
copy (`+0x5f8`) and the epilogue (`+0x65c`). -/
abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.storedPC (img : Obj.Image) : BitVec 64 := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0xe88#64

set_option linter.unusedVariables false in
/-- **`session_message_encrypt_with_stores`** (`(ls_off% "signal_session_ratchet::encrypt")`), parameterized by a `SessionStoreSpec`
`kit` with initial state `st0` and an `IdentityStoreSpec` `ikit` with initial state `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = kit.ss_vt ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗
        logOff img ∗ stackAt s.sp (withStoresEncStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            kit.callsRel st0 answers (x.model C S uuidParse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S uuidParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encRecord answers (x.model C S uuidParse answers).2⌝ ∗
          kit.storeAt x.ssA (kit.storeFinal st0 answers (x.model C S uuidParse answers).2) ∗
          ikit.identityAt x.idA (ikit.idFinal ist0 answers (x.model C S uuidParse answers).2) ∗
          apiEncResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗
          logOff img ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ∗
          anyHeap }
    img

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV_pre_addrOk {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact hpre2.1.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Frame predicates -/

set_option linter.unusedVariables false in
/-- The borrowed inputs and the environment, unchanged at every seam (the tape advanced by
`draws`), the callees' stack below the frame and the saved registers. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest draws ∗ logOff img ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

/-- **The generic seam**, parameterized by `ss_vt` and `id_vt`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (pc : BitVec 64) (evs : List TraceEvent) (draws : Nat)
    (regs : BitVec 64 → State → Prop) (slots scratch : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMeta img x s0 s ∧ s.trace = s0.trace ++ evs ∧ regs sp s ∧
    x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
    x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ scratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R)

abbrev _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeam (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (pc : BitVec 64) (evs : List TraceEvent) (draws : Nat) (regs : BitVec 64 → State → Prop)
    (slots scratch : BitVec 64 → SepProp) (R : SepProp) (s0 s : State) : Prop :=
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV (ssVtable img.base) (idVtable img.base) A ctl img x pc evs draws regs slots scratch R s0 s

/-- **Cur** (`+0x20c`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x21 = sp + 0x128#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => sessionRecordAt A (sp + 0x110#64) g r ∗ memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8))
    curScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

/-- **Otr** (`+0x2c8`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x0 = sp + 0x128#64 ∧ s.readReg64 .x8 = sp + 0x580#64 ∧
      s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x23 = sp + 0x58#64 ∧ s.readReg64 .x24 = sp + 0x58#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x27 = sp + 0xc0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118)
    curScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

/-- **Key** (`+0x344`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.keyPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x0 = sp + 0x128#64 ∧ s.readReg64 .x8 = sp + 0x580#64 ∧
      s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x23 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x27 = sp + 0xc0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8)
    curScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

/-- **Cm** (`+0xa70`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

/-- **Save** (`+0xbd4`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
    (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true)) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.savePC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtra kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x s0 ∗ R)
    s0 s

/-- **Apply** (`+0xd9c`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.ApplyStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true) ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c)) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.applyPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true) ++
      ikit.saveEvs x.rem.val k (.ok c))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtra kit st0 ikit
      (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c))
      x s0 ∗ R) s0 s

/-- **Stored** (`+0xe88`), parameterized by `kit`, `st0`, `ikit`, `ist0`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.StoredStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
    (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true) ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c) ∧
    kit.storeRel st0 x.rem.val (storedRecord sess otr' taken) (.ok ())) ∧
  CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncSeamV kit.ss_vt ikit.id_vt A ctl img x (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.storedPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true) ++
      ikit.saveEvs x.rem.val k (.ok c) ++
      kit.storeEvs encRecord x.rem.val (storedRecord sess otr' taken) (.ok ()))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => (∃∗ g : RecordGhost,
        sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1)
    cmScratch
    (encStoreExtra kit (kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()))
      ikit (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c))
      x s0 ∗ R)
    s0 s

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
