/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit

/-!
# Seam Decomposition and Frame Layout for `session_message_encrypt_with_stores`

Intermediate seam states, `0xbe0`-byte stack-frame predicates, and specification `withStoresEncSpecV`
for `session_message_encrypt_with_stores` (`0x3caf4`), parameterized by record scope `Scope` and
store contracts `SessionStoreSpec` / `IdentityStoreSpec`.

## Main-Path Seams

| Seam | Offset | Protocol step completed | Predicate |
| --- | --- | --- | --- |
| Entry | `+0x000` | — | `withStoresEncSpecV.pre` |
| `Cur` | `+0x20c` | `load_session = Ok(Some r)`, current session `sess` | `CurStateV` |
| `Otr` | `+0x2c8` | `from_session_state = Ok (otr, taken)` | `OtrStateV` |
| `Key` | `+0x344` | `taken.remoteIdentity = some k` | `KeyStateV` |
| `Cm` | `+0xa70` | `CiphertextMessage` `m` and updated `otr'` constructed | `CmStateV` |
| `Save` | `+0xbd4` | `is_trusted_identity = Ok true` | `SaveStateV` |
| `Apply` | `+0xd9c` | `save_identity = Ok c` | `ApplyStateV` |
| `Stored` | `+0xe88` | `store_session = Ok ()` | `StoredStateV` |

Error and panic exits run directly to an outcome of `withStoresEncSpecV` via shared error-tail
lemmas rather than separate error seams.

## Stack Frame Layout (`sp = s0.sp - 0xbe0`, `x29 = s0.sp - 0x60`)

| Range | Contents |
| --- | --- |
| `sp+0x000..0x058` | Call scratch and cross-seam pointer spills (`curScratch`, `cmScratch`) |
| `sp+0x058..0x110` | Prologue argument spills (`encSpillsAtV`) |
| `sp+0x110..0x280` | Loaded `SessionRecord` (368 B; `SessionState` at `sp+0x128`) |
| `sp+0x280..0x288` | `SessionState` pointer spill (`sp+0x128`) |
| `sp+0x288..0x350` | `OutgoingTripleRatchet` (200 B, `otrAt`) |
| `sp+0x350..0x370` | Remote identity key (32 B) |
| `sp+0x370..0x468` | `CiphertextMessage` result staging (248 B, `apiEncResultAt` layout) |
| `sp+0x468..0x46a` | Async state byte (`0`) and OTR PQ-`Vec` drop flag (`1` after `from_session_state`) |
| `sp+0x46a..0xb80` | Async poll buffers and call staging |
| `sp+0xb80..0xbe0` | Saved callee-saved registers `x19..x30` (`encSavedRegs`) |
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Frame Constants and Seam PCs -/

/-- Stack frame size of `session_message_encrypt_with_stores` (`0xbe0` bytes). -/
abbrev encFrameSize : Nat := 0xbe0

/-- Stack budget at entry to `_with_stores` (`entryStack` minus the wrapper's `0x30`-byte frame). -/
abbrev withStoresEncStack : Nat := entryStack - 0x30

abbrev encSubStack : Nat := withStoresEncStack - encFrameSize

/-- Callee stack budget below the `0xbe0`-byte frame for given `SessionStoreSpec` and `IdentityStoreSpec`. -/
abbrev encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  max encSubStack
    (max (max (max kit.loadShimStack kit.loadPollStack)
              (max kit.storeShimStack kit.storePollStack))
         (max (max ikit.trustShimStack ikit.trustPollStack)
              (max ikit.saveShimStack ikit.savePollStack)))

abbrev withStoresEncStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) : Nat :=
  encSubStackV kit ikit + encFrameSize

theorem encSubStack_le_encSubStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    encSubStack ≤ encSubStackV kit ikit :=
  Nat.le_max_left _ _

theorem withStoresEncStack_le_withStoresEncStackV {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b) :
    withStoresEncStack ≤ withStoresEncStackV kit ikit := by
  unfold withStoresEncStackV
  have h := encSubStack_le_encSubStackV kit ikit
  have h2 : withStoresEncStack = encSubStack + encFrameSize := by decide
  omega

abbrev encEntry (img : Obj.Image) : BitVec 64 := entryOf img encryptWithStoresName

/-- `Cur` seam PC (`+0x20c`): `load_session` returned `Ok(Some r)` with a current session. -/
abbrev curPC (img : Obj.Image) : BitVec 64 := encEntry img + 0x20c#64
/-- `Otr` seam PC (`+0x2c8`): before `remote_identity_key`. -/
abbrev otrPC (img : Obj.Image) : BitVec 64 := encEntry img + 0x2c8#64
/-- `Key` seam PC (`+0x344`): before `unacknowledged_pre_key_message_items`. -/
abbrev keyPC (img : Obj.Image) : BitVec 64 := encEntry img + 0x344#64
/-- `Cm` seam PC (`+0xa70`): join of the `SignalMessage` and `PreKeySignalMessage` branches. -/
abbrev cmPC (img : Obj.Image) : BitVec 64 := encEntry img + 0xa70#64
/-- `Save` seam PC (`+0xbd4`): after `is_trusted_identity = Ok true`, before `save_identity`. -/
abbrev savePC (img : Obj.Image) : BitVec 64 := encEntry img + 0xbd4#64
/-- `Apply` seam PC (`+0xd9c`): after `save_identity`, before `apply_to_session_state`. -/
abbrev applyPC (img : Obj.Image) : BitVec 64 := encEntry img + 0xd9c#64
/-- `Stored` seam PC (`+0xe88`): after `store_session = Ok ()`, before record drop and epilogue. -/
abbrev storedPC (img : Obj.Image) : BitVec 64 := encEntry img + 0xe88#64

/-- Default `HookSessionStore` vtable address in `.rodata` (`x5`). -/
abbrev ssVtable (b : BitVec 64) : BitVec 64 := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 100) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 104) + 8)
abbrev idVtable (b : BitVec 64) : BitVec 64 := b + bv% (ls_xref% (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 136) (ls_off% "<libsignal_protocol::proto::wire::PreKeySignalMessage as core::fmt::Debug>::fmt" + 140) + 16)

/-- `.rodata` vtable slots for `is_trusted_identity` (`+0x30`) and `save_identity` (`+0x28`). -/
def IdVtableOk (img : Obj.Image) (id_vt : BitVec 64) : Prop :=
  (∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((id_vt + 0x30#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 184))) ∗ P) ∧
  (∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((id_vt + 0x28#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#3]" + 88))) ∗ P)

/-- `.rodata` vtable slot for `store_session` (`+0x20`). -/
def StoreVtableOk (img : Obj.Image) (ss_vt : BitVec 64) : Prop :=
  ∀ {s : State} {P : SepProp}, img.FrozenLoaded s → (s.mem ⊨ P) →
    s.mem ⊨ ((ss_vt + 0x20#64) ↦₆₄ᵣ (img.base + bv% (ls_off% "<[u8] as subtle::ConstantTimeEq>::ct_eq" + 16792))) ∗ P

/-! ## Specification of `session_message_encrypt_with_stores` -/

/-- Ghost input bundle for `session_message_encrypt_with_stores`, extending `EncryptGhost` with
the session-store (`x4`) and identity-store (`x6`) data pointers. -/
structure WithStoresEncGhost extends EncryptGhost where
  ssA : BitVec 64
  idA : BitVec 64

/-- Store footprints and extra callee stack carried in the frame across non-store segments. -/
def encStoreExtra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) : SepProp :=
  ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    kit.storeAt x.ssA st ∗
    ikit.identityAt x.idA ist ∗
    memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (encSubStackV kit ikit - encSubStack)

theorem withStoresEncStack_split_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ⊢
      encStoreExtra kit st ikit ist x s0 ∗ stackAt s0.sp withStoresEncStack := by
  unfold encStoreExtra stackAt
  have hle := encSubStack_le_encSubStackV kit ikit
  have hw : withStoresEncStack = encSubStack + encFrameSize := by decide
  have hsum : (encSubStackV kit ikit - encSubStack) + withStoresEncStack = withStoresEncStackV kit ikit := by
    unfold withStoresEncStackV; omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hsplit :
      memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (withStoresEncStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 withStoresEncStack) withStoresEncStack := by
    refine memRegion_split'
      (b := s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (b' := s0.sp - BitVec.ofNat 64 withStoresEncStack)
      (n := encSubStackV kit ikit - encSubStack) (k := withStoresEncStack)
      hsum.symm ?_ (by omega)
    bv_omega
  rw [hsplit, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right hbound (Entails.refl _)

theorem withStoresEncStack_join_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtra kit st ikit ist x s0 ∗ stackAt s0.sp withStoresEncStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt s0.sp (withStoresEncStackV kit ikit) := by
  unfold encStoreExtra stackAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hbound => ?_
  have hle := encSubStack_le_encSubStackV kit ikit
  have hw : withStoresEncStack = encSubStack + encFrameSize := by decide
  have hsum : (encSubStackV kit ikit - encSubStack) + withStoresEncStack = withStoresEncStackV kit ikit := by
    unfold withStoresEncStackV; omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hsplit :
      memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (withStoresEncStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 withStoresEncStack) withStoresEncStack := by
    refine memRegion_split'
      (b := s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (b' := s0.sp - BitVec.ofNat 64 withStoresEncStack)
      (n := encSubStackV kit ikit - encSubStack) (k := withStoresEncStack)
      hsum.symm ?_ (by omega)
    bv_omega
  rw [hsplit]
  exact Entails.refl _

theorem encSubStack_join_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    encStoreExtra kit st ikit ist x s0 ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) := by
  unfold encStoreExtra stackAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun _ => ?_
  have hle := encSubStack_le_encSubStackV kit ikit
  have hsum : (encSubStackV kit ikit - encSubStack) + encSubStack = encSubStackV kit ikit := by omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hbase : s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit) =
      s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit) := by
    unfold withStoresEncStackV encFrameSize at hbound ⊢
    bv_omega
  have hsplit :
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) encSubStack := by
    rw [hbase]
    refine memRegion_split'
      (b := s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
      (b' := s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack)
      (n := encSubStackV kit ikit - encSubStack) (k := encSubStack)
      hsum.symm ?_ (by unfold withStoresEncStackV encFrameSize at hbound; omega)
    unfold withStoresEncStackV encFrameSize at hbound
    bv_omega
  rw [hsplit]
  exact Entails.refl _

theorem encSubStack_split_extra {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ⊢
      encStoreExtra kit st ikit ist x s0 ∗ stackAt (s0.sp - 0xbe0#64) encSubStack := by
  unfold encStoreExtra stackAt
  have hle := encSubStack_le_encSubStackV kit ikit
  have hsum : (encSubStackV kit ikit - encSubStack) + encSubStack = encSubStackV kit ikit := by omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hbase : s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit) =
      s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit) := by
    unfold withStoresEncStackV encFrameSize at hbound ⊢
    bv_omega
  have hsplit :
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) encSubStack := by
    rw [hbase]
    refine memRegion_split'
      (b := s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
      (b' := s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack)
      (n := encSubStackV kit ikit - encSubStack) (k := encSubStack)
      hsum.symm ?_ (by unfold withStoresEncStackV encFrameSize at hbound; omega)
    unfold withStoresEncStackV encFrameSize at hbound
    bv_omega
  rw [hsplit, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right hbound (Entails.refl _)

/-- Stack layout of `now: SystemTime` passed by value at caller `sp` (`tv_sec` at `+0`, `tv_nsec`
at `+8`, 4 bytes padding at `+12`). -/
def nowAt (p : BitVec 64) (t : SystemTime) : SepProp :=
  (p ↦₆₄ t.tvSec) ∗ ((p + 8#64) ↦₃₂ t.tvNsec) ∗ memRegion (p + 12#64) 4

/-- Specification of `session_message_encrypt_with_stores` (`0x3caf4`) at default hook store
vtables `ssVtable img.base` and `idVtable img.base`. -/
def withStoresEncSpec (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) : Spec WithStoresEncGhost :=
  Spec.inImage
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = ssVtable img.base ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = idVtable img.base ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStack ≤ s.sp.toNat⌝ ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗
        logOff img ∗ stackAt s.sp withStoresEncStack ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            sf.trace = s0.trace ++
              (x.model C S uuidParse answers).2.map (storeEvent encRecord answers)⌝ ∗
          apiEncResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
          logOff img ∗ stackAt s0.sp withStoresEncStack ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              s0.trace ++ [loadEvent encRecord x.rem.val answers.loadSession] <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ∗
          anyHeap }
    img

/-- Specification of `session_message_encrypt_with_stores` (`0x3caf4`) parameterized by
`SessionStoreSpec` and `IdentityStoreSpec`. -/
def withStoresEncSpecV {A : RustAlloc} {img : Obj.Image}
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
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗
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
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
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

theorem withStoresEncSpecV_pre_addrOk {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  dsimp only [withStoresEncSpecV, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre2 := hpre.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre2
  exact hpre2.1.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## Frame Predicates -/

/-- Callee-saved registers `x19..x30` spilled at `[sp0 - 96 .. sp0)`. -/
def encSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗ ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

/-- Machine and code-loading invariants common to every seam. -/
def encMidMeta (img : Obj.Image) (x : WithStoresEncGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp - 0xbe0#64 ∧ s0.spAligned = true ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧ s.readReg64 .x19 = x.ret ∧ img.FrozenLoaded s ∧
    s.symtab = img.symtab ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Prologue argument spills at `sp + 0x58 .. sp + 0x110`, parameterized by store vtables. -/
def encSpillsAtV (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
  ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
  ((sp + 0xc8#64) ↦₆₄ x.locA) ∗ ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

abbrev encSpillsAt (b sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  encSpillsAtV (ssVtable b) (idVtable b) sp x

/-- Call scratch `sp + 0x00 .. sp + 0x58` at `Cur`, `Otr`, and `Key`, retaining the
`SessionState` pointer spill `[sp + 0x50] = sp + 0x128`. -/
def curScratch (sp : BitVec 64) : SepProp :=
  memRegion sp 0x50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Call scratch `sp + 0x00 .. sp + 0x58` at `Cm`, `Save`, `Apply`, and `Stored`, retaining the
OTR (`[sp + 0x38] = sp + 0x288`), remote identity key (`[sp + 0x40] = sp + 0x350`), and
`SessionState` (`[sp + 0x50] = sp + 0x128`) pointer spills. -/
def cmScratch (sp : BitVec 64) : SepProp :=
  memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
    ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗ memRegion (sp + 0x48#64) 8 ∗
    ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

/-- Borrowed caller inputs, RNG tape advanced by `draws`, callee stack, and saved registers. -/
def encCommon (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff img ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

/-- Generic seam state parameterized by store vtables, PC, trace events, RNG draws, registers,
and stack slot predicates. -/
def EncSeamV (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (pc : BitVec 64) (evs : List TraceEvent) (draws : Nat)
    (regs : BitVec 64 → State → Prop) (slots scratch : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMeta img x s0 s ∧ s.trace = s0.trace ++ evs ∧ regs sp s ∧
    x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
    x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ scratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R)

abbrev EncSeam (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image) (x : WithStoresEncGhost)
    (pc : BitVec 64) (evs : List TraceEvent) (draws : Nat) (regs : BitVec 64 → State → Prop)
    (slots scratch : BitVec 64 → SepProp) (R : SepProp) (s0 s : State) : Prop :=
  EncSeamV (ssVtable img.base) (idVtable img.base) A ctl img x pc evs draws regs slots scratch R s0 s

/-- Session record after `from_session_state` moves the SPQR state out into `otr`. -/
def takenRecord (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    SessionRecord (List (BitVec 8)) :=
  { currentSession := some { sess with state := taken } }

/-- `OutgoingTripleRatchet.fromSessionState` transfers `s.pqRatchetState` into `otr.pqrState`. -/
theorem fromSessionState_pqrState {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    otr.pqrState = s.pqRatchetState := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact h.1 ▸ rfl

/-- Updated `SessionRecord` written by `store_session` (`otr'` applied to `taken`). -/
def storedRecord (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : SessionRecord (List (BitVec 8)) :=
  { currentSession := some { sess with state := otr'.applyToSessionState taken } }

/-- Pure relation for the message-encryption branch: produces `SignalMessage` when no pending
pre-key is present, or checks expiry against `x.now` and wraps a `PreKeySignalMessage`. -/
def EncEncryptStep (C : Crypto) (S : SpqrModel) (uuidParse : UuidParser) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8))) : Prop :=
  match sess.pendingPreKey with
  | none =>
    ∃ sm, execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr =
        .ok (sm, otr') ∧ m = .signalMessage sm
  | some items =>
    ∃ ts expiry sm, SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
      ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧ expiry.lt x.now = false ∧
      execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
          (serializeAddrVals (serviceIdParse uuidParse) x.loc.val x.rem.val) x.rest) otr =
        .ok (sm, otr') ∧
      m = .preKeySignalMessage (PreKeySignalMessage.new otr'.sessionVersion
        sess.localRegistrationId items.preKeyId items.signedPreKeyId
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
        items.baseKey otr'.localIdentityKey sm)

/-! ## Seam States -/

abbrev loadOk (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) : TraceEvent :=
  loadEvent encRecord x.rem.val (.ok (some r))

/-- `Cur` seam state (`+0x20c`). -/
def CurStateV {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (curPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x21 = sp + 0x128#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => sessionRecordAt A (sp + 0x110#64) g r ∗ memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8))
    curScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

abbrev CurState (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  CurStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope ctl encRecord x r g sess R s0 s

/-- Stack slots shared across `Otr`..`Cm`: `takenRecord`, `SessionState` spill, and drop flags. -/
def takenSlots (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : SepProp :=
  (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken)) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8)

/-- `Otr` seam state (`+0x2c8`). -/
def OtrStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (otrPC img)
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

abbrev OtrState (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  OtrStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s

/-- `Key` seam state (`+0x344`). -/
def KeyStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (keyPC img)
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

abbrev KeyState (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  KeyStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s

/-- Pure protocol facts established up to the `Cm` seam (`Scope r` through `EncEncryptStep`). -/
def StepsThroughEncrypt (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (S : SpqrModel)
    (uuidParse : UuidParser) (x : WithStoresEncGhost)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8))) :
    Prop :=
  r.currentSession = some sess ∧ Scope r ∧
    execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
    taken.remoteIdentity = some k ∧ EncEncryptStep C S uuidParse x sess otr m otr'

/-- Stack slots shared across `Cm`..`Apply`: `takenRecord`, updated `otr'`, identity key `k`,
and `CiphertextMessage` `m`. -/
def cmSlots (A : RustAlloc) (sp : BitVec 64) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (m : CiphertextMessage) : SepProp :=
  takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m)

/-- `Cm` seam state (`+0xa70`). -/
def CmStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (cmPC img)
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R) s0 s

abbrev CmState (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (img : Obj.Image)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  CmStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope C ctl uuidParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

/-- `Save` seam state (`+0xbd4`). -/
def SaveStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (savePC img)
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

abbrev SaveState (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
    (s0 s : State) : Prop :=
  SaveStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope C ctl uuidParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

/-- `Apply` seam state (`+0xd9c`). -/
def ApplyStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (applyPC img)
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

abbrev ApplyState (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  ApplyStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope C ctl uuidParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s

/-- `Stored` seam state (`+0xe88`). -/
def StoredStateV {A : RustAlloc} {img : Obj.Image}
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
  EncSeamV kit.ss_vt ikit.id_vt A ctl img x (storedPC img)
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

abbrev StoredState (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (img : Obj.Image) (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
    (s0 s : State) : Prop :=
  StoredStateV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) ()
    Scope C ctl uuidParse S encRecord x r sess otr taken k m otr' c R s0 s

def okAnswers (r : SessionRecord (List (BitVec 8))) (c : IdentityChange) :
    StoreAnswers (List (BitVec 8)) Unit :=
  { loadSession := .ok (some r), isTrustedIdentity := .ok true, saveIdentity := .ok c,
    storeSession := .ok () }

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
