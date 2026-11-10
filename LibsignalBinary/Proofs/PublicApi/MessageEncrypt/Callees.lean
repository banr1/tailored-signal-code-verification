/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.Defs
public import LibsignalBinary.Specifications.LibsignalPublicApiRepr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks

/-!
# In-Image Callee Contracts for `session_message_encrypt_with_stores`

Specifications at rebased addresses `img.base + off` for the four in-image helpers invoked by
`session_message_decrypt`/`encrypt` (`0x3caf4`), bundled into `EncCallees`:
- `unackItemsSpec` (`0x1245c`, 82 insns): `SessionState::unacknowledged_pre_key_message_items`;
- `kyberMapSpec` (`0x34254`, 38 insns): `Option<(KyberPreKeyId, &[u8])>::map(KyberPayload::new)`;
- `preKeyMsgNewSpec` (`0x15130`, 549 insns): `PreKeySignalMessage::new`;
- `cmDropSpec` (`0x353b0`, 96 insns): `drop_glue::<CiphertextMessage>`.

Logging calls behind `logOff` (`+0xc84 b.ls`, including `encode_hex` at `+0xc98`) are unreachable.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi

/-! ## `unacknowledged_pre_key_message_items` (`0x1245c`) -/

/-- Stack bound for `unacknowledged_pre_key_message_items`: 176-byte frame (`sub sp, sp, #176`) plus `timeAdd`. -/
abbrev unackItemsStack : Nat := extHookStack + 0x200

/-- Borrowed slice `(ptr, len)` returned by `kyber_ciphertext()` at `a`: null pointer and
unspecified length on `none`; `(g.vec.ptr, k.ciphertext.length)` on `some g`. -/
def unackKyberSliceAt (a : BitVec 64) : Option TailVecGhost → SepProp
  | none => (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 8
  | some g => (a ↦₆₄ g.vec.ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length)

/-- Layout of the 88-byte `Result<Option<UnacknowledgedPreKeyMessageItems>, SignalProtocolError>`
written to `out`: `u32` niche tag at `+0` (`0`/`1` = `Some` with `pre_key_id` `None`/`Some` at `+4`,
`2` = `None`), optional `kyber_pre_key_id` at `+8`, `UNIX_EPOCH + timestamp` at `+0x10`, 32-byte
base key at `+0x20`, `kyber_ciphertext` slice at `+0x40`, and `signed_pre_key_id` at `+0x50`. -/
def unackOutAt (out : BitVec 64) (kyG : Option TailVecGhost) (kyber : Option PendingKyberPreKey) :
    Option PendingPreKey → SepProp
  | none => (out ↦₃₂ 2#32) ∗ memRegion (out + 4#64) 84
  | some items =>
    ∃∗ ts : SystemTime, ⌜SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts⌝ ∗
      optU32At out items.preKeyId ∗ optU32At (out + 8#64) (kyber.map (·.preKeyId)) ∗
      ((out + 0x10#64) ↦₆₄ ts.tvSec) ∗ ((out + 0x18#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (out + 0x1c#64) 4 ∗ ((out + 0x20#64) ↦ₛ items.baseKey.bytes.toList) ∗
      unackKyberSliceAt (out + 0x40#64) kyG ∗ ((out + 0x50#64) ↦₃₂ items.signedPreKeyId) ∗
      memRegion (out + 0x54#64) 4

/-- Call parameters for `unacknowledged_pre_key_message_items`: `&SessionState` (`x0`), ghost state, model session, and `sret` (`x8`). -/
structure UnackCall where
  ss : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  out : BitVec 64

/-- Contract for `SessionState::unacknowledged_pre_key_message_items`: writes the pending pre-key
items to `x.out` with timestamp `UNIX_EPOCH + Duration::from_secs(t)` (`timeAdd` at `0x12518`) while
preserving the session, panicking iff timestamp addition overflows. -/
def unackItemsSpec (A : RustAlloc) (img : Obj.Image) : Spec UnackCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ s.readReg64 .x8 = x.out⌝ ∗ sessionStateReprAt A x.ss x.G x.sess ∗
      memRegion x.out 88 ∗ logOff img ∗ stackAt s.sp unackItemsStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ sessionStateReprAt A x.ss x.G x.sess ∗
      unackOutAt x.out x.G.kyber x.sess.pendingKyberPreKey x.sess.pendingPreKey ∗ logOff img ∗
      stackAt s0.sp unackItemsStack
  onPanic := fun x s0 sf =>
    ⌜(∃ items, x.sess.pendingPreKey = some items ∧
        SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = none) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## The Kyber closure (`0x34254`) -/

/-- Call parameters for the `KyberPayload::new` `Option::map` closure: 24-byte `Option<KyberPayload>`
`sret` (`x0`), `Option<(u32, &[u8])>` argument pointer (`x1`: `pre_key_id` at `+0`, slice pointer
at `+8` with `0` for `None`, length at `+0x10`), backing slice pointer, and model payload. -/
structure KyberMapCall where
  out : BitVec 64
  arg : BitVec 64
  ptr : BitVec 64
  kp : Option KyberPayload

/-- Memory layout of the `Option<(u32, &[u8])>` closure argument at `x.arg`. -/
def kyberArgAt (x : KyberMapCall) : SepProp :=
  match x.kp with
  | none => memRegion x.arg 8 ∗ ((x.arg + 8#64) ↦₆₄ 0#64) ∗ memRegion (x.arg + 0x10#64) 8
  | some k =>
    ⌜x.ptr ≠ 0#64 ∧ k.ciphertext.length < 2 ^ 32⌝ ∗ (x.arg ↦₃₂ k.preKeyId) ∗
      memRegion (x.arg + 4#64) 4 ∗ ((x.arg + 8#64) ↦₆₄ x.ptr) ∗
      ((x.arg + 0x10#64) ↦₆₄ BitVec.ofNat 64 k.ciphertext.length) ∗ (x.ptr ↦ₛ k.ciphertext)

/-- Contract for the `Option<(KyberPreKeyId, &[u8])>::map(KyberPayload::new)` closure (`0x34254`):
allocates and copies the ciphertext slice into a boxed `Option<KyberPayload>` (`optKyberAt`),
leaving the input unchanged and panicking only on allocation failure. -/
def kyberMapSpec (A : RustAlloc) : Spec KyberMapCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.arg⌝ ∗ kyberArgAt x ∗ memRegion x.out 24 ∗
      A.pool ∗ stackAt s.sp (allocHookStack + 0x40)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ kyberArgAt x ∗ (∃∗ bp : BitVec 64, optKyberAt A x.out bp x.kp) ∗
      A.pool ∗ stackAt s0.sp (allocHookStack + 0x40)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `PreKeySignalMessage::new` (`0x15130`) -/

/-- Stack bound for `PreKeySignalMessage::new`, covering its frame, `encoded_len`, and allocator hooks. -/
abbrev preKeyMsgNewStack : Nat := allocHookStack + 0x1000

/-- ABI call parameters for `PreKeySignalMessage::new`: `w0` version, `w1` registration ID,
`w2`/`w3` `Option<u32>` `pre_key_id` (tag and value), `w4` `signed_pre_key_id`, `x5` moved
`Option<KyberPayload>`, `x6` 32-byte base key, `x7` 32-byte identity key, `[sp]` moved 120-byte
`SignalMessage`, and `x8` 248-byte `sret`. -/
structure PreKeyMsgNewCall where
  ret : BitVec 64
  ver : BitVec 8
  regId : BitVec 32
  preKeyId : Option (BitVec 32)
  spk : BitVec 32
  kyA : BitVec 64
  kyPtr : BitVec 64
  kp : Option KyberPayload
  bkA : BitVec 64
  baseKey : PublicKey
  ikA : BitVec 64
  ik : IdentityKey
  msgA : BitVec 64
  msgG : SignalMessageGhost
  msg : SignalMessage

def PreKeyMsgNewCall.model (x : PreKeyMsgNewCall) : PreKeySignalMessage :=
  PreKeySignalMessage.new x.ver x.regId x.preKeyId x.spk x.kp x.baseKey x.ik x.msg

/-- Contract for `PreKeySignalMessage::new`: consumes the `Option<KyberPayload>` and `SignalMessage`
and writes `Ok(x.model)` in niche layout. Bounding `1 + encoded_len < 2^42` in the precondition
rules out capacity and length-addition overflow panics (`0x15998`, `0x159c0`), so the call panics
only on allocation failure. -/
def preKeyMsgNewSpec (A : RustAlloc) : Spec PreKeyMsgNewCall where
  pre := fun x s =>
    ⌜(s.readReg64 .x0).setWidth 8 = x.ver ∧ (s.readReg64 .x1).setWidth 32 = x.regId ∧
      (s.readReg64 .x2).setWidth 32 = (if x.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, x.preKeyId = some v → (s.readReg64 .x3).setWidth 32 = v) ∧
      (s.readReg64 .x4).setWidth 32 = x.spk ∧ s.readReg64 .x5 = x.kyA ∧ s.readReg64 .x6 = x.bkA ∧
      s.readReg64 .x7 = x.ikA ∧ s.readReg64 .x8 = x.ret ∧ x.model.serialized.length < 2 ^ 42⌝ ∗
      (s.sp ↦₆₄ x.msgA) ∗ optKyberAt A x.kyA x.kyPtr x.kp ∗ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 248 ∗ A.pool ∗ stackAt s.sp preKeyMsgNewStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g x.ret x.model) ∗
      (s0.sp ↦₆₄ x.msgA) ∗ memRegion x.kyA 24 ∗ (x.bkA ↦ₛ x.baseKey.bytes.toList) ∗
      (x.ikA ↦ₛ x.ik.publicKey.bytes.toList) ∗ memRegion x.msgA 120 ∗ A.pool ∗
      stackAt s0.sp preKeyMsgNewStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-! ## `drop_glue::<CiphertextMessage>` (`0x353b0`) -/

/-- Contract for `drop_glue::<CiphertextMessage>`: deallocates all heap buffers of a
`CiphertextMessage` in `apiEncResultAt` `Ok` niche layout without panicking. -/
def cmDropSpec (A : RustAlloc) : Spec (BitVec 64 × CiphertextMessage) where
  pre := fun (p, m) s =>
    ⌜s.readReg64 .x0 = p⌝ ∗ apiEncResultAt A p (.ok m) ∗ A.pool ∗ stackAt s.sp (allocHookStack + 0x40)
  post := fun (p, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion p 248 ∗ A.pool ∗ stackAt s0.sp (allocHookStack + 0x40)

/-! ## Callee hypotheses -/

def UnackItemsOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items")) (unackItemsSpec A img)

def UnackItemsOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (img.base + bv% (ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items")) (unackItemsSpec A img)

def KyberMapOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<core::option::Option<(libsignal_protocol::state::kyber_prekey::KyberPreKeyId, &[u8])>>::map::<libsignal_protocol::protocol::KyberPayload, libsignal_protocol::session_management::message_encrypt<libsignal_session::HookRng>::{closure#0}::{closure#2}>")) (kyberMapSpec A)

def PreKeyMsgNewOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new")) (preKeyMsgNewSpec A)

def PreKeyMsgNewOk_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs) (img.base + bv% (ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new")) (preKeyMsgNewSpec A)

def CmDropOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::CiphertextMessage> [local#1]")) (cmDropSpec A)

/-- `OTR::encrypt` (`0x33e0c`) on `tripleRatchetProgAt`. -/
def OtrEncryptOk (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrEncryptName)
    (otrEncryptSpec C A ctl parse S img)

/-- `otrEncryptSpec` restricted to outgoing triple-ratchet states whose SPQR state satisfies `Q`. -/
def otrEncryptSpecQ (Q : List (BitVec 8) → Prop) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (img : Obj.Image) : Spec OtrEncryptGhost :=
  { otrEncryptSpec C A ctl parse S img with
    pre := fun x s => ⌜Q x.ot.pqrState⌝ ∗ (otrEncryptSpec C A ctl parse S img).pre x s }

/-- `OTR::encrypt` (`0x33e0c`) on `tripleRatchetProgAt` for `otrEncryptSpecQ Q`. -/
def OtrEncryptOkQ (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) :
    Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrEncryptName) (otrEncryptSpecQ Q C A ctl parse S img)

/-- `otrEncryptSpec` restricted to `(pqrState, rest)` satisfying `Q`, with `F` framed. -/
def otrEncryptSpecQF (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (img : Obj.Image) : Spec OtrEncryptGhost :=
  { otrEncryptSpec C A ctl parse S img with
    pre := fun x s => ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptSpec C A ctl parse S img).pre x s
    post := fun x s0 sf => F ∗ (otrEncryptSpec C A ctl parse S img).post x s0 sf }

def OtrEncryptOkQF (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
    ((tripleRatchetProgAt img.base C ctl abs).fnAddr otrEncryptName)
    (otrEncryptSpecQF Q F C A ctl parse S img)

/-- `OTR::encrypt` (`0x33e0c`) on `tripleRatchetProgAt` for `otrEncryptSpecT` (`pqrState.length < 2^32`, `64 ≤ rest.length`, `TokenInit img` framed). -/
abbrev OtrEncryptOkQT (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  OtrEncryptOkQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    (LibsignalSpqrV1.TokenInit img) img C A ctl parse S abs

/-- Bundle of all in-image callee contracts required by the `MessageEncrypt` segments alongside `PublicApiHooks` and `StoreKitOkS`. -/
structure EncCallees (Q : List (BitVec 8) → Prop) (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) :
    Prop where
  otrFrom : OutgoingRatchet.OtrFromOk img C A ctl abs
  otrApply : OutgoingRatchet.OtrApplyOk img C A ctl abs
  remoteIk : OutgoingRatchet.RemoteIdentityKeyOk img C A ctl abs
  otrEnc : OtrEncryptOkQ Q img C A ctl parse S abs
  unack : UnackItemsOk img C A ctl abs
  kyber : KyberMapOk img C A ctl abs
  psmNew : PreKeyMsgNewOk img C A ctl abs
  cmDrop : CmDropOk img C A ctl abs
  /-- `drop_glue::<SessionStructure> [local#2]` (`0x35958`) for dropping the session record at `+0xef4`. -/
  dropSs : FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
