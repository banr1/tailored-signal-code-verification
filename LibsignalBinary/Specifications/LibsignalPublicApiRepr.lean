/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi

/-!
# Memory Layouts and Store Trace Events for the Public Session API

**Checked by Lean.** Separation-logic representation predicates (`sessionStateReprAt`,
`sessionRecordAt`, `apiErrAt`, `apiDecResultAt`, `apiEncResultAt`, `preKeyMsgAt`) and store-call
trace events (`storeEvent`) relating the compiled `session_message_decrypt_signal` and
`session_message_encrypt` entry points to `LibsignalSessionApi.lean`.

Each store hook appends a single `TraceEvent.userDefined` recording both the call arguments and the
returned answer (`storeEvent encRecord answers`), parameterized by `encRecord` for `SessionRecord`
payloads. `sessionRecordAt` is functional in memory so that hook preconditions determine a unique
model record. Failing store hooks map uniformly to `ApplicationCallbackError("store hook", …)`
(`E = Unit`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApiRepr

open Arm64 CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Addresses -/

/-- The **value** of a `ProtocolAddress`: the name bytes and the device byte (W0's `Addr`). The
ghost `AddrGhost` also pins the name's `(cap, ptr)`, which no model value depends on. -/
structure AddrVal where
  name : List (BitVec 8)
  device : BitVec 8
  deriving DecidableEq

/-- The value of an address ghost. -/
def _root_.CryptoVerification.LibsignalTripleRatchetRepr.AddrGhost.val (g : AddrGhost) : AddrVal :=
  ⟨g.name.bytes, g.device⟩

/-- `serialize_addresses` on address values (the triple ratchet's `serializeAddresses` reads only
`name.bytes` and `device`; the two agree on `AddrGhost.val`, a proof lemma). -/
def serializeAddrVals (parse : ServiceIdParser) (sender recipient : AddrVal) :
    Option (List (BitVec 8)) := do
  let s ← parse sender.name
  let r ← parse recipient.name
  return addrBytes s sender.device ++ addrBytes r recipient.device

/-! ## Store events -/

/-- An address in an event payload: `varint (name length) ‖ name ‖ device` (self-delimiting). -/
def addrEnc (a : AddrVal) : List (BitVec 8) :=
  LibsignalSessionApi.Prost.varint a.name.length ++ a.name ++ [a.device]

/-- A direction in an event payload: the hook's `direction` argument (`stores/src/lib.rs:160–163`). -/
def directionByte : Direction → BitVec 8
  | .sending => 0#8
  | .receiving => 1#8

/-- The status byte of an answer: the hook's status (`stores/src/lib.rs:40–47`): `0` = the first
`Ok` answer, `1` = the second, `2` = an error (the hook may return any status ≥ 2). -/
def okStatus (second : Bool) : BitVec 8 := if second then 1#8 else 0#8
def errStatus : BitVec 8 := 2#8

/-- `load_session(address)` answered `ans` (tag `loadSession`): `addrEnc address`, then `0`
(`Ok(None)`), `1 ‖ encRecord r` (`Ok(Some r)`) or `2` (error). -/
def loadEvent (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (a : AddrVal) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → TraceEvent
  | .ok none => .userDefined "loadSession" (addrEnc a ++ [okStatus false])
  | .ok (some r) => .userDefined "loadSession" (addrEnc a ++ okStatus true :: encRecord r)
  | .error () => .userDefined "loadSession" (addrEnc a ++ [errStatus])

/-- `is_trusted_identity(address, identity, direction)` answered `ans` (tag `isTrustedIdentity`). -/
def trustEvent (a : AddrVal) (k : IdentityKey) (d : Direction) : Except Unit Bool → TraceEvent
  | .ok b => .userDefined "isTrustedIdentity" (addrEnc a ++ k.serialize ++ [directionByte d, okStatus b])
  | .error () => .userDefined "isTrustedIdentity" (addrEnc a ++ k.serialize ++ [directionByte d, errStatus])

/-- `save_identity(address, identity)` answered `ans` (tag `saveIdentity`). -/
def saveEvent (a : AddrVal) (k : IdentityKey) : Except Unit IdentityChange → TraceEvent
  | .ok c => .userDefined "saveIdentity" (addrEnc a ++ k.serialize ++ [okStatus (c == .replacedExisting)])
  | .error () => .userDefined "saveIdentity" (addrEnc a ++ k.serialize ++ [errStatus])

/-- `store_session(address, record)` answered `ans` (tag `store`, DyLean's `storeLocalState`):
`addrEnc address ‖ status ‖ encRecord record`. -/
def storeSessionEvent (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (a : AddrVal)
    (r : SessionRecord (List (BitVec 8))) : Except Unit Unit → TraceEvent
  | .ok () => .userDefined "store" (addrEnc a ++ okStatus false :: encRecord r)
  | .error () => .userDefined "store" (addrEnc a ++ errStatus :: encRecord r)

/-- **The event of a W0 store call with its answer**: the answer of the
call's kind in `answers`. -/
def storeEvent (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (answers : StoreAnswers (List (BitVec 8)) Unit) :
    StoreCall AddrVal (List (BitVec 8)) → TraceEvent
  | .loadSession a => loadEvent encRecord a answers.loadSession
  | .isTrustedIdentity a k d => trustEvent a k d answers.isTrustedIdentity
  | .saveIdentity a k => saveEvent a k answers.saveIdentity
  | .storeSession a r => storeSessionEvent encRecord a r answers.storeSession

/-! ## `SessionRecord` (368 bytes)

`SessionRecord { previous_sessions: Vec<Vec<u8>> @0, current_session: Option<SessionState> @0x18 }`
(`state/session.rs:705–708`; the field order is rustc's). `current_session = None` is the niche
`noneCap` in SS word 0 (SS + 0, `local_identity_public`'s capacity; `session_state()` at
`message_decrypt_signal_with_stores+0x1c4: ldr x9, [sp, #0x138]; cmn x9, #1`). Scope
restriction: no previous sessions (`previous_sessions.len = 0`). -/

/-- A prost `Option<u32>` at the start of a byte list (8 bytes: a `u32` tag, 0 = `None`, 1 =
`Some`, then the value). -/
def OptU32Rel (bs : List (BitVec 8)) : Option (BitVec 32) → Prop
  | none => bs.take 4 = [0#8, 0#8, 0#8, 0#8]
  | some v => bs.take 4 = [1#8, 0#8, 0#8, 0#8] ∧ (bs.drop 4).take 4 = leBytes 4 v.toNat

/-- The pending pre-key of W0 against the triple ratchet's ghost (`SessionGhost.pending`):
`base_key` (the ghost `Vec`) deserializes to the model key and is exactly 33 bytes (the canonical
`PublicKey::serialize` that `set_unacknowledged_pre_key_message` stores, `state/session.rs:520`;
upstream's reader also accepts trailing bytes, such records are outside the specs); the 24-byte
tail holds `pre_key_id: Option<u32>` @+0x18, `timestamp: u64` @+0x20, `signed_pre_key_id: i32`
@+0x28 (offsets in the 48-byte `PendingPreKey`). -/
def PendingRel : Option TailVecGhost → Option PendingPreKey → Prop
  | none, none => True
  | some g, some p =>
    PublicKey.deserialize g.vec.bytes = .ok p.baseKey ∧ OptU32Rel g.tail p.preKeyId ∧
      (g.tail.drop 8).take 8 = leBytes 8 p.timestamp.toNat ∧
      (g.tail.drop 16).take 4 = leBytes 4 p.signedPreKeyId.toNat ∧ g.vec.bytes.length = 33
  | _, _ => False

/-- The pending Kyber pre-key: `ciphertext` (the ghost `Vec`) @0, `pre_key_id: u32` @+0x18 (the
tail's first 4 bytes). -/
def KyberRel : Option TailVecGhost → Option PendingKyberPreKey → Prop
  | none, none => True
  | some g, some k => g.vec.bytes = k.ciphertext ∧ g.tail.take 4 = leBytes 4 k.preKeyId.toNat
  | _, _ => False

/-- **A current session at `ss` (344 bytes)**: `LibsignalTripleRatchetRepr.sessionStateAt` for the
session-model part, and the W0 fields `LibsignalTripleRatchetRepr` frames byte-exactly in its ghost:
`alice_base_key` (`G.alice`), the registration ids (`G.regIds`: remote @SS + 0x150, local @SS +
0x154), the two pending pre-keys. `sessionStateAt` already relates `G.pending.isSome` to the
session model's flag, so the session is `Session.Wf`. Every W0 field is a function of the memory
(functional, module docstring). -/
def sessionStateReprAt (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  ⌜PendingRel G.pending s.pendingPreKey ∧ KyberRel G.kyber s.pendingKyberPreKey ∧
    G.alice.bytes = s.aliceBaseKey ∧ G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat ∧
    (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat⌝ ∗
    sessionStateAt A ss G s.state

/-- The ghost layout of a `SessionRecord`: the (empty) `previous_sessions` buffer and the current
session's ghost. -/
structure RecordGhost where
  prevCap : BitVec 64
  prevPtr : BitVec 64
  cur : Option SessionGhost

/-- **A `SessionRecord` at `r` (368 bytes)** holding the W0 record `rec`: `previous_sessions` an
empty `Vec<Vec<u8>>` (element 24 bytes, align 8; no previous sessions) @0; `current_session`
@0x18: `None` = SS word 0 `noneCap`, the other 336 bytes unspecified; `Some s` = `sessionStateReprAt`. -/
def sessionRecordAt (A : RustAlloc) (r : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) r g.prevCap g.prevPtr [] ∗
    match g.cur, rec.currentSession with
    | none, none => ((r + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (r + 0x20#64) 336
    | some G, some s => sessionStateReprAt A (r + 0x18#64) G s
    | _, _ => ⌜False⌝

/-! ## Results of the public entry points -/

/-- `Option<Result<Vec<u8>, SPE>>::None` (`poll_once` pending, unreachable): word 0 `-3`
(`message_decrypt_signal_with_stores+0xa8..+0xb0: mov x9, #-3; str x9, [x27]`). -/
def pendingTag : BitVec 64 := 0xFFFFFFFFFFFFFFFD#64

/-- SPE variant indices of the three errors W0 adds (`error.rs` declaration order). -/
def speUntrustedIdentity : Nat := 12
def speSessionNotFound : Nat := 19
def speApplicationCallback : Nat := 26

/-- The `"store hook"` literal of `hook_error()` (10 bytes, rodata `0x56ab0`; store poll
`+0x3c..+0x40`). -/
def storeHookStr : List (BitVec 8) := utf8 "store hook"

/-- An owned clone of an address value at `a` (32 bytes, `ProtocolAddress::clone`): some fresh
name `Vec` with exactly the name bytes, the device byte, 7 bytes unspecified. -/
def addrCloneAt (A : RustAlloc) (a : BitVec 64) (v : AddrVal) : SepProp :=
  vecU8 A a v.name ∗ ((a + 0x18#64) ↦₈ v.device) ∗ memRegion (a + 0x19#64) 7

/-- **An SPE at `e` (48 bytes) for a W0 error other than `protocol`**:
* `sessionNotFound a op`: `SessionNotFound { address: Some(clone), op }` is SPE's dataful variant
  (index 19, no tag word): the address clone @0, `op: &'static str` @0x20 with W0's `op` bytes
  (`"message_decrypt_signal"`, `session_management.rs:311`; `"message_encrypt"`, L60, 64, 86);
* `untrustedIdentity a`: `speWord 12`, the address clone @8, 8 bytes unspecified;
* `store ()`: `speWord 26`, `&'static str "store hook"` @8, `Box<dyn Error>` @0x18 (data = some
  non-null dangling pointer, the box of a ZST; vtable = some pointer), 8 bytes unspecified. -/
def apiErrAt (A : RustAlloc) (e : BitVec 64) : ApiError AddrVal Unit → SepProp
  | .sessionNotFound a op => addrCloneAt A e a ∗ strRefAt (e + 0x20#64) (utf8 op)
  | .untrustedIdentity a =>
    (e ↦₆₄ speWord speUntrustedIdentity) ∗ addrCloneAt A (e + 8#64) a ∗ memRegion (e + 0x28#64) 8
  | .store () =>
    (e ↦₆₄ speWord speApplicationCallback) ∗ strRefAt (e + 8#64) storeHookStr ∗
      (∃∗ d : BitVec 64, ⌜d ≠ 0⌝ ∗ ((e + 0x18#64) ↦₆₄ d)) ∗
      (∃∗ vt : BitVec 64, (e + 0x20#64) ↦₆₄ vt) ∗ memRegion (e + 0x28#64) 8
  | .protocol _ => ⌜False⌝
  | .panic => ⌜False⌝

/-- **The decrypt entry's result at `r` (48 bytes, `Option<Result<Vec<u8>, SPE>>`)** for the W0
result: `Ok` and the session-model errors as `LibsignalTripleRatchet.recordResultAt` (including
`"decryption failed"` for a record without a current session); the W0 errors as `apiErrAt`; a panic
never returns. The `None` (pending) word `pendingTag` is never produced. -/
def apiDecResultAt (A : RustAlloc) (r : BitVec 64) :
    Except (ApiError AddrVal Unit) (List (BitVec 8)) → SepProp
  | .ok pt => vecResultAt A r (.ok pt)
  | .error (.protocol e) => LibsignalTripleRatchet.recordResultAt A r (.error e)
  | .error e => apiErrAt A r e

/-! ## The encrypt entry's result (248 bytes)

`Option<Result<CiphertextMessage, SPE>>`: `PreKeySignalMessage` (248 bytes) is the dataful variant
at +0, so its word 0 is the inner message's `pq_ratchet` capacity (`≤ isize::MAX`, never a tag);
the other variants are tagged in word 0: `Some(Ok(SignalMessage))` = `2^63` with the message at +8,
`Some(Err)` = `-1` with the SPE at +8, `None` (pending, unreachable) = `-2`. -/

/-- `Some(Ok(CiphertextMessage::SignalMessage(_)))` word 0 (`2^63`). -/
def ctSignalTag : BitVec 64 := 0x8000000000000000#64

/-- The ghost of a `PreKeySignalMessage` in memory: the inner message's and the `Box` pointers. -/
structure PreKeyMsgGhost where
  msg : SignalMessageGhost
  serPtr : BitVec 64
  kyberPtr : BitVec 64

/-- `Option<u32>` at `a` (8 bytes, `pre_key_id: Option<PreKeyId>`): a `u32` tag (0 = `None`,
1 = `Some`) then the value (unspecified for `None`). -/
def optU32At (a : BitVec 64) : Option (BitVec 32) → SepProp
  | none => (a ↦₃₂ 0#32) ∗ memRegion (a + 4#64) 4
  | some v => (a ↦₃₂ 1#32) ∗ ((a + 4#64) ↦₃₂ v)

/-- `Option<KyberPayload>` at `a` (24 bytes): `KyberPayload { ciphertext: Box<[u8]> @0,
pre_key_id: u32 @0x10 }`; `None` = a null `ciphertext` pointer. -/
def optKyberAt (A : RustAlloc) (a ptr : BitVec 64) : Option KyberPayload → SepProp
  | none => (a ↦₆₄ 0#64) ∗ memRegion (a + 8#64) 16
  | some k => boxU8At A a ptr k.ciphertext ∗ ((a + 0x10#64) ↦₃₂ k.preKeyId) ∗ memRegion (a + 0x14#64) 4

/-- **A `PreKeySignalMessage` at `a` (248 bytes)** holding `m`: `message` @0 (`signalMessageAt`),
`pre_key_id` @0x78, `serialized: Box<[u8]>` @0x80, `kyber_payload` @0x90, `base_key` @0xa8,
`identity_key` @0xc8 (32 bytes each), `registration_id` @0xe8, `signed_pre_key_id` @0xec,
`message_version` @0xf0, 7 bytes padding. -/
def preKeyMsgAt (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64) (m : PreKeySignalMessage) :
    SepProp :=
  signalMessageAt A g.msg a m.message ∗ optU32At (a + 0x78#64) m.preKeyId ∗
    boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗ optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
    ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
    ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
    ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
    ((a + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0xf1#64) 7

/-- **The encrypt entry's result at `r` (248 bytes)** for the W0 result: a `SignalMessage` behind
`ctSignalTag`; a `PreKeySignalMessage` at +0; an error behind `errTag` with the SPE at +8: the
session-model errors as `speAt` (`InvalidState`'s function name `"encrypt"`, `OTR::encrypt`), the
W0 errors as `apiErrAt` (`SessionNotFound`'s op from W0, `"message_encrypt"`); a panic never
returns. -/
def apiEncResultAt (A : RustAlloc) (r : BitVec 64) :
    Except (ApiError AddrVal Unit) CiphertextMessage → SepProp
  | .ok (.signalMessage m) =>
    (r ↦₆₄ ctSignalTag) ∗ (∃∗ g : SignalMessageGhost, signalMessageAt A g (r + 8#64) m) ∗
      memRegion (r + 0x80#64) 120
  | .ok (.preKeySignalMessage m) => ∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g r m
  | .error (.protocol e) => (r ↦₆₄ errTag) ∗ speAt A (utf8 "encrypt") (r + 8#64) e ∗ memRegion (r + 56#64) 192
  | .error e => (r ↦₆₄ errTag) ∗ apiErrAt A (r + 8#64) e ∗ memRegion (r + 56#64) 192

end CryptoVerification.LibsignalPublicApiRepr
