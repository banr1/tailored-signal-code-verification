/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession

/-!
# libsignal's public session API over abstract stores

**Trusted in part.** The theorems of `Computational/Theorems/` use only `key`,
`PreKeySignalMessage`, `new`, `ProtoPreKeySignalMessage`, `encode`, `PendingPreKey`,
`PendingKyberPreKey`, `KyberPayload`, `varint`, `uint32Field`, `bytesField` from this file (the
pre-key message types and the `Prost` field encoders): read them. Everything else here (the session
API, its errors and store calls) and every proof is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Models the public entry points `messageEncrypt` (`session_management.rs:43–151`) and
`messageDecryptSignal` (`session_management.rs:297–354`) over the core session model of
`LibsignalSession.lean`:

* **Time and staleness**: `SystemTime` (`checkedAddSecs`, `lt`) and the 30-day unacknowledged
  session limit `maxUnacknowledgedSessionAge`.
* **Session records and `PreKeySignalMessage`**: `PendingPreKey`, `PendingKyberPreKey`, `Session`,
  `SessionRecord`, `KyberPayload`, `ProtoPreKeySignalMessage`, `PreKeySignalMessage`,
  `CiphertextMessage`, and concrete `Prost` wire encoders (`varint`, `key`, `uint32Field`,
  `bytesField`).
* **Stores and errors**: `Direction`, `IdentityChange`, `StoreAnswers`, `StoreCall`, `ApiError`,
  `Api`, `storeCall`, `liftProtocol`, and `execOk`. Each entry point invokes at most the four store
  methods (`loadSession`, `isTrustedIdentity`, `saveIdentity`, `storeSession`) in fixed order,
  taking their answers via `StoreAnswers` and emitting the executed `StoreCall` trace.
* **Scope and panics**: single current session (`previous_sessions = []`), `log::max_level() = Off`,
  distinct local and remote identity keys (`self_session = false`), canonical 33-byte stored keys,
  and `ApiError.panic` modeling `panic = "abort"` non-termination (`SystemTime` overflow or
  session-model `u32::MAX` overflow).
-/

@[expose] public section

namespace CryptoGames
namespace LibsignalSessionApi

open LibsignalSession

/-! ### Time (`std::time::SystemTime` on Linux) -/

/-- `std::time::SystemTime` on Linux: `SystemTime { t: Timespec }` (`std/sys/time/unix.rs:8–11`)
with `Timespec { tv_sec: i64, tv_nsec: Nanoseconds(u32) }` (`std/sys/pal/unix/time.rs:25–29`;
`tv_nsec < 10⁹` is the type's invariant). `tvSec` is read as a **signed** 64-bit integer. -/
structure SystemTime where
  /-- `tv_sec` (`i64`): seconds since the Unix epoch. -/
  tvSec : BitVec 64
  /-- `tv_nsec` (`u32`, `< 10⁹`): nanoseconds. -/
  tvNsec : BitVec 32
  deriving DecidableEq, Repr

namespace SystemTime

/-- `SystemTime::UNIX_EPOCH` (`tv_sec = 0`, `tv_nsec = 0`). -/
def unixEpoch : SystemTime := ⟨0, 0⟩

/-- `t.checked_add(Duration::from_secs(secs))` (`std/time.rs`, `SystemTime::checked_add`, i.e.
`Timespec::checked_add_duration`, `std/sys/pal/unix/time.rs:145–157`) for a whole number of
seconds: `tv_sec.checked_add_unsigned(secs)`; `none` if the sum exceeds `i64::MAX`. With zero
sub-second nanoseconds the nanosecond carry of `checked_add_duration` cannot happen. `t + d`
(`impl Add<Duration> for SystemTime`, `std/time.rs:738–748`) panics exactly when this is
`none`. -/
def checkedAddSecs (t : SystemTime) (secs : ℕ) : Option SystemTime :=
  if t.tvSec.toInt + secs ≤ 2 ^ 63 - 1 then some ⟨BitVec.ofInt 64 (t.tvSec.toInt + secs), t.tvNsec⟩
  else none

/-- `a < b` for `SystemTime`: the derived lexicographic order on `(tv_sec, tv_nsec)`
(`#[derive(PartialOrd)]` on `SystemTime`, `std/sys/time/unix.rs:8`, and on `Timespec`,
`std/sys/pal/unix/time.rs:25`), `tv_sec` signed, `tv_nsec` unsigned. -/
def lt (a b : SystemTime) : Bool :=
  a.tvSec.slt b.tvSec || (a.tvSec == b.tvSec && a.tvNsec < b.tvNsec)

end SystemTime

/-- `consts::MAX_UNACKNOWLEDGED_SESSION_AGE = Duration::from_secs(60 * 60 * 24 * 30)`
(`consts.rs:25`): 30 days, in seconds. -/
def maxUnacknowledgedSessionAge : ℕ := 60 * 60 * 24 * 30

/-! ### The session record (`state/session.rs`, `proto/storage.proto`) -/

/-- `session_structure::PendingPreKey` (`proto/storage.proto:35–40`), as
`unacknowledged_pre_key_message_items` reads it (`state/session.rs:549–564`). -/
structure PendingPreKey where
  /-- `pre_key_id` (`optional uint32`; `PreKeyId`). -/
  preKeyId : Option (BitVec 32)
  /-- `signed_pre_key_id` (stored as `int32`, read back `as u32`, the same 32 bits;
  `SignedPreKeyId`). -/
  signedPreKeyId : BitVec 32
  /-- `base_key`, deserialized (see "Deviations"). -/
  baseKey : PublicKey
  /-- `timestamp` (`uint64`): seconds since the Unix epoch when the session was created. -/
  timestamp : BitVec 64
  deriving DecidableEq

/-- `session_structure::PendingKyberPreKey` (`proto/storage.proto:42–45`): the Kyber pre-key id
(`KyberPreKeyId`) and the KEM (key encapsulation mechanism) ciphertext of an unacknowledged PQXDH
session. -/
structure PendingKyberPreKey where
  /-- `pre_key_id` (`uint32`). -/
  preKeyId : BitVec 32
  /-- `ciphertext` (bytes). -/
  ciphertext : List (BitVec 8)
  deriving DecidableEq

/-- A current session: the session model's `SessionState` (the ratchet-relevant part of
`SessionStructure`) and the `SessionStructure` fields it leaves out (`state/session.rs:146–171`;
the field list is `proto/storage.proto:10–68`). Together they are the whole `SessionStructure`. -/
structure Session (PQ : Type) where
  /-- The session model's session state. Its `pendingPreKey` flag is not read by the API (see
  `Session.Wf`). -/
  state : SessionState PQ
  /-- `pending_pre_key`: `some` while the session is unacknowledged (locally initiated, no reply
  decrypted yet). -/
  pendingPreKey : Option PendingPreKey
  /-- `pending_kyber_pre_key`. -/
  pendingKyberPreKey : Option PendingKyberPreKey
  /-- `local_registration_id` (`u32`). -/
  localRegistrationId : BitVec 32
  /-- `remote_registration_id` (`u32`; carried along, not read by the API). -/
  remoteRegistrationId : BitVec 32
  /-- `alice_base_key` (bytes; carried along, not read by the API). -/
  aliceBaseKey : List (BitVec 8)
  deriving DecidableEq

/-- The invariant of a `Session` decoded from a `SessionStructure`: the session model's flag is
`pending_pre_key.is_some()`, which the two fields here both describe. -/
def Session.Wf {PQ : Type} (s : Session PQ) : Prop :=
  s.state.pendingPreKey = s.pendingPreKey.isSome

/-- `SessionRecord { current_session, previous_sessions }` (`state/session.rs:705–708`) with
`previous_sessions = []` (see "Scope" in the module docstring). -/
structure SessionRecord (PQ : Type) where
  /-- `current_session` (`None` for a fresh record, `SessionRecord::new_fresh`). -/
  currentSession : Option (Session PQ)
  deriving DecidableEq

/-! ### `PreKeySignalMessage` and `CiphertextMessage` (`protocol.rs`) -/

/-- `KyberPayload { pre_key_id, ciphertext }` (`protocol.rs:311–323`). -/
structure KyberPayload where
  /-- `pre_key_id` (`KyberPreKeyId`, `u32`). -/
  preKeyId : BitVec 32
  /-- `ciphertext` (`kem::SerializedCiphertext`). -/
  ciphertext : List (BitVec 8)
  deriving DecidableEq

/-- prost's `proto::wire::PreKeySignalMessage` (`proto/wire.proto:19–28`, proto2: every field is
optional). -/
structure ProtoPreKeySignalMessage where
  /-- Field 5. -/
  registrationId : Option (BitVec 32)
  /-- Field 1. -/
  preKeyId : Option (BitVec 32)
  /-- Field 6. -/
  signedPreKeyId : Option (BitVec 32)
  /-- Field 7. -/
  kyberPreKeyId : Option (BitVec 32)
  /-- Field 8. -/
  kyberCiphertext : Option (List (BitVec 8))
  /-- Field 2. -/
  baseKey : Option (List (BitVec 8))
  /-- Field 3. -/
  identityKey : Option (List (BitVec 8))
  /-- Field 4 (the serialized inner `SignalMessage`). -/
  message : Option (List (BitVec 8))
  deriving DecidableEq

/-! prost 0.14.4's wire encoding (`prost/src/encoding.rs`, `encoding/varint.rs`), only what the
`PreKeySignalMessage` encoder needs. Cited as `prost/…` from the crate root. -/

namespace Prost

/-- `encode_varint` (`prost/src/encoding/varint.rs:11–22`): base-128 (LEB128), 7 bits per byte,
least significant group first, the high bit set on every byte but the last. -/
def varint (n : ℕ) : List (BitVec 8) :=
  if h : n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128)
termination_by n
decreasing_by omega

/-- `encode_key` (`prost/src/encoding.rs:106–110`): the varint of `tag << 3 | wire_type`. -/
def key (tag wireType : ℕ) : List (BitVec 8) := varint (8 * tag + wireType)

/-- An `optional uint32` field (`uint32::encode`: the `varint!` macro,
`prost/src/encoding.rs:263–266`, at `:356`): nothing for `None`; else key (wire type 0, varint) and
the value as a varint. -/
def uint32Field (tag : ℕ) : Option (BitVec 32) → List (BitVec 8)
  | none => []
  | some v => key tag 0 ++ varint v.toNat

/-- An `optional bytes` field (`bytes::encode`, `prost/src/encoding.rs:691–695`): nothing for
`None`; else key (wire type 2, length-delimited), the length as a varint, the bytes. -/
def bytesField (tag : ℕ) : Option (List (BitVec 8)) → List (BitVec 8)
  | none => []
  | some b => key tag 2 ++ varint b.length ++ b

end Prost

/-- **prost's encoder for `proto::wire::PreKeySignalMessage`** (`Message::encode`, infallible into a
`Vec`: `expect("can always append to a Vec")`): the fields in **ascending tag order** (prost-derive
sorts the fields by tag, `prost-derive/src/lib.rs:91`), each `Some` field emitted, each `None`
omitted. Concrete, unlike the session model's abstract `SignalMessage` codec; checked byte-exactly
by the KATs (known-answer tests). -/
def ProtoPreKeySignalMessage.encode (m : ProtoPreKeySignalMessage) : List (BitVec 8) :=
  Prost.uint32Field 1 m.preKeyId ++
  Prost.bytesField 2 m.baseKey ++
  Prost.bytesField 3 m.identityKey ++
  Prost.bytesField 4 m.message ++
  Prost.uint32Field 5 m.registrationId ++
  Prost.uint32Field 6 m.signedPreKeyId ++
  Prost.uint32Field 7 m.kyberPreKeyId ++
  Prost.bytesField 8 m.kyberCiphertext

/-- `PreKeySignalMessage` (`protocol.rs:326–338`), with `serialized = versionByte ‖ protobuf`. -/
structure PreKeySignalMessage where
  messageVersion : BitVec 8
  registrationId : BitVec 32
  preKeyId : Option (BitVec 32)
  signedPreKeyId : BitVec 32
  kyberPayload : Option KyberPayload
  baseKey : PublicKey
  identityKey : IdentityKey
  /-- Inner `SignalMessage`. -/
  message : SignalMessage
  serialized : List (BitVec 8)
  deriving DecidableEq

/-- **`PreKeySignalMessage::new`** (`protocol.rs:341–379`): the protobuf with every field `Some`
except `pre_key_id` and the two Kyber fields (`None` without a Kyber payload), the inner message's
`serialized` bytes as `message`, behind the version byte `((message_version & 0xF) << 4) | 4`
(the session model's `versionByte`). Infallible: upstream returns `Ok` unconditionally. -/
def PreKeySignalMessage.new (messageVersion : BitVec 8)
    (registrationId : BitVec 32) (preKeyId : Option (BitVec 32)) (signedPreKeyId : BitVec 32)
    (kyberPayload : Option KyberPayload) (baseKey : PublicKey) (identityKey : IdentityKey)
    (message : SignalMessage) : PreKeySignalMessage :=
  let protoMessage : ProtoPreKeySignalMessage :=
    { registrationId := some registrationId, preKeyId, signedPreKeyId := some signedPreKeyId,
      kyberPreKeyId := kyberPayload.map (·.preKeyId),
      kyberCiphertext := kyberPayload.map (·.ciphertext),
      baseKey := some baseKey.serialize, identityKey := some identityKey.serialize,
      message := some message.serialized }
  { messageVersion, registrationId, preKeyId, signedPreKeyId, kyberPayload, baseKey, identityKey,
    message, serialized := versionByte messageVersion :: protoMessage.encode }

/-- `CiphertextMessage` (`protocol.rs:25–30`), restricted to the two variants `message_encrypt`
returns. -/
inductive CiphertextMessage where
  /-- `CiphertextMessage::SignalMessage`. -/
  | signalMessage (m : SignalMessage)
  /-- `CiphertextMessage::PreKeySignalMessage`. -/
  | preKeySignalMessage (m : PreKeySignalMessage)
  deriving DecidableEq

/-! ### Stores (`storage/traits.rs`) -/

/-- `Direction` (`storage/traits.rs:25–30`), the role passed to `is_trusted_identity`. -/
inductive Direction where
  /-- `Direction::Sending`. -/
  | sending
  /-- `Direction::Receiving`. -/
  | receiving
  deriving DecidableEq, Repr

/-- `IdentityChange` (`storage/traits.rs:36–41`), the answer of `save_identity` (ignored by both
entry points). -/
inductive IdentityChange where
  /-- `IdentityChange::NewOrUnchanged`. -/
  | newOrUnchanged
  /-- `IdentityChange::ReplacedExisting`. -/
  | replacedExisting
  deriving DecidableEq, Repr

/-- **The answers of the store calls** (see the module docstring): one per method; an entry point
uses an answer only if it makes that call. `E` is the store's error. -/
structure StoreAnswers (PQ E : Type) where
  /-- `SessionStore::load_session(address) -> Result<Option<SessionRecord>>`. -/
  loadSession : Except E (Option (SessionRecord PQ))
  /-- `IdentityKeyStore::is_trusted_identity(address, identity, direction) -> Result<bool>`. -/
  isTrustedIdentity : Except E Bool
  /-- `IdentityKeyStore::save_identity(address, identity) -> Result<IdentityChange>`. -/
  saveIdentity : Except E IdentityChange
  /-- `SessionStore::store_session(address, record) -> Result<()>`. -/
  storeSession : Except E Unit

/-- **A store call** with its arguments, as recorded in the trace. -/
inductive StoreCall (Addr PQ : Type) where
  /-- `session_store.load_session(address)`. -/
  | loadSession (address : Addr)
  /-- `identity_store.is_trusted_identity(address, identity, direction)`. -/
  | isTrustedIdentity (address : Addr) (identity : IdentityKey) (direction : Direction)
  /-- `identity_store.save_identity(address, identity)`. -/
  | saveIdentity (address : Addr) (identity : IdentityKey)
  /-- `session_store.store_session(address, record)`. -/
  | storeSession (address : Addr) (record : SessionRecord PQ)
  deriving DecidableEq

/-! ### Errors and the API monad -/

/-- The errors of the two entry points: those of the session model, the API's own, and the
store's. -/
inductive ApiError (Addr E : Type) where
  /-- **A Rust panic**: the binary does not return (`panic = "abort"`, see the module docstring).
  Not a returned error. -/
  | panic
  /-- An error of the session model (`SignalProtocolError` other than its `panic`), propagated by
  `?`. -/
  | protocol (e : SignalProtocolError)
  /-- `SignalProtocolError::SessionNotFound(SessionNotFound::new(address, op))` (`error.rs:69,
  110–126`); `op` is upstream's `&'static str` (`"message_encrypt"`, `"message_decrypt_signal"`). -/
  | sessionNotFound (address : Addr) (op : String)
  /-- `SignalProtocolError::UntrustedIdentity(address)` (`error.rs:51`). -/
  | untrustedIdentity (address : Addr)
  /-- An error returned by a store call, propagated unchanged by `?`. -/
  | store (e : E)
  deriving DecidableEq

/-- An entry point's computation: may fail with an `ApiError`, and records its store calls. The
trace is kept on error too (it is what the stores have seen). -/
abbrev Api (Addr PQ E α : Type) := ExceptT (ApiError Addr E) (StateM (List (StoreCall Addr PQ))) α

/-- Run an `Api` computation from the empty trace: (result, trace). -/
def Api.run {Addr PQ E α : Type} (m : Api Addr PQ E α) :
    Except (ApiError Addr E) α × List (StoreCall Addr PQ) :=
  (ExceptT.run m).run []

/-- Make a store call: append it to the trace, then return its answer (an error answer is
propagated, `.await?`). -/
def storeCall {Addr PQ E α : Type} (call : StoreCall Addr PQ) (answer : Except E α) :
    Api Addr PQ E α := do
  modify (· ++ [call])
  match answer with
  | .ok a => pure a
  | .error e => throw (.store e)

/-- An error of the session model as an `ApiError`: its `panic` is the top-level `ApiError.panic`,
every other error is propagated as `ApiError.protocol`. -/
def ApiError.ofProtocol {Addr E : Type} : SignalProtocolError → ApiError Addr E
  | .panic => .panic
  | e => .protocol e

/-- Propagate an error of the session model (`?` on a `Result<_, SignalProtocolError>`; a
session-model panic is a panic). -/
def liftProtocol {Addr PQ E α : Type} : Except SignalProtocolError α → Api Addr PQ E α
  | .ok a => pure a
  | .error e => throw (ApiError.ofProtocol e)

/-- Run a session-model `Mut` method and return its result with the final state; on error the state
is dropped (every caller here discards it, as upstream discards the mutated local). -/
def execOk {σ α : Type} (m : Mut σ α) (s : σ) : Except SignalProtocolError (α × σ) :=
  match Mut.exec m s with
  | (.ok a, s') => .ok (a, s')
  | (.error e, _) => .error e

/-! ### `message_encrypt` -/

/-- `message_encrypt` (`session_management.rs:43–151`): loads the session, checks 30-day pending
pre-key staleness against `now`, encrypts via `OutgoingTripleRatchet.encrypt` (wrapping in
`PreKeySignalMessage` when unacknowledged), checks and saves the remote identity, and stores the
updated `SessionRecord`. -/
def messageEncrypt {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (codec : SignalMessageProtoCodec)
    (spqr : Spqr PQ PQC)
    (serializeAddresses : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ptext : List (BitVec 8)) (remoteAddress localAddress : Addr)
    (now : SystemTime) (coins : PQC) :
    Except (ApiError Addr E) CiphertextMessage × List (StoreCall Addr PQ) := Api.run do
  let some record ← storeCall (.loadSession remoteAddress) answers.loadSession
    | throw (.sessionNotFound remoteAddress "message_encrypt")
  let some session := record.currentSession
    | throw (.sessionNotFound remoteAddress "message_encrypt")
  let (otr, taken) ← liftProtocol (execOk OutgoingTripleRatchet.fromSessionState session.state)
  let some theirIdentityKey := taken.remoteIdentity | throw .panic
  let (message, otr) ← match session.pendingPreKey with
    | some items => do
      let some timestamp := SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat
        | throw .panic
      let some expiry := timestamp.checkedAddSecs maxUnacknowledgedSessionAge
        | throw .panic
      if expiry.lt now then throw (.sessionNotFound remoteAddress "message_encrypt")
      let kyberPayload := session.pendingKyberPreKey.map fun k => ⟨k.preKeyId, k.ciphertext⟩
      let (signalMessage, otr) ← liftProtocol (execOk (OutgoingTripleRatchet.encrypt C codec spqr
        ptext (serializeAddresses localAddress remoteAddress) coins) otr)
      pure (CiphertextMessage.preKeySignalMessage (PreKeySignalMessage.new
        otr.sessionVersion session.localRegistrationId items.preKeyId items.signedPreKeyId
        kyberPayload items.baseKey otr.localIdentityKey signalMessage), otr)
    | none => do
      let (signalMessage, otr) ← liftProtocol
        (execOk (OutgoingTripleRatchet.encrypt C codec spqr ptext none coins) otr)
      pure (CiphertextMessage.signalMessage signalMessage, otr)
  let trusted ← storeCall (.isTrustedIdentity remoteAddress theirIdentityKey .sending)
    answers.isTrustedIdentity
  if !trusted then throw (.untrustedIdentity remoteAddress)
  let _ ← storeCall (.saveIdentity remoteAddress theirIdentityKey) answers.saveIdentity
  let record : SessionRecord PQ :=
    { currentSession := some { session with state := otr.applyToSessionState taken } }
  storeCall (.storeSession remoteAddress record) answers.storeSession
  return message

/-! ### `message_decrypt_signal` -/

/-- `try_decrypt_from_record` (`session_management.rs:368–556`, `Whisper`, no previous sessions):
runs `SessionState.tryDecryptFromRecord` on the current session and clears `pendingPreKey` and
`pendingKyberPreKey` on success. -/
def SessionRecord.tryDecryptFromRecord {PQ PQC : Type} [Inhabited PQ] (C : Crypto)
    (spqr : Spqr PQ PQC) (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage)
    (coins : BitVec 256) (record : SessionRecord PQ) :
    Except SignalProtocolError (List (BitVec 8) × SessionRecord PQ) :=
  match record.currentSession with
  | none => .error (.invalidMessage .whisper .decryptionFailed)
  | some session =>
    match SessionState.tryDecryptFromRecord C spqr expected ciphertext .whisper coins
        session.state with
    | (.ok ptext, state) =>
      let updated : Session PQ :=
        { session with state := state, pendingPreKey := none, pendingKyberPreKey := none }
      .ok (ptext, { currentSession := some updated })
    | (.error e, _) => .error e

/-- `message_decrypt_signal` (`session_management.rs:297–354`): loads the session, decrypts
`ciphertext` via `SessionRecord.tryDecryptFromRecord`, checks and saves the remote identity, and
stores the updated `SessionRecord`. -/
def messageDecryptSignal {Addr PQ PQC E : Type} [Inhabited PQ] (C : Crypto) (spqr : Spqr PQ PQC)
    (serializeAddresses : Addr → Addr → Option (List (BitVec 8)))
    (answers : StoreAnswers PQ E) (ciphertext : SignalMessage) (remoteAddress localAddress : Addr)
    (coins : BitVec 256) :
    Except (ApiError Addr E) (List (BitVec 8)) × List (StoreCall Addr PQ) := Api.run do
  let some record ← storeCall (.loadSession remoteAddress) answers.loadSession
    | throw (.sessionNotFound remoteAddress "message_decrypt_signal")
  let (ptext, record) ← liftProtocol (record.tryDecryptFromRecord C spqr
    (serializeAddresses remoteAddress localAddress) ciphertext coins)
  let some session := record.currentSession | throw .panic
  let some theirIdentityKey := session.state.remoteIdentity | throw .panic
  let trusted ← storeCall (.isTrustedIdentity remoteAddress theirIdentityKey .receiving)
    answers.isTrustedIdentity
  if !trusted then throw (.untrustedIdentity remoteAddress)
  let _ ← storeCall (.saveIdentity remoteAddress theirIdentityKey) answers.saveIdentity
  storeCall (.storeSession remoteAddress record) answers.storeSession
  return ptext

end LibsignalSessionApi
end CryptoGames
