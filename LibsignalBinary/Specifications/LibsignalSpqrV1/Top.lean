/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalTripleRatchet

/-!
# SPQR V1: top-level protocol model (`src/lib.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use only part of this file (see
`Computational/docs/TRUSTED_BASE.md`): the rest (`toSpqrRecvModel`, `SecretOutput` and its
accessors, `CurrentVersion` / `currentVersion`, `decodeVarintChecked`, `decodeVarintCheckedLoop`,
`sendPanicsB`, `recvPanicsSaltB`, and the error-conversion helpers `fromEncodingError`,
`fromSerializeError`, `fromAuthenticatorError` of `Error`, `SpqrApiError` and `SpqrApiResult`) is
checked by Lean.

Models `spqr/src/lib.rs` over `PqRatchetStatePB` and `SpqrApiDeps`: API records (`Params`, `Send`,
`Recv`), version and initialization (`stateVersion`, `decodeState`, `initInner`, `initialState`,
`currentVersion`), top-level `send` (`sendAfterStates`) and `recv`, explicit panic type
`SpqrApiPanic` and predicates (`sendPanicsPureB`, `recvPanicsB`), adapters `toSpqrModel` and
`toSpqrRecvModel` (DEV-SPQR2, DEV-LS25), empty-state agreement (`recv_empty_state`,
`toSpqrModel_recv_empty`, `not_toSpqrModel_recvPanics_empty`), and kernel-checked guards
(`guard_version_and_types`, `guard_varint_and_preamble`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)

/-! ## Core types and conversions (`src/lib.rs`) -/

/-- Session initialization parameters (`pub struct Params<'a>`, `src/lib.rs:55–61`). -/
structure Params where
  direction : Direction
  version : Version
  minVersion : Version
  authKey : Bytes
  chainParams : ChainParams := ChainParams.default
  deriving DecidableEq, Repr, Inhabited

/-- Step secret tagged by direction (`pub enum SecretOutput`, `src/lib.rs:72–85`). -/
inductive SecretOutput where
  | none
  | send (secret : Secret)
  | recv (secret : Secret)
  deriving DecidableEq, Repr, Inhabited

namespace SecretOutput

def sendSecret : SecretOutput → Option Secret
  | .send s => some s
  | .recv _ => Option.none
  | .none => Option.none

def recvSecret : SecretOutput → Option Secret
  | .send _ => Option.none
  | .recv s => some s
  | .none => Option.none

def secret : SecretOutput → Option Secret
  | .send s => some s
  | .recv s => some s
  | .none => Option.none

def hasSecret : SecretOutput → Bool
  | .none => false
  | .send _ => true
  | .recv _ => true

end SecretOutput

/-- Version negotiation status (`pub enum CurrentVersion`, `src/lib.rs:87–94`). -/
inductive CurrentVersion where
  | stillNegotiating (version : Version) (minVersion : Version)
  | negotiationComplete (version : Version)
  deriving DecidableEq, Repr, Inhabited

/-- Output of `send` (`pub struct Send`, `src/lib.rs:242–246`). -/
structure Send where
  state : SerializedState
  msg : SerializedMessage
  key : MessageKey
  deriving DecidableEq, Repr, Inhabited

/-- Output of `recv` (`pub struct Recv`, `src/lib.rs:327–330`). -/
structure Recv where
  state : SerializedState
  key : MessageKey
  deriving DecidableEq, Repr, Inhabited

namespace Error

def fromEncodingError : Error := .encodingDecoding

def fromSerializeError : Error := .serialization

def fromAuthenticatorError : Error := .macVerifyFailed

end Error

/-! ## Explicit panic sites and result types (`src/lib.rs`) -/

/-- Rust panic sites in `src/lib.rs` and its callees (`overflow-checks = true`). -/
inductive SpqrApiPanic where
  | chain (p : ChainPanic)
  | spqr (p : SpqrPanic)
  | v1
  /-- `src/lib.rs:292`: `assert!(key.is_none())` in `send` when `chain` is `None`. -/
  | sendKeySomeWithoutChain
  /-- `src/lib.rs:299`: `msg.epoch - 1` underflow in `send`. -/
  | sendEpochUnderflow
  /-- `src/lib.rs:305`: `assert!(!msg.is_empty())` in `send`. -/
  | sendMsgEmpty
  /-- `src/lib.rs:306`: `assert_eq!(msg[0], Version::V1.into())` in `send`. -/
  | sendMsgBadVersion
  /-- `src/lib.rs:425`: `assert!(current_version > 0 && version_still_negotiating)` in `recv`. -/
  | recvNegotiateAssert
  /-- `src/lib.rs:429`: `version_negotiation.as_ref().expect("still negotiating")` in `recv`. -/
  | recvExpectStillNegotiating
  /-- `src/lib.rs:433`: `msg.version.try_into().expect("should support all lower versions")` in `recv`. -/
  | recvExpectLowerVersion
  /-- `src/lib.rs:462`: `msg.epoch - 1` underflow in `recv`. -/
  | recvEpochUnderflow
  /-- `src/lib.rs:541`: `from[start_at + i]` bounds check in `decode_varint`. -/
  | decodeVarintBounds
  /-- `src/lib.rs:542`: `<< (7 * i as i32)` shift overflow when `7 * i >= 64` in `decode_varint`. -/
  | decodeVarintShiftOverflow
  deriving DecidableEq, Repr, Inhabited

/-- Outcome of a fallible top-level SPQR operation: clean `Err(Error)` or `SpqrApiPanic`. -/
inductive SpqrApiError where
  | err (e : Error)
  | panic (p : SpqrApiPanic)
  deriving DecidableEq, Repr, Inhabited

namespace SpqrApiError

def isPanic : SpqrApiError → Bool
  | .panic _ => true
  | .err _ => false

def ofChainError : ChainError → SpqrApiError
  | .err e => .err e
  | .panic p => .panic (.chain p)

end SpqrApiError

abbrev SpqrApiResult (α : Type) := Except SpqrApiError α

namespace SpqrApiResult

def ofError {α : Type} (r : Except Error α) : SpqrApiResult α :=
  match r with
  | .ok v => .ok v
  | .error e => .error (.err e)

def ofPanic {α : Type} (r : Except SpqrApiPanic α) : SpqrApiResult α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.panic p)

def ofChainPanic {α : Type} (r : Except ChainPanic α) : SpqrApiResult α :=
  match r with
  | .ok v => .ok v
  | .error p => .error (.panic (.chain p))

def ofChainResult {α : Type} (r : ChainResult α) : SpqrApiResult α :=
  match r with
  | .ok v => .ok v
  | .error ce => .error (SpqrApiError.ofChainError ce)

def isPanic {α : Type} (r : SpqrApiResult α) : Bool :=
  match r with
  | .ok _ => false
  | .error e => e.isPanic

end SpqrApiResult

/-! ## Explicit index/shift-checked `decode_varint` loop (`src/lib.rs:537–553`) -/

/-- Index-based loop of `decode_varint` (`src/lib.rs:537–553`) making `decodeVarintBounds` and
`decodeVarintShiftOverflow` explicit. -/
def decodeVarintCheckedLoop (fromBytes : Bytes) (startAt maxI i : Nat) (out : BitVec 64)
    (done : Bool) : SpqrApiResult (BitVec 64 × Nat) :=
  if _h : i < maxI && !done then
    match fromBytes[startAt + i]? with
    | none => .error (.panic .decodeVarintBounds)
    | some byte =>
      if 7 * i ≥ 64 then
        .error (.panic .decodeVarintShiftOverflow)
      else
        let shifted : BitVec 64 := ((byte.zeroExtend 64) &&& 0x7f#64) <<< (7 * i)
        let out' := out ||| shifted
        let i' := i + 1
        let done' := (byte &&& 0x80#8) == 0#8
        decodeVarintCheckedLoop fromBytes startAt maxI i' out' done'
  else
    if done then
      .ok (out, startAt + i)
    else
      .error (.err .msgDecode)
termination_by maxI - i
decreasing_by
  have hi : i < maxI := by
    cases Bool.and_eq_true_iff.mp _h with
    | intro h1 _ => exact of_decide_eq_true h1
  omega

/-- Index-based `decode_varint(from, &mut at)` (`src/lib.rs:524–554`). -/
def decodeVarintChecked (fromBytes : Bytes) (atIdx : Nat) : SpqrApiResult (BitVec 64 × Nat) :=
  let startAt := atIdx
  if startAt ≥ fromBytes.length then
    .error (.err .msgDecode)
  else
    let maxI := min MAX_VARINT_BYTES_LEN (fromBytes.length - startAt)
    decodeVarintCheckedLoop fromBytes startAt maxI 0 0#64 false

/-! ## `PqRatchetStatePB` and `SpqrApiDeps` dependency bundle -/

/-- `pqrpb::PqRatchetState` (`src/proto/pq_ratchet.proto:25–38`), parameterized by `V1StatePB`. -/
structure PqRatchetStatePB (V1StatePB : Type) where
  inner : Option V1StatePB := none
  versionNegotiation : Option VersionNegotiationPB := none
  chain : Option ChainPB := none
  deriving DecidableEq, Repr, Inhabited

/-- Abstract dependency bundle for `src/lib.rs` over `PqRatchetState` codecs (`Proto.lean`) and V1
`States` / `Message` operations (`States.lean`). -/
structure SpqrApiDeps where
  V1StatePB : Type
  decodeState : Bytes → Except Unit (PqRatchetStatePB V1StatePB)
  encodeState : PqRatchetStatePB V1StatePB → Bytes
  States : Type
  statesFromPb : V1StatePB → SpqrApiResult States
  statesIntoPb : States → V1StatePB
  MessageV1 : Type
  /-- `States::send(self, rng)` (`src/v1/chunked/states.rs:115–289`), returning
  `((msg, key, state), remainingTape)`. -/
  statesSend : States → Bytes → SpqrApiResult (MessageV1 × Option EpochSecret × States) × Bytes
  statesRecv : States → MessageV1 → SpqrApiResult (Option EpochSecret × States)
  msgSerialize : MessageV1 → BitVec 32 → Bytes
  msgDeserialize : Epoch → Bytes → SpqrApiResult MessageV1
  msgEpoch : MessageV1 → Epoch
  initV1Inner : Direction → Bytes → Except SpqrApiPanic V1StatePB

/-! ## `state_version`, `decode_state`, `init_inner`, `initial_state`, `current_version` -/

def stateVersion {V1StatePB : Type} (state : PqRatchetStatePB V1StatePB) : Version :=
  match state.inner with
  | none => .v0
  | some _ => .v1

/-- `spqr::decode_state` (`src/lib.rs:495–505`). -/
def decodeState (D : SpqrApiDeps) (s : SerializedState) :
    Except Error (PqRatchetStatePB D.V1StatePB) :=
  if s.isEmpty then
    .ok { inner := none, versionNegotiation := none, chain := none }
  else
    match D.decodeState s with
    | .ok st => .ok st
    | .error () => .error .stateDecode

def initInner (D : SpqrApiDeps) (v : Version) (d : Direction) (authKey : Bytes) :
    Except SpqrApiPanic (Option D.V1StatePB) :=
  match v with
  | .v0 => .ok none
  | .v1 => some <$> D.initV1Inner d authKey

/-- `spqr::initial_state` (`src/lib.rs:211–235`). -/
def initialState (D : SpqrApiDeps) (params : Params) : SpqrApiResult SerializedState :=
  match params.version with
  | .v0 => .ok emptyState
  | .v1 => do
    let inner ← SpqrApiResult.ofPanic (initInner D params.version params.direction params.authKey)
    let versionNegotiation : Option VersionNegotiationPB :=
      some {
        authKey := params.authKey
        direction := params.direction.toI32
        minVersion := params.minVersion.toI32
        chainParams := some params.chainParams.intoPb
      }
    .ok <| D.encodeState {
      inner := inner
      chain := none
      versionNegotiation := versionNegotiation
    }

/-- `spqr::current_version` (`src/lib.rs:248–261`). -/
def currentVersion (D : SpqrApiDeps) (state : SerializedState) : Except Error CurrentVersion := do
  let statePb ← decodeState D state
  let version := stateVersion statePb
  match statePb.versionNegotiation with
  | none => .ok (.negotiationComplete version)
  | some vn =>
    match Version.fromI32? vn.minVersion with
    | some minVer => .ok (.stillNegotiating version minVer)
    | none => .error .stateDecode

/-! ## `send` and `recv` (`src/lib.rs:264–486`) -/

/-- Continuation of `send` after `States::send` (`src/lib.rs:274–323`): updates the symmetric
chain, derives the message key, serializes the message, and re-encodes the state. -/
def sendAfterStates (D : SpqrApiDeps) (hkdf : HkdfFn)
    (statePb : PqRatchetStatePB D.V1StatePB)
    (msg : D.MessageV1) (key : Option EpochSecret) (state : D.States) : SpqrApiResult Send := do
  let chain : Option Chain ←
    match statePb.chain with
    | none =>
      match statePb.versionNegotiation with
      | some vn =>
        -- Signed `i32` comparison (`vn.min_version > Version::V0 as i32`).
        if BitVec.slt Version.v0.toI32 vn.minVersion then do
          let c ← SpqrApiResult.ofError (chainFromVersionNegotiation hkdf vn)
          pure (some c)
        else
          pure none
      | none => .error (.err .chainNotAvailable)
    | some pb => do
      let c ← SpqrApiResult.ofError (Chain.fromPb pb)
      pure (some c)
  let (index, msgKey, chainPb) ←
    match chain with
    | none =>
      if key.isNone then
        pure (0#32, ([] : Bytes), (none : Option ChainPB))
      else
        .error (.panic .sendKeySomeWithoutChain)
    | some chain0 => do
      let chain1 ←
        match key with
        | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
        | none => pure chain0
      let epoch := D.msgEpoch msg
      if epoch == 0#64 then
        .error (.panic .sendEpochUnderflow)
      else do
        let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64))
        pure (idx, mk, some chain2.intoPb)
  let msgBytes := D.msgSerialize msg index
  match msgBytes with
  | [] => .error (.panic .sendMsgEmpty)
  | b0 :: _ =>
    if b0 != Version.v1.toU8 then
      .error (.panic .sendMsgBadVersion)
    else
      let newStateBytes := D.encodeState {
        inner := some (D.statesIntoPb state)
        versionNegotiation := statePb.versionNegotiation
        chain := chainPb
      }
      let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
      .ok {
        state := newStateBytes
        msg := msgBytes
        key := outKey
      }

/-- `spqr::send` (`src/lib.rs:264–325`), returning `(result, remainingTape)`. -/
def send (D : SpqrApiDeps) (hkdf : HkdfFn) (state : SerializedState) (tape : Bytes) :
    SpqrApiResult Send × Bytes :=
  match decodeState D state with
  | .error e => (.error (.err e), tape)
  | .ok statePb =>
    match statePb.inner with
    | none =>
      (.ok { state := [], msg := [], key := none }, tape)
    | some pb =>
      match D.statesFromPb pb with
      | .error e => (.error e, tape)
      | .ok st0 =>
        let (sendRes, tape') := D.statesSend st0 tape
        match sendRes with
        | .error e => (.error e, tape')
        | .ok (msg, key, st1) =>
          (sendAfterStates D hkdf statePb msg key st1, tape')

/-- `spqr::recv` (`src/lib.rs:355–486`). In the `Ordering::Greater` branch (`src/lib.rs:383–420`),
`key` is wrapped in `some` unconditionally without filtering empty keys (`some []` when
`msg.index == 0`, DEV-SPQR2). -/
def recv (D : SpqrApiDeps) (hkdf : HkdfFn) (state : SerializedState) (msg : SerializedMessage) :
    SpqrApiResult Recv := do
  let msg ← SpqrApiResult.ofError (msgPreamble msg)
  let prenegotiatedStatePb ← SpqrApiResult.ofError (decodeState D state)
  let currentVersion : BitVec 8 := (stateVersion prenegotiatedStatePb).toU8
  let (minVersion, versionStillNegotiating) : BitVec 8 × Bool :=
    match prenegotiatedStatePb.versionNegotiation with
    | some vn => (vn.minVersion.truncate 8, true)
    | none => (currentVersion, currentVersion == 0#8)
  if msg.version < minVersion then
    .error (.err .minimumVersion)
  else if msg.version != currentVersion && !versionStillNegotiating then
    .error (.err .versionMismatch)
  else if currentVersion == 0#8 then
    .ok { state := [], key := none }
  else if msg.version > currentVersion then do
    let zeroEpoch : Epoch := 0#64
    let chain0 ←
      SpqrApiResult.ofError
        (chainFrom hkdf prenegotiatedStatePb.chain prenegotiatedStatePb.versionNegotiation)
    let (chain1, rawKey) ← SpqrApiResult.ofChainResult (chain0.recvKey hkdf zeroEpoch msg.index)
    let newStateBytes := D.encodeState {
      chain := some chain1.intoPb
      versionNegotiation := prenegotiatedStatePb.versionNegotiation
      inner := prenegotiatedStatePb.inner
    }
    .ok {
      key := some rawKey
      state := newStateBytes
    }
  else do
    let statePb : PqRatchetStatePB D.V1StatePB ←
      if msg.version == currentVersion then
        pure prenegotiatedStatePb
      else do
        if !(currentVersion > 0#8 && versionStillNegotiating) then
          .error (.panic .recvNegotiateAssert)
        else
          let vn ←
            match prenegotiatedStatePb.versionNegotiation with
            | some vn => pure vn
            | none => .error (.panic .recvExpectStillNegotiating)
          let v ←
            match Version.fromU8? msg.version with
            | some v => pure v
            | none => .error (.panic .recvExpectLowerVersion)
          let dir ←
            match Direction.fromI32? vn.direction with
            | some d => pure d
            | none => .error (.err .stateDecode)
          let inner' ← SpqrApiResult.ofPanic (initInner D v dir vn.authKey)
          let chain' ← SpqrApiResult.ofError (chainFrom hkdf prenegotiatedStatePb.chain (some vn))
          pure {
            inner := inner'
            versionNegotiation := none
            chain := some chain'.intoPb
          }
    match statePb.inner with
    | none =>
      .ok { state := [], key := none }
    | some pb => do
      let sckaMsg ← D.msgDeserialize msg.epoch msg.remaining
      let st0 ← D.statesFromPb pb
      let (key, st1) ← D.statesRecv st0 sckaMsg
      if msg.epoch == 0#64 then
        .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := msg.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom hkdf statePb.chain statePb.versionNegotiation)
        let chain1 ←
          match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
          | none => pure chain0
        let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey hkdf msgKeyEpoch msg.index)
        let newStateBytes := D.encodeState {
          inner := some (D.statesIntoPb st1)
          versionNegotiation := none
          chain := some chain2.intoPb
        }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        .ok {
          state := newStateBytes
          key := outKey
        }

/-! ## Bridging `Send` / `Recv` to `SpqrModel` and `SpqrRecvModel` (DEV-SPQR2) -/

/-- Converts a `MessageKey` (`Option Bytes`) to `Option Salt`: `none ↦ some none`, 32-byte `some k`
`↦ some (some ⟨k, h⟩)`, and any other length `↦ none`. -/
def messageKeyToSalt? : MessageKey → Option Salt
  | none => some none
  | some k =>
    if h : k.length = 32 then
      some (some ⟨k, h⟩)
    else
      none

/-- Converts a `recv` message key to `Option Salt`, mapping `some []` to `some none` (DEV-SPQR2,
DEV-LS25). -/
def recvKeyToSalt? (k : MessageKey) : Option Salt :=
  if k = some [] then some none else messageKeyToSalt? k

theorem recvKeyToSalt?_some_nil : recvKeyToSalt? (some []) = some none := rfl

theorem recvKeyToSalt?_of_ne {k : MessageKey} (h : k ≠ some []) :
    recvKeyToSalt? k = messageKeyToSalt? k := by
  unfold recvKeyToSalt?; simp [h]

theorem recvKeyToSalt?_of_isSome {k : MessageKey} (h : (messageKeyToSalt? k).isSome = true) :
    recvKeyToSalt? k = messageKeyToSalt? k := by
  refine recvKeyToSalt?_of_ne ?_
  rintro rfl
  simp [messageKeyToSalt?] at h

/-- `true` iff `send` panics or produces a non-32-byte `Some` key. -/
def sendPanicsB (D : SpqrApiDeps) (hkdf : HkdfFn) (stateBytes tape : Bytes) : Bool :=
  match (send D hkdf stateBytes tape).1 with
  | .ok s => (messageKeyToSalt? s.key).isNone
  | .error (.err _) => false
  | .error (.panic _) => true

/-- `true` iff `recv` panics or produces a `Some` key rejected by `recvKeyToSalt?` (DEV-SPQR2). -/
def recvPanicsSaltB (D : SpqrApiDeps) (hkdf : HkdfFn) (stateBytes msgBytes : Bytes) : Bool :=
  match recv D hkdf stateBytes msgBytes with
  | .ok r => (recvKeyToSalt? r.key).isNone
  | .error (.err _) => false
  | .error (.panic _) => true

/-- `true` iff `recv` returns `.error (.panic _)`. -/
def recvPanicsB (D : SpqrApiDeps) (hkdf : HkdfFn) (stateBytes msgBytes : Bytes) : Bool :=
  match recv D hkdf stateBytes msgBytes with
  | .ok _ => false
  | .error (.err _) => false
  | .error (.panic _) => true

/-- `true` iff `send` returns `.error (.panic _)`. -/
def sendPanicsPureB (D : SpqrApiDeps) (hkdf : HkdfFn) (stateBytes tape : Bytes) : Bool :=
  match (send D hkdf stateBytes tape).1 with
  | .ok _ => false
  | .error (.err _) => false
  | .error (.panic _) => true

/-- Packages `send` and `recv` as a `SpqrModel` (`LibsignalTripleRatchet.lean`), mapping `some []`
on `recv` to `none` via `recvKeyToSalt?` (DEV-SPQR2). -/
def toSpqrModel (D : SpqrApiDeps) (hkdf : HkdfFn) : SpqrModel where
  send := fun stateBytes tape =>
    match (send D hkdf stateBytes tape).1 with
    | .ok s =>
      match messageKeyToSalt? s.key with
      | some salt => some (s.state, salt, s.msg)
      | none => none
    | .error _ => none
  draws := fun stateBytes tape =>
    tape.length - (send D hkdf stateBytes tape).2.length
  recv := fun stateBytes msgBytes =>
    match recv D hkdf stateBytes msgBytes with
    | .ok r =>
      match recvKeyToSalt? r.key with
      | some salt => .ok (r.state, salt)
      | none => .error false
    | .error (.err e) => .error e.isStateDecode
    | .error (.panic _) => .error false
  recvPanics := fun stateBytes msgBytes =>
    recvPanicsB D hkdf stateBytes msgBytes
  sendPanics := fun stateBytes tape =>
    sendPanicsPureB D hkdf stateBytes tape

/-- Packages `recv` as a `SpqrRecvModel` (`Interface.lean`, DEV-SPQR2) preserving the exact
`Option Bytes` message key. -/
def toSpqrRecvModel (D : SpqrApiDeps) (hkdf : HkdfFn) : SpqrRecvModel where
  recv := fun stateBytes msgBytes =>
    match recv D hkdf stateBytes msgBytes with
    | .ok r => .ok (r.state, r.key)
    | .error (.err e) => .error e.isStateDecode
    | .error (.panic _) => .error false
  recvPanics := fun stateBytes msgBytes =>
    recvPanicsB D hkdf stateBytes msgBytes = true

/-! ## Empty-state agreement with `CryptoVerification.LibsignalSpqr.spqrRecvEmpty` -/

theorem recv_empty_state (D : SpqrApiDeps) (hkdf : HkdfFn) (msg : SerializedMessage) :
    recv D hkdf [] msg =
      if CryptoVerification.LibsignalSpqr.msgPreambleOk msg then
        .ok { state := [], key := none }
      else
        .error (.err .msgDecode) := by
  unfold recv
  rw [show msgPreamble msg = _ from msg_preamble_eq_msgPreamble? msg]
  rw [show decodeState D [] = .ok { inner := none, versionNegotiation := none, chain := none } from rfl]
  rw [CryptoVerification.LibsignalSpqr.msgPreambleOk]
  cases CryptoVerification.LibsignalSpqr.msgPreamble? msg with
  | none => rfl
  | some p =>
    dsimp only [SpqrApiResult.ofError, Bind.bind, Except.bind, stateVersion, Version.toU8]
    simp

theorem toSpqrModel_recv_empty (D : SpqrApiDeps) (hkdf : HkdfFn) (msg : SerializedMessage) :
    (toSpqrModel D hkdf).recv [] msg = CryptoVerification.LibsignalSpqr.spqrRecvEmpty msg := by
  simp only [toSpqrModel, recv_empty_state, CryptoVerification.LibsignalSpqr.spqrRecvEmpty]
  cases CryptoVerification.LibsignalSpqr.msgPreambleOk msg <;> rfl

theorem not_toSpqrModel_recvPanics_empty (D : SpqrApiDeps) (hkdf : HkdfFn) (msg : SerializedMessage) :
    ¬ (toSpqrModel D hkdf).recvPanics [] msg := by
  simp only [toSpqrModel, recvPanicsB, recv_empty_state]
  cases CryptoVerification.LibsignalSpqr.msgPreambleOk msg <;> decide

/-! ## Kernel-checked guards -/

section Guards

theorem guard_version_and_types :
    emptyState = [] ∧
      Version.DISABLED = .v0 ∧
      Version.MAX = .v1 ∧
      Version.v0.toU8 = 0#8 ∧
      Version.v1.toU8 = 1#8 ∧
      Version.fromU8? 0#8 = some .v0 ∧
      Version.fromU8? 1#8 = some .v1 ∧
      Version.fromU8? 2#8 = none ∧
      Version.tryFromU8 0#8 = .ok .v0 ∧
      Version.tryFromU8 1#8 = .ok .v1 ∧
      (Version.tryFromU8 2#8).isOk = false ∧
      Version.v0.toI32 = 0#32 ∧
      Version.v1.toI32 = 1#32 ∧
      Version.fromI32? 0#32 = some .v0 ∧
      Version.fromI32? 1#32 = some .v1 ∧
      Version.fromI32? 2#32 = none ∧
      SecretOutput.none.hasSecret = false ∧
      (SecretOutput.send [1#8]).sendSecret = some [1#8] ∧
      (SecretOutput.send [1#8]).recvSecret = none ∧
      (SecretOutput.recv [2#8]).recvSecret = some [2#8] ∧
      (SecretOutput.recv [2#8]).secret = some [2#8] ∧
      Error.stateDecode.isStateDecode = true ∧
      Error.msgDecode.isStateDecode = false ∧
      Error.fromEncodingError = .encodingDecoding ∧
      Error.fromSerializeError = .serialization ∧
      Error.fromAuthenticatorError = .macVerifyFailed := by
  decide +kernel

theorem guard_varint_and_preamble :
    encodeVarint 0#64 = [0x00#8] ∧
      encodeVarint 0x012c#64 = [0xac#8, 0x02#8] ∧
      encodeVarint 0xffffffffffffffff#64 = List.replicate 9 0xff#8 ++ [0x01#8] ∧
      decodeVarintAt [0xff#8, 0xac#8, 0x02#8, 0xff#8] 1 = .ok (0x012c#64, 3) ∧
      decodeVarintChecked [0xff#8, 0xac#8, 0x02#8, 0xff#8] 1 = .ok (0x012c#64, 3) ∧
      decodeVarint [0x00#8] = .ok (0#64, []) ∧
      decodeVarint [] = .error .msgDecode ∧
      decodeVarint (List.replicate 9 0xff#8 ++ [0x02#8]) =
        .ok (0x7fffffffffffffff#64, []) ∧
      decodeVarint (List.replicate 10 0x80#8 ++ [0x00#8]) = .error .msgDecode ∧
      decodeVarintCheckedLoop (List.replicate 11 0x80#8) 0 11 10 0#64 false =
        .error (.panic .decodeVarintShiftOverflow) ∧
      decodeVarintCheckedLoop [] 0 1 0 0#64 false =
        .error (.panic .decodeVarintBounds) ∧
      msgPreamble [] = .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } ∧
      msgPreamble [0x01#8, 0xac#8, 0x02#8, 0x03#8, 0x09#8] =
        .ok { version := 1#8, epoch := 300#64, index := 3#32, remaining := [0x09#8] } ∧
      msgPreamble [0x01#8, 0x00#8, 0x00#8] = .error .msgDecode ∧
      msgPreamble [0x01#8, 0x01#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x10#8] =
        .error .msgDecode := by
  decide +kernel

end Guards

end CryptoVerification.LibsignalSpqrV1
