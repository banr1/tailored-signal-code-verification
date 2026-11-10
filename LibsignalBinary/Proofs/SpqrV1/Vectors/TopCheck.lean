/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top

/-!
# Executable Guards for `Wire.lean` and `Top.lean`

Instantiates `SpqrApiDeps` with a self-contained stub V1 state machine (`StubStates`) to check:
* version-negotiation branches (including `Ordering::Greater` with `msg.index == 0` -> `some []`,
  `DEV-SPQR2`, `vn.min_version` casts, and V0 shortcuts);
* `encode_varint`, `decode_varint`, `decode_varint_at`, `decodeVarintCheckedLoop`, and
  `msg_preamble` boundary and overflow cases;
* `send` / `recv` error precedence, RNG draw counts, panic sites, `toSpqrModel`, and
  `toSpqrRecvModel`;
* translations of the unit tests in `src/lib.rs` (`mod lib_test`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.TopCheck

open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalSpqrV1

/-! ## Concrete test HKDF -/

/-- Fast, deterministic, domain-separated `HkdfFn` for executable protocol guards.
Produces `okmLen` bytes uniquely determined by `(salt, ikm, info)`. -/
def testHkdf : HkdfFn := fun salt ikm info okmLen =>
  let foldTag (seed : BitVec 32) (bs : Bytes) : BitVec 32 :=
    bs.foldl (fun acc (b : BitVec 8) => (acc * 16777619#32) ^^^ (b.zeroExtend 32 + 0x9e3779b9#32)) seed
  let h0 := foldTag 0x811c9dc5#32 salt
  let h1 := foldTag (h0 ^^^ 0x11111111#32) ikm
  let h2 := foldTag (h1 ^^^ 0x22222222#32) info
  (List.range okmLen).map fun i =>
    let w := h2 + BitVec.ofNat 32 (i * 0x45d9f3b + 1)
    (w ^^^ (w >>> 16) ^^^ (w >>> 8)).truncate 8

/-! ## Stub V1 State Machine and Bijective State Codec for `SpqrApiDeps` -/

/-- Mode tag controlling stub `States` behavior (normal protocol operation vs fault injection for
error-precedence and panic guards). -/
inductive StubMode where
  /-- Normal V1 state at `epoch` (starts at `1#64`). Never emits an `EpochSecret` unless advancing. -/
  | normal
  /-- On `send`, emits `EpochSecret { epoch := epoch, secret := [epoch] }` and increments `epoch`
  for future sends; on `recv` of a message with `payloadTag == 2#8`, emits the same `EpochSecret`
  and increments `epoch`. -/
  | ratchet
  /-- `States::from_pb` returns `Err(Error::StateDecode)`. -/
  | errFromPbStateDecode
  /-- `States::from_pb` returns `Err(Error::Serialization)`. -/
  | errFromPbSerialization
  /-- `States::from_pb` panics with `SpqrApiPanic.v1`. -/
  | panicFromPbV1
  /-- `States::send` consumes 3 RNG bytes and returns `Err(Error::EncodingDecoding)`. -/
  | errSendEncoding
  /-- `States::send` consumes 3 RNG bytes and panics with `SpqrApiPanic.v1`. -/
  | panicSendV1
  /-- `States::send` returns `key = Some(EpochSecret { epoch: 1, secret: [9] })` (triggers
  `assert!(key.is_none())` at `src/lib.rs:292` when `chain` is `None`). -/
  | sendKeySome
  /-- `States::send` returns a message with `epoch = 0` (triggers `msg.epoch - 1` underflow panic
  at `src/lib.rs:299`). -/
  | sendEpochZero
  /-- `States::send` returns a message whose `serialize` produces `[]` (triggers
  `assert!(!msg.is_empty())` at `src/lib.rs:305`). -/
  | sendSerializeEmpty
  /-- `States::send` returns a message whose `serialize` starts with version byte `0x02` (triggers
  `assert_eq!(msg[0], Version::V1.into())` at `src/lib.rs:306`). -/
  | sendSerializeBadVer
  /-- `States::send` returns `key = Some(EpochSecret { epoch: 99, secret: [7] })` (triggers
  `Chain::add_epoch` mismatch panic `ChainPanic.addEpochMismatch` at `src/chain.rs:361`). -/
  | sendBadEpochSecret
  /-- `States::recv` returns `Err(Error::MacVerifyFailed)`. -/
  | errRecvMac
  /-- `States::recv` panics with `SpqrApiPanic.v1`. -/
  | panicRecvV1
  /-- `States::recv` returns `key = Some(EpochSecret { epoch: 99, secret: [7] })` (triggers
  `Chain::add_epoch` mismatch panic in `recv` at `src/lib.rs:465`). -/
  | recvBadEpochSecret
  deriving DecidableEq, Repr, Inhabited

namespace StubMode

def toByte : StubMode → BitVec 8
  | .normal => 0#8
  | .ratchet => 1#8
  | .errFromPbStateDecode => 2#8
  | .errFromPbSerialization => 3#8
  | .panicFromPbV1 => 4#8
  | .errSendEncoding => 5#8
  | .panicSendV1 => 6#8
  | .sendKeySome => 7#8
  | .sendEpochZero => 8#8
  | .sendSerializeEmpty => 9#8
  | .sendSerializeBadVer => 10#8
  | .sendBadEpochSecret => 11#8
  | .errRecvMac => 12#8
  | .panicRecvV1 => 13#8
  | .recvBadEpochSecret => 14#8

def fromByte? : BitVec 8 → Option StubMode
  | 0#8 => some .normal
  | 1#8 => some .ratchet
  | 2#8 => some .errFromPbStateDecode
  | 3#8 => some .errFromPbSerialization
  | 4#8 => some .panicFromPbV1
  | 5#8 => some .errSendEncoding
  | 6#8 => some .panicSendV1
  | 7#8 => some .sendKeySome
  | 8#8 => some .sendEpochZero
  | 9#8 => some .sendSerializeEmpty
  | 10#8 => some .sendSerializeBadVer
  | 11#8 => some .sendBadEpochSecret
  | 12#8 => some .errRecvMac
  | 13#8 => some .panicRecvV1
  | 14#8 => some .recvBadEpochSecret
  | _ => none

end StubMode

structure StubV1StatePB where
  dir : Direction := .a2b
  epoch : Epoch := 1#64
  step : BitVec 32 := 0#32
  mode : StubMode := .normal
  deriving DecidableEq, Repr, Inhabited

structure StubStates where
  dir : Direction := .a2b
  epoch : Epoch := 1#64
  step : BitVec 32 := 0#32
  mode : StubMode := .normal
  deriving DecidableEq, Repr, Inhabited

/-- Stub V1 message (`MessageV1`).
`serKind = 0` is normal (`[1, ...epoch, ...index, payloadTag]`),
`serKind = 1` serializes to `[]` (testing `:305` panic),
`serKind = 2` serializes with leading byte `2#8` (testing `:306` panic). -/
structure StubMsg where
  epoch : Epoch := 1#64
  payloadTag : BitVec 8 := 1#8
  serKind : BitVec 8 := 0#8
  deriving DecidableEq, Repr, Inhabited

/-! ### Self-contained byte codec for `PqRatchetStatePB StubV1StatePB` -/

def putU32 (v : BitVec 32) (acc : Bytes) : Bytes :=
  encodeVarint (v.zeroExtend 64) acc

def getU32 (bs : Bytes) (atIdx : Nat) : Option (BitVec 32 × Nat) :=
  match decodeVarintAt bs atIdx with
  | .ok (v, at') =>
    if v.toNat < 2 ^ 32 then some (v.truncate 32, at') else none
  | .error _ => none

def putU64 (v : BitVec 64) (acc : Bytes) : Bytes :=
  encodeVarint v acc

def getU64 (bs : Bytes) (atIdx : Nat) : Option (BitVec 64 × Nat) :=
  match decodeVarintAt bs atIdx with
  | .ok (v, at') => some (v, at')
  | .error _ => none

def putBytes (b : Bytes) (acc : Bytes) : Bytes :=
  encodeVarint (BitVec.ofNat 64 b.length) acc ++ b

def getBytes (bs : Bytes) (atIdx : Nat) : Option (Bytes × Nat) := do
  let (len64, at1) ← getU64 bs atIdx
  let len := len64.toNat
  if at1 + len ≤ bs.length then
    some ((bs.drop at1).take len, at1 + len)
  else
    none

def putOpt {α : Type} (put : α → Bytes → Bytes) (o : Option α) (acc : Bytes) : Bytes :=
  match o with
  | none => acc ++ [0#8]
  | some v => put v (acc ++ [1#8])

def getOpt {α : Type} (get : Bytes → Nat → Option (α × Nat)) (bs : Bytes) (atIdx : Nat) :
    Option (Option α × Nat) := do
  let tag ← bs[atIdx]?
  if tag == 0#8 then
    some (none, atIdx + 1)
  else if tag == 1#8 then do
    let (v, at') ← get bs (atIdx + 1)
    some (some v, at')
  else
    none

def putChainParamsPB (p : ChainParamsPB) (acc : Bytes) : Bytes :=
  putU32 p.maxOooKeys (putU32 p.maxJump acc)

def getChainParamsPB (bs : Bytes) (atIdx : Nat) : Option (ChainParamsPB × Nat) := do
  let (mj, at1) ← getU32 bs atIdx
  let (mo, at2) ← getU32 bs at1
  some ({ maxJump := mj, maxOooKeys := mo }, at2)

def putVersionNegotiationPB (vn : VersionNegotiationPB) (acc : Bytes) : Bytes :=
  let acc1 := putBytes vn.authKey acc
  let acc2 := putU32 vn.direction acc1
  let acc3 := putU32 vn.minVersion acc2
  putOpt putChainParamsPB vn.chainParams acc3

def getVersionNegotiationPB (bs : Bytes) (atIdx : Nat) :
    Option (VersionNegotiationPB × Nat) := do
  let (ak, at1) ← getBytes bs atIdx
  let (dir, at2) ← getU32 bs at1
  let (mv, at3) ← getU32 bs at2
  let (cp, at4) ← getOpt getChainParamsPB bs at3
  some ({ authKey := ak, direction := dir, minVersion := mv, chainParams := cp }, at4)

def putEpochDirectionPB (ed : EpochDirectionPB) (acc : Bytes) : Bytes :=
  putBytes ed.prev (putBytes ed.next (putU32 ed.ctr acc))

def getEpochDirectionPB (bs : Bytes) (atIdx : Nat) :
    Option (EpochDirectionPB × Nat) := do
  let (ctr, at1) ← getU32 bs atIdx
  let (next, at2) ← getBytes bs at1
  let (prev, at3) ← getBytes bs at2
  some ({ ctr := ctr, next := next, prev := prev }, at3)

def putChainEpochPB (ce : ChainEpochPB) (acc : Bytes) : Bytes :=
  putOpt putEpochDirectionPB ce.recv (putOpt putEpochDirectionPB ce.send acc)

def getChainEpochPB (bs : Bytes) (atIdx : Nat) : Option (ChainEpochPB × Nat) := do
  let (s, at1) ← getOpt getEpochDirectionPB bs atIdx
  let (r, at2) ← getOpt getEpochDirectionPB bs at1
  some ({ send := s, recv := r }, at2)

def putLinks : List ChainEpochPB → Bytes → Bytes
  | [], acc => acc
  | x :: xs, acc => putLinks xs (putChainEpochPB x acc)

def getLinks : Nat → Bytes → Nat → Option (List ChainEpochPB × Nat)
  | 0, _, atIdx => some ([], atIdx)
  | n + 1, bs, atIdx => do
    let (head, at1) ← getChainEpochPB bs atIdx
    let (tail, at2) ← getLinks n bs at1
    some (head :: tail, at2)

def putChainPB (c : ChainPB) (acc : Bytes) : Bytes :=
  let acc1 := putU32 c.direction acc
  let acc2 := putU64 c.currentEpoch acc1
  let acc3 := putU64 (BitVec.ofNat 64 c.links.length) acc2
  let acc4 := putLinks c.links acc3
  let acc5 := putBytes c.nextRoot acc4
  let acc6 := putU64 c.sendEpoch acc5
  putOpt putChainParamsPB c.params acc6

def getChainPB (bs : Bytes) (atIdx : Nat) : Option (ChainPB × Nat) := do
  let (dir, at1) ← getU32 bs atIdx
  let (curEp, at2) ← getU64 bs at1
  let (linksLen64, at3) ← getU64 bs at2
  let (links, at4) ← getLinks linksLen64.toNat bs at3
  let (nextRoot, at5) ← getBytes bs at4
  let (sendEp, at6) ← getU64 bs at5
  let (params, at7) ← getOpt getChainParamsPB bs at6
  some ({
    direction := dir
    currentEpoch := curEp
    links := links
    nextRoot := nextRoot
    sendEpoch := sendEp
    params := params
  }, at7)

def putStubV1StatePB (s : StubV1StatePB) (acc : Bytes) : Bytes :=
  let dByte : BitVec 8 := match s.dir with | .a2b => 0#8 | .b2a => 1#8
  let acc1 := acc ++ [dByte, s.mode.toByte]
  let acc2 := putU64 s.epoch acc1
  putU32 s.step acc2

def getStubV1StatePB (bs : Bytes) (atIdx : Nat) : Option (StubV1StatePB × Nat) := do
  let dByte ← bs[atIdx]?
  let mByte ← bs[atIdx + 1]?
  let dir ← if dByte == 0#8 then some Direction.a2b else if dByte == 1#8 then some Direction.b2a else none
  let mode ← StubMode.fromByte? mByte
  let (ep, at1) ← getU64 bs (atIdx + 2)
  let (st, at2) ← getU32 bs at1
  some ({ dir := dir, epoch := ep, step := st, mode := mode }, at2)

/-- Encode `PqRatchetStatePB StubV1StatePB` to `Bytes` (prefixed with magic byte `0x53#8`). -/
def stubEncodeState (st : PqRatchetStatePB StubV1StatePB) : Bytes :=
  let acc0 : Bytes := [0x53#8]
  let acc1 := putOpt putStubV1StatePB st.inner acc0
  let acc2 := putOpt putVersionNegotiationPB st.versionNegotiation acc1
  putOpt putChainPB st.chain acc2

def stubDecodeState (bs : Bytes) : Except Unit (PqRatchetStatePB StubV1StatePB) :=
  match bs with
  | 0x53#8 :: _ =>
    match (do
      let (inner, at1) ← getOpt getStubV1StatePB bs 1
      let (vn, at2) ← getOpt getVersionNegotiationPB bs at1
      let (chain, at3) ← getOpt getChainPB bs at2
      if at3 == bs.length then
        some { inner := inner, versionNegotiation := vn, chain := chain }
      else
        none) with
    | some st => .ok st
    | none => .error ()
  | _ => .error ()

def stubStatesFromPb (pb : StubV1StatePB) : SpqrApiResult StubStates :=
  match pb.mode with
  | .errFromPbStateDecode => .error (.err .stateDecode)
  | .errFromPbSerialization => .error (.err .serialization)
  | .panicFromPbV1 => .error (.panic .v1)
  | _ => .ok { dir := pb.dir, epoch := pb.epoch, step := pb.step, mode := pb.mode }

def stubStatesIntoPb (st : StubStates) : StubV1StatePB :=
  { dir := st.dir, epoch := st.epoch, step := st.step, mode := st.mode }

/-- Stub `States::send`: consumes 2 bytes from `tape` (or 3 bytes in fault modes
`errSendEncoding` / `panicSendV1`). -/
def stubStatesSend (st : StubStates) (tape : Bytes) :
    SpqrApiResult (StubMsg × Option EpochSecret × StubStates) × Bytes :=
  match st.mode with
  | .errSendEncoding =>
    (.error (.err .encodingDecoding), tape.drop 3)
  | .panicSendV1 =>
    (.error (.panic .v1), tape.drop 3)
  | .sendKeySome =>
    let msg : StubMsg := { epoch := st.epoch, payloadTag := 1#8, serKind := 0#8 }
    let sec : EpochSecret := { epoch := 1#64, secret := [9#8] }
    (.ok (msg, some sec, { st with step := st.step + 1#32 }), tape.drop 2)
  | .sendEpochZero =>
    let msg : StubMsg := { epoch := 0#64, payloadTag := 1#8, serKind := 0#8 }
    (.ok (msg, none, st), tape.drop 2)
  | .sendSerializeEmpty =>
    let msg : StubMsg := { epoch := st.epoch, payloadTag := 1#8, serKind := 1#8 }
    (.ok (msg, none, st), tape.drop 2)
  | .sendSerializeBadVer =>
    let msg : StubMsg := { epoch := st.epoch, payloadTag := 1#8, serKind := 2#8 }
    (.ok (msg, none, st), tape.drop 2)
  | .sendBadEpochSecret =>
    let msg : StubMsg := { epoch := st.epoch, payloadTag := 1#8, serKind := 0#8 }
    let sec : EpochSecret := { epoch := 99#64, secret := [7#8] }
    (.ok (msg, some sec, st), tape.drop 2)
  | .ratchet =>
    let nextEpoch := st.epoch + 1#64
    let sec : EpochSecret := { epoch := st.epoch, secret := [BitVec.ofNat 8 st.epoch.toNat] }
    let msg : StubMsg := { epoch := nextEpoch, payloadTag := 2#8, serKind := 0#8 }
    (.ok (msg, some sec, { st with epoch := nextEpoch, step := st.step + 1#32 }), tape.drop 2)
  | _ =>
    let msg : StubMsg := { epoch := st.epoch, payloadTag := 1#8, serKind := 0#8 }
    (.ok (msg, none, { st with step := st.step + 1#32 }), tape.drop 2)

def stubStatesRecv (st : StubStates) (msg : StubMsg) :
    SpqrApiResult (Option EpochSecret × StubStates) :=
  match st.mode with
  | .errRecvMac => .error (.err .macVerifyFailed)
  | .panicRecvV1 => .error (.panic .v1)
  | .recvBadEpochSecret =>
    .ok (some { epoch := 99#64, secret := [7#8] }, st)
  | _ =>
    if msg.payloadTag == 2#8 then
      let prevEpoch := msg.epoch - 1#64
      let sec : EpochSecret := { epoch := prevEpoch, secret := [BitVec.ofNat 8 prevEpoch.toNat] }
      .ok (some sec, { st with epoch := msg.epoch, step := st.step + 1#32 })
    else
      .ok (none, { st with step := st.step + 1#32 })

def stubMsgSerialize (msg : StubMsg) (index : BitVec 32) : Bytes :=
  if msg.serKind == 1#8 then
    []
  else if msg.serKind == 2#8 then
    let b1 := encodeVarint msg.epoch [2#8]
    let b2 := encodeVarint (index.zeroExtend 64) b1
    b2 ++ [msg.payloadTag]
  else
    let b1 := encodeVarint msg.epoch [Version.v1.toU8]
    let b2 := encodeVarint (index.zeroExtend 64) b1
    b2 ++ [msg.payloadTag]

/-- Stub `Message::deserialize`:
* empty `remaining` -> `Err(Error::MsgDecode)` (`src/v1/chunked/states/serialize.rs:201–203`)
* `remaining = [0xfe#8]` -> panics with `SpqrApiPanic.v1`
* `remaining = [0xff#8]` -> `Err(Error::MsgDecode)` (`MessageType::try_from` failure)
* otherwise succeeds with `payloadTag = remaining[0]`. -/
def stubMsgDeserialize (epoch : Epoch) (remaining : Bytes) : SpqrApiResult StubMsg :=
  match remaining with
  | [] => .error (.err .msgDecode)
  | b0 :: _ =>
    if b0 == 0xfe#8 then
      .error (.panic .v1)
    else if b0 == 0xff#8 then
      .error (.err .msgDecode)
    else
      .ok { epoch := epoch, payloadTag := b0, serKind := 0#8 }

/-- Stub `initV1Inner`: panics with `SpqrApiPanic.v1` if `authKey == [0xff#8]`, otherwise initializes
a normal V1 state for direction `d`. -/
def stubInitV1Inner (d : Direction) (authKey : Bytes) : Except SpqrApiPanic StubV1StatePB :=
  if authKey == [0xff#8] then
    .error .v1
  else
    .ok { dir := d, epoch := 1#64, step := 0#32, mode := .normal }

def stubDeps : SpqrApiDeps where
  V1StatePB := StubV1StatePB
  decodeState := stubDecodeState
  encodeState := stubEncodeState
  States := StubStates
  statesFromPb := stubStatesFromPb
  statesIntoPb := stubStatesIntoPb
  MessageV1 := StubMsg
  statesSend := stubStatesSend
  statesRecv := stubStatesRecv
  msgSerialize := stubMsgSerialize
  msgDeserialize := stubMsgDeserialize
  msgEpoch := fun m => m.epoch
  initV1Inner := stubInitV1Inner

/-- Encode a synthetic V1 state with custom `StubV1StatePB`, `VersionNegotiationPB`, and `ChainPB`. -/
def mkStateBytes (inner : Option StubV1StatePB)
    (vn : Option VersionNegotiationPB := none) (chain : Option ChainPB := none) : Bytes :=
  stubEncodeState { inner := inner, versionNegotiation := vn, chain := chain }

/-- Default `VersionNegotiationPB` for direction `d` and `minVersion`. -/
def mkVn (d : Direction) (minVer : BitVec 32)
    (chainParams : Option ChainParamsPB := some ChainParams.default.intoPb) :
    VersionNegotiationPB :=
  { authKey := List.replicate 32 41#8
    direction := d.toI32
    minVersion := minVer
    chainParams := chainParams }

/-! ## 1. `encode_varint`, `decode_varint`, and `msg_preamble` Edge Cases -/

/-- Round-trip and edge-case guards for `encodeVarint`, `decodeVarint`, `decodeVarintAt`,
`decodeVarintCheckedLoop`, and `msgPreamble` (`src/lib.rs:507–590`,
`src/v1/chunked/states/serialize.rs:229–263`). -/
theorem guard_varint_and_preamble_edges :
    -- Round-trip on boundary values (0, 1, 127, 128, 300, 16383, 16384, u32::MAX, u32::MAX + 1, u64::MAX)
    ([0#64, 1#64, 0x7f#64, 0x80#64, 0x012c#64, 0x3fff#64, 0x4000#64,
      0xffffffff#64, 0x100000000#64, 0xffffffffffffffff#64].all fun u =>
        let enc := encodeVarint u
        decodeVarint enc == .ok (u, []) &&
        decodeVarintAt enc 0 == .ok (u, enc.length) &&
        decodeVarintChecked enc 0 == .ok (u, enc.length)) = true ∧
    -- Non-zero starting offset `at` with prefix and suffix bytes
    decodeVarintAt [0xaa#8, 0xbb#8, 0x80#8, 0x01#8, 0xcc#8] 2 = .ok (128#64, 4) ∧
    decodeVarintChecked [0xaa#8, 0xbb#8, 0x80#8, 0x01#8, 0xcc#8] 2 = .ok (128#64, 4) ∧
    -- `start_at >= from.len()` returns `Err(Error::MsgDecode)`
    decodeVarintAt [0x01#8] 1 = .error .msgDecode ∧
    decodeVarintAt [0x01#8] 5 = .error .msgDecode ∧
    -- Truncated multi-byte varint returns `Err(Error::MsgDecode)`
    decodeVarint [0x80#8, 0x80#8] = .error .msgDecode ∧
    -- 10-byte varint with non-terminated 10th byte (`i = 9` has bit 7 set): returns `Err(MsgDecode)`
    decodeVarint (List.replicate 10 0xff#8 ++ [0x00#8]) = .error .msgDecode ∧
    -- 10-byte varint at byte 9 (`i = 9`, `7 * 9 = 63 < 64`): does NOT panic; bit 0 of byte 9 is
    -- placed at bit 63 and bits 1..6 of byte 9 are dropped (`0x7f << 63 == 0x8000000000000000`)
    decodeVarint (List.replicate 9 0x80#8 ++ [0x7f#8]) = .ok (0x8000000000000000#64, []) ∧
    decodeVarint (List.replicate 9 0x80#8 ++ [0x02#8]) = .ok (0#64, []) ∧
    -- Direct call to `decodeVarintCheckedLoop` at byte 10 (`i = 10`, `7 * 10 = 70 >= 64`): panics
    -- with `SpqrApiPanic.decodeVarintShiftOverflow` under `overflow-checks = true`
    decodeVarintCheckedLoop (List.replicate 12 0x01#8) 0 12 10 0#64 false =
      .error (.panic .decodeVarintShiftOverflow) ∧
    -- `msgPreamble` edge cases:
    -- 1) empty message -> version 0, epoch 0, index 0, remaining []
    msgPreamble [] = .ok { version := 0#8, epoch := 0#64, index := 0#32, remaining := [] } ∧
    -- 2) lone version byte (truncated epoch) -> Err(MsgDecode)
    msgPreamble [1#8] = .error .msgDecode ∧
    -- 3) epoch == 0 -> Err(MsgDecode)
    msgPreamble [1#8, 0#8, 0#8] = .error .msgDecode ∧
    -- 4) 10-byte epoch that wraps to 0 in u64 (nine 0x80 then 0x02) -> Err(MsgDecode)
    msgPreamble (1#8 :: (List.replicate 9 0x80#8 ++ [0x02#8, 0x00#8])) =
      .error .msgDecode ∧
    -- 5) missing index after valid epoch -> Err(MsgDecode)
    msgPreamble [1#8, 1#8] = .error .msgDecode ∧
    -- 6) index == u32::MAX (0xffffffff = [0xff, 0xff, 0xff, 0xff, 0x0f]) -> Ok
    msgPreamble [1#8, 1#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0x0f#8, 0x42#8] =
      .ok { version := 1#8, epoch := 1#64, index := 0xffffffff#32, remaining := [0x42#8] } ∧
    -- 7) index == u32::MAX + 1 (0x100000000 = [0x80, 0x80, 0x80, 0x80, 0x10]) -> Err(MsgDecode)
    msgPreamble [1#8, 1#8, 0x80#8, 0x80#8, 0x80#8, 0x80#8, 0x10#8] =
      .error .msgDecode := by
  decide +kernel

/-! ## 2. Version Negotiation Branches, DEV-SPQR2 (`Ordering::Greater` with `index = 0`), and Casts -/

/-- Tests all version-negotiation branches in `recv`, `send`, `currentVersion`, `toSpqrModel`, and
`toSpqrRecvModel`:
* `Ordering::Greater` with `msg.index == 0` (DEV-SPQR2): `Chain::recv_key(0, 0)` returns `Ok([])`
  and `src/lib.rs:406` wraps it in `Some([])` without an `is_empty()` filter; `toSpqrRecvModel`
  preserves `.ok (state', some [])` with `recvPanics = False`
* `Ordering::Equal`, `Ordering::Less`
* `Error::MinimumVersion`, `Error::VersionMismatch`, `current_version == 0` shortcut
* `vn.min_version as u8` truncation in `recv` (`0x100 as u8 == 0`, `0x101 as u8 == 1`) vs
  `vn.min_version.try_into()` in `currentVersion` (`Err(Error::StateDecode)`)
* signed `i32` comparison `vn.min_version > Version::V0 as i32` in `send` (`0xffffffff` is `-1 < 0`,
  so no chain is created when `min_version = -1`). -/
def runVersionNegotiationBranches : Bool :=
  -- 0) DEV-SPQR2: `Ordering::Greater` (`msg.version = 0x99 > current_version = 1`) with
  -- `msg.index == 0`: `recv` returns `Ok(Recv { state, key: Some([]) })`, and `toSpqrRecvModel`
  -- preserves `some []`.
  let stV1B := mkStateBytes (some { dir := .b2a }) (some (mkVn .b2a 1#32)) none
  let msgGreaterIdx0 : Bytes := [0x99#8, 0x01#8, 0x00#8]
  let recvGreater0 := recv stubDeps testHkdf stV1B msgGreaterIdx0
  let RM := toSpqrRecvModel stubDeps testHkdf
  let M := toSpqrModel stubDeps testHkdf
  let greaterIdx0Ok :=
    match recvGreater0, RM.recv stV1B msgGreaterIdx0 with
    | .ok r, .ok (st', key') =>
      r.key == some [] && key' == some [] && st' == r.state && !r.state.isEmpty &&
      !recvPanicsB stubDeps testHkdf stV1B msgGreaterIdx0 &&
      -- In `toSpqrModel`, `recvKeyToSalt?` reads `some []` as no salt (DEV-SPQR2 repair): no
      -- panic, and `.ok` with salt `none`:
      !recvPanicsSaltB stubDeps testHkdf stV1B msgGreaterIdx0 &&
      M.recv stV1B msgGreaterIdx0 == .ok (r.state, none)
    | _, _ => false
  -- 1) Truncating `vn.min_version as u8` in `recv` vs `currentVersion`:
  -- With `vn.minVersion = 0x100#32` (256), `currentVersion` fails with `StateDecode`,
  -- while `recv` truncates `0x100 as u8 = 0`, allowing downgrade to V0 on an empty message.
  let stTrunc0 := mkStateBytes (some { dir := .a2b }) (some (mkVn .a2b 0x00000100#32)) none
  let cvTrunc0 := currentVersion stubDeps stTrunc0
  let recvTrunc0 := recv stubDeps testHkdf stTrunc0 []
  -- With `vn.minVersion = 0x101#32` (257), `0x101 as u8 = 1`, so `msg.version = 0 < 1` returns
  -- `Err(Error::MinimumVersion)`.
  let stTrunc1 := mkStateBytes (some { dir := .a2b }) (some (mkVn .a2b 0x00000101#32)) none
  let recvTrunc1 := recv stubDeps testHkdf stTrunc1 []
  -- 2) Signed `vn.min_version > 0i32` in `send`:
  -- With `vn.minVersion = 0xffffffff#32` (`-1i32`), `BitVec.slt 0#32 0xffffffff#32` is `false`,
  -- so `send` takes the `else { None }` branch and returns `key = None`.
  let stNegMin := mkStateBytes (some { dir := .a2b }) (some (mkVn .a2b 0xffffffff#32)) none
  let (sendNegMin, _) := send stubDeps testHkdf stNegMin [1#8, 2#8]
  let negMinKeyNone :=
    match sendNegMin with
    | .ok s => s.key.isNone
    | .error _ => false
  -- 3) `recv` on state with `inner = None` (`current_version = 0`) and `version_negotiation = None`:
  -- `version_still_negotiating` is `current_version == 0` (`true`), so even a message with
  -- `msg.version = 5` is NOT rejected by `VersionMismatch` and takes the `current_version == 0`
  -- shortcut returning `Ok(Recv { state: [], key: None })`.
  let recvEmptyV5 := recv stubDeps testHkdf [] [5#8, 1#8, 0#8]
  -- 4) `recv` `Ordering::Less` when `current_version = 1` and `msg.version = 0`: downgrades to V0
  -- (`state = []`, `key = None`).
  let stNegotiatingV0 := mkStateBytes (some { dir := .a2b }) (some (mkVn .a2b 0#32)) none
  let recvDowngradeNonEmptyMsg := recv stubDeps testHkdf stNegotiatingV0 [0#8, 1#8, 0#8]
  greaterIdx0Ok &&
    cvTrunc0 == .error .stateDecode &&
    recvTrunc0 == .ok { state := [], key := none } &&
    recvTrunc1 == .error (.err .minimumVersion) &&
    negMinKeyNone &&
    recvEmptyV5 == .ok { state := [], key := none } &&
    recvDowngradeNonEmptyMsg == .ok { state := [], key := none }

theorem guard_version_negotiation_branches : runVersionNegotiationBranches = true := by
  decide +kernel

/-! ## 3. Error Precedence, Panic Sites, RNG Draws, `toSpqrModel`, and `toSpqrRecvModel` -/

/-- Verifies exact error precedence, panic sites, RNG `draws`, `toSpqrModel`, and `toSpqrRecvModel`. -/
def runErrorPrecedenceAndPanics : Bool :=
  let vnV1 := mkVn .a2b 1#32
  let vnV0 := mkVn .a2b 0#32
  let tape : Bytes := [10#8, 20#8, 30#8, 40#8, 50#8]

  -- A. `initialState` panic propagation from `initV1Inner`:
  let pInit := initialState stubDeps {
    version := .v1, minVersion := .v0, direction := .a2b, authKey := [0xff#8]
  }

  -- B. `send` error precedence & RNG draws:
  -- B1. Corrupt state bytes -> `Err(StateDecode)`, 0 RNG bytes consumed
  let (sCorrupt, tCorrupt) := send stubDeps testHkdf [0xff#8] tape
  -- B2. Empty state -> `Ok(empty)`, 0 RNG bytes consumed
  let (sEmpty, tEmpty) := send stubDeps testHkdf [] tape
  -- B3. `States::from_pb` fails or panics BEFORE `States::send` -> 0 RNG bytes consumed
  let stFromPbErr := mkStateBytes (some { mode := .errFromPbSerialization }) (some vnV1) none
  let (sFromPbErr, tFromPbErr) := send stubDeps testHkdf stFromPbErr tape
  let stFromPbPanic := mkStateBytes (some { mode := .panicFromPbV1 }) (some vnV1) none
  let (pFromPbSend, tFromPbPanic) := send stubDeps testHkdf stFromPbPanic tape
  -- B4. `States::send` fails AFTER consuming 3 RNG bytes (even when `chain` & `vn` are both `None`,
  -- so `States::send` error precedes `ChainNotAvailable`!)
  let stSendErrNoChain := mkStateBytes (some { mode := .errSendEncoding }) none none
  let (sSendErr, tSendErr) := send stubDeps testHkdf stSendErrNoChain tape
  -- B5. `States::send` succeeds (consuming 2 RNG bytes), then `chain = None` and `vn = None` ->
  -- `Err(ChainNotAvailable)` with 2 RNG bytes consumed
  let stNoChainNoVn := mkStateBytes (some { mode := .normal }) none none
  let (sNoChain, tNoChain) := send stubDeps testHkdf stNoChainNoVn tape

  -- C. `send` panic sites:
  -- C1. `States::send` panics (`SpqrApiPanic.v1`)
  let stPanicV1 := mkStateBytes (some { mode := .panicSendV1 }) (some vnV1) none
  let (pSendV1, tPanicV1) := send stubDeps testHkdf stPanicV1 tape
  -- C2. `src/lib.rs:292`: `assert!(key.is_none())` when `chain` is `None` (`vn.min_version == 0`)
  let stKeySomeNoChain := mkStateBytes (some { mode := .sendKeySome }) (some vnV0) none
  let (pKeySome, _) := send stubDeps testHkdf stKeySomeNoChain tape
  -- C3. `src/lib.rs:299`: `msg.epoch - 1` underflow when `msg.epoch == 0`
  let stEpochZero := mkStateBytes (some { mode := .sendEpochZero }) (some vnV1) none
  let (pEpochZero, _) := send stubDeps testHkdf stEpochZero tape
  -- C4. `src/lib.rs:297` vs `:299`: `chain.add_epoch` runs BEFORE `msg.epoch - 1`, so bad
  -- `epoch_secret` panics with `ChainPanic.addEpochMismatch`
  let stBadEpochSec := mkStateBytes (some { mode := .sendBadEpochSecret }) (some vnV1) none
  let (pBadEpochSec, _) := send stubDeps testHkdf stBadEpochSec tape
  -- C5. `src/lib.rs:305`: `assert!(!msg.is_empty())`
  let stMsgEmpty := mkStateBytes (some { mode := .sendSerializeEmpty }) (some vnV1) none
  let (pMsgEmpty, _) := send stubDeps testHkdf stMsgEmpty tape
  -- C6. `src/lib.rs:306`: `assert_eq!(msg[0], Version::V1.into())`
  let stMsgBadVer := mkStateBytes (some { mode := .sendSerializeBadVer }) (some vnV1) none
  let (pMsgBadVer, _) := send stubDeps testHkdf stMsgBadVer tape

  -- D. `recv` error precedence & panic sites:
  -- D1. `msg_preamble` runs BEFORE `decode_state`: invalid msg `[1]` + corrupt state `[0xff]`
  -- returns `Err(MsgDecode)`, whereas valid empty msg `[]` + corrupt state `[0xff]` returns
  -- `Err(StateDecode)`.
  let rMsgBeforeState := recv stubDeps testHkdf [0xff#8] [1#8]
  let rEmptyMsgBadState := recv stubDeps testHkdf [0xff#8] []
  -- D2. In `Ordering::Less`, `vn.direction.try_into()` runs BEFORE `chain_from`:
  -- bad direction `99#32` + missing `chainParams = none` returns `Err(StateDecode)` (not
  -- `ChainNotAvailable`).
  let vnBadDirNoParams : VersionNegotiationPB :=
    { authKey := [1#8], direction := 99#32, minVersion := 0#32, chainParams := none }
  let stBadDirNoParams := mkStateBytes (some { mode := .normal }) (some vnBadDirNoParams) none
  let rLessOrder := recv stubDeps testHkdf stBadDirNoParams []
  -- D3. In V1 `recv`, `Message::deserialize` runs BEFORE `States::from_pb`:
  -- invalid remaining `[]` + `errFromPbSerialization` returns `Err(MsgDecode)`.
  let stFromPbErrV1 := mkStateBytes (some { mode := .errFromPbSerialization }) (some vnV1) none
  let rDeserBeforeFromPb := recv stubDeps testHkdf stFromPbErrV1 [1#8, 1#8, 1#8]
  -- D4. `States::from_pb` runs BEFORE `States::recv` (both error and panic):
  let rFromPbBeforeRecv := recv stubDeps testHkdf stFromPbErrV1 [1#8, 1#8, 1#8, 1#8]
  let pFromPbRecv := recv stubDeps testHkdf stFromPbPanic [1#8, 1#8, 1#8, 1#8]
  -- D5. `States::recv` runs BEFORE `chain_from`:
  -- `errRecvMac` + `chain = None, vn = None` returns `Err(MacVerifyFailed)` (not `ChainNotAvailable`).
  let stRecvMacNoChain := mkStateBytes (some { mode := .errRecvMac }) none none
  let rRecvBeforeChain := recv stubDeps testHkdf stRecvMacNoChain [1#8, 1#8, 1#8, 1#8]
  -- D6. `States::recv` panic (`SpqrApiPanic.v1`) and `Chain::add_epoch` panic in `recv`:
  let stRecvPanic := mkStateBytes (some { mode := .panicRecvV1 }) (some vnV1) none
  let pRecvV1 := recv stubDeps testHkdf stRecvPanic [1#8, 1#8, 1#8, 1#8]
  let stRecvBadSec := mkStateBytes (some { mode := .recvBadEpochSecret }) (some vnV1) none
  let pRecvBadSec := recv stubDeps testHkdf stRecvBadSec [1#8, 1#8, 1#8, 1#8]

  -- E. `toSpqrModel` and `toSpqrRecvModel` checks:
  let M := toSpqrModel stubDeps testHkdf
  let RM := toSpqrRecvModel stubDeps testHkdf
  let mRecvStateDecode := M.recv [0xff#8] []
  let mRecvMsgDecode := M.recv [0xff#8] [1#8]
  let rmRecvStateDecode := RM.recv [0xff#8] []
  let rmRecvMsgDecode := RM.recv [0xff#8] [1#8]
  let mDrawsOk := M.draws (mkStateBytes (some { mode := .normal }) (some vnV1) none) tape
  let mDrawsEmpty := M.draws [] tape
  let mDrawsErr := M.draws stSendErrNoChain tape

  pInit == .error (.panic .v1) &&
    sCorrupt == .error (.err .stateDecode) && tCorrupt == tape &&
    sEmpty == .ok { state := [], msg := [], key := none } && tEmpty == tape &&
    sFromPbErr == .error (.err .serialization) && tFromPbErr == tape &&
    pFromPbSend == .error (.panic .v1) && tFromPbPanic == tape &&
    sSendErr == .error (.err .encodingDecoding) && tSendErr == [40#8, 50#8] &&
    sNoChain == .error (.err .chainNotAvailable) && tNoChain == [30#8, 40#8, 50#8] &&
    pSendV1 == .error (.panic .v1) && tPanicV1 == [40#8, 50#8] &&
    pKeySome == .error (.panic .sendKeySomeWithoutChain) &&
    pEpochZero == .error (.panic .sendEpochUnderflow) &&
    pBadEpochSec == .error (.panic (.chain .addEpochMismatch)) &&
    pMsgEmpty == .error (.panic .sendMsgEmpty) &&
    pMsgBadVer == .error (.panic .sendMsgBadVersion) &&
    rMsgBeforeState == .error (.err .msgDecode) &&
    rEmptyMsgBadState == .error (.err .stateDecode) &&
    rLessOrder == .error (.err .stateDecode) &&
    rDeserBeforeFromPb == .error (.err .msgDecode) &&
    rFromPbBeforeRecv == .error (.err .serialization) &&
    pFromPbRecv == .error (.panic .v1) &&
    rRecvBeforeChain == .error (.err .macVerifyFailed) &&
    pRecvV1 == .error (.panic .v1) &&
    pRecvBadSec == .error (.panic (.chain .addEpochMismatch)) &&
    mRecvStateDecode == .error true &&
    mRecvMsgDecode == .error false &&
    rmRecvStateDecode == .error true &&
    rmRecvMsgDecode == .error false &&
    mDrawsOk == 2 && mDrawsEmpty == 0 && mDrawsErr == 3 &&
    sendPanicsB stubDeps testHkdf stEpochZero tape &&
    !sendPanicsB stubDeps testHkdf [] tape &&
    recvPanicsB stubDeps testHkdf stRecvPanic [1#8, 1#8, 1#8, 1#8] &&
    !recvPanicsB stubDeps testHkdf [0xff#8] []

theorem guard_error_precedence_and_panics : runErrorPrecedenceAndPanics = true := by
  decide +kernel

/-! ## 4. Translations of `src/lib.rs` `mod lib_test` (`:601–1419`) -/

def send1 (state : SerializedState) : SpqrApiResult Send :=
  (send stubDeps testHkdf state [1#8, 2#8, 3#8, 4#8]).1

def recv1 (state : SerializedState) (msg : SerializedMessage) : SpqrApiResult Recv :=
  recv stubDeps testHkdf state msg

/-- Translation of `lib_test::ratchet_v0_empty_states` and `lib_test::empty_constructor_for_state`
(`src/lib.rs:698–784`). -/
def runRatchetV0EmptyStates : Bool :=
  let alex0 := emptyState
  let blake0 := emptyState
  match send1 alex0 with
  | .ok sA1 =>
    match recv1 blake0 sA1.msg with
    | .ok rB1 =>
      match send1 rB1.state with
      | .ok sB1 =>
        match recv1 sA1.state sB1.msg with
        | .ok rA1 =>
          alex0.isEmpty && sA1.state.isEmpty && sA1.msg.isEmpty && sA1.key.isNone &&
            rB1.state.isEmpty && rB1.key == sA1.key &&
            sB1.state.isEmpty && sB1.msg.isEmpty && sB1.key.isNone &&
            rA1.state.isEmpty && rA1.key == sB1.key
        | _ => false
      | _ => false
    | _ => false
  | _ => false

theorem guard_ratchet_v0_empty_states : runRatchetV0EmptyStates = true := by
  decide +kernel

/-- Check a list of `(msg, wantKey)` pairs sequentially with `recv1`, threading `state`. -/
def recvSeqCheck (state : SerializedState) :
    List (SerializedMessage × MessageKey) → Bool
  | [] => true
  | (m, wantKey) :: rest =>
    match recv1 state m with
    | .ok r => r.key == wantKey && recvSeqCheck r.state rest
    | .error _ => false

/-- Translation of `lib_test::empty_key_until_version_negotiation` (`src/lib.rs:787–908`). -/
def runEmptyKeyUntilVersionNegotiation : Bool :=
  let authKey := List.replicate 32 41#8
  match initialState stubDeps { version := .v1, minVersion := .v0, direction := .a2b, authKey := authKey },
        initialState stubDeps { version := .v1, minVersion := .v0, direction := .b2a, authKey := authKey } with
  | .ok alex0, .ok blake0 =>
    match send1 alex0 with
    | .ok sA1 =>
      match send1 sA1.state with
      | .ok sA2 =>
        match send1 sA2.state with
        | .ok sA3 =>
          match send1 blake0 with
          | .ok sB1 =>
            match send1 sB1.state with
            | .ok sB2 =>
              match send1 sB2.state with
              | .ok sB3 =>
                match recv1 sA3.state sB2.msg with
                | .ok rB2 =>
                  match send1 rB2.state with
                  | .ok sA4 =>
                    match send1 sA4.state with
                    | .ok sA5 =>
                      match recv1 sB3.state sA1.msg with
                      | .ok rA1 =>
                        match send1 rA1.state with
                        | .ok sB4 =>
                          match send1 sB4.state with
                          | .ok sB5 =>
                            sA1.key.isNone && sA2.key.isNone && sA3.key.isNone &&
                              sB1.key.isNone && sB2.key.isNone && sB3.key.isNone &&
                              rB2.key.isNone && sA4.key.isSome && sA5.key.isSome &&
                              rA1.key.isNone && sB4.key.isSome && sB5.key.isSome &&
                              recvSeqCheck rA1.state [
                                (sA3.msg, sA3.key),
                                (sA4.msg, sA4.key),
                                (sA2.msg, sA2.key),
                                (sA5.msg, sA5.key)
                              ] &&
                              recvSeqCheck sA5.state [
                                (sB1.msg, sB1.key),
                                (sB3.msg, sB3.key),
                                (sB4.msg, sB4.key),
                                (sB5.msg, sB5.key)
                              ]
                          | _ => false
                        | _ => false
                      | _ => false
                    | _ => false
                  | _ => false
                | _ => false
              | _ => false
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _ => false
  | _, _ => false

theorem guard_empty_key_until_version_negotiation :
    runEmptyKeyUntilVersionNegotiation = true := by
  decide +kernel

/-- Translation of `lib_test::min_version_v1_always_creates_keys_a2b` and
`lib_test::min_version_v1_always_creates_keys_b2a` (`src/lib.rs:911–988`). -/
def runMinVersionV1AlwaysCreatesKeys : Bool :=
  let authKey := List.replicate 32 41#8
  let a2bCase :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v0, direction := .b2a, authKey := authKey } with
    | .ok alex, .ok blake =>
      match send1 alex, send1 blake with
      | .ok sA1, .ok sB1 =>
        match recv1 sB1.state sA1.msg with
        | .ok rB =>
          match send1 rB.state with
          | .ok sB2 => sA1.key.isSome && sB1.key.isNone && rB.key == sA1.key && sB2.key.isSome
          | _ => false
        | _ => false
      | _, _ => false
    | _, _ => false
  let b2aCase :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v0, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .b2a, authKey := authKey } with
    | .ok alex, .ok blake =>
      match send1 blake, send1 alex with
      | .ok sB1, .ok sA1 =>
        match recv1 sA1.state sB1.msg with
        | .ok rA =>
          match send1 rA.state with
          | .ok sA2 => sB1.key.isSome && sA1.key.isNone && rA.key == sB1.key && sA2.key.isSome
          | _ => false
        | _ => false
      | _, _ => false
    | _, _ => false
  a2bCase && b2aCase

theorem guard_min_version_v1_always_creates_keys :
    runMinVersionV1AlwaysCreatesKeys = true := by
  decide +kernel

/-- Translation of `lib_test::negotiate_to_v0_a2b`, `lib_test::negotiate_to_v0_b2a`,
`lib_test::negotiation_refused_a2b`, `lib_test::negotiation_refused_b2a`,
`lib_test::disallow_downgrade_due_to_unsupported_version`,
`lib_test::high_version_to_v1_uses_chain_keys`, and `lib_test::empty_recv_fails_minv1`
(`src/lib.rs:991–1418`). -/
def runNegotiationSuite : Bool :=
  let authKey := List.replicate 32 41#8
  -- 1. negotiate_to_v0_a2b (`:991–1043`)
  let negA2B :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v0, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := .v0, minVersion := .v0, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      currentVersion stubDeps alex0 == .ok (.stillNegotiating Version.MAX .v0) &&
        currentVersion stubDeps blake0 == .ok (.negotiationComplete .v0) &&
        match send1 alex0 with
        | .ok sA1 =>
          match recv1 blake0 sA1.msg with
          | .ok rB1 =>
            match send1 rB1.state with
            | .ok sB1 =>
              sB1.msg.isEmpty &&
                match recv1 sA1.state sB1.msg with
                | .ok rA1 =>
                  currentVersion stubDeps rA1.state == .ok (.negotiationComplete .v0)
                | _ => false
            | _ => false
          | _ => false
        | _ => false
    | _, _ => false

  -- 2. negotiate_to_v0_b2a (`:1046–1097`)
  let negB2A :=
    match initialState stubDeps { version := .v0, minVersion := .v0, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v0, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      currentVersion stubDeps alex0 == .ok (.negotiationComplete .v0) &&
        currentVersion stubDeps blake0 == .ok (.stillNegotiating Version.MAX .v0) &&
        match send1 alex0 with
        | .ok sA1 =>
          match recv1 blake0 sA1.msg with
          | .ok rB1 =>
            match send1 rB1.state with
            | .ok sB1 =>
              match recv1 sA1.state sB1.msg with
              | .ok rA1 =>
                currentVersion stubDeps rA1.state == .ok (.negotiationComplete .v0) &&
                  currentVersion stubDeps rB1.state == .ok (.negotiationComplete .v0)
              | _ => false
            | _ => false
          | _ => false
        | _ => false
    | _, _ => false

  -- 3. negotiation_refused_a2b & negotiation_refused_b2a (`:1100–1180`)
  let refusedA2B :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := .v0, minVersion := .v0, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      match send1 alex0 with
      | .ok sA1 =>
        match recv1 blake0 sA1.msg with
        | .ok rB1 =>
          match send1 rB1.state with
          | .ok sB1 => recv1 sA1.state sB1.msg == .error (.err .minimumVersion)
          | _ => false
        | _ => false
      | _ => false
    | _, _ => false

  let refusedB2A :=
    match initialState stubDeps { version := .v0, minVersion := .v0, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      match send1 alex0 with
      | .ok sA1 => recv1 blake0 sA1.msg == .error (.err .minimumVersion)
      | _ => false
    | _, _ => false

  -- 4. disallow_downgrade_due_to_unsupported_version (`:1287–1316`)
  let disallowAfterComplete :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v0, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      match send1 alex0 with
      | .ok sA1 =>
        match recv1 blake0 sA1.msg with
        | .ok rB1 =>
          recv1 rB1.state [0xff#8, 0x01#8, 0x01#8] == .error (.err .versionMismatch)
        | _ => false
      | _ => false
    | _, _ => false

  -- 5. high_version_to_v1_uses_chain_keys (`:1319–1354`)
  let highVersionChainKeys :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      match send1 alex0 with
      | .ok sA1 =>
        match send1 sA1.state with
        | .ok sA2 =>
          match recv1 blake0 [0x99#8, 0x03#8, 0x02#8] with
          | .ok rB2 =>
            match recv1 rB2.state [0x99#8, 0x01#8, 0x01#8] with
            | .ok rB1 =>
              sA1.key.isSome && sA2.key.isSome &&
                rB2.key == sA2.key && rB1.key == sA1.key
            | _ => false
          | _ => false
        | _ => false
      | _ => false
    | _, _ => false

  -- 6. empty_recv_fails_minv1 (`:1357–1418`)
  let emptyRecvFailsMinV1 :=
    match initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .a2b, authKey := authKey },
          initialState stubDeps { version := Version.MAX, minVersion := .v1, direction := .b2a, authKey := authKey } with
    | .ok alex0, .ok blake0 =>
      recv1 alex0 [] == .error (.err .minimumVersion) &&
        recv1 blake0 [] == .error (.err .minimumVersion) &&
        match send1 alex0 with
        | .ok sA1 =>
          match recv1 blake0 sA1.msg with
          | .ok rB1 =>
            recv1 sA1.state [] == .error (.err .minimumVersion) &&
              recv1 rB1.state [] == .error (.err .minimumVersion) &&
              match send1 rB1.state with
              | .ok sB1 =>
                match recv1 sA1.state sB1.msg with
                | .ok rA1 =>
                  recv1 rA1.state [] == .error (.err .minimumVersion) &&
                    recv1 sB1.state [] == .error (.err .minimumVersion)
                | _ => false
              | _ => false
          | _ => false
        | _ => false
    | _, _ => false

  negA2B && negB2A && refusedA2B && refusedB2A &&
    disallowAfterComplete && highVersionChainKeys && emptyRecvFailsMinV1

theorem guard_negotiation_suite : runNegotiationSuite = true := by
  decide +kernel

/-- Multi-epoch lockstep ratchet test (`lib_test::ratchet` and `lib_test::lockstep_run_with_logging`,
`src/lib.rs:601–695, 1186–1238`), exercising `Chain::add_epoch` and multi-epoch `send_key` /
`recv_key` across 4 rounds. -/
def lockstepLoop : Nat → SerializedState → SerializedState → Bool
  | 0, _, _ => true
  | n + 1, alex, blake =>
    match send1 alex with
    | .ok sA =>
      match recv1 blake sA.msg with
      | .ok rB =>
        match send1 rB.state with
        | .ok sB =>
          match recv1 sA.state sB.msg with
          | .ok rA =>
            sA.key.isSome && sA.key == rB.key &&
              sB.key.isSome && sB.key == rA.key &&
              sA.key != sB.key &&
              lockstepLoop n rA.state sB.state
          | _ => false
        | _ => false
      | _ => false
    | _ => false

def runMultiEpochLockstep : Bool :=
  let vnA := mkVn .a2b 1#32
  let vnB := mkVn .b2a 1#32
  let alex0 := mkStateBytes (some { dir := .a2b, epoch := 1#64, mode := .ratchet }) (some vnA) none
  let blake0 := mkStateBytes (some { dir := .b2a, epoch := 1#64, mode := .normal }) (some vnB) none
  lockstepLoop 4 alex0 blake0

theorem guard_multi_epoch_lockstep : runMultiEpochLockstep = true := by
  decide +kernel

end CryptoVerification.SpqrV1.Vectors.TopCheck
