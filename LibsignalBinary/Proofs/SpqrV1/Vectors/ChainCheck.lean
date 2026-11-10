/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Chain
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Chain
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain

/-!
# Differential Vector Checks for `Chain.lean`

Replays all differential test vectors in `Vectors/Chain.lean` against `Chain.lean`
instantiated with `spqrHkdfWith sha256Compress`, checking `KeyOpResult`, state transitions,
`prost` protobuf wire round-trips, and cross-trace Alice/Bob key agreement via `#guard`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.ChainCheck

open CryptoGames.HMAC (ShaState sha256With hmacWith toBEBytes)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Vectors.Chain

/-! ## Reference SHA-256 Compression Function -/

/-- SHA-256 round constants `K₀ … K₆₃` (FIPS 180-4 §4.2.2). -/
def K256 : List (BitVec 32) :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def bigS0 (x : BitVec 32) : BitVec 32 := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bigS1 (x : BitVec 32) : BitVec 32 := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def smallS0 (x : BitVec 32) : BitVec 32 := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def smallS1 (x : BitVec 32) : BitVec 32 := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

def be32 (b : List (BitVec 8)) : BitVec 32 :=
  b.foldl (fun acc x => (acc <<< 8) ||| x.zeroExtend 32) 0

/-- Message schedule `W₀ … W₆₃` of a 64-byte block. -/
def schedule (blk : List (BitVec 8)) : Array (BitVec 32) := Id.run do
  let mut w : Array (BitVec 32) := #[]
  for t in [0:16] do
    w := w.push (be32 ((blk.drop (4 * t)).take 4))
  for t in [16:64] do
    w := w.push (smallS1 w[t-2]! + w[t-7]! + smallS0 w[t-15]! + w[t-16]!)
  return w

/-- The SHA-256 compression function (FIPS 180-4 §6.2.2, steps 1–4). -/
def sha256Compress (H : ShaState) (blk : List (BitVec 8)) : ShaState := Id.run do
  let w := schedule blk
  let h0 := H.toList
  let mut a := h0[0]!; let mut b := h0[1]!; let mut c := h0[2]!; let mut d := h0[3]!
  let mut e := h0[4]!; let mut f := h0[5]!; let mut g := h0[6]!; let mut h := h0[7]!
  for t in [0:64] do
    let t1 := h + bigS1 e + ((e &&& f) ^^^ (~~~e &&& g)) + K256[t]! + w[t]!
    let t2 := bigS0 a + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    h := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
  let out := [a, b, c, d, e, f, g, h]
  return List.Vector.ofFn fun i => h0[i.val]! + out[i.val]!

def realHkdf : HkdfFn :=
  spqrHkdfWith sha256Compress

/-! ## Protobuf Wire Codec for `ChainPB` -/

/-- Unsigned base-128 varint encoding (protobuf wire type 0). -/
def encodeVarint (n : Nat) : Bytes :=
  if n < 128 then
    [BitVec.ofNat 8 n]
  else
    BitVec.ofNat 8 ((n % 128) + 128) :: encodeVarint (n / 128)
termination_by n
decreasing_by omega

/-- Unsigned base-128 varint decoding (`(value, remainingBytes)`). -/
def decodeVarint (bs : Bytes) (shift : Nat := 0) (acc : Nat := 0) : Option (Nat × Bytes) :=
  match bs with
  | [] => none
  | b :: rest =>
    let low := (b &&& 0x7f#8).toNat
    let acc' := acc + (low <<< shift)
    if (b &&& 0x80#8) == 0#8 then
      some (acc', rest)
    else
      decodeVarint rest (shift + 7) acc'

/-- Length-delimited field encoding (protobuf wire type 2). -/
def encodeTagLen (tag : BitVec 8) (payload : Bytes) : Bytes :=
  tag :: encodeVarint payload.length ++ payload

/-- Decode a length-delimited byte slice after reading its tag byte. -/
def decodeLenBytes (bs : Bytes) : Option (Bytes × Bytes) := do
  let (len, rest) ← decodeVarint bs
  if rest.length < len then none
  else some (rest.take len, rest.drop len)

/-- `prost::Message::encode` for `pqrpb::chain::epoch::EpochDirection`. -/
def encodeEpochDirectionPB (pb : EpochDirectionPB) : Bytes :=
  (if pb.ctr == 0#32 then [] else 0x08#8 :: encodeVarint pb.ctr.toNat) ++
  (if pb.next.isEmpty then [] else encodeTagLen 0x12#8 pb.next) ++
  (if pb.prev.isEmpty then [] else encodeTagLen 0x1a#8 pb.prev)

/-- `prost::Message::decode` for `pqrpb::chain::epoch::EpochDirection`. -/
def decodeEpochDirectionPB : Bytes → EpochDirectionPB → Option EpochDirectionPB
  | [], acc => some acc
  | 0x08#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeEpochDirectionPB rest' { acc with ctr := BitVec.ofNat 32 v }
    else none
  | 0x12#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    if rest'.length < rest.length then
      decodeEpochDirectionPB rest' { acc with next := b }
    else none
  | 0x1a#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    if rest'.length < rest.length then
      decodeEpochDirectionPB rest' { acc with prev := b }
    else none
  | _, _ => none
termination_by bs _ => bs.length

/-- `prost::Message::encode` for `pqrpb::chain::Epoch`. -/
def encodeChainEpochPB (pb : ChainEpochPB) : Bytes :=
  (match pb.send with | none => [] | some s => encodeTagLen 0x0a#8 (encodeEpochDirectionPB s)) ++
  (match pb.recv with | none => [] | some r => encodeTagLen 0x12#8 (encodeEpochDirectionPB r))

/-- `prost::Message::decode` for `pqrpb::chain::Epoch`. -/
def decodeChainEpochPB : Bytes → ChainEpochPB → Option ChainEpochPB
  | [], acc => some acc
  | 0x0a#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    let s ← decodeEpochDirectionPB b {}
    if rest'.length < rest.length then
      decodeChainEpochPB rest' { acc with send := some s }
    else none
  | 0x12#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    let r ← decodeEpochDirectionPB b {}
    if rest'.length < rest.length then
      decodeChainEpochPB rest' { acc with recv := some r }
    else none
  | _, _ => none
termination_by bs _ => bs.length

/-- `prost::Message::encode` for `pqrpb::ChainParams`. -/
def encodeChainParamsPB (pb : ChainParamsPB) : Bytes :=
  (if pb.maxJump == 0#32 then [] else 0x08#8 :: encodeVarint pb.maxJump.toNat) ++
  (if pb.maxOooKeys == 0#32 then [] else 0x10#8 :: encodeVarint pb.maxOooKeys.toNat)

/-- `prost::Message::decode` for `pqrpb::ChainParams`. -/
def decodeChainParamsPB : Bytes → ChainParamsPB → Option ChainParamsPB
  | [], acc => some acc
  | 0x08#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeChainParamsPB rest' { acc with maxJump := BitVec.ofNat 32 v }
    else none
  | 0x10#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeChainParamsPB rest' { acc with maxOooKeys := BitVec.ofNat 32 v }
    else none
  | _, _ => none
termination_by bs _ => bs.length

/-- `prost::Message::encode` for `pqrpb::Chain`. -/
def encodeChainPB (pb : ChainPB) : Bytes :=
  (if pb.direction == 0#32 then [] else 0x08#8 :: encodeVarint pb.direction.toNat) ++
  (if pb.currentEpoch == 0#64 then [] else 0x10#8 :: encodeVarint pb.currentEpoch.toNat) ++
  (pb.links.flatMap fun link => encodeTagLen 0x1a#8 (encodeChainEpochPB link)) ++
  (if pb.nextRoot.isEmpty then [] else encodeTagLen 0x22#8 pb.nextRoot) ++
  (if pb.sendEpoch == 0#64 then [] else 0x28#8 :: encodeVarint pb.sendEpoch.toNat) ++
  (match pb.params with | none => [] | some p => encodeTagLen 0x32#8 (encodeChainParamsPB p))

/-- `prost::Message::decode` for `pqrpb::Chain`. -/
def decodeChainPBLoop : Bytes → ChainPB → Option ChainPB
  | [], acc => some acc
  | 0x08#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with direction := BitVec.ofNat 32 v }
    else none
  | 0x10#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with currentEpoch := BitVec.ofNat 64 v }
    else none
  | 0x1a#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    let link ← decodeChainEpochPB b {}
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with links := acc.links ++ [link] }
    else none
  | 0x22#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with nextRoot := b }
    else none
  | 0x28#8 :: rest, acc => do
    let (v, rest') ← decodeVarint rest
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with sendEpoch := BitVec.ofNat 64 v }
    else none
  | 0x32#8 :: rest, acc => do
    let (b, rest') ← decodeLenBytes rest
    let p ← decodeChainParamsPB b {}
    if rest'.length < rest.length then
      decodeChainPBLoop rest' { acc with params := some p }
    else none
  | _, _ => none
termination_by bs _ => bs.length

def decodeChainPB (bs : Bytes) : Option ChainPB :=
  decodeChainPBLoop bs {}

/-! ## Error Formatting (`format_chain_err`) -/

def formatError : Error → String
  | .epochOutOfRange ep => s!"EpochOutOfRange:{ep.toNat}"
  | .sendKeyEpochDecreased a b => s!"SendKeyEpochDecreased:{a.toNat}:{b.toNat}"
  | .keyJump ctr atIdx => s!"KeyJump:{ctr.toNat}:{atIdx.toNat}"
  | .keyTrimmed atIdx => s!"KeyTrimmed:{atIdx.toNat}"
  | .keyAlreadyRequested atIdx => s!"KeyAlreadyRequested:{atIdx.toNat}"
  | .stateDecode => "StateDecode"
  | .chainNotAvailable => "ChainNotAvailable"
  | _ => "Other"

def formatChainError : ChainError → String
  | .err e => formatError e
  | .panic p => s!"Panic:{reprStr p}"

/-! ## `cedGcTrace` Replay -/

/-- Parameters for `cedGcTrace` (`max_jump = 25`, `max_ooo_keys = 10`, `trim_size = 12`). -/
def cedGcParams : ChainParamsPB :=
  { maxJump := 25#32, maxOooKeys := 10#32 }

def execCedStep (ced : ChainEpochDirection) (step : CedStepVec) :
    ChainEpochDirection × KeyOpResult :=
  if step.op == "next_key" then
    match ced.nextKey realHkdf with
    | .ok (ced', (idx, k)) => (ced', .okIdxKey idx k)
    | .error p => (ced, .err s!"Panic:{reprStr p}")
  else if step.op == "key" then
    match ced.key realHkdf step.arg cedGcParams with
    | .ok (ced', k) => (ced', .okKey k)
    | .error e => (ced, .err (formatChainError e))
  else
    (ced, .err s!"UnknownOp:{step.op}")

/-- Check a single `CedStepVec` transition and `intoPb`/`fromPb` + wire round-trip. -/
def checkCedStep (ced : ChainEpochDirection) (step : CedStepVec) :
    ChainEpochDirection × Bool :=
  let (ced', actualRes) := execCedStep ced step
  let argOk :=
    if step.op == "next_key" then
      match actualRes with
      | .okIdxKey idx _ => idx == step.arg
      | _ => false
    else true
  let pb := ced'.intoPb
  let stepOk :=
    argOk &&
    actualRes == step.result &&
    ced'.ctr == step.ctrAfter &&
    ced'.next == step.nextAfter &&
    ced'.prev.data == step.prevDataAfter &&
    pb.ctr == step.ctrAfter &&
    pb.next == step.nextAfter &&
    pb.prev == step.prevDataAfter &&
    decodeEpochDirectionPB (encodeEpochDirectionPB pb) {} == some pb &&
    ChainEpochDirection.fromPb pb == .ok ced'
  (ced', stepOk)

def checkCedTraceSteps (ced : ChainEpochDirection) : List CedStepVec → List Bool
  | [] => []
  | step :: rest =>
    let (ced', ok) := checkCedStep ced step
    ok :: checkCedTraceSteps ced' rest

/-- Find the first mismatching step index (0-based) in `cedGcTrace`, or `none` if all match. -/
def firstCedMismatch? (ced : ChainEpochDirection) (steps : List CedStepVec) (idx : Nat := 0) :
    Option (Nat × CedStepVec × KeyOpResult × ChainEpochDirection) :=
  match steps with
  | [] => none
  | step :: rest =>
    let (ced', actualRes) := execCedStep ced step
    let (_, ok) := checkCedStep ced step
    if ok then
      firstCedMismatch? ced' rest (idx + 1)
    else
      some (idx, step, actualRes, ced')

/-! ## `aliceChainTrace` and `bobChainTrace` Replay -/

/-- Parameters for `aliceChainTrace` and `bobChainTrace` (`max_jump = 15`, `max_ooo_keys = 6`). -/
def chainTraceParams : ChainParamsPB :=
  ({ maxJump := 15#32, maxOooKeys := 6#32 : ChainParams }).intoPb

def execChainStep (c : Chain) (step : ChainStepVec) : Chain × KeyOpResult :=
  if step.op == "add_epoch" then
    match c.addEpoch realHkdf { epoch := step.epoch, secret := step.indexOrSecret } with
    | .ok c' => (c', .okKey [])
    | .error p => (c, .err s!"Panic:{reprStr p}")
  else if step.op == "send_key" then
    match c.sendKey realHkdf step.epoch with
    | .ok (c', (idx, k)) => (c', .okIdxKey idx k)
    | .error e => (c, .err (formatChainError e))
  else if step.op == "recv_key" then
    match c.recvKey realHkdf step.epoch step.indexArg with
    | .ok (c', k) => (c', .okKey k)
    | .error e => (c, .err (formatChainError e))
  else
    (c, .err s!"UnknownOp:{step.op}")

/-- Check a single `ChainStepVec` transition, its protobuf wire encoding/decoding `chainPbAfter`,
and `Chain.fromPb` round-trip (matching `tools/spqr-vectors/src/main.rs:823–833`). -/
def checkChainStep (c : Chain) (step : ChainStepVec) : Chain × Bool :=
  let (c', actualRes) := execChainStep c step
  let pb := c'.intoPb
  let encodedPb := encodeChainPB pb
  let decodedPb? := decodeChainPB step.chainPbAfter
  let idxOk :=
    if step.op == "send_key" then
      match actualRes with
      | .okIdxKey idx _ => idx == step.indexArg
      | .err _ => step.indexArg == 0#32
      | _ => false
    else true
  match Chain.fromPb pb, decodedPb?.map Chain.fromPb with
  | .ok cRoundTrip, some (.ok cFromWire) =>
    let stepOk :=
      idxOk &&
      actualRes == step.result &&
      encodedPb == step.chainPbAfter &&
      decodedPb? == some pb &&
      cRoundTrip == c' &&
      cFromWire == c'
    (cFromWire, stepOk)
  | _, _ => (c', false)

def checkChainTraceSteps (c : Chain) : List ChainStepVec → List Bool
  | [] => []
  | step :: rest =>
    let (c', ok) := checkChainStep c step
    ok :: checkChainTraceSteps c' rest

/-- Find the first mismatching step index (0-based) in a `Chain` trace, or `none` if all match. -/
def firstChainMismatch? (c : Chain) (steps : List ChainStepVec) (idx : Nat := 0) :
    Option (Nat × ChainStepVec × KeyOpResult × Bytes) :=
  match steps with
  | [] => none
  | step :: rest =>
    let (c', actualRes) := execChainStep c step
    let (_, ok) := checkChainStep c step
    if ok then
      firstChainMismatch? c' rest (idx + 1)
    else
      some (idx, step, actualRes, encodeChainPB c'.intoPb)

def aliceInitChain? : Except Error Chain :=
  Chain.new realHkdf chainInitKey .a2b chainTraceParams

def bobInitChain? : Except Error Chain :=
  Chain.new realHkdf chainInitKey .b2a chainTraceParams

/-- Check initial Alice chain protobuf serialization, wire decode, `chainFrom`, and `aliceChainTrace`. -/
def runAliceChainTrace : Bool :=
  let vn : VersionNegotiationPB :=
    { authKey := chainInitKey
      direction := Direction.a2b.toI32
      minVersion := 1#32
      chainParams := some chainTraceParams }
  match aliceInitChain?, decodeChainPB aliceChainInitPb with
  | .ok c0, some pbDecoded =>
    let pb0 := c0.intoPb
    encodeChainPB pb0 == aliceChainInitPb &&
      pbDecoded == pb0 &&
      Chain.fromPb pbDecoded == .ok c0 &&
      chainFrom realHkdf none (some vn) == .ok c0 &&
      chainFrom realHkdf (some pbDecoded) none == .ok c0 &&
      (checkChainTraceSteps c0 aliceChainTrace).all id
  | _, _ => false

/-- Check initial Bob chain protobuf serialization, wire decode, `chainFrom`, and `bobChainTrace`. -/
def runBobChainTrace : Bool :=
  let vn : VersionNegotiationPB :=
    { authKey := chainInitKey
      direction := Direction.b2a.toI32
      minVersion := 1#32
      chainParams := some chainTraceParams }
  match bobInitChain?, decodeChainPB bobChainInitPb with
  | .ok c0, some pbDecoded =>
    let pb0 := c0.intoPb
    encodeChainPB pb0 == bobChainInitPb &&
      pbDecoded == pb0 &&
      Chain.fromPb pbDecoded == .ok c0 &&
      chainFrom realHkdf none (some vn) == .ok c0 &&
      chainFrom realHkdf (some pbDecoded) none == .ok c0 &&
      (checkChainTraceSteps c0 bobChainTrace).all id
  | _, _ => false

/-! ## Cross-Trace Alice/Bob Key Agreement -/

/-- Extract all successful `(epoch, index, key)` triples sent in a trace. -/
def sentKeys (steps : List ChainStepVec) : List (Epoch × BitVec 32 × Bytes) :=
  steps.filterMap fun s =>
    if s.op == "send_key" then
      match s.result with
      | .okIdxKey idx k => some (s.epoch, idx, k)
      | _ => none
    else none

/-- Extract all successful `(epoch, index, key)` triples received in a trace (excluding `(0, 0)`). -/
def recvdKeys (steps : List ChainStepVec) : List (Epoch × BitVec 32 × Bytes) :=
  steps.filterMap fun s =>
    if s.op == "recv_key" && !(s.epoch == 0#64 && s.indexArg == 0#32) then
      match s.result with
      | .okKey k => some (s.epoch, s.indexArg, k)
      | _ => none
    else none

/-- Every key received by Bob was sent by Alice with the exact same `(epoch, index, key)`, and
every key received by Alice on epochs 1 and 2 was sent by Bob with the exact same `(epoch, index, key)`. -/
def checkAliceBobKeyAgreement : Bool :=
  let aliceSent := sentKeys aliceChainTrace
  let bobRecvd := recvdKeys bobChainTrace
  let bobSent := sentKeys bobChainTrace
  let aliceRecvdFromBob := (recvdKeys aliceChainTrace).filter fun (ep, _, _) => ep == 1#64 || ep == 2#64
  bobRecvd.length == 9 &&
    aliceRecvdFromBob.length == 3 &&
    bobRecvd.all (fun entry => aliceSent.contains entry) &&
    aliceRecvdFromBob.all (fun entry => bobSent.contains entry)

/-! ## Kernel-checked parameter theorem and `#guard` vector checks -/

theorem guard_chain_trace_params :
    cedGcParams.maxJumpOrDefault = 25#32 ∧
      cedGcParams.maxOooKeysOrDefault = 10#32 ∧
      cedGcParams.trimSize = 12 ∧
      chainTraceParams.maxJumpOrDefault = 15#32 ∧
      chainTraceParams.maxOooKeysOrDefault = 6#32 ∧
      chainTraceParams.trimSize = 7 := by
  decide +kernel

-- SHA-256 and HMAC-SHA256 sanity checks:
#guard sha256With sha256Compress (asciiBytes "abc") ==
  unhex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard sha256With sha256Compress [] ==
  unhex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hmacWith sha256Compress (asciiBytes "Jefe") (asciiBytes "what do ya want for nothing?") ==
  unhex "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

-- Part 1: `cedGcTrace` (18 steps)
#guard cedInitKey.length == 32
#guard cedGcTrace.length == 18
#guard (firstCedMismatch? (ChainEpochDirection.new cedInitKey) cedGcTrace).isNone
#guard checkCedTraceSteps (ChainEpochDirection.new cedInitKey) cedGcTrace == List.replicate 18 true

-- Part 2: `aliceChainInitPb` and `aliceChainTrace` (25 steps)
#guard chainInitKey.length == 32
#guard aliceChainTrace.length == 25
#guard (match aliceInitChain? with | .ok c0 => (firstChainMismatch? c0 aliceChainTrace).isNone | _ => false)
#guard (match aliceInitChain? with | .ok c0 => checkChainTraceSteps c0 aliceChainTrace == List.replicate 25 true | _ => false)
#guard runAliceChainTrace

-- Part 3: `bobChainInitPb` and `bobChainTrace` (18 steps)
#guard bobChainTrace.length == 18
#guard (match bobInitChain? with | .ok c0 => (firstChainMismatch? c0 bobChainTrace).isNone | _ => false)
#guard (match bobInitChain? with | .ok c0 => checkChainTraceSteps c0 bobChainTrace == List.replicate 18 true | _ => false)
#guard runBobChainTrace

-- Part 4: Cross-trace Alice/Bob send/recv key agreement
#guard checkAliceBobKeyAgreement

end CryptoVerification.SpqrV1.Vectors.ChainCheck
