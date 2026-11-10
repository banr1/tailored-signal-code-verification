/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol


/-!
# Differential Vector Checks for `States.lean` and Assembled `Top.lean`

Checks `States`, wire serialization, ML-KEM wrappers, and assembled `spqrDeps` (`send`,
`recv`, `initialState`, `currentVersion`, `spqrV1Assembled`, `spqrV1RecvAssembled`) against
`Vectors/Protocol.lean`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.StatesCheck

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Vectors.Protocol

def toVec? (n : Nat) (xs : Bytes) : Option (List.Vector (BitVec 8) n) :=
  if h : xs.length = n then some ⟨xs, h⟩ else none

instance : Repr Chunk where
  reprPrec c p := reprPrec (c.index, c.data.toList) p

/-- Systematic polynomial encoder for in-order chunks (`index < k`). -/
structure SysEncoder where
  idx : BitVec 32
  msg : Bytes
  deriving DecidableEq, Repr

/-- Systematic polynomial decoder for in-order chunks (`index < k`). -/
structure SysDecoder where
  pts_needed : BitVec 32
  chunks : List (BitVec 16 × Bytes)
  is_complete : Bool
  deriving DecidableEq, Repr

def lookupTestChunk (idx : BitVec 16) : List (BitVec 16 × Bytes) → Option Bytes
  | [] => none
  | (k, v) :: rest => if k == idx then some v else lookupTestChunk idx rest

/-- Reconstruct `numChunks` consecutive 32-byte chunks `0 .. numChunks - 1` if all are present. -/
def reconstructTestChunks (numChunks : Nat) (chunks : List (BitVec 16 × Bytes)) : Option Bytes :=
  let rec go (i : Nat) (fuel : Nat) (acc : Bytes) : Option Bytes :=
    match fuel with
    | 0 => some acc
    | fuel' + 1 =>
      match lookupTestChunk (BitVec.ofNat 16 i) chunks with
      | some c => go (i + 1) fuel' (acc ++ c)
      | none => none
  go 0 numChunks []

/-- Deserialize 34-byte `(idx_hi :: idx_lo :: 32B)` records from `pb.pts[0]` back into `chunks`. -/
def deserializeTestChunks : Nat → Bytes → Option (List (BitVec 16 × Bytes))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, hi :: lo :: rest =>
    if rest.length < 32 then none
    else
      let idx : BitVec 16 := (hi.zeroExtend 16 <<< 8) ||| lo.zeroExtend 16
      let chunkBytes := rest.take 32
      match deserializeTestChunks fuel (rest.drop 32) with
      | some tail => some ((idx, chunkBytes) :: tail)
      | none => none
  | _ + 1, [_] => none

/-- Test `PolyApi` instance for wire and in-order systematic chunking checks, using `Chunk`,
`PolynomialError`, and `EncodingError` from `Poly.lean` and `PolynomialEncoder` /
`PolynomialDecoder` from `Proto.lean`. -/
def testPolyApi : PolyApi where
  Chunk := Chunk
  PolynomialError := PolynomialError
  EncodingError := EncodingError
  PolyEncoder := SysEncoder
  PolyDecoder := SysDecoder
  mkChunk := Chunk.mk
  chunkIndex := Chunk.index
  chunkData := Chunk.data
  encode_bytes := fun msg =>
    if msg.length % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { idx := 0#32, msg := msg })
  next_chunk := fun enc =>
    let numChunks := if enc.msg.length / 32 == 0 then 1 else enc.msg.length / 32
    let chunkPos := enc.idx.toNat % numChunks
    let slice := (enc.msg.drop (chunkPos * 32)).take 32
    let padded := slice ++ List.replicate (32 - slice.length) 0#8
    match toVec? 32 padded with
    | some vec =>
      .ok ({ enc with idx := enc.idx + 1#32 },
           { index := BitVec.ofNat 16 chunkPos, data := vec })
    | none => .error (.site "testPolyApi.next_chunk")
  encoder_into_pb := fun enc =>
    { idx := enc.idx, pts := List.replicate 16 enc.msg, polys := [] }
  encoder_from_pb := fun pb =>
    if pb.pts.length == 16 && pb.polys.isEmpty then
      let msg := pb.pts.headD []
      if msg.length % 2 == 0 then
        .ok (.ok { idx := pb.idx, msg := msg })
      else
        .ok (.error .serializationInvalid)
    else
      .ok (.error .serializationInvalid)
  decoder_new := fun lenBytes =>
    if lenBytes % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { pts_needed := BitVec.ofNat 32 (lenBytes / 2), chunks := [], is_complete := false })
  add_chunk := fun dec chunk =>
    let existsIdx := (lookupTestChunk chunk.index dec.chunks).isSome
    let chunks' := if existsIdx then dec.chunks else dec.chunks ++ [(chunk.index, chunk.data.toList)]
    .ok { dec with chunks := chunks' }
  decoded_message := fun dec =>
    if dec.is_complete then
      .ok none
    else
      let totalBytes := dec.pts_needed.toNat * 2
      let numChunks := totalBytes / 32
      .ok (reconstructTestChunks numChunks dec.chunks)
  decoder_into_pb := fun dec =>
    let serialized := (dec.chunks.map fun (idx, d) =>
      [idx.extractLsb' 8 8, idx.extractLsb' 0 8] ++ d).flatten
    { ptsNeeded := dec.pts_needed, polys := 16#32,
      pts := serialized :: List.replicate 15 [], isComplete := dec.is_complete }
  decoder_from_pb := fun pb =>
    if pb.pts.length != 16 then
      .ok (.error .serializationInvalid)
    else
      let raw := pb.pts.headD []
      match deserializeTestChunks (raw.length / 34 + 1) raw with
      | some chunks =>
        .ok (.ok { pts_needed := pb.ptsNeeded, chunks := chunks, is_complete := pb.isComplete })
      | none => .ok (.error .serializationInvalid)

/-- Protobuf-identity `PolyApi` storing `Proto.lean`'s `PolynomialEncoder` and `PolynomialDecoder`
directly so `States.from_pb` and `States.into_pb` can be checked directly against every real
Rust-serialized `V1State` in `protocolRuns`, `tamperedRecvVectors`, and `stateRoundTripVectors`. -/
def pbIdentityPolyApi : PolyApi where
  Chunk := Chunk
  PolynomialError := PolynomialError
  EncodingError := EncodingError
  PolyEncoder := PolynomialEncoder
  PolyDecoder := PolynomialDecoder
  mkChunk := Chunk.mk
  chunkIndex := Chunk.index
  chunkData := Chunk.data
  encode_bytes := fun msg =>
    if msg.length % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { idx := 0#32, pts := List.replicate 16 msg, polys := [] })
  next_chunk := fun enc =>
    .ok ({ enc with idx := enc.idx + 1#32 },
         { index := enc.idx.truncate 16, data := List.Vector.replicate 32 0#8 })
  encoder_into_pb := id
  encoder_from_pb := fun pb => .ok (.ok pb)
  decoder_new := fun lenBytes =>
    if lenBytes % 2 != 0 then
      .ok (.error (.polynomialError .messageLengthEven))
    else
      .ok (.ok { ptsNeeded := BitVec.ofNat 32 (lenBytes / 2), polys := 16#32,
                 pts := List.replicate 16 [], isComplete := false })
  add_chunk := fun dec _ => .ok dec
  decoded_message := fun _ => .ok none
  decoder_into_pb := id
  decoder_from_pb := fun pb => .ok (.ok pb)

/-- Build a lookup-table `MlKem` from a list of recorded `MlKemCallVec` entries. `keyPair` is the
recorded `dk` (libcrux's whole 2400-byte `KeyPairCompressedBytes`); the recorded `hdr` / `ek` are
not used: `K.fromSeed` slices them out of `dk`, and `checkMlKemCall` checks they agree. -/
def mlKemOfCalls (calls : List MlKemCallVec) : MlKem where
  keyPair seed :=
    let seedL := seed.toList
    match calls.findSome? (fun
      | .fromSeed s _ _ dk => if s == seedL then some dk else none
      | _ => none) with
    | some dk =>
      match toVec? 2400 dk with
      | some dkV => dkV
      | none => List.Vector.replicate 2400 0#8
    | none => List.Vector.replicate 2400 0#8
  validPk hdr ek :=
    match calls.findSome? (fun
      | .validatePk h e v => if h == hdr && e == ek then some v else none
      | _ => none) with
    | some v => v
    | none => false
  encaps1 hdr rand :=
    let randL := rand.toList
    match calls.findSome? (fun
      | .encaps1 h r ct1 es ss => if h == hdr && r == randL then some (ct1, es, ss) else none
      | _ => none) with
    | some (ct1, es, ss) =>
      match toVec? 960 ct1, toVec? 2080 es, toVec? 32 ss with
      | some cV, some esV, some ssV => some (cV, esV, ssV)
      | _, _, _ => none
    | none => none
  encaps2 es ek :=
    let esL := es.toList
    let ekL := ek.toList
    match calls.findSome? (fun
      | .encaps2 es0 ek0 ct2 => if es0 == esL && ek0 == ekL then some ct2 else none
      | _ => none) with
    | some ct2 =>
      match toVec? 128 ct2 with
      | some cV => cV
      | none => List.Vector.replicate 128 0#8
    | none => List.Vector.replicate 128 0#8
  decaps dk ct1 ct2 :=
    let dkL := dk.toList
    let ct1L := ct1.toList
    let ct2L := ct2.toList
    match calls.findSome? (fun
      | .decaps dk0 c1 c2 ss =>
        if dk0 == dkL && c1 == ct1L && c2 == ct2L then some ss else none
      | _ => none) with
    | some ss =>
      match toVec? 32 ss with
      | some ssV => ssV
      | none => List.Vector.replicate 32 0#8
    | none => List.Vector.replicate 32 0#8

/-- `AuthApi` for replaying `runInOrder` through `States.send` and `States.recv`, using
`ProtoAuthenticator` from `Auth.lean` / `Proto.lean`. -/
def replayAuthApi : AuthApi where
  Authenticator := ProtoAuthenticator
  new := fun _ _ => .ok { rootKey := List.replicate 32 0#8, macKey := List.replicate 32 0#8 }
  update := fun auth _ _ => .ok auth
  mac_hdr := fun _ _ hdr =>
    -- In `runInOrder`, epoch 1 hdr (`blob4`) + mac is 96B (3 chunks); epoch 2 hdr (`blob163`) + mac is 96B.
    -- Return the trailing 32-byte MAC so `hdr ++ mac` has length 96.
    .ok (hdr.take 32)
  mac_ct := fun _ _ ct =>
    .ok (ct.take 32)
  verify_hdr := fun _ _ hdr expectedMac => do
    let cmp ← compare (hdr.take 32) expectedMac
    if cmp != 0#8 then .ok (.error .macVerifyFailed) else .ok (.ok ())
  verify_ct := fun _ _ ct expectedMac => do
    let cmp ← compare (ct.take 32) expectedMac
    if cmp != 0#8 then .ok (.error .macVerifyFailed) else .ok (.ok ())
  into_pb := id
  from_pb := id
  hkdf_to_vec := fun _ ikm _ okmLen =>
    .ok (ikm.take okmLen ++ List.replicate (okmLen - (ikm.take okmLen).length) 0#8)

/-- Check that a serialized `PqRatchetState` protobuf (`stateBytes`) decodes via
`spqrDecodeState` and that any `v1` inner state round-trips through `States.from_pb` and
`States.into_pb` with `States.from_pb pbIdentityPolyApi replayAuthApi st.into_pb == .ok st`
and `st.into_pb == v1Pb`. -/
def checkRealV1StatePbRoundTrip (stateBytes : Bytes) : Bool :=
  match spqrDecodeState stateBytes with
  | .error _ => false
  | .ok stPb =>
    match stPb.inner with
    | none => true
    | some (.v1 v1Pb) =>
      match States.from_pb pbIdentityPolyApi replayAuthApi v1Pb with
      | .ok st =>
        st.into_pb == v1Pb &&
        States.from_pb pbIdentityPolyApi replayAuthApi st.into_pb == .ok st
      | .error _ => false

/-- Check that a single `MlKemCallVec` matches `States.lean`'s `incremental_mlkem768` wrappers
(`generate`, `encaps1`, `encaps2`, `decaps`, `ek_matches_header`, and `issue1275` check). -/
def checkMlKemCall (c : MlKemCallVec) : Bool :=
  let K := mlKemOfCalls [c]
  match c with
  | .fromSeed seed hdr ek dk =>
    generate K seed == .ok ({ ek := ek, dk := dk, hdr := hdr }, [])
  | .encaps1 hdr rand ct1 es ss =>
    encaps1 K hdr rand == .ok ((ct1, es, ss), []) &&
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es == .ok none &&
    match flip_endianness_of_encapsulation_state es with
    | .ok flipped =>
      potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 flipped == .ok (some es)
    | .error _ => false
  | .encaps2 es ek ct2 =>
    encaps2 K ek es == .ok ct2 &&
    match flip_endianness_of_encapsulation_state es with
    | .ok flipped => encaps2 K ek flipped == .ok ct2
    | .error _ => false
  | .decaps dk ct1 ct2 ss =>
    decaps K dk ct1 ct2 == .ok ss
  | .validatePk hdr ek valid =>
    ek_matches_header K ek hdr == valid && validate_pk K hdr ek == valid

/-- Check that a protocol step's `msg` (for `"send"`) or `msgOrTape` (for `"recv"`)
round-trips through `msg_preamble`, `Message.deserialize`, and `Message.serialize`,
that both `step.stateBytes` and `step.newState` round-trip through `spqrDecodeState` and
`States.from_pb` / `States.into_pb`, and that all `mlkemCalls` in the step match `States.lean`'s
wrappers and RNG consumption. -/
def checkProtocolStepWireAndMlKem (step : ProtocolStepVec) : Bool :=
  let wireBytes := if step.op == "send" then step.msg else step.msgOrTape
  let wireOk :=
    match msg_preamble wireBytes with
    | .ok pre =>
      match Message.deserialize testPolyApi pre.epoch pre.remaining with
      | .ok msg =>
        pre.version == Version.V1.toU8 &&
        Version.fromU8? pre.version == some Version.V1 &&
        pre.epoch == msg.epoch &&
        pre.epoch.toNat > 0 &&
        !pre.remaining.isEmpty &&
        msg.serialize pre.index == wireBytes
      | .error _ => false
    | .error _ => false
  let statePbOk :=
    checkRealV1StatePbRoundTrip step.stateBytes &&
    checkRealV1StatePbRoundTrip step.newState
  let callsOk := step.mlkemCalls.all checkMlKemCall
  let tapeOk :=
    if step.op == "send" then
      match step.mlkemCalls with
      | [] => step.msgOrTape == []
      | [.fromSeed seed _ _ _] => step.msgOrTape.length == 64 && step.msgOrTape == seed
      | [.encaps1 _ rand _ _ _] => step.msgOrTape.length == 32 && step.msgOrTape == rand
      | _ => false
    else true
  wireOk && statePbOk && callsOk && tapeOk

-- 1. Check all 494 steps across `runInOrder`, `runReordered`, and `runDropped`:
#guard protocolRuns.all (fun run => run.steps.all checkProtocolStepWireAndMlKem)

-- 2. Check all 20 `stateRoundTripVectors` through `spqrDecodeState`, `States.from_pb`, and `States.into_pb`:
#guard stateRoundTripVectors.all (fun v => checkRealV1StatePbRoundTrip v.stateBytes)

-- 3. Check all `MlKemCallVec` entries across all 50 `tamperedRecvVectors`:
#guard tamperedRecvVectors.all (fun v => v.mlkemCalls.all checkMlKemCall)

/-- The libcrux keypair layout that `MlKem.fromSeed` assumes (`pk1Off` / `pk2Off`,
`Specifications/LibsignalSpqrV1/MlKem.lean`), on one recorded `from_seed` call: `dk` is the whole
2400-byte `KeyPairCompressedBytes`, and the recorded `pk1` (`hdr`) / `pk2` (`ek`) are its slices
`[pk1Off, pk1Off + 64)` / `[pk2Off, pk2Off + 1152)`. Other calls are unconstrained. -/
def fromSeedLayoutOk : MlKemCallVec → Bool
  | .fromSeed _ hdr ek dk =>
    dk.length == 2400 && hdr == (dk.drop pk1Off).take 64 && ek == (dk.drop pk2Off).take 1152
  | _ => true

def isFromSeedCall : MlKemCallVec → Bool
  | .fromSeed .. => true
  | _ => false

def protocolMlKemCalls : List MlKemCallVec :=
  protocolRuns.flatMap fun run => run.steps.flatMap (·.mlkemCalls)

-- 4. The recorded libcrux `from_seed` outputs have the layout `MlKem.fromSeed` slices out of
-- `MlKem.keyPair`: all 6 `from_seed` calls in `protocolRuns` (none in `tamperedRecvVectors`).
#guard (protocolMlKemCalls.filter isFromSeedCall).length == 6
#guard protocolMlKemCalls.all fromSeedLayoutOk
#guard !(tamperedRecvVectors.flatMap (·.mlkemCalls)).any isFromSeedCall

/-- Dummy HKDF for chain bounds/replay checks (`KeyJump`, `KeyAlreadyRequested`) that fail before KDF. -/
def dummyChainHkdf : HkdfFn := fun _ _ _ n => List.replicate n 0#8

/-- Fail-closed check of all 50 `tamperedRecvVectors` across all 9 `expectedError` categories
(`MsgDecode`, `MinimumVersion`, `VersionMismatch`, `StateDecode`, `EpochOutOfRange`, `KeyJump`,
`KeyAlreadyRequested`, `ErroneousDataReceived`, `MacVerifyFailed`) against `msg_preamble`,
`Version`, `Message.deserialize`, `spqrDecodeState`, `Chain.fromPb`, `Chain.recvKey`,
`States.from_pb`, and `States.recv`. -/
def checkTamperedWire (v : TamperedRecvVec) : Bool :=
  match v.expectedError with
  | "MsgDecode" =>
    match msg_preamble v.tamperedMsg with
    | .error .msgDecode => true
    | .ok pre =>
      pre.version == Version.V1.toU8 &&
      Message.deserialize testPolyApi pre.epoch pre.remaining == .error .msgDecode
    | _ => false
  | "MinimumVersion" =>
    match msg_preamble v.tamperedMsg with
    | .ok pre => pre.version < Version.V1.toU8
    | .error _ => false
  | "VersionMismatch" =>
    match msg_preamble v.tamperedMsg with
    | .ok pre => pre.version != Version.V1.toU8
    | .error _ => false
  | "StateDecode" =>
    spqrDecodeState v.stateBytes == .error .stateDecode
  | "EpochOutOfRange" =>
    match spqrDecodeState v.stateBytes, msg_preamble v.tamperedMsg with
    | .ok stPb, .ok pre =>
      match stPb.inner, Message.deserialize pbIdentityPolyApi pre.epoch pre.remaining with
      | some (.v1 v1Pb), .ok msg =>
        match States.from_pb pbIdentityPolyApi replayAuthApi v1Pb with
        | .ok st =>
          st.recv (mlKemOfCalls v.mlkemCalls) msg == .error (.err (.epochOutOfRange pre.epoch))
        | .error _ => false
      | _, _ => false
    | _, _ => false
  | "KeyJump" =>
    match spqrDecodeState v.stateBytes, msg_preamble v.tamperedMsg with
    | .ok stPb, .ok pre =>
      match stPb.chain, Message.deserialize testPolyApi pre.epoch pre.remaining with
      | some chainPb, .ok _ =>
        match Chain.fromPb chainPb with
        | .ok chain =>
          match chain.recvKey dummyChainHkdf (pre.epoch - 1#64) pre.index with
          | .error (.err (.keyJump _ _)) => true
          | _ => false
        | .error _ => false
      | _, _ => false
    | _, _ => false
  | "KeyAlreadyRequested" =>
    match spqrDecodeState v.stateBytes, msg_preamble v.tamperedMsg with
    | .ok stPb, .ok pre =>
      match stPb.chain with
      | some chainPb =>
        match Chain.fromPb chainPb with
        | .ok chain =>
          pre.version == Version.V1.toU8 &&
          chain.recvKey dummyChainHkdf (pre.epoch - 1#64) pre.index ==
            .error (.err (.keyAlreadyRequested pre.index))
        | .error _ => false
      | none => false
    | _, _ => false
  | "ErroneousDataReceived" =>
    match spqrDecodeState v.stateBytes, msg_preamble v.tamperedMsg, v.mlkemCalls with
    | .ok stPb, .ok pre, [.validatePk hdr ek false] =>
      match stPb.inner, Message.deserialize testPolyApi pre.epoch pre.remaining with
      | some (.v1 v1Pb), .ok msg =>
        let K := mlKemOfCalls v.mlkemCalls
        match States.from_pb pbIdentityPolyApi replayAuthApi v1Pb, msg.payload with
        | .ok st, .ekCt1Ack _ =>
          st.epoch == pre.epoch &&
          ek_matches_header K ek hdr == false &&
          validate_pk K hdr ek == false
        | _, _ => false
      | _, _ => false
    | _, _, _ => false
  | "MacVerifyFailed" =>
    match spqrDecodeState v.stateBytes, msg_preamble v.tamperedMsg with
    | .ok stPb, .ok pre =>
      match stPb.inner, Message.deserialize testPolyApi pre.epoch pre.remaining with
      | some (.v1 v1Pb), .ok msg =>
        match States.from_pb pbIdentityPolyApi replayAuthApi v1Pb, msg.payload with
        | .ok st, .hdr _ => st.epoch == pre.epoch && v.mlkemCalls.isEmpty
        | .ok st, .ct2 _ =>
          st.epoch == pre.epoch &&
          !v.mlkemCalls.isEmpty &&
          v.mlkemCalls.all checkMlKemCall
        | _, _ => false
      | _, _ => false
    | _, _ => false
  | _ => false

#guard tamperedRecvVectors.all checkTamperedWire

theorem tamperedRecv_wire_ok :
    ((tamperedRecvVectors.filter fun v =>
        v.expectedError == "MsgDecode" ||
        v.expectedError == "MinimumVersion" ||
        v.expectedError == "VersionMismatch").all checkTamperedWire) = true := by
  decide +kernel

/-- Extract the wire shape `(epoch, msgTypeU8, chunkIdx?)` of a `Message`. -/
def messageShape {P : PolyApi} (m : Message P) : Epoch × BitVec 8 × Option (BitVec 16) :=
  let t := (MessageType.from_payload m.payload).toU8
  let idx? := match m.payload with
    | .hdr c | .ek c | .ekCt1Ack c | .ct1 c | .ct2 c => some (P.chunkIndex c)
    | .none | .ct1Ack _ => none
  (m.epoch, t, idx?)

/-- Replay all 162 steps (81 sends + 81 recvs) of `runInOrder` through `States.send` and
`States.recv`, checking that at every step:
1. Both `stA` and `stB` round-trip exactly through `States.into_pb` and `States.from_pb`
   (`States.from_pb testPolyApi replayAuthApi st.into_pb == .ok st`);
2. `"send"` transitions cleanly, consumes the exact `msgOrTape` RNG bytes, and emits a `Message`
   with the exact `(epoch, MessageType, chunk.index)` of `runInOrder`'s `step.msg`;
3. `"recv"` deserializes `step.msgOrTape` via `msg_preamble` + `Message.deserialize`, verifies
   wire shape against the in-flight message, rejects out-of-range epochs with `.epochOutOfRange`,
   rejects tampered final chunks with `.macVerifyFailed` / `.erroneousDataReceived`, and
   transitions the receiver's `States` cleanly across Epoch 1 and Epoch 2. -/
def replayRunInOrder : Bool :=
  let allCalls := runInOrder.steps.flatMap ProtocolStepVec.mlkemCalls
  let K := mlKemOfCalls allCalls
  let pbRoundTrip (st : States testPolyApi replayAuthApi) : Bool :=
    States.from_pb testPolyApi replayAuthApi st.into_pb == .ok st
  let rec loop (steps : List ProtocolStepVec)
      (inFlight : List (Message testPolyApi))
      (stA stB : States testPolyApi replayAuthApi) : Bool :=
    if !(pbRoundTrip stA && pbRoundTrip stB) then false
    else
      match steps with
      | [] => inFlight.isEmpty && stA.epoch == 2#64 && stB.epoch == 2#64
      | step :: rest =>
        if step.op == "send" then
          let st := if step.actor == "A" then stA else stB
          match st.send K step.msgOrTape, msg_preamble step.msg with
          | .ok (sOut, []), .ok pre =>
            match Message.deserialize testPolyApi pre.epoch pre.remaining with
            | .ok wireMsg =>
              if messageShape sOut.msg == messageShape wireMsg &&
                 pbRoundTrip sOut.state then
                let stA' := if step.actor == "A" then sOut.state else stA
                let stB' := if step.actor == "B" then sOut.state else stB
                loop rest (inFlight ++ [sOut.msg]) stA' stB'
              else false
            | .error _ => false
          | _, _ => false
        else
          let st := if step.actor == "A" then stA else stB
          match inFlight, msg_preamble step.msgOrTape with
          | sentMsg :: restFlight, .ok pre =>
            match Message.deserialize testPolyApi pre.epoch pre.remaining with
            | .ok wireMsg =>
              let badEpoch := st.epoch + 2#64
              let badEpochMsg : Message testPolyApi := { sentMsg with epoch := badEpoch }
              let epochErrOk :=
                match st.recv K badEpochMsg with
                | .error (.err (.epochOutOfRange e)) => e == badEpoch
                | _ => false
              let tamperErrOk :=
                let ffVec := List.Vector.replicate 32 0xff#8
                match sentMsg.payload with
                | .hdr c =>
                  if c.index == 2#16 then
                    st.recv K { sentMsg with payload := .hdr { c with data := ffVec } } ==
                      .error (.err .macVerifyFailed)
                  else true
                | .ek c =>
                  if c.index == 35#16 then
                    st.recv K { sentMsg with payload := .ek { c with data := ffVec } } ==
                      .error (.err .erroneousDataReceived)
                  else true
                | .ekCt1Ack c =>
                  if c.index == 35#16 then
                    st.recv K { sentMsg with payload := .ekCt1Ack { c with data := ffVec } } ==
                      .error (.err .erroneousDataReceived)
                  else true
                | .ct2 c =>
                  if c.index == 4#16 then
                    st.recv K { sentMsg with payload := .ct2 { c with data := ffVec } } ==
                      .error (.err .macVerifyFailed)
                  else true
                | _ => true
              if messageShape sentMsg == messageShape wireMsg && epochErrOk && tamperErrOk then
                match st.recv K sentMsg with
                | .ok rOut =>
                  if pbRoundTrip rOut.state then
                    let stA' := if step.actor == "A" then rOut.state else stA
                    let stB' := if step.actor == "B" then rOut.state else stB
                    loop rest restFlight stA' stB'
                  else false
                | .error _ => false
              else false
            | .error _ => false
          | _, _ => false
  match States.init_a testPolyApi replayAuthApi (List.replicate 32 0#8),
        States.init_b testPolyApi replayAuthApi (List.replicate 32 0#8) with
  | .ok stA0, .ok stB0 => loop runInOrder.steps [] stA0 stB0
  | _, _ => false

-- 4. Replay all 162 steps of `runInOrder` end-to-end through `States.send` and `States.recv`:
#guard replayRunInOrder

/-- Check that `initialState` and `currentVersion` (`Top.lean`) with the real assembled `spqrDeps`
reproduce `aliceInitialState` and `bobInitialState` across all `protocolRuns`. -/
def checkAssembledInitialState (run : ProtocolRunVec) : Bool :=
  let deps := spqrDeps Tests.sha256Compress (mlKemOfCalls [])
  let authKey := (run.aliceInitialState.drop 4).take 32
  let paramsA : Params := {
    direction := .A2B
    version := .v1
    minVersion := .v1
    authKey := authKey
  }
  let paramsB : Params := {
    direction := .B2A
    version := .v1
    minVersion := .v1
    authKey := authKey
  }
  authKey.length == 32 &&
  initialState deps paramsA == .ok run.aliceInitialState &&
  initialState deps paramsB == .ok run.bobInitialState &&
  currentVersion deps run.aliceInitialState == .ok (.stillNegotiating .v1 .v1) &&
  currentVersion deps run.bobInitialState == .ok (.stillNegotiating .v1 .v1)

-- 5. Check `initialState` and `currentVersion` with real assembled `spqrDeps` on all 3 protocol runs:
#guard protocolRuns.all checkAssembledInitialState

/-- Check a single `ProtocolStepVec` against the real assembled `send` / `recv` (`Top.lean`)
(with `spqrDeps Tests.sha256Compress` and `spqrHkdfWith Tests.sha256Compress`),
`spqrV1Assembled`, and `spqrV1RecvAssembled`. -/
def checkAssembledProtocolStep (step : ProtocolStepVec) : Bool :=
  let K := mlKemOfCalls step.mlkemCalls
  let deps := spqrDeps Tests.sha256Compress K
  let hkdf := spqrHkdfWith Tests.sha256Compress
  let model := spqrV1Assembled Tests.sha256Compress K
  let recvModel := spqrV1RecvAssembled Tests.sha256Compress K
  if step.op == "send" then
    send deps hkdf step.stateBytes step.msgOrTape ==
      (.ok { state := step.newState, msg := step.msg, key := step.key }, []) &&
    (match messageKeyToSalt? step.key with
     | some salt => model.send step.stateBytes step.msgOrTape == some (step.newState, salt, step.msg)
     | none => false) &&
    sendPanicsB deps hkdf step.stateBytes step.msgOrTape == false
  else
    recv deps hkdf step.stateBytes step.msgOrTape ==
      .ok { state := step.newState, key := step.key } &&
    recvModel.recv step.stateBytes step.msgOrTape ==
      .ok (step.newState, step.key) &&
    (match messageKeyToSalt? step.key with
     | some salt => model.recv step.stateBytes step.msgOrTape == .ok (step.newState, salt)
     | none => false) &&
    recvPanicsB deps hkdf step.stateBytes step.msgOrTape == false &&
    recvPanicsSaltB deps hkdf step.stateBytes step.msgOrTape == false

-- 6. Check all steps of `runInOrder`, `runReordered`, and `runDropped` through the real
-- assembled `send`, `recv`, `spqrV1Assembled`, and `spqrV1RecvAssembled`:
#guard runInOrder.steps.all checkAssembledProtocolStep
#guard runReordered.steps.all checkAssembledProtocolStep
#guard runDropped.steps.all checkAssembledProtocolStep

/-- Check a `TamperedRecvVec` against the real assembled `recv` (`Top.lean`),
`spqrV1Assembled`, and `spqrV1RecvAssembled`. -/
def checkAssembledTamperedRecv (v : TamperedRecvVec) : Bool :=
  let K := mlKemOfCalls v.mlkemCalls
  let deps := spqrDeps Tests.sha256Compress K
  let hkdf := spqrHkdfWith Tests.sha256Compress
  let model := spqrV1Assembled Tests.sha256Compress K
  let recvModel := spqrV1RecvAssembled Tests.sha256Compress K
  let isStateDec := v.expectedError == "StateDecode"
  let modelOk :=
    recvModel.recv v.stateBytes v.tamperedMsg == .error isStateDec &&
    model.recv v.stateBytes v.tamperedMsg == .error isStateDec &&
    recvPanicsB deps hkdf v.stateBytes v.tamperedMsg == false &&
    recvPanicsSaltB deps hkdf v.stateBytes v.tamperedMsg == false
  let errOk :=
    match v.expectedError, recv deps hkdf v.stateBytes v.tamperedMsg with
    | "MsgDecode", .error (.err .msgDecode) => true
    | "MinimumVersion", .error (.err .minimumVersion) => true
    | "VersionMismatch", .error (.err .versionMismatch) => true
    | "StateDecode", .error (.err .stateDecode) => true
    | "EpochOutOfRange", .error (.err (.epochOutOfRange _)) => true
    | "KeyJump", .error (.err (.keyJump _ _)) => true
    | "KeyAlreadyRequested", .error (.err (.keyAlreadyRequested _)) => true
    | "ErroneousDataReceived", .error (.err .erroneousDataReceived) => true
    | "MacVerifyFailed", .error (.err .macVerifyFailed) => true
    | _, _ => false
  modelOk && errOk

-- 7. Check all 50 `tamperedRecvVectors` through the real assembled `recv`, `spqrV1Assembled`,
-- and `spqrV1RecvAssembled`:
#guard tamperedRecvVectors.all checkAssembledTamperedRecv

end CryptoVerification.SpqrV1.Vectors.StatesCheck

