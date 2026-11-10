/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Authenticator
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Chain
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Polynomial
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Authenticator
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Chain
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Polynomial
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Protocol

/-!
# Differential Vector Checks for `Proto.lean`

Checks the `prost` protobuf codec in `Proto.lean` against all protobuf vectors in
`Vectors/Authenticator.lean`, `Vectors/Chain.lean`, `Vectors/Polynomial.lean`, and
`Vectors/Protocol.lean`, together with adversarial wire-format edge cases.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.ProtoCheck

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1

/-! ## `Authenticator` Vectors -/

def checkAuthVec (v : Vectors.Authenticator.AuthUpdateVec) : Bool :=
  let expected : ProtoAuthenticator := { rootKey := v.rootKeyAfter, macKey := v.macKeyAfter }
  ProtoAuthenticator.decode v.pbBytesAfter == .ok expected &&
  ProtoAuthenticator.encode expected == v.pbBytesAfter

/-- Check that every `Authenticator::update` vector decodes to the exact `(rootKeyAfter, macKeyAfter)`
and re-encodes to the exact `pbBytesAfter`. -/
def checkAuthVectors : Bool :=
  Vectors.Authenticator.authUpdateVectors.all checkAuthVec

#guard checkAuthVectors

/-! ## `ChainPB` Vectors -/

/-- Check that a serialized `ChainPB` protobuf decodes and re-encodes to the exact same bytes, and
passes `Chain.fromPb` from `Chain.lean`. -/
def checkChainBlob (bs : Bytes) : Bool :=
  match ChainPB.decode bs with
  | .ok c => ChainPB.encode c == bs && (Chain.fromPb c).isOk
  | .error _ => false

/-- Check `aliceChainInitPb`, `bobChainInitPb`, and all `chainPbAfter` in `aliceChainTrace` and
`bobChainTrace`. -/
def checkChainVectors : Bool :=
  checkChainBlob Vectors.Chain.aliceChainInitPb &&
  checkChainBlob Vectors.Chain.bobChainInitPb &&
  (Vectors.Chain.aliceChainTrace.all fun s => checkChainBlob s.chainPbAfter) &&
  (Vectors.Chain.bobChainTrace.all fun s => checkChainBlob s.chainPbAfter)

#guard checkChainVectors
theorem checkChainInitPb_ok :
    (checkChainBlob Vectors.Chain.aliceChainInitPb && checkChainBlob Vectors.Chain.bobChainInitPb) = true := by
  decide +kernel

/-! ## `PolynomialEncoder` and `PolynomialDecoder` Vectors -/

/-- Check `pointsEncoderPb`, `polysEncoderPb`, and all scenario `midDecoderPb` in a `PolyMsgTestVec`. -/
def checkPolyBundle (v : Vectors.Polynomial.PolyMsgTestVec) : Bool :=
  let pointsOk :=
    match PolynomialEncoder.decode v.pointsEncoderPb with
    | .ok pe =>
      pe.idx == 0#32 &&
      pe.pts.length == 16 &&
      pe.polys.isEmpty &&
      PolynomialEncoder.encode pe == v.pointsEncoderPb
    | .error _ => false
  let polysOk :=
    match PolynomialEncoder.decode v.polysEncoderPb with
    | .ok pe =>
      pe.pts.isEmpty &&
      pe.polys.length == 16 &&
      PolynomialEncoder.encode pe == v.polysEncoderPb
    | .error _ => false
  let scenariosOk :=
    v.scenarios.all fun sc =>
      match PolynomialDecoder.decode sc.midDecoderPb with
      | .ok pd =>
        pd.ptsNeeded.toNat == v.msgLen / 2 &&
        pd.polys == 16#32 &&
        pd.pts.length == 16 &&
        pd.isComplete == false &&
        PolynomialDecoder.encode pd == sc.midDecoderPb
      | .error _ => false
  pointsOk && polysOk && scenariosOk

def checkPolyVectors : Bool :=
  Vectors.Polynomial.polyMsgVectors.all checkPolyBundle

#guard checkPolyVectors

/-! ## `PqRatchetState` Round-Trip and Protocol Run Vectors -/

/-- Match the decoded `PqRatchetState` inner state tag name against the vector's `variant` string. -/
def stateMatchesVariant (st : PqRatchetState) (variant : String) : Bool :=
  if variant == "EmptyV0" then
    st.inner.isNone && st.chain.isNone && st.versionNegotiation.isNone
  else
    match st.inner with
    | none => false
    | some (.v1 v1) =>
      match v1.innerState with
      | some (.keysUnsampled _)        => variant == "KeysUnsampled"
      | some (.keysSampled _)          => variant == "KeysSampled"
      | some (.headerSent _)           => variant == "HeaderSent"
      | some (.ct1Received _)          => variant == "Ct1Received"
      | some (.ekSentCt1Received _)    => variant == "EkSentCt1Received"
      | some (.noHeaderReceived _)     => variant == "NoHeaderReceived"
      | some (.headerReceived _)       => variant == "HeaderReceived"
      | some (.ct1Sampled _)           => variant == "Ct1Sampled"
      | some (.ekReceivedCt1Sampled _) => variant == "EkReceivedCt1Sampled"
      | some (.ct1Acknowledged _)      => variant == "Ct1Acknowledged"
      | some (.ct2Sampled _)           => variant == "Ct2Sampled"
      | none                           => false

def checkStateRoundTripVectors : Bool :=
  Vectors.Protocol.stateRoundTripVectors.all fun v =>
    match spqrDecodeState v.stateBytes with
    | .ok st => stateMatchesVariant st v.variant && Proto.encodeState st == v.stateBytes
    | .error _ => false

#guard checkStateRoundTripVectors

/-- Check that a serialized `PqRatchetState` blob decodes and re-encodes to the exact same bytes. -/
def checkStateBlob (bs : Bytes) : Bool :=
  match spqrDecodeState bs with
  | .ok st => Proto.encodeState st == bs
  | .error _ => false

/-- Check every state (`aliceInitialState`, `bobInitialState`, `stateBytes`, `newState`) in a
`ProtocolRunVec`. -/
def checkProtocolRunStates (run : Vectors.Protocol.ProtocolRunVec) : Bool :=
  checkStateBlob run.aliceInitialState &&
  checkStateBlob run.bobInitialState &&
  run.steps.all fun s =>
    checkStateBlob s.stateBytes &&
    checkStateBlob s.newState

#guard checkProtocolRunStates Vectors.Protocol.runInOrder
#guard checkProtocolRunStates Vectors.Protocol.runReordered
#guard checkProtocolRunStates Vectors.Protocol.runDropped

/-- Check that the tampered-message vectors expecting `"StateDecode"` fail at `spqrDecodeState`,
and all other `stateBytes` in `tamperedRecvVectors` round-trip cleanly. -/
def checkTamperedDecodeVectors : Bool :=
  Vectors.Protocol.tamperedRecvVectors.all fun v =>
    if v.expectedError == "StateDecode" then
      spqrDecodeState v.stateBytes == .error .stateDecode
    else
      checkStateBlob v.stateBytes

#guard checkTamperedDecodeVectors

/-! ## Adversarial Wire-Format Guards -/

/-- Adversarial edge-case checks for `prost` 0.14.4 decoding:
1. 100 nested empty unknown groups (`0x7b`×100 ++ `0x7c`×100, tag 15 `startGroup`/`endGroup`)
   succeeds at depth `100..1`.
2. 101 nested groups (`0x7b`×101 ++ `0x7c`×101) fails with `.recursionLimitExceeded`.
3. 100 nested groups with an inner varint (`0x7b`×100 ++ `[0x08, 0x01]` ++ `0x7c`×100) fails with
   `.recursionLimitExceeded` (`Error.stateDecode` via `spqrDecodeState`) because `skip_field` calls
   `ctx.limit_reached()?` at depth 0 before dispatching on `wire_type`.
4. Wire-type mismatch (`[0x08, 0x00]` on `PqRatchetState`, tag 1 with `varint` instead of
   `lengthDelimited`) fails with `.unexpectedWireType .lengthDelimited .varint`.
5. 11-byte varint (`0x80`×10 ++ `[0x01]`) fails with `.invalidVarint`.
6. Tag 0 (`[0x00, 0x00]`) fails with `.invalidTag 0#32`.
7. Key `> u32::MAX` (`Proto.encodeVarint 0x100000000#64`) fails with `.invalidKey 0x100000000#64`.
8. Sub-message overrun (`[0x0a, 0x05, 0x01, 0x02]`) fails with `.bufferUnderflow`. -/
def checkAdversarialProto : Bool :=
  let grp100 := List.replicate 100 0x7b#8 ++ List.replicate 100 0x7c#8
  let grp101 := List.replicate 101 0x7b#8 ++ List.replicate 101 0x7c#8
  let grp100Varint := List.replicate 100 0x7b#8 ++ [0x08#8, 0x01#8] ++ List.replicate 100 0x7c#8
  Proto.decodeState grp100 == .ok default &&
  Proto.decodeState grp101 == .error .recursionLimitExceeded &&
  Proto.decodeState grp100Varint == .error .recursionLimitExceeded &&
  spqrDecodeState grp100Varint == .error .stateDecode &&
  Proto.decodeState [0x08#8, 0x00#8] == .error (.unexpectedWireType .lengthDelimited .varint) &&
  Proto.decodeVarint (List.replicate 10 0x80#8 ++ [0x01#8]) == .error .invalidVarint &&
  Proto.decodeState [0x00#8, 0x00#8] == .error (.invalidTag 0#32) &&
  Proto.decodeState (Proto.encodeVarint 0x100000000#64) == .error (.invalidKey 0x100000000#64) &&
  Proto.decodeState [0x0a#8, 0x05#8, 0x01#8, 0x02#8] == .error .bufferUnderflow

#guard checkAdversarialProto
theorem checkAdversarialProto_ok : checkAdversarialProto = true := by decide +kernel

end CryptoVerification.SpqrV1.Vectors.ProtoCheck
