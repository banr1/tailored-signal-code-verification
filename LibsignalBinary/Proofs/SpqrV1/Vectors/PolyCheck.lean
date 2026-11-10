/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Proofs.SpqrV1.Vectors.Polynomial
public meta import LibsignalBinary.Proofs.SpqrV1.Vectors.Polynomial
public meta import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly

/-!
# Differential Vector Checks for `Poly.lean`

Checks `PolyEncoder`, `PolyDecoder`, protobuf round-trips, and Lagrange basis tables in
`Poly.lean` against `Vectors/Polynomial.lean` via `decide +kernel` (on `polyMsg64`) and `#guard`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Vectors.PolyCheck

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Vectors.Polynomial

def encodeVarintAux : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | fuel + 1, n =>
    if n < 128 then
      [BitVec.ofNat 8 n]
    else
      BitVec.ofNat 8 ((n % 128) + 128) :: encodeVarintAux fuel (n / 128)

def encodeVarint (n : Nat) : List (BitVec 8) :=
  encodeVarintAux 10 n

/-- Proto3 wire encoding of `ProtoPolynomialEncoder` (`src/proto/pq_ratchet.proto:8–16`). -/
def encodeProtoPolynomialEncoder (pb : ProtoPolynomialEncoder) : List (BitVec 8) :=
  let f1 := if pb.idx == 0#32 then [] else 0x08#8 :: encodeVarint pb.idx.toNat
  let f2 := pb.pts.flatMap (fun b => 0x12#8 :: encodeVarint b.length ++ b)
  let f3 := pb.polys.flatMap (fun b => 0x1a#8 :: encodeVarint b.length ++ b)
  f1 ++ f2 ++ f3

/-- Proto3 wire encoding of `ProtoPolynomialDecoder` (`src/proto/pq_ratchet.proto:18–23`). -/
def encodeProtoPolynomialDecoder (pb : ProtoPolynomialDecoder) : List (BitVec 8) :=
  let f1 := if pb.ptsNeeded == 0#32 then [] else 0x08#8 :: encodeVarint pb.ptsNeeded.toNat
  let f2 := if pb.polys == 0#32 then [] else 0x10#8 :: encodeVarint pb.polys.toNat
  let f3 := pb.pts.flatMap (fun b => 0x1a#8 :: encodeVarint b.length ++ b)
  let f4 := if pb.isComplete then [0x20#8, 0x01#8] else []
  f1 ++ f2 ++ f3 ++ f4

/-- Step `PolyEncoder.nextChunk` across a list of expected `ChunkVec`s. -/
def checkEncoderChunks : PolyEncoder → List ChunkVec → Option PolyEncoder
  | enc, [] => some enc
  | enc, expected :: rest =>
    match enc.nextChunk with
    | .ok (enc', c) =>
      if c.index == expected.index && c.data.val == expected.data then
        checkEncoderChunks enc' rest
      else
        none
    | .error _ => none

/-- Check `PolyEncoder` (`encodeBytes`, `intoPb`/`fromPb` in `Points` state, all `nextChunk` outputs,
and `intoPb`/`fromPb` in `Polys` state) against a `PolyMsgTestVec`. -/
def checkEncoderBundle (v : PolyMsgTestVec) : Bool :=
  match PolyEncoder.encodeBytes v.msg with
  | .ok (.ok enc0) =>
    let pb0 := enc0.intoPb
    let pb0Ok := encodeProtoPolynomialEncoder pb0 == v.pointsEncoderPb
    let rt0Ok :=
      match PolyEncoder.fromPb pb0 with
      | .ok (.ok enc0Rt) => enc0Rt == enc0
      | _ => false
    match checkEncoderChunks enc0 v.chunks with
    | some encFinal =>
      let pbFinal := encFinal.intoPb
      let pbFinalOk := encodeProtoPolynomialEncoder pbFinal == v.polysEncoderPb
      let rtFinalOk :=
        match PolyEncoder.fromPb pbFinal with
        | .ok (.ok encFinalRt) => encFinalRt == encFinal
        | _ => false
      pb0Ok && rt0Ok && pbFinalOk && rtFinalOk
    | none => false
  | _ => false

/-- Step a `PolyDecoder` through `chunkIndices` for one `DecoderScenarioVec`. -/
def checkDecoderScenarioSteps (v : PolyMsgTestVec) (s : DecoderScenarioVec) :
    Nat → PolyDecoder → List (BitVec 16) → Bool
  | _, _, [] => false
  | step, dec, cidx :: rest =>
    let decOpt : Option PolyDecoder :=
      if step == s.midPbStep then
        let pb := dec.intoPb
        if encodeProtoPolynomialDecoder pb == s.midDecoderPb then
          match PolyDecoder.fromPb pb with
          | .ok (.ok decRt) => some decRt
          | _ => none
        else
          none
      else
        some dec
    match decOpt with
    | none => false
    | some dec1 =>
      match dec1.decodedMessage with
      | .ok none =>
        match v.chunks[cidx.toNat]? with
        | none => false
        | some cVec =>
          if cVec.index != cidx then
            false
          else if h : cVec.data.length = 32 then
            match dec1.addChunk { index := cVec.index, data := ⟨cVec.data, h⟩ } with
            | .error _ => false
            | .ok dec2 =>
              match dec2.decodedMessage with
              | .ok (some reconstructed) =>
                reconstructed == v.msg && rest.isEmpty && s.completedAtStep == some (step + 1)
              | .ok none =>
                checkDecoderScenarioSteps v s (step + 1) dec2 rest
              | .error _ => false
          else
            false
      | _ => false

def checkDecoderScenario (v : PolyMsgTestVec) (s : DecoderScenarioVec) : Bool :=
  match PolyDecoder.new s.msgLen with
  | .ok (.ok dec0) => checkDecoderScenarioSteps v s 0 dec0 s.chunkIndices
  | _ => false

def checkAllScenarios (v : PolyMsgTestVec) : Bool :=
  v.scenarios.all (checkDecoderScenario v)

 def runCheckPolyMsg64Kernel : Bool :=
  checkEncoderBundle polyMsg64 &&
    match polyMsg64.scenarios with
    | s :: _ => checkDecoderScenario polyMsg64 s
    | [] => false

/-- Kernel-checked `checkEncoderBundle` and first `DecoderScenarioVec` on `polyMsg64`. -/
theorem check_polyMsg64_kernel : runCheckPolyMsg64Kernel = true := by
  decide +kernel

/-! ## Full Differential Vector and Basis-Table Guards -/

#guard checkEncoderBundle polyMsg64
#guard checkAllScenarios polyMsg64

#guard checkEncoderBundle polyMsg96
#guard checkAllScenarios polyMsg96

#guard checkEncoderBundle polyMsg160
#guard checkAllScenarios polyMsg160

#guard (lagrangePolysForCompletePoints 30).isOk
#guard (lagrangePolysForCompletePoints 34).isOk
#guard (lagrangePolysForCompletePoints 36).isOk

#guard checkEncoderBundle polyMsg960
#guard checkAllScenarios polyMsg960

#guard checkEncoderBundle polyMsg1152
#guard checkAllScenarios polyMsg1152

end CryptoVerification.SpqrV1.Vectors.PolyCheck

