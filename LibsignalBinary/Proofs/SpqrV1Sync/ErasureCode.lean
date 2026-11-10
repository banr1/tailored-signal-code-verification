/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.AddChunk
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecodedMessage
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.Encoder
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.PointAt

/-!
# SPQR V1 Polynomial Erasure Encoder, Decoder, and State Codecs

Specifications for the `spqrPolyApi` operations (`PolyEncoder.encodeBytes`, `nextChunk`,
`PolyDecoder.new`, `addChunk`, `decodedMessage`) and protobuf state conversions
(`PolyEncoder.intoPb` / `fromPb`, `PolyDecoder.intoPb` / `fromPb`) for even-length messages with
`msg.length ≤ 2 ^ 20`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Erasure

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open Polynomial

/-! ## Encoder -/

/-- `PolyEncoder.encodeBytes` initializes the 16-lane `msgPoints` layout at chunk counter `0`. -/
theorem encodeBytes_spec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0)
    (hlen : msg.length ≤ 2 ^ 20) :
    PolyEncoder.encodeBytes msg = .ok (.ok { idx := 0#32, s := .points (msgPoints msg) }) :=
  EncodeBytes.encodeBytes_spec_aux msg heven hlen

/-- `PolyEncoder.pointAt` evaluates lane `j` at `idxPt idx` and preserves `EncInv`. -/
theorem pointAt_spec (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) (j idx : Nat) (hj : j < 16) (hidx : idx < 2 ^ 16) :
    ∃ e', e.pointAt j idx = .ok (e', (msgPoly msg j).eval (idxPt idx)) ∧
      EncInv msg e' ∧ e'.idx = e.idx := by
  exact PointAt.pointAt_spec_impl msg e he hlen j idx hj hidx

/-- `PolyEncoder.chunkAt` emits `chunkData msg idx` and preserves `EncInv`. -/
theorem chunkAt_spec (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) (idx : BitVec 16) :
    ∃ e', e.chunkAt idx = .ok (e', { index := idx, data := chunkData msg idx }) ∧
      EncInv msg e' ∧ e'.idx = e.idx :=
  ChunkAt.chunkAt_spec_of_pointAt msg e he idx (fun e' he' j k hj hk => pointAt_spec msg e' he' hlen j k hj hk)

/-- `PolyEncoder.nextChunk` emits `chunkData msg` at the truncated 16-bit counter and increments
`e.idx`. -/
theorem nextChunk_spec (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) :
    ∃ e', e.nextChunk =
        .ok (e', { index := e.idx.setWidth 16, data := chunkData msg (e.idx.setWidth 16) }) ∧
      EncInv msg e' ∧ e'.idx = e.idx + 1#32 :=
  NextChunk.nextChunk_spec_of_chunkAt msg e (chunkAt_spec msg e he hlen (e.idx.setWidth 16))

/-! ## Decoder -/

/-- `PolyDecoder.new` initializes an empty decoder satisfying `DecInv msg ∅`. -/
theorem decoderNew_spec (msg : List (BitVec 8)) (heven : msg.length % 2 = 0) :
    ∃ dec, PolyDecoder.new msg.length = .ok (.ok dec) ∧ DecInv msg ∅ dec :=
  DecoderNew.decoderNew_spec_aux msg heven

/-- `PolyDecoder.addChunk` on an honest chunk preserves `DecInv` and extends the received index
set by `idx.toNat`. -/
theorem addChunk_spec (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (hlen : msg.length ≤ 2 ^ 20) (idx : BitVec 16) :
    ∃ dec', dec.addChunk { index := idx, data := chunkData msg idx } = .ok dec' ∧
      DecInv msg (insert idx.toNat S) dec' :=
  AddChunk.addChunk_spec_aux msg S dec hd hlen idx

/-- `PolyDecoder.decodedMessage` reconstructs `some msg` once at least `needed msg.length 0`
distinct chunk indices have been added. -/
theorem decodedMessage_spec (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (heven : msg.length % 2 = 0) (hlen : msg.length ≤ 2 ^ 20)
    (hS : needed msg.length 0 ≤ S.card) :
    dec.decodedMessage = .ok (some msg) := by
  exact DecodedMessage.decodedMessage_spec_aux msg S dec hd heven hlen hS

/-- With fewer than `needed msg.length 0` distinct chunk indices, `decodedMessage` returns
`.ok none`. -/
theorem decodedMessage_none (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (hS : S.card < needed msg.length 0) :
    dec.decodedMessage = .ok none := by
  exact DecodedMessage.decodedMessage_none_aux msg S dec hd hS

/-! ## State codecs -/

/-- `PolyEncoder.fromPb` inverts `PolyEncoder.intoPb` under `EncInv` when `32 ≤ msg.length ≤ 2 ^ 20`
(making all 16 polynomial coefficient lists non-empty). -/
theorem encoder_fromPb_intoPb (msg : List (BitVec 8)) (e : PolyEncoder) (he : EncInv msg e)
    (hlen : msg.length ≤ 2 ^ 20) (hshort : 32 ≤ msg.length) :
    PolyEncoder.fromPb e.intoPb = .ok (.ok e) := by
  exact EncoderCodec.encoder_fromPb_intoPb_proof msg e he hlen hshort

/-- `PolyDecoder.fromPb` inverts `PolyDecoder.intoPb` under `DecInv` when `msg.length ≤ 2 ^ 20`. -/
theorem decoder_fromPb_intoPb (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (hlen : msg.length ≤ 2 ^ 20) :
    PolyDecoder.fromPb dec.intoPb = .ok (.ok dec) :=
  DecoderCodec.decoder_fromPb_intoPb msg S dec hd hlen

end CryptoVerification.SpqrV1Sync.Erasure
