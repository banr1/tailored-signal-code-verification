/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# SPQR V1: Top-Level `States`, `Chain::encoded_len`, and `encodeState_len_lt` Bounds

Bounds `rawV1State` across `States.from_pb`, `States.init_a`, `States.init_b`, `States.send`,
and `States.recv`, and proves that under the `DEV-SPQR3` input bound (`state.length < 2^32`),
every constructed `Chain` satisfies `ChainEncodedLenFits` (`< 2^61`) and every output state
from `send`, `recv`, `spqrV1`, and `spqrV1Recv` has length `< 2^61`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.StateSize

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HKDF (Salt)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr

/-! ## `PolyDecoder` Point-Count Helpers and `States` Transition Bounds -/

@[simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
@[simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]
@[simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]
@[simp] private theorem liftM_spqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    (liftM r : Except StatesPanic α) = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
@[simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

theorem PolyDecoder.fromPb_ptsNeeded {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) :
    dec.ptsNeeded = pb.ptsNeeded.toNat := by
  unfold PolyDecoder.fromPb pbToProtoPolyDecoder at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · rcases except_bind_eq_ok h with ⟨ptsRes, _, h2⟩; cases ptsRes with
    | error _ => simp [Pure.pure, Except.pure] at h2
    | ok outPts => have hinj := Except.ok.inj (Except.ok.inj h2); subst hinj; rfl

theorem PolyDecoder.newWithPolyCount_ptsNeeded {lenBytes polys : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.newWithPolyCount lenBytes polys = .ok (.ok dec)) :
    dec.ptsNeeded = lenBytes / 2 := by
  unfold PolyDecoder.newWithPolyCount at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · have hinj := Except.ok.inj (Except.ok.inj h); subst hinj; rfl

theorem PolyDecoder.new_ptsNeeded {lenBytes : Nat} {dec : PolyDecoder}
    (h : PolyDecoder.new lenBytes = .ok (.ok dec)) : dec.ptsNeeded = lenBytes / 2 :=
  PolyDecoder.newWithPolyCount_ptsNeeded h

theorem PolyDecoder.addChunkLoop_ptsNeeded (chunk : Chunk) :
    ∀ (i rem : Nat) (self self' : PolyDecoder),
      PolyDecoder.addChunkLoop chunk i rem self = .ok self' → self'.ptsNeeded = self.ptsNeeded
  | _, 0, self, self', h => by rw [PolyDecoder.addChunkLoop] at h; exact (Except.ok.inj h) ▸ rfl
  | i, rem + 1, self, self', h => by
    rw [PolyDecoder.addChunkLoop] at h; cases hget : self.pts[(chunk.index.toNat * 16 + i) % 16]? with
    | none => rw [hget] at h; contradiction
    | some polyPts =>
      rw [hget] at h; rw [PolyDecoder.addChunkLoop_ptsNeeded chunk (i + 1) rem _ self' h]; split <;> rfl

theorem PolyDecoder.addChunk_ptsNeeded {self self' : PolyDecoder} {chunk : Chunk}
    (h : self.addChunk chunk = .ok self') : self'.ptsNeeded = self.ptsNeeded :=
  PolyDecoder.addChunkLoop_ptsNeeded chunk 0 16 self self' h

set_option maxHeartbeats 400000 in
theorem PolyDecoder.decodedMessageLoop_length (self : PolyDecoder) (pointsVecs : List (List Pt)) :
    ∀ (i rem : Nat) (polys polys' : List (Option Poly)) (out out' : Bytes),
      PolyDecoder.decodedMessageLoop self pointsVecs i rem polys out = .ok (polys', out') → out'.length = out.length + 2 * rem
  | _, 0, _, _, out, out', h => by
    rw [PolyDecoder.decodedMessageLoop] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).2; subst hinj; omega
  | i, rem + 1, polys, polys', out, out', h => by
    rw [PolyDecoder.decodedMessageLoop] at h; cases hpts : self.pts[i % 16]? with
    | none => rw [hpts] at h; nomatch h
    | some polyPts =>
      rw [hpts] at h; dsimp only [] at h; have hu16 : ∀ v, (u16ToBeBytes v).length = 2 := fun _ => rfl
      split at h
      · split at h <;> [skip; exact nomatch h]
        have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem polys polys' _ out' h
        rw [ih, List.length_append, hu16]; omega
      · split at h <;> [skip; exact nomatch h]; rename_i optPoly _; cases optPoly with
        | some _ =>
          dsimp only [] at h; simp only [pure_bind_except] at h; split at h <;> [skip; exact nomatch h]
          rcases except_bind_eq_ok h with ⟨yVal, _, h2⟩
          have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem polys polys' _ out' h2
          rw [ih, List.length_append, hu16]; omega
        | none =>
          dsimp only [] at h; split at h <;> [skip; exact nomatch h]
          rcases except_bind_eq_ok h with ⟨interp, _, h1⟩; simp only [pure_bind_except] at h1
          split at h1 <;> [skip; exact nomatch h1]; rcases except_bind_eq_ok h1 with ⟨yVal, _, h2⟩
          have ih := PolyDecoder.decodedMessageLoop_length self pointsVecs (i + 1) rem _ polys' _ out' h2
          rw [ih, List.length_append, hu16]; omega

theorem PolyDecoder.decodedMessage_length {self : PolyDecoder} {out : Bytes}
    (h : self.decodedMessage = .ok (some out)) : out.length = 2 * self.ptsNeeded := by
  unfold PolyDecoder.decodedMessage at h; dsimp only [] at h; split at h
  · simp [Pure.pure, Except.pure] at h
  · rcases except_bind_eq_ok h with ⟨⟨retNone, pointsVecs⟩, _, h1⟩; dsimp only [] at h1; split at h1
    · simp [Pure.pure, Except.pure] at h1
    · split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨⟨polys', out1⟩, hloop, h2⟩
      have hinj := Option.some.inj (Except.ok.inj h2); subst hinj
      simpa using PolyDecoder.decodedMessageLoop_length self pointsVecs 0 self.ptsNeeded
        (List.replicate 16 none) polys' [] out1 hloop

private theorem poly_nextChunk_liftM_eq_ok {enc enc' : PolyEncoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.next_chunk enc) :
      Except StatesPanic (spqrPolyApi.PolyEncoder × spqrPolyApi.Chunk)) = .ok (enc', chunk)) :
    enc.nextChunk = .ok (enc', chunk) := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_addChunk_liftM_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.add_chunk dec chunk) : Except StatesPanic spqrPolyApi.PolyDecoder) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_addChunk_ofPanic_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk dec chunk) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)
private theorem poly_decodedMessage_liftM_eq_ok {dec : PolyDecoder} {msg? : Option Bytes}
    (h : (liftM (spqrPolyApi.decoded_message dec) : Except StatesPanic (Option Bytes)) = .ok msg?) :
    dec.decodedMessage = .ok msg? := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_decoderNew_liftM_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : (liftM (spqrPolyApi.decoder_new lenBytes) :
      Except StatesPanic (Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder)) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
private theorem poly_decoderNew_ofPanic_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : StatesResult.ofPanic (spqrPolyApi.decoder_new lenBytes) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

theorem expectEncodeBytes_raw_le {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ 1048928 := by
  unfold expectEncodeBytes spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1); cases res with
  | error _ => contradiction
  | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact PolyEncoder.encodeBytes_raw_le h1'

theorem expectDecoderNew_raw_le {site : String} {lenBytes : Nat} {dec : PolyDecoder}
    (h : expectDecoderNew spqrPolyApi site lenBytes = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ 352 ∧ dec.ptsNeeded = lenBytes / 2 := by
  unfold expectDecoderNew at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := poly_decoderNew_liftM_eq_ok h1; cases res with
  | error _ => contradiction
  | ok dec' => have hinj := Except.ok.inj h2; subst hinj; exact ⟨PolyDecoder.new_raw_le h1', PolyDecoder.new_ptsNeeded h1'⟩

theorem encoderFromPbStateDecode_raw_le {pb? : Option PolynomialEncoder} {dec : PolyEncoder}
    (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyEnc (protoPolyEncoderToPb dec.intoPb) ≤ optRaw rawPolyEnc pb? := by
  unfold encoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1); cases res with
    | error _ => contradiction
    | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact PolyEncoder.fromPb_raw_le h1'

theorem decoderFromPbStateDecode_raw_le {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ optRaw rawPolyDec pb? ∧
      ∃ d, pb? = some d ∧ dec.ptsNeeded = d.ptsNeeded.toNat := by
  unfold decoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1); cases res with
    | error _ => contradiction
    | ok dec' => have hinj := Except.ok.inj h2; subst hinj; exact ⟨PolyDecoder.fromPb_raw_le h1', pb, rfl, PolyDecoder.fromPb_ptsNeeded h1'⟩

theorem generate_lengths {K : MlKem} {tape tape' : Bytes} {keys : Keys}
    (h : generate K tape = .ok (keys, tape')) :
    keys.ek.length = 1152 ∧ keys.dk.length = 2400 ∧ keys.hdr.length = 64 := by
  unfold generate at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
  exact ⟨List.Vector.toList_length _, List.Vector.toList_length _, List.Vector.toList_length _⟩

theorem encaps1_lengths {K : MlKem} {hdr tape tape' : Bytes}
    {ct1 : Ciphertext1} {es : EncapsulationState} {ss : Secret}
    (h : encaps1 K hdr tape = .ok ((ct1, es, ss), tape')) :
    ct1.length = 960 ∧ es.length = 2080 ∧ ss.length = 32 := by
  unfold encaps1 at h; split at h <;> [contradiction; skip]; split at h <;> [contradiction; skip]
  have hinj := (Prod.mk.inj (Except.ok.inj h)).1
  have h1 := (Prod.mk.inj hinj).1; have h2 := (Prod.mk.inj (Prod.mk.inj hinj).2).1
  have h3 := (Prod.mk.inj (Prod.mk.inj hinj).2).2; subst h1; subst h2; subst h3
  exact ⟨List.Vector.toList_length _, List.Vector.toList_length _, List.Vector.toList_length _⟩

theorem ek_matches_header_length {K : MlKem} {ek : EncapsulationKey} {hdr : Header}
    (h : ek_matches_header K ek hdr = true) : ek.length = 1152 := by
  unfold ek_matches_header MlKem.validPkBytes at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

/-! ### Unchunked `from_pb` bounds -/

@[local simp] private theorem spqrPolyApi_encoder_into_pb (enc : spqrPolyApi.PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_encoder_into_pb' (enc : PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb (dec : spqrPolyApi.PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrPolyApi_decoder_into_pb' (dec : PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[local simp] private theorem spqrAuthApi_into_pb {F : ShaCompress}
    (a : (spqrAuthApi F).Authenticator) : (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl
@[local simp] private theorem spqrAuthApi_into_pb' {F : ShaCompress} (a : Authenticator) :
    (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl
@[local simp] private theorem spqrAuthApi_from_pb {F : ShaCompress} (pb : ProtoAuthenticator) :
    (spqrAuthApi F).from_pb pb = Authenticator.fromPb pb := rfl

attribute [local simp]
  States.into_pb Chunked.SendEk.KeysUnsampled.into_pb Chunked.SendEk.KeysSampled.into_pb
  Chunked.SendEk.HeaderSent.into_pb Chunked.SendEk.Ct1Received.into_pb
  Chunked.SendEk.EkSentCt1Received.into_pb Chunked.SendCt.NoHeaderReceived.into_pb
  Chunked.SendCt.HeaderReceived.into_pb Chunked.SendCt.Ct1Sampled.into_pb
  Chunked.SendCt.EkReceivedCt1Sampled.into_pb Chunked.SendCt.Ct1Acknowledged.into_pb
  Chunked.SendCt.Ct2Sampled.into_pb rawV1State rawInnerState rawChKeysUnsampled rawChKeysSampled
  rawChHeaderSent rawChCt1Received rawChEkSentCt1Received rawChNoHeaderReceived rawChHeaderReceived
  rawChCt1Sampled rawChEkReceivedCt1Sampled rawChCt1Acknowledged rawChCt2Sampled
  Option.map optRaw_none optRaw_some Authenticator.rawAuth_intoPb_fromPb

theorem ucKeysUnsampled_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.KeysUnsampled}
    {s : Unchunked.SendEk.KeysUnsampled (spqrAuthApi F)} (h : Unchunked.SendEk.KeysUnsampled.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcKeysUnsampled s.into_pb = rawUcKeysUnsampled pb := by
  unfold Unchunked.SendEk.KeysUnsampled.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.KeysUnsampled.into_pb, rawUcKeysUnsampled, hauth]

theorem ucHeaderSent_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.HeaderSent}
    {s : Unchunked.SendEk.HeaderSent (spqrAuthApi F)} (h : Unchunked.SendEk.HeaderSent.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcHeaderSent s.into_pb = rawUcHeaderSent pb := by
  unfold Unchunked.SendEk.HeaderSent.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.HeaderSent.into_pb, rawUcHeaderSent, hauth]

theorem ucEkSent_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.EkSent}
    {s : Unchunked.SendEk.EkSent (spqrAuthApi F)} (h : Unchunked.SendEk.EkSent.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcEkSent s.into_pb = rawUcEkSent pb := by
  unfold Unchunked.SendEk.EkSent.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSent.into_pb, rawUcEkSent, hauth]

theorem ucEkSentCt1Received_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.EkSentCt1Received}
    {s : Unchunked.SendEk.EkSentCt1Received (spqrAuthApi F)} (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcEkSentCt1Received s.into_pb = rawUcEkSentCt1Received pb := by
  unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSentCt1Received.into_pb, rawUcEkSentCt1Received, hauth]

theorem ucNoHeaderReceived_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.NoHeaderReceived}
    {s : Unchunked.SendCt.NoHeaderReceived (spqrAuthApi F)} (h : Unchunked.SendCt.NoHeaderReceived.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcNoHeaderReceived s.into_pb = rawUcNoHeaderReceived pb := by
  unfold Unchunked.SendCt.NoHeaderReceived.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.NoHeaderReceived.into_pb, rawUcNoHeaderReceived, hauth]

theorem ucHeaderReceived_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.HeaderReceived}
    {s : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)} (h : Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcHeaderReceived s.into_pb = rawUcHeaderReceived pb := by
  unfold Unchunked.SendCt.HeaderReceived.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.HeaderReceived.into_pb, rawUcHeaderReceived, hauth]

theorem ucCt1Sent_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.Ct1Sent}
    {s : Unchunked.SendCt.Ct1Sent (spqrAuthApi F)} (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcCt1Sent s.into_pb = rawUcCt1Sent pb := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1Sent.into_pb, rawUcCt1Sent, hauth]

theorem ucCt1SentEkReceived_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)} (h : Unchunked.SendCt.Ct1SentEkReceived.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcCt1SentEkReceived s.into_pb = rawUcCt1SentEkReceived pb := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawUcCt1SentEkReceived, hauth]

theorem ucCt2Sent_from_pb_raw_eq {F : ShaCompress} {pb : V1State.Unchunked.Ct2Sent}
    {s : Unchunked.SendCt.Ct2Sent (spqrAuthApi F)} (h : Unchunked.SendCt.Ct2Sent.from_pb (spqrAuthApi F) pb = .ok s) :
    rawUcCt2Sent s.into_pb = rawUcCt2Sent pb := by
  unfold Unchunked.SendCt.Ct2Sent.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct2Sent.into_pb, rawUcCt2Sent, hauth]

/-! ### Chunked `States` invariant and `from_pb` / `init` / `send` / `recv` bounds -/

/-- Well-formedness bound on `receiving_ct1.ptsNeeded` in `States.headerSent` (checked by
`Chunked.SendEk.HeaderSent.from_pb` at `src/v1/chunked/send_ek/serialize.rs:53–57` and established by
`KeysSampled.recv_ct1_chunk` at `src/v1/chunked/send_ek.rs:88`). -/
def StatesPtsNeededBound {F : ShaCompress} : States spqrPolyApi (spqrAuthApi F) → Prop
  | .headerSent s => s.receiving_ct1.ptsNeeded ≤ 480
  | _ => True

set_option maxHeartbeats 400000 in
theorem States.from_pb_raw_le {F : ShaCompress} {pb : V1State}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st) :
    rawV1State st.into_pb ≤ rawV1State pb ∧ StatesPtsNeededBound st := by
  unfold States.from_pb at h; cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h; cases inner with
    | keysUnsampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.KeysUnsampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', h2⟩; have hinj2 := Except.ok.inj h2; subst hinj2
        have heq := ucKeysUnsampled_from_pb_raw_eq huc'; exact ⟨by simp [hinner, huc, heq], trivial⟩
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.KeysSampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucHeaderSent_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.HeaderSent.from_pb at hv
      have hchk : ∀ d, s.receivingCt1 = some d → d.ptsNeeded.toNat = CIPHERTEXT1_SIZE / 2 := by
        intro d hd; rw [hd] at hv; dsimp only [] at hv; by_contra hne
        have htr : (d.ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2) = true := bne_iff_ne.mpr hne
        rw [htr] at hv; contradiction
      cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
          rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩; contradiction
      | some d0 =>
        have hd_pts := hchk d0 hrec
        have hfls : (d0.ptsNeeded.toNat != CIPHERTEXT1_SIZE / 2) = false := bne_eq_false_iff_eq.mpr hd_pts
        rw [hrec] at hv; dsimp only [] at hv; rw [hfls] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
          have h1 := ucEkSent_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
          rcases decoderFromPbStateDecode_raw_le hdec with ⟨h3, d, hd, hpts⟩
          have hd_eq := Option.some.inj hd; subst hd_eq; simp only [optRaw_some] at h3
          refine ⟨by simp [hinner, huc, hrec, h1]; omega, ?_⟩
          simp only [StatesPtsNeededBound, hpts, hd_pts, CIPHERTEXT1_SIZE]; omega
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.Ct1Received.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucEkSentCt1Received_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.EkSentCt1Received.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApi F) u
            let receivingCt2 ← decoderFromPbStateDecode spqrPolyApi s.receivingCt2
            Except.ok { uc := uc, receiving_ct2 := receivingCt2 }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucEkSentCt1Received_from_pb_raw_eq huc'; have h2 := (decoderFromPbStateDecode_raw_le hdec).1
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.NoHeaderReceived.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.NoHeaderReceived.from_pb (spqrAuthApi F) u
            let receivingHdr ← decoderFromPbStateDecode spqrPolyApi s.receivingHdr
            Except.ok { uc := uc, receiving_hdr := receivingHdr }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucNoHeaderReceived_from_pb_raw_eq huc'; have h2 := (decoderFromPbStateDecode_raw_le hdec).1
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | headerReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.HeaderReceived.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApi F) u
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucHeaderReceived_from_pb_raw_eq huc'; have h2 := (decoderFromPbStateDecode_raw_le hdec).1
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct1Sampled.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u
            let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi s.sendingCt1
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) =
              Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
        have h1 := ucCt1Sent_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
        have h3 := (decoderFromPbStateDecode_raw_le hdec).1; refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt1SentEkReceived_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApi F) u
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt1Sent_from_pb_raw_eq huc'; have h2 := (decoderFromPbStateDecode_raw_le hdec).1
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct2Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt2Sent_from_pb_raw_eq huc'; have h2 := encoderFromPbStateDecode_raw_le henc
        refine ⟨?_, trivial⟩; simp [hinner, huc, h1]; omega

attribute [local simp]
  Unchunked.SendEk.KeysUnsampled.into_pb Unchunked.SendEk.HeaderSent.into_pb
  Unchunked.SendEk.EkSent.into_pb Unchunked.SendEk.EkSentCt1Received.into_pb
  Unchunked.SendCt.NoHeaderReceived.into_pb Unchunked.SendCt.HeaderReceived.into_pb
  Unchunked.SendCt.Ct1Sent.into_pb Unchunked.SendCt.Ct1SentEkReceived.into_pb
  Unchunked.SendCt.Ct2Sent.into_pb
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent

theorem States.init_a_raw_le {F : ShaCompress} {authKey : Bytes}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok st) :
    rawV1State st.into_pb ≤ 72 ∧ StatesPtsNeededBound st := by
  unfold States.init_a Chunked.SendEk.KeysUnsampled.new Unchunked.SendEk.KeysUnsampled.new spqrAuthApi at h
  dsimp only [Bind.bind, Except.bind] at h; have hinj := Except.ok.inj h; subst hinj
  have hauth := Authenticator.new_rawAuth_le F authKey 1#64; refine ⟨?_, trivial⟩; simp; omega

theorem States.init_b_raw_le {F : ShaCompress} {authKey : Bytes}
    {st : States spqrPolyApi (spqrAuthApi F)}
    (h : States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok st) :
    rawV1State st.into_pb ≤ 424 ∧ StatesPtsNeededBound st := by
  unfold States.init_b at h; rcases except_bind_eq_ok h with ⟨s, hs, hst⟩
  have hst_eq := Except.ok.inj hst; subst hst_eq
  unfold Chunked.SendCt.NoHeaderReceived.new Unchunked.SendCt.NoHeaderReceived.new at hs
  rcases except_bind_eq_ok hs with ⟨decRes, hdec, hs1⟩; rcases except_bind_eq_ok hs1 with ⟨uc, huc, h2⟩
  unfold spqrAuthApi at huc; dsimp only [Bind.bind, Except.bind] at huc
  have huc_eq := Except.ok.inj huc; subst huc_eq
  have hdec' := poly_decoderNew_liftM_eq_ok hdec; cases decRes with
  | error _ => contradiction
  | ok dec =>
    have hinj := Except.ok.inj h2; subst hinj
    have hauth := Authenticator.new_rawAuth_le F authKey 1#64
    have hpoly := PolyDecoder.new_raw_le hdec'; refine ⟨?_, trivial⟩; simp; omega

theorem spqrDeps_initV1Inner_raw_le {F : ShaCompress} {K : MlKem}
    {dir : Direction} {authKey : Bytes} {v1pb : V1State}
    (h : (spqrDeps F K).initV1Inner dir authKey = .ok v1pb) : rawV1State v1pb ≤ 424 := by
  unfold spqrDeps at h; dsimp only at h; cases dir with
  | a2b =>
    cases ha : States.init_a spqrPolyApi (spqrAuthApi F) authKey <;> rw [ha] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; have hle := (States.init_a_raw_le ha).1; omega
  | b2a =>
    cases hb : States.init_b spqrPolyApi (spqrAuthApi F) authKey <;> rw [hb] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; exact (States.init_b_raw_le hb).1

theorem initInner_spqrDeps_raw_le {F : ShaCompress} {K : MlKem}
    {v : Version} {dir : Direction} {authKey : Bytes} {inner? : Option V1State}
    (h : initInner (spqrDeps F K) v dir authKey = .ok inner?) :
    optRaw rawPqInner (inner?.map PqRatchetState.Inner.v1) ≤ 424 := by
  unfold initInner at h; cases v with
  | v0 => dsimp only at h; have hinj := Except.ok.inj h; subst hinj; simp
  | v1 =>
    dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
    rename_i v1pb hv1; have hinj := Except.ok.inj h; subst hinj
    simpa only [Option.map, optRaw_some, rawPqInner] using spqrDeps_initV1Inner_raw_le hv1

/-! ### `States.send` and `States.recv` bounds -/

theorem States.send_raw_le {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {tape tape' : Bytes}
    {sendOut : V1Send spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.send K tape = .ok (sendOut, tape')) :
    rawV1State sendOut.state.into_pb ≤ rawV1State self.into_pb + 1052480 ∧
      StatesPtsNeededBound sendOut.state := by
  unfold States.send at h; cases self with
  | keysUnsampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk, tape1⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header at h1
    dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨⟨uc, toSend, mac, tape2⟩, huc, h1b⟩
    rcases except_bind_eq_ok huc with ⟨⟨keys, tape3⟩, hgen, huc2⟩; rcases except_bind_eq_ok huc2 with ⟨mac', _, huc3⟩
    have huc_eq := (Prod.mk.inj (Except.ok.inj huc3)).1; subst huc_eq
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩; rcases except_bind_eq_ok h1c with ⟨⟨enc1, chunk1⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq
    rcases generate_lengths hgen with ⟨hek, hdk, _⟩; have henc0_le := expectEncodeBytes_raw_le henc0
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
    refine ⟨?_, trivial⟩; simp [hek, hdk]; omega
  | keysSampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, trivial⟩; simp; omega
  | headerSent state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.HeaderSent.send_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, hpts⟩; simp; omega
  | ct1Received state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendEk.Ct1Received.send_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, trivial⟩; simp; omega
  | ekSentCt1Received state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | noHeaderReceived state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | headerReceived state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk, sec, tape1⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk Unchunked.SendCt.HeaderReceived.send_ct1 at h1
    dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨⟨uc, ct1, sec1, tape2⟩, huc, h1b⟩
    rcases except_bind_eq_ok huc with ⟨⟨⟨ct1', es, ss⟩, tape3⟩, henc1, huc2⟩; rcases except_bind_eq_ok huc2 with ⟨secret, _, huc3⟩
    rcases except_bind_eq_ok huc3 with ⟨auth, hauth, huc4⟩; unfold spqrAuthApi at hauth
    dsimp only [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at hauth
    have hauth_eq := Except.ok.inj hauth; subst hauth_eq; have huc_inj := Prod.mk.inj (Except.ok.inj huc4)
    have huc_eq := huc_inj.1; have hct1_eq := (Prod.mk.inj huc_inj.2).1; subst huc_eq; subst hct1_eq
    rcases except_bind_eq_ok h1b with ⟨enc0, henc0, h1c⟩; rcases except_bind_eq_ok h1c with ⟨⟨enc1, chunk1⟩, hnext, h1d⟩
    have hst_eq := (Prod.mk.inj (Except.ok.inj h1d)).1; subst hst_eq; rcases encaps1_lengths henc1 with ⟨hct1_len, hes_len, _⟩
    have hauth_le := Authenticator.update_rawAuth_le F state.uc.auth state.uc.epoch secret
    have henc0_le := expectEncodeBytes_raw_le henc0
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
    refine ⟨?_, trivial⟩; simp [hct1_len, hes_len]; omega
  | ct1Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, trivial⟩; simp; omega
  | ekReceivedCt1Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, trivial⟩; simp; omega
  | ct1Acknowledged state =>
    dsimp only [] at h; have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | ct2Sampled state =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨⟨state', chunk⟩, h1, h2⟩
    rw [statesResult_ofPanic_eq_ok] at h1; have hinj := (Prod.mk.inj (Except.ok.inj h2)).1; subst hinj
    unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨⟨enc1, chunk1⟩, hnext, h1b⟩; have hst_eq := (Prod.mk.inj (Except.ok.inj h1b)).1; subst hst_eq
    have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext); refine ⟨?_, trivial⟩; simp; omega

set_option maxHeartbeats 400000 in
theorem States.recv_raw_le {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.recv K msg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State self.into_pb + 1052480 ∧
      StatesPtsNeededBound recvOut.state := by
  unfold States.recv at h; cases self with
  | keysUnsampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | keysSampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      rcases except_bind_eq_ok h1c with ⟨enc0, henc0, h1d⟩; have hs' := Except.ok.inj h1d; subst hs'
      rcases expectDecoderNew_raw_le hdec0 with ⟨hdec0_le, hdec0_pts⟩
      have hadd' := poly_addChunk_liftM_eq_ok hadd; have hadd_le := PolyDecoder.addChunk_raw_le hadd'
      have hadd_pts := PolyDecoder.addChunk_ptsNeeded hadd'; have henc0_le := expectEncodeBytes_raw_le henc0
      refine ⟨by simp [Unchunked.SendEk.HeaderSent.send_ek]; omega, ?_⟩
      simp only [StatesPtsNeededBound, hadd_pts, hdec0_pts, CIPHERTEXT1_SIZE]; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | headerSent state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, hpts⟩)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, hmsg, h1c⟩
      have hadd' := poly_addChunk_liftM_eq_ok hadd; have hmsg' := poly_decodedMessage_liftM_eq_ok hmsg
      have hadd_le := PolyDecoder.addChunk_raw_le hadd'; have hadd_pts := PolyDecoder.addChunk_ptsNeeded hadd'
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj
        refine ⟨by simp; omega, ?_⟩; simp only [StatesPtsNeededBound] at hpts ⊢; omega
      | some decoded =>
        rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
        have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendEk.EkSent.recv_ct1 at huc; split at huc <;> [contradiction; skip]
        have huc_eq := Except.ok.inj huc; subst huc_eq; have hdec_len := PolyDecoder.decodedMessage_length hmsg'
        simp only [StatesPtsNeededBound] at hpts; refine ⟨?_, trivial⟩; simp [hdec_len, hadd_pts]; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, hpts⟩
  | ct1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      have hs' := Except.ok.inj h1c; subst hs'; have hdec0_le := (expectDecoderNew_raw_le hdec0).1
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_liftM_eq_ok hadd); refine ⟨?_, trivial⟩; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | ekSentCt1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; refine ⟨?_, trivial⟩; simp; omega
      | some ct2Full =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨⟨uc, sec⟩, huc, h1d⟩; rcases except_bind_eq_ok h1d with ⟨receivingHdr, hdec0, h1e⟩
        rw [statesResult_ofPanic_eq_ok] at hdec0; have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at huc; dsimp only [] at huc
        rcases except_bind_eq_ok huc with ⟨ss0, _, huc1⟩; rcases except_bind_eq_ok huc1 with ⟨ss, _, huc2⟩
        rcases except_bind_eq_ok huc2 with ⟨auth, hauth, huc3⟩; rcases except_bind_eq_ok huc3 with ⟨verifyRes, _, huc4⟩
        unfold spqrAuthApi at hauth; dsimp only [StatesResult.ofPanic] at hauth
        have hauth_eq := Except.ok.inj hauth; subst hauth_eq; cases verifyRes with
        | error _ => contradiction
        | ok u =>
          cases u; dsimp only [] at huc4; split at huc4 <;> [contradiction; skip]
          have huc_eq := (Prod.mk.inj (Except.ok.inj huc4)).1; subst huc_eq
          have hauth_le := Authenticator.update_rawAuth_le F state.uc.auth state.uc.epoch ss
          have hdec0_le := (expectDecoderNew_raw_le hdec0).1; refine ⟨?_, trivial⟩; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | noHeaderReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; refine ⟨?_, trivial⟩; simp; omega
      | some hdrFull =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨receivingEkRes, hek0, h1d⟩; rcases except_bind_eq_ok h1d with ⟨uc, huc, h1e⟩
        have hek0' := poly_decoderNew_ofPanic_eq_ok hek0; cases receivingEkRes with
        | error _ => contradiction
        | ok receivingEk =>
          have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
          unfold Unchunked.SendCt.NoHeaderReceived.recv_header at huc; split at huc <;> [contradiction; skip]
          rcases except_bind_eq_ok huc with ⟨verifyRes, _, huc2⟩; cases verifyRes with
          | error _ => contradiction
          | ok u =>
            cases u; have huc_eq := Except.ok.inj huc2; subst huc_eq
            have hek_le := PolyDecoder.new_raw_le hek0'; refine ⟨?_, trivial⟩; simp [HEADER_SIZE]; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | headerReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
  | ct1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
    | none =>
      dsimp only [] at h1c; split at h1c <;>
        (have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; refine ⟨?_, trivial⟩; simp; omega)
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; rename_i hek_match; have huc_eq := Except.ok.inj huc; subst huc_eq
      have hek_len := ek_matches_header_length hek_match; split at h1d
      · rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
        have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hct2; dsimp only [] at hct2
        rcases except_bind_eq_ok hct2 with ⟨ct2', _, hct2b⟩; rcases except_bind_eq_ok hct2b with ⟨mac', _, hct2c⟩
        have huc2_eq := (Prod.mk.inj (Except.ok.inj hct2c)).1; subst huc2_eq
        have henc2_le := expectEncodeBytes_raw_le henc2; refine ⟨?_, trivial⟩; simp; omega
      · have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        refine ⟨?_, trivial⟩; simp [hek_len]; omega
  | ekReceivedCt1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    have hisAck : ∀ b : Bool, (if b = true then do
        let s' ← StatesResult.ofPanic (state.recv_ct1_ack K msg.epoch)
        Except.ok ({ state := States.ct2Sampled s', key := none } : V1Recv spqrPolyApi (spqrAuthApi F))
      else Except.ok { state := States.ekReceivedCt1Sampled state, key := none }) = .ok recvOut →
      rawV1State recvOut.state.into_pb ≤ rawV1State (States.ekReceivedCt1Sampled state).into_pb + 1052480 ∧
        StatesPtsNeededBound recvOut.state := by
      intro b hb; cases b
      · have hinj := Except.ok.inj hb; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩
      · simp only [ite_true] at hb; rcases except_bind_eq_ok hb with ⟨s', h1, h2⟩
        rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
        unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
        dsimp only [] at h1; split at h1 <;> [contradiction; skip]
        rcases except_bind_eq_ok h1 with ⟨⟨uc2, ct2, mac⟩, hct2, h1b⟩
        rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩; have hs' := Except.ok.inj h1c; subst hs'
        unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hct2; dsimp only [] at hct2
        rcases except_bind_eq_ok hct2 with ⟨ct2', _, hct2b⟩; rcases except_bind_eq_ok hct2b with ⟨mac', _, hct2c⟩
        have huc2_eq := (Prod.mk.inj (Except.ok.inj hct2c)).1; subst huc2_eq
        have henc2_le := expectEncodeBytes_raw_le henc2; refine ⟨?_, trivial⟩; simp; omega
    exact hisAck _ h
  | ct1Acknowledged state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd); cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; refine ⟨?_, trivial⟩; simp; omega
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
      have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; have huc_eq := Except.ok.inj huc; subst huc_eq
      unfold Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at hct2; dsimp only [] at hct2
      rcases except_bind_eq_ok hct2 with ⟨ct2', _, hct2b⟩; rcases except_bind_eq_ok hct2b with ⟨mac', _, hct2c⟩
      have huc2_eq := (Prod.mk.inj (Except.ok.inj hct2c)).1; subst huc2_eq
      have henc2_le := expectEncodeBytes_raw_le henc2; refine ⟨?_, trivial⟩; simp; omega
  | ct2Sampled state =>
    dsimp only [] at h; split at h
    · split at h <;> [skip; contradiction]; rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
      unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch Unchunked.SendCt.Ct2Sent.recv_next_epoch at h1
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨uc, huc, h1b⟩
      have hs' := Except.ok.inj h1b; subst hs'; split at huc <;> [contradiction; skip]; split at huc <;> [contradiction; skip]
      have huc_eq := Except.ok.inj huc; subst huc_eq; refine ⟨?_, trivial⟩; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; exact ⟨by dsimp only []; omega, trivial⟩

/-! ## Top-Level `decodeState`, `Chain::encoded_len`, and `encodeState_len_lt` -/

theorem decodeState_spqrDeps_raw_le {F : ShaCompress} {K : MlKem}
    {s : SerializedState} {statePb : PqRatchetStatePB V1State}
    (h : decodeState (spqrDeps F K) s = .ok statePb) :
    rawPqState (pbToPqRatchetState statePb) ≤ 201 * s.length := by
  unfold decodeState at h; split at h
  · have hinj := Except.ok.inj h; subst hinj; simp [rawPqState, pbToPqRatchetState]
  · unfold spqrDeps at h; dsimp only at h; cases hdec : Proto.decodeState s with
    | error _ => rw [hdec] at h; contradiction
    | ok st =>
      rw [hdec] at h; have hinj := Except.ok.inj h; subst hinj
      rw [pbToPqRatchetState_pqRatchetStateToPb]; exact decodeState_rawPqState_le hdec

/-- Any `ChainPB` whose `rawChain` is bounded by `356 * 2^32` satisfies
`chainPBEncodedLen pb < 2^61` (and `< 2^63`, `< 2^64`, `ChainEncodedLenFits pb`). -/
theorem chainPBEncodedLen_lt_of_rawChain_le {pb : ChainPB} (h : rawChain pb ≤ 356 * 2 ^ 32) :
    chainPBEncodedLen pb < 2 ^ 61 ∧ chainPBEncodedLen pb < 2 ^ 63 ∧ ChainEncodedLenFits pb := by
  have h1 := chainPBEncodedLen_le_rawChain pb; refine ⟨by omega, by omega, ?_⟩; unfold ChainEncodedLenFits; omega

/-- Any `PqRatchetState` whose `rawPqState` is bounded by `356 * 2^32 + 2000000` has
`(Proto.encodeState st).length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem encodeState_length_lt_of_rawPqState_le {st : PqRatchetState}
    (h : rawPqState st ≤ 356 * 2 ^ 32 + 2000000) :
    (Proto.encodeState st).length < 2 ^ 61 ∧ (Proto.encodeState st).length < 2 ^ 62 - 10 ∧
      (Proto.encodeState st).length < 2 ^ 63 ∧ (Proto.encodeState st).length < 2 ^ 64 := by
  have h1 := encodeState_length_le_rawPqState st; omega

/-- Bound on `sendAfterStates`: bounds the output `chainPb` and the output serialized state `out.state`. -/
theorem sendAfterStates_raw_le {F : ShaCompress} {K : MlKem} {hkdf : HkdfFn}
    {statePb : PqRatchetStatePB V1State} {msg : Message spqrPolyApi} {key : Option EpochSecret}
    {st1 : States spqrPolyApi (spqrAuthApi F)} {out : Send}
    (h : sendAfterStates (spqrDeps F K) hkdf statePb msg key st1 = .ok out) :
    ∃ chainPb : Option ChainPB,
      optRaw rawChain chainPb ≤ optRaw rawChain statePb.chain + 624 ∧
      out.state = Proto.encodeState (pbToPqRatchetState {
        inner := some st1.into_pb, versionNegotiation := statePb.versionNegotiation, chain := chainPb }) := by
  unfold sendAfterStates at h; simp only [pure_bind_except] at h
  have hchain? : ∃ chain? : Option Chain,
      (∀ c0, chain? = some c0 → rawChain c0.intoPb ≤ optRaw rawChain statePb.chain + 296) ∧
      ((do
        let (index, msgKey, chainPb) ← match chain? with
          | none =>
            if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB))
            else Except.error (SpqrApiError.panic SpqrApiPanic.sendKeySomeWithoutChain)
          | some chain0 => do
            let chain1 ← match key with
              | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
              | none => pure chain0
            let epoch := (spqrDeps F K).msgEpoch msg
            if epoch == 0#64 then Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
            else do
              let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf (epoch - 1#64))
              pure (idx, mk, some chain2.intoPb)
        let msgBytes := (spqrDeps F K).msgSerialize msg index
        match msgBytes with
        | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
          else
            let newStateBytes := (spqrDeps F K).encodeState {
              inner := some ((spqrDeps F K).statesIntoPb st1),
              versionNegotiation := statePb.versionNegotiation, chain := chainPb }
            let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
            Except.ok ({ state := newStateBytes, msg := msgBytes, key := outKey } : Send)) :
        SpqrApiResult Send) = .ok out := by
    cases hch_opt : statePb.chain with
    | none =>
      rw [hch_opt] at h; dsimp only [] at h; cases hvn : statePb.versionNegotiation with
      | none => rw [hvn] at h; contradiction
      | some vn =>
        rw [hvn] at h; dsimp only [] at h; split at h
        · rcases except_bind_eq_ok h with ⟨c, hc, h1⟩; rw [SpqrApiResult.ofError_eq_ok] at hc
          have hle := chainFromVersionNegotiation_raw_le hkdf vn hc
          refine ⟨some c, ?_, h1⟩; intro c0 hc0; have heq := Option.some.inj hc0; subst heq; simp; omega
        · refine ⟨none, ?_, h⟩; intro _ hc; nomatch hc
    | some pb =>
      rw [hch_opt] at h; dsimp only [] at h; rcases except_bind_eq_ok h with ⟨c, hc, h1⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc; have heq := Chain.fromPb_raw_eq hc
      refine ⟨some c, ?_, h1⟩; intro c0 hc0; have hc_eq := Option.some.inj hc0; subst hc_eq; simp [heq]
  rcases hchain? with ⟨chain?, hch_le, h1⟩; simp only [pure_bind_except] at h1; cases chain? with
  | none =>
    dsimp only [] at h1; split at h1
    · split at h1 <;> [contradiction; skip]; split at h1 <;> [contradiction; skip]
      have hinj := Except.ok.inj h1; subst hinj; exact ⟨none, by simp, rfl⟩
    · dsimp only [Bind.bind, Except.bind] at h1; contradiction
  | some chain0 =>
    have hc0_le := hch_le chain0 rfl
    have htail : ∀ (chain1 : Chain),
        rawChain chain1.intoPb ≤ optRaw rawChain statePb.chain + 592 →
        (if ((spqrDeps F K).msgEpoch msg == 0#64) = true then do
          let __x : BitVec 32 × Bytes × Option ChainPB ←
            Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
          match (spqrDeps F K).msgSerialize msg __x.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F K).encodeState {
                inner := some ((spqrDeps F K).statesIntoPb st1),
                versionNegotiation := statePb.versionNegotiation, chain := __x.2.2 },
              msg := (spqrDeps F K).msgSerialize msg __x.1,
              key := if __x.2.1.isEmpty = true then none else some __x.2.1 } : Send)
        else do
          let __x ← SpqrApiResult.ofChainResult (chain1.sendKey hkdf ((spqrDeps F K).msgEpoch msg - 1#64))
          match (spqrDeps F K).msgSerialize msg __x.2.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDeps F K).encodeState {
                inner := some ((spqrDeps F K).statesIntoPb st1),
                versionNegotiation := statePb.versionNegotiation, chain := some __x.1.intoPb },
              msg := (spqrDeps F K).msgSerialize msg __x.2.1,
              key := if List.isEmpty __x.2.2 = true then none else some __x.2.2 } : Send)) = .ok out →
        ∃ chainPb : Option ChainPB,
          optRaw rawChain chainPb ≤ optRaw rawChain statePb.chain + 624 ∧
          out.state = Proto.encodeState (pbToPqRatchetState {
            inner := some st1.into_pb, versionNegotiation := statePb.versionNegotiation, chain := chainPb }) := by
      intro chain1 hc1_le hstep2; split at hstep2
      · dsimp only [Bind.bind, Except.bind] at hstep2; contradiction
      · rcases except_bind_eq_ok hstep2 with ⟨⟨chain2, idx, mk⟩, hc2, h2⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hc2; have hsend := Chain.sendKey_raw_le hkdf chain1 _ hc2
        have hchainPb_le : optRaw rawChain (some chain2.intoPb) ≤ optRaw rawChain statePb.chain + 624 := by simp; omega
        dsimp only [] at h2; split at h2 <;> [contradiction; skip]; split at h2 <;> [contradiction; skip]
        have hinj2 := Except.ok.inj h2; subst hinj2; exact ⟨some chain2.intoPb, hchainPb_le, rfl⟩
    cases key with
    | none => exact htail chain0 (by omega) h1
    | some es =>
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨chain1, hc1, hstep2⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1; have hadd := Chain.addEpoch_raw_le hkdf chain0 es hc1
      exact htail chain1 (by omega) hstep2

/-- If `s.length < 2^32` and `(send (spqrDeps F K) hkdf s tape).1 = .ok out`,
then `out.state.length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem send_state_len_lt (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (tape : Bytes) (out : Send) (hs : s.length < 2 ^ 32)
    (h : (send (spqrDeps F K) hkdf s tape).1 = .ok out) :
    out.state.length < 2 ^ 61 ∧ out.state.length < 2 ^ 62 - 10 ∧
      out.state.length < 2 ^ 63 ∧ out.state.length < 2 ^ 64 := by
  unfold send at h; cases hdec : decodeState (spqrDeps F K) s with
  | error _ => rw [hdec] at h; contradiction
  | ok statePb =>
    rw [hdec] at h; dsimp only [] at h; have hraw := decodeState_spqrDeps_raw_le hdec
    cases hinner : statePb.inner with
    | none => rw [hinner] at h; have hinj := Except.ok.inj h; subst hinj; simp
    | some pb =>
      rw [hinner] at h; dsimp only [] at h; cases hfrom : (spqrDeps F K).statesFromPb pb with
      | error _ => rw [hfrom] at h; contradiction
      | ok st0' =>
        rw [hfrom] at h; dsimp only [] at h; unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
        cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
        | error e => rw [hs0] at hfrom; cases e <;> contradiction
        | ok st0 =>
          have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
          rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
          cases hsend : ((spqrDeps F K).statesSend st0 tape).1 with
          | error _ => rw [hsend] at h; contradiction
          | ok val =>
            rcases val with ⟨msg, key, st1⟩; rw [hsend] at h; dsimp only [] at h
            unfold spqrDeps at hsend; dsimp only [] at hsend; cases hsend0 : st0.send K tape with
            | error se => rw [hsend0] at hsend; cases se <;> contradiction
            | ok p =>
              rcases p with ⟨sOut, tape'⟩; have hsend' := hsend; rw [hsend0] at hsend'
              have hst1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hsend')).2).2; subst hst1
              have hst1_raw := (States.send_raw_le hst0_pts hsend0).1
              rcases sendAfterStates_raw_le h with ⟨chainPb, hch_le, hout_eq⟩; rw [hout_eq]
              apply encodeState_length_lt_of_rawPqState_le
              have hraw' : optRaw rawVN statePb.versionNegotiation + optRaw rawChain statePb.chain +
                  rawV1State pb ≤ 201 * s.length := by
                simpa only [pbToPqRatchetState, rawPqState, rawPqInner, hinner, Option.map, optRaw_some] using hraw
              have hgoal : rawPqState (pbToPqRatchetState {
                  inner := some sOut.state.into_pb, versionNegotiation := statePb.versionNegotiation,
                  chain := chainPb }) = optRaw rawVN statePb.versionNegotiation + optRaw rawChain chainPb +
                  rawV1State sOut.state.into_pb := rfl
              rw [hgoal]; omega

private theorem if_error_eq_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε} {rest : Except ε α}
    {v : α} (h : (if c then Except.error e else rest) = .ok v) : rest = .ok v := by
  by_cases hc : c <;> simp [hc] at h; exact h

private theorem if_eq_ok_cases {ε α : Type} {c : Prop} [Decidable c] {t f : Except ε α} {v : α}
    (h : (if c then t else f) = .ok v) : t = .ok v ∨ f = .ok v := by
  by_cases hc : c <;> simp [hc] at h <;> [exact Or.inl h; exact Or.inr h]

private theorem if_pure_bind_eq_ok {ε α β : Type} {c : Prop} [Decidable c]
    {a : α} {K : α → Except ε β} {f : Except ε β} {v : β}
    (h : (if c then (Pure.pure a >>= K) else f) = .ok v) (P : α → Prop) (ha : P a)
    (hf : f = .ok v → ∃ a', P a' ∧ K a' = .ok v) : ∃ a', P a' ∧ K a' = .ok v := by
  rcases if_eq_ok_cases h with h1 | h1; · (rw [pure_bind_except] at h1; exact ⟨a, ha, h1⟩)
  exact hf h1

set_option maxHeartbeats 400000 in
/-- If `s.length < 2^32` and `recv (spqrDeps F K) hkdf s msgBytes = .ok out`,
then `out.state.length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem recv_state_len_lt (F : ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    (s : SerializedState) (msgBytes : SerializedMessage) (out : Recv)
    (hs : s.length < 2 ^ 32) (h : recv (spqrDeps F K) hkdf s msgBytes = .ok out) :
    out.state.length < 2 ^ 61 ∧ out.state.length < 2 ^ 62 - 10 ∧
      out.state.length < 2 ^ 63 ∧ out.state.length < 2 ^ 64 := by
  unfold recv at h; dsimp only [] at h
  rcases except_bind_eq_ok h with ⟨msg, _, h1⟩; rcases except_bind_eq_ok h1 with ⟨prePb, hdec, h2⟩
  rw [SpqrApiResult.ofError_eq_ok] at hdec; have hraw := decodeState_spqrDeps_raw_le hdec
  have hraw' : optRaw rawVN prePb.versionNegotiation + optRaw rawChain prePb.chain +
      optRaw rawPqInner (prePb.inner.map PqRatchetState.Inner.v1) ≤ 201 * s.length := hraw
  replace h2 := if_error_eq_ok (if_error_eq_ok h2); rcases if_eq_ok_cases h2 with h2 | h2
  · have hinj := Except.ok.inj h2; subst hinj; simp
  · rcases if_eq_ok_cases h2 with h2 | h2
    · rcases except_bind_eq_ok h2 with ⟨chain0, hc0, h3⟩; rcases except_bind_eq_ok h3 with ⟨⟨chain1, rawKey⟩, hc1, h4⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc0; rw [SpqrApiResult.ofChainResult_eq_ok] at hc1
      dsimp only [] at h4; have hinj := Except.ok.inj h4; subst hinj
      have hc0_le := chainFrom_raw_le hkdf prePb.chain prePb.versionNegotiation hc0
      have hc1_le := Chain.recvKey_raw_le hkdf chain0 0#64 msg.index hc1
      dsimp only [spqrDeps]; apply encodeState_length_lt_of_rawPqState_le
      have hgoal : rawPqState (pbToPqRatchetState {
          inner := prePb.inner, versionNegotiation := prePb.versionNegotiation, chain := some chain1.intoPb }) =
          optRaw rawVN prePb.versionNegotiation + rawChain chain1.intoPb +
          optRaw rawPqInner (prePb.inner.map PqRatchetState.Inner.v1) := rfl
      rw [hgoal]; omega
    · rcases if_pure_bind_eq_ok h2
        (fun statePb => rawPqState (pbToPqRatchetState statePb) ≤ 201 * s.length + 720) (by omega)
        (by
          intro h2; rcases if_eq_ok_cases h2 with h2 | h2
          · dsimp only [Bind.bind, Except.bind] at h2; contradiction
          · cases hvn : prePb.versionNegotiation with
            | none => rw [hvn] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
            | some vn =>
              rw [hvn] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
              cases hv : Version.fromU8? msg.version with
              | none => rw [hv] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
              | some v =>
                rw [hv] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                cases hd : Direction.fromI32? vn.direction with
                | none => rw [hd] at h2; dsimp only [Bind.bind, Except.bind] at h2; contradiction
                | some dir =>
                  rw [hd] at h2; dsimp only [] at h2; rw [pure_bind_except] at h2
                  rcases except_bind_eq_ok h2 with ⟨inner', hinit, hst4⟩
                  rcases except_bind_eq_ok hst4 with ⟨chain', hch', hst5⟩
                  rw [SpqrApiResult.ofPanic_eq_ok] at hinit; rw [SpqrApiResult.ofError_eq_ok] at hch'
                  have hinit_le := initInner_spqrDeps_raw_le hinit
                  have hch'_le := chainFrom_raw_le hkdf prePb.chain (some vn) hch'
                  have hstPb_le : rawPqState (pbToPqRatchetState {
                      inner := inner', versionNegotiation := none, chain := some chain'.intoPb }) ≤
                      201 * s.length + 720 := by
                    have hgoal : rawPqState (pbToPqRatchetState {
                        inner := inner', versionNegotiation := none, chain := some chain'.intoPb }) =
                        0 + rawChain chain'.intoPb + optRaw rawPqInner (inner'.map PqRatchetState.Inner.v1) := rfl
                    rw [hvn] at hraw'; rw [hgoal]; omega
                  rw [pure_bind_except] at hst5
                  exact ⟨{ inner := inner', versionNegotiation := none,
                           chain := some chain'.intoPb }, hstPb_le, hst5⟩)
        with ⟨statePb, hstPb_le, h3⟩
      cases hinner : statePb.inner with
      | none => rw [hinner] at h3; have hinj := Except.ok.inj h3; subst hinj; simp
      | some pb =>
        rw [hinner] at h3; dsimp only [] at h3
        rcases except_bind_eq_ok h3 with ⟨sckaMsg, _, h4⟩; rcases except_bind_eq_ok h4 with ⟨st0', hfrom, h5⟩
        rcases except_bind_eq_ok h5 with ⟨⟨key, st1⟩, hrecv, h6⟩
        unfold spqrDeps liftStatesResult at hfrom; dsimp only [] at hfrom
        cases hs0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb with
        | error se => rw [hs0] at hfrom; cases se <;> contradiction
        | ok st0 =>
          have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
          rcases States.from_pb_raw_le hs0 with ⟨hst0_raw, hst0_pts⟩
          unfold spqrDeps at hrecv; dsimp only [] at hrecv; cases hr0 : st0.recv K sckaMsg with
          | error se => rw [hr0] at hrecv; cases se <;> contradiction
          | ok rOut =>
            have hrecv' := hrecv; rw [hr0] at hrecv'; have hst1_eq := (Prod.mk.inj (Except.ok.inj hrecv')).2; subst hst1_eq
            have hst1_raw := (States.recv_raw_le hst0_pts hr0).1
            dsimp only [] at h6; split at h6 <;> [contradiction; skip]
            rcases except_bind_eq_ok h6 with ⟨chain0, hc0, h7⟩; rw [SpqrApiResult.ofError_eq_ok] at hc0
            have hc0_le := chainFrom_raw_le hkdf statePb.chain statePb.versionNegotiation hc0
            have hstPb' : optRaw rawVN statePb.versionNegotiation + optRaw rawChain statePb.chain +
                rawV1State pb ≤ 201 * s.length + 720 := by
              simpa only [pbToPqRatchetState, rawPqState, rawPqInner, hinner, Option.map, optRaw_some] using hstPb_le
            have htail : ∀ (chain1 : Chain),
                rawChain chain1.intoPb ≤ rawChain chain0.intoPb + 296 →
                (do
                  let __x_1 ← SpqrApiResult.ofChainResult (Chain.recvKey hkdf chain1 (msg.epoch - 1#64) msg.index)
                  Except.ok ({
                    state := (spqrDeps F K).encodeState {
                      inner := some ((spqrDeps F K).statesIntoPb rOut.state),
                      versionNegotiation := none, chain := some __x_1.1.intoPb },
                    key := if List.isEmpty __x_1.2 = true then none else some __x_1.2 } : Recv)) = .ok out →
                out.state.length < 2 ^ 61 ∧ out.state.length < 2 ^ 62 - 10 ∧
                  out.state.length < 2 ^ 63 ∧ out.state.length < 2 ^ 64 := by
              intro chain1 hc1_le h8; rcases except_bind_eq_ok h8 with ⟨⟨chain2, msgKey⟩, hc2, h9⟩
              rw [SpqrApiResult.ofChainResult_eq_ok] at hc2; have hinj := Except.ok.inj h9; subst hinj
              have hc2_le := Chain.recvKey_raw_le hkdf chain1 (msg.epoch - 1#64) msg.index hc2
              dsimp only [spqrDeps]; apply encodeState_length_lt_of_rawPqState_le
              have hgoal : rawPqState (pbToPqRatchetState {
                  inner := some rOut.state.into_pb, versionNegotiation := none, chain := some chain2.intoPb }) =
                  0 + rawChain chain2.intoPb + rawV1State rOut.state.into_pb := rfl
              rw [hgoal]; omega
            cases key with
            | none => dsimp only [] at h7; rw [pure_bind_except] at h7; exact htail chain0 (by omega) h7
            | some es =>
              dsimp only [] at h7; rcases except_bind_eq_ok h7 with ⟨chain1, hc1, h8⟩
              rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1; exact htail chain1 (Chain.addEpoch_raw_le hkdf chain0 es hc1) h8

/-- Under `s.length < 2^32` and `decodeState (spqrDeps F K) s = .ok statePb`, any `Chain`
obtained from `statePb` by `Chain.fromPb` or `chainFrom` followed by at most two `addEpoch` /
`chainFrom` steps and one `sendKey` or `recvKey` step satisfies `chainPBEncodedLen c.intoPb < 2^61`
and `ChainEncodedLenFits c.intoPb`. -/
theorem chain_encodedLen_fits_of_decodeState (F : ShaCompress) (K : MlKem)
    {s : SerializedState} {statePb : PqRatchetStatePB V1State} {c : Chain}
    (hs : s.length < 2 ^ 32) (hdec : decodeState (spqrDeps F K) s = .ok statePb)
    (hc : rawChain c.intoPb ≤ optRaw rawChain statePb.chain + 1000 + 36 * 2 ^ 32) :
    chainPBEncodedLen c.intoPb < 2 ^ 61 ∧ chainPBEncodedLen c.intoPb < 2 ^ 63 ∧
      ChainEncodedLenFits c.intoPb := by
  have hraw := decodeState_spqrDeps_raw_le hdec
  have hch : optRaw rawChain statePb.chain ≤ rawPqState (pbToPqRatchetState statePb) := by
    simp [pbToPqRatchetState, rawPqState]; omega
  apply chainPBEncodedLen_lt_of_rawChain_le; omega

/-- Under `DEV-SPQR3` (`s.length < 2^32`), `(spqrV1 F K).send s tape = some (s', salt, msg)`
implies `s'.length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem encodeState_len_lt_send (F : ShaCompress) (K : MlKem)
    (s : Bytes) (tape : Bytes) (s' : Bytes) (salt : Salt) (msg : Bytes)
    (hs : s.length < 2 ^ 32) (h : (spqrV1 F K).send s tape = some (s', salt, msg)) :
    s'.length < 2 ^ 61 ∧ s'.length < 2 ^ 62 - 10 ∧
      s'.length < 2 ^ 63 ∧ s'.length < 2 ^ 64 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hsend : (send (spqrDeps F K) (spqrHkdfWith F) s tape).1 with
  | error _ => rw [hsend] at h; contradiction
  | ok out =>
    rw [hsend] at h; dsimp only [] at h; cases hsalt : messageKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h; have hinj := (Prod.mk.inj (Option.some.inj h)).1; subst hinj
      exact send_state_len_lt F K (spqrHkdfWith F) s tape out hs hsend

/-- Under `DEV-SPQR3` (`s.length < 2^32`), `(spqrV1 F K).recv s msg = .ok (s', salt)`
implies `s'.length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem encodeState_len_lt_recv (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (salt : Salt)
    (hs : s.length < 2 ^ 32) (h : (spqrV1 F K).recv s msg = .ok (s', salt)) :
    s'.length < 2 ^ 61 ∧ s'.length < 2 ^ 62 - 10 ∧
      s'.length < 2 ^ 63 ∧ s'.length < 2 ^ 64 := by
  rw [spqrV1_eq] at h; unfold toSpqrModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) s msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only [] at h; cases hsalt : recvKeyToSalt? out.key with
    | none => rw [hsalt] at h; contradiction
    | some _ =>
      rw [hsalt] at h; dsimp only [] at h
      have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
      exact recv_state_len_lt F K (spqrHkdfWith F) s msg out hs hrecv

/-- Under `DEV-SPQR3` (`s.length < 2^32`), `(spqrV1Recv F K).recv s msg = .ok (s', key)`
implies `s'.length < 2^61` (and `< 2^62 - 10`, `< 2^63`, `< 2^64`). -/
theorem encodeState_len_lt_spqrV1Recv (F : ShaCompress) (K : MlKem)
    (s msg : Bytes) (s' : Bytes) (key : MessageKey)
    (hs : s.length < 2 ^ 32) (h : (spqrV1Recv F K).recv s msg = .ok (s', key)) :
    s'.length < 2 ^ 61 ∧ s'.length < 2 ^ 62 - 10 ∧
      s'.length < 2 ^ 63 ∧ s'.length < 2 ^ 64 := by
  rw [spqrV1Recv_eq] at h; unfold toSpqrRecvModel at h; dsimp only at h
  cases hrecv : recv (spqrDeps F K) (spqrHkdfWith F) s msg with
  | error e => rw [hrecv] at h; cases e <;> contradiction
  | ok out =>
    rw [hrecv] at h; dsimp only [] at h
    have hinj := (Prod.mk.inj (Except.ok.inj h)).1; subst hinj
    exact recv_state_len_lt F K (spqrHkdfWith F) s msg out hs hrecv

end CryptoVerification.SpqrV1.Top.StateSize
