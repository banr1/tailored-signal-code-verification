/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthSend.Wire
public import Symbolic.Proofs.SpecLemmas.ProofHubsPure
import Symbolic.Proofs.Swarm.SHARED.StateSizePure
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Fold

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open Symbolic.Swarm.TRREF.SpqrSemOf
open Symbolic.Swarm.TRREF.GrowthRecv

@[scoped simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (pure x >>= f) = f x := rfl

@[scoped simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

@[scoped simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by cases m <;> simp [Except.mapError]

@[scoped simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [liftSpqrPanic]

@[scoped simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by cases r <;> simp [StatesResult.ofPanic]

private theorem poly_nextChunk_liftM_eq_ok {enc enc' : PolyEncoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.next_chunk enc) :
      Except StatesPanic (spqrPolyApi.PolyEncoder × spqrPolyApi.Chunk)) = .ok (enc', chunk)) :
    enc.nextChunk = .ok (enc', chunk) := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)

theorem rawOptAuth_eq_optAuthWeight : ∀ (o : Option ProtoAuthenticator), optRaw rawAuth o = optAuthWeight o
  | none => rfl | some _ => rfl

theorem sum_map_add_const (xs : List Bytes) (c : Nat) :
    (xs.map (fun b => b.length + c)).sum = bytesSum xs + c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, bytesSum_cons, List.length_cons, Nat.mul_succ, ih]; omega

theorem polyEncoder_fromPb_raw_le_weight {pb : PolynomialEncoder} {enc : PolyEncoder}
    (h : PolyEncoder.fromPb (pbToProtoPolyEncoder pb) = .ok (.ok enc)) : rawPolyEnc pb ≤ encWeight pb + 352 := by
  unfold PolyEncoder.fromPb at h; split at h
  · split at h
    · simp [pure, Except.pure] at h
    · split at h
      · simp [pure, Except.pure] at h
      · rename_i h1 h2 h3
        have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h3
        have hpolys : pb.polys.length = 0 := by cases hpol : pb.polys with | nil => rfl | cons _ _ => simp [pbToProtoPolyEncoder, hpol] at h2
        simp only [rawPolyEnc, encWeight, sum_map_add_const, hpts, hpolys]; omega
  · split at h
    · rename_i h1 h2
      have hpts : pb.pts.length = 0 := by cases hpt : pb.pts with | nil => rfl | cons _ _ => simp [pbToProtoPolyEncoder, hpt] at h1
      have hpolys : pb.polys.length = 16 := by simpa [pbToProtoPolyEncoder, NUM_POLYS, CHUNK_SIZE, beq_iff_eq] using h2
      simp only [rawPolyEnc, encWeight, sum_map_add_const, hpts, hpolys]; omega
    · simp [pure, Except.pure] at h

theorem encoderFromPbStateDecode_raw_le_weight {pb? : Option PolynomialEncoder} {enc : PolyEncoder}
    (h : encoderFromPbStateDecode spqrPolyApi pb? = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ optEncWeight pb? + 352 := by
  have hraw := encoderFromPbStateDecode_raw_le h; unfold encoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok enc' =>
      have hinj := Except.ok.inj h2; subst hinj; have hpb := polyEncoder_fromPb_raw_le_weight h1'
      simp only [optRaw_some, optEncWeight, optWeight] at hraw ⊢; omega

theorem polyDecoder_fromPb_raw_le_weight {pb : PolynomialDecoder} {dec : PolyDecoder}
    (h : PolyDecoder.fromPb (pbToProtoPolyDecoder pb) = .ok (.ok dec)) : rawPolyDec pb ≤ decWeight pb + 352 := by
  unfold PolyDecoder.fromPb at h; split at h
  · simp [pure, Except.pure] at h
  · rename_i h1; have hpts : pb.pts.length = 16 := by simpa [pbToProtoPolyDecoder, NUM_POLYS, CHUNK_SIZE, bne_iff_ne] using h1
    simp only [rawPolyDec, decWeight, sum_map_add_const, hpts]; omega

theorem decoderFromPbStateDecode_raw_le_weight {pb? : Option PolynomialDecoder} {dec : PolyDecoder}
    (h : decoderFromPbStateDecode spqrPolyApi pb? = .ok dec) :
    rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ optDecWeight pb? + 352 := by
  have hraw := (decoderFromPbStateDecode_raw_le h).1; unfold decoderFromPbStateDecode spqrPolyApi at h; cases pb? with
  | none => contradiction
  | some pb =>
    dsimp only [] at h; rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    have h1' := except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h1)
    cases res with
    | error _ => contradiction
    | ok dec' =>
      have hinj := Except.ok.inj h2; subst hinj; have hpb := polyDecoder_fromPb_raw_le_weight h1'
      simp only [optRaw_some, optDecWeight, optWeight] at hraw ⊢; omega

@[local simp] private theorem spqrPolyApi_encoder_into_pb (enc : spqrPolyApi.PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl

@[local simp] private theorem spqrPolyApi_encoder_into_pb' (enc : PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl

@[local simp] private theorem spqrPolyApi_decoder_into_pb (dec : spqrPolyApi.PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl

@[local simp] private theorem spqrPolyApi_decoder_into_pb' (dec : PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl

@[local simp] private theorem spqrAuthApiWithMac_into_pb {F : ShaCompress} {mac : HmacFn}
    (a : (spqrAuthApiWithMac F mac).Authenticator) : (spqrAuthApiWithMac F mac).into_pb a = Authenticator.intoPb a := rfl

@[local simp] private theorem spqrAuthApiWithMac_into_pb' {F : ShaCompress} {mac : HmacFn}
    (a : Authenticator) : (spqrAuthApiWithMac F mac).into_pb a = Authenticator.intoPb a := rfl

@[local simp] private theorem spqrAuthApiWithMac_from_pb {F : ShaCompress} {mac : HmacFn}
    (pb : ProtoAuthenticator) : (spqrAuthApiWithMac F mac).from_pb pb = Authenticator.fromPb pb := rfl

@[local simp] private theorem spqrAuthApi_into_pb' {F : ShaCompress} (a : Authenticator) :
    (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl

attribute [local simp]
  States.into_pb Chunked.SendEk.KeysUnsampled.into_pb Chunked.SendEk.KeysSampled.into_pb
  Chunked.SendEk.HeaderSent.into_pb Chunked.SendEk.Ct1Received.into_pb
  Chunked.SendEk.EkSentCt1Received.into_pb Chunked.SendCt.NoHeaderReceived.into_pb
  Chunked.SendCt.HeaderReceived.into_pb Chunked.SendCt.Ct1Sampled.into_pb
  Chunked.SendCt.EkReceivedCt1Sampled.into_pb Chunked.SendCt.Ct1Acknowledged.into_pb
  Chunked.SendCt.Ct2Sampled.into_pb
  Unchunked.SendEk.KeysUnsampled.into_pb Unchunked.SendEk.HeaderSent.into_pb
  Unchunked.SendEk.EkSent.into_pb Unchunked.SendEk.EkSentCt1Received.into_pb
  Unchunked.SendCt.NoHeaderReceived.into_pb Unchunked.SendCt.HeaderReceived.into_pb
  Unchunked.SendCt.Ct1Sent.into_pb Unchunked.SendCt.Ct1SentEkReceived.into_pb
  Unchunked.SendCt.Ct2Sent.into_pb
  rawV1State rawInnerState rawChKeysUnsampled rawChKeysSampled
  rawChHeaderSent rawChCt1Received rawChEkSentCt1Received rawChNoHeaderReceived rawChHeaderReceived
  rawChCt1Sampled rawChEkReceivedCt1Sampled rawChCt1Acknowledged rawChCt2Sampled
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent
  Option.map optRaw_none optRaw_some Authenticator.rawAuth_intoPb_fromPb

theorem ucKeysUnsampled_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.KeysUnsampled}
    {s : Unchunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.KeysUnsampled.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcKeysUnsampled s.into_pb ≤ optAuthWeight pb.auth := by
  have heq : rawUcKeysUnsampled s.into_pb = rawUcKeysUnsampled pb := by
    unfold Unchunked.SendEk.KeysUnsampled.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.KeysUnsampled.into_pb, rawUcKeysUnsampled, hauth]
  rw [heq]; simp [rawUcKeysUnsampled, rawOptAuth_eq_optAuthWeight]

theorem ucHeaderSent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.HeaderSent}
    {s : Unchunked.SendEk.HeaderSent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.HeaderSent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcHeaderSent s.into_pb ≤ optAuthWeight pb.auth + 3552 := by
  have heq : rawUcHeaderSent s.into_pb = rawUcHeaderSent pb := by
    unfold Unchunked.SendEk.HeaderSent.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.HeaderSent.into_pb, rawUcHeaderSent, hauth]
  rw [heq]; unfold Unchunked.SendEk.HeaderSent.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, ENCAPSULATION_KEY_SIZE, DECAPSULATION_KEY_SIZE] at hlen
  simp only [rawUcHeaderSent, rawOptAuth_eq_optAuthWeight, hlen.1, hlen.2]; omega

theorem ucEkSent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.EkSent}
    {s : Unchunked.SendEk.EkSent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.EkSent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcEkSent s.into_pb ≤ optAuthWeight pb.auth + 2400 := by
  have heq : rawUcEkSent s.into_pb = rawUcEkSent pb := by
    unfold Unchunked.SendEk.EkSent.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSent.into_pb, rawUcEkSent, hauth]
  rw [heq]; unfold Unchunked.SendEk.EkSent.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [beq_iff_eq, DECAPSULATION_KEY_SIZE] at hlen; simp only [rawUcEkSent, rawOptAuth_eq_optAuthWeight, hlen]; omega

theorem ucEkSentCt1Received_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.EkSentCt1Received}
    {s : Unchunked.SendEk.EkSentCt1Received (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcEkSentCt1Received s.into_pb ≤ optAuthWeight pb.auth + 3360 := by
  have heq : rawUcEkSentCt1Received s.into_pb = rawUcEkSentCt1Received pb := by
    unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSentCt1Received.into_pb, rawUcEkSentCt1Received, hauth]
  rw [heq]; unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcEkSentCt1Received, rawOptAuth_eq_optAuthWeight, hlen.1, hlen.2]; omega

theorem ucNoHeaderReceived_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.NoHeaderReceived}
    {s : Unchunked.SendCt.NoHeaderReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.NoHeaderReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcNoHeaderReceived s.into_pb ≤ optAuthWeight pb.auth := by
  have heq : rawUcNoHeaderReceived s.into_pb = rawUcNoHeaderReceived pb := by
    unfold Unchunked.SendCt.NoHeaderReceived.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.NoHeaderReceived.into_pb, rawUcNoHeaderReceived, hauth]
  rw [heq]; simp [rawUcNoHeaderReceived, rawOptAuth_eq_optAuthWeight]

theorem ucHeaderReceived_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.HeaderReceived}
    {s : Unchunked.SendCt.HeaderReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcHeaderReceived s.into_pb ≤ optAuthWeight pb.auth + 64 := by
  have heq : rawUcHeaderReceived s.into_pb = rawUcHeaderReceived pb := by
    unfold Unchunked.SendCt.HeaderReceived.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.HeaderReceived.into_pb, rawUcHeaderReceived, hauth]
  rw [heq]; unfold Unchunked.SendCt.HeaderReceived.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [beq_iff_eq, HEADER_SIZE] at hlen; simp only [rawUcHeaderReceived, rawOptAuth_eq_optAuthWeight, hlen]; omega

theorem ucCt1Sent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1Sent}
    {s : Unchunked.SendCt.Ct1Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1Sent s.into_pb ≤ optAuthWeight pb.auth + 3104 := by
  have heq : rawUcCt1Sent s.into_pb = rawUcCt1Sent pb := by
    unfold Unchunked.SendCt.Ct1Sent.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1Sent.into_pb, rawUcCt1Sent, hauth]
  rw [heq]; unfold Unchunked.SendCt.Ct1Sent.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcCt1Sent, rawOptAuth_eq_optAuthWeight, hlen.1.1, hlen.1.2, hlen.2]; omega

theorem ucCt1SentEkReceived_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1SentEkReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1SentEkReceived s.into_pb ≤ optAuthWeight pb.auth + 4192 := by
  have heq : rawUcCt1SentEkReceived s.into_pb = rawUcCt1SentEkReceived pb := by
    unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawUcCt1SentEkReceived, hauth]
  rw [heq]; unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h; split at h <;> [skip; contradiction]; rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, ENCAPSULATION_STATE_SIZE, ENCAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcCt1SentEkReceived, rawOptAuth_eq_optAuthWeight, hlen.1.1, hlen.1.2, hlen.2]; omega

theorem ucCt2Sent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct2Sent}
    {s : Unchunked.SendCt.Ct2Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct2Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt2Sent s.into_pb ≤ optAuthWeight pb.auth := by
  have heq : rawUcCt2Sent s.into_pb = rawUcCt2Sent pb := by
    unfold Unchunked.SendCt.Ct2Sent.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct2Sent.into_pb, rawUcCt2Sent, hauth]
  rw [heq]; simp [rawUcCt2Sent, rawOptAuth_eq_optAuthWeight]

private theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; have : (u16ToBeBytes g.value).length = 2 := rfl; omega

local notation "pointRaw'" => (fun (pt : Point) => 2 * List.length (Point.value pt) + 22)

private theorem map_intoPb_encoder_pts' (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) = pts.map pointRaw' := by
  induction pts with
  | nil => rfl
  | cons pt ps ih => rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [flatMap_u16ToBeBytes_length]

private theorem sum_map_set_le' {α : Type} (f : α → Nat) (xs : List α) (idx : Nat) (x x' : α) (c : Nat)
    (hget : xs[idx]? = some x) (hle : f x' ≤ f x + c) : ((xs.set idx x').map f).sum ≤ (xs.map f).sum + c := by
  induction xs generalizing idx with
  | nil => simp at hget
  | cons a rest ih =>
    cases idx with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget; simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i => simp only [List.getElem?_cons_succ] at hget; have hih := ih i hget; simp only [List.set_cons_succ, List.map_cons, List.sum_cons]; omega

theorem distributeMsgChunks_sum_le' (i : Nat) (msg : List (BitVec 8)) (pts : List Point)
    {pts' : List Point} (h : PolyEncoder.distributeMsgChunks i msg pts = .ok pts') :
    (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length := by
  suffices ∀ n i (msg : List (BitVec 8)) (pts : List Point), msg.length ≤ n →
      PolyEncoder.distributeMsgChunks i msg pts = .ok pts' → (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length from
    this msg.length i msg pts (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro i msg pts hn h; cases msg with
    | nil => unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro i msg pts hn h; rcases msg with _ | ⟨c0, _ | ⟨c1, rest⟩⟩
    · unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyEncoder.distributeMsgChunks at h; contradiction
    · unfold PolyEncoder.distributeMsgChunks at h; dsimp only [] at h; split at h
      · rename_i pt hpt
        have hih := ih (i + 1) rest _ (by simp only [List.length_cons] at hn; omega) h
        have hset := sum_map_set_le' pointRaw' pts (i % pts.length) pt
          { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] } 2 hpt
          (by simp only [List.length_append, List.length_singleton]; omega)
        simp only [List.length_cons]; omega
      · contradiction

theorem polyEncoder_encodeBytes_raw_le_msg {msg : List (BitVec 8)} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) : rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h; split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · rcases hpts : PolyEncoder.distributeMsgChunks 0 msg (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := distributeMsgChunks_sum_le' 0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw').sum = 352 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc, map_intoPb_encoder_pts', List.map_nil, List.sum_nil]; omega

theorem expectEncodeBytes_raw_le_msg {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) : rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold expectEncodeBytes spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1); cases res with
  | error _ => contradiction
  | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact polyEncoder_encodeBytes_raw_le_msg h1'

theorem macHdrWithMac_length_le {mac : HmacFn} {self : Authenticator} {ep : Epoch} {hdr macBytes : Bytes}
    (h : macHdrWithMac mac self ep hdr = .ok macBytes) : macBytes.length ≤ 32 := by
  unfold macHdrWithMac at h; dsimp only [] at h; split at h
  · cases hmac : mac self.macKey (Authenticator.hdrLabel ++ CryptoGames.HMAC.toBEBytes 8 ep ++ hdr) with
    | none => rw [hmac] at h; contradiction
    | some tag =>
      rw [hmac] at h; dsimp only [] at h; split at h
      · injection h with h; subst h; exact List.length_take_le 32 tag
      · contradiction
  · contradiction

theorem states_from_pb_and_send_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sOut : V1Send spqrPolyApi (spqrAuthApiWithMac F mac)} {coins tape' : Bytes}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb = .ok st0)
    (hsend' : st0.send K coins = .ok (sOut, tape')) : rawV1State sOut.state.into_pb ≤ v1Weight pb + 4960 := by
  rcases sOut with ⟨msg, key, st1⟩; unfold States.from_pb at hfrom
  cases hinner : pb.innerState with
  | none => rw [hinner] at hfrom; contradiction
  | some inner =>
    rw [hinner] at hfrom; cases inner with
    | keysUnsampled s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.KeysUnsampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', h2⟩; have hinj2 := Except.ok.inj h2; subst hinj2
        have h1 := ucKeysUnsampled_from_pb_raw_le_weight huc'; unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk, tape1⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        have hst1_eq : st1 = .keysSampled state' := by injection hsinj with _ _ h; exact h.symm
        subst hst1_eq
        unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header at hs1
        dsimp only [] at hs1; rcases except_bind_eq_ok hs1 with ⟨⟨uc1, toSend, macB, tape2⟩, huc1, hs1b⟩
        rcases except_bind_eq_ok huc1 with ⟨⟨keys, tape3⟩, hgen, huc2⟩; rcases except_bind_eq_ok huc2 with ⟨mac', hmac', huc3⟩
        have huc3_inj := Prod.mk.inj (Except.ok.inj huc3)
        have huc1_eq := huc3_inj.1; have htoSend_eq : toSend = keys.hdr := (Prod.mk.inj huc3_inj.2).1.symm
        have hmacB_eq : macB = mac' := (Prod.mk.inj (Prod.mk.inj huc3_inj.2).2).1.symm
        subst huc1_eq htoSend_eq hmacB_eq
        rcases except_bind_eq_ok hs1b with ⟨enc0, henc0, hs1c⟩; rcases except_bind_eq_ok hs1c with ⟨⟨enc1, chunk1⟩, hnext, hs1d⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1d)).1; subst hst_eq
        rcases generate_lengths hgen with ⟨hek, hdk, hhdr⟩
        have hmac_len := macHdrWithMac_length_le (liftSpqrPanic_eq_ok.mp hmac')
        have henc0_le := expectEncodeBytes_raw_le_msg henc0; dsimp only [] at henc0_le; rw [List.length_append, hhdr] at henc0_le
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        simp only [v1Weight, innerStateW, ckKeysUnsampledW, hinner, huc] at h1 ⊢; simp [hek, hdk] at h1 ⊢; omega
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.KeysSampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucHeaderSent_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        unfold Chunked.SendEk.KeysSampled.send_hdr_chunk at hs1; dsimp only [] at hs1
        rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckKeysSampledW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.HeaderSent.from_pb at hv; cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩; contradiction
      | some d0 =>
        rw [hrec] at hv; dsimp only [] at hv; split at hv <;> [contradiction; skip]
        cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
          have h1 := ucEkSent_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
          have h3 := decoderFromPbStateDecode_raw_le_weight (pb? := some d0) hdec
          unfold States.send at hsend'; dsimp only [] at hsend'
          rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
          rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
          unfold Chunked.SendEk.HeaderSent.send_ek_chunk at hs1; dsimp only [] at hs1
          rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
          have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
          have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
          injection hsinj with _ _ hst1; subst hst1
          simp only [v1Weight, innerStateW, ckHeaderSentW, hinner, huc, hrec] at h1 h2 h3 ⊢; simp at h1 h2 h3 ⊢; omega
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.Ct1Received.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucEkSentCt1Received_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        unfold Chunked.SendEk.Ct1Received.send_ek_chunk at hs1; dsimp only [] at hs1
        rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckCt1ReceivedW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendEk.EkSentCt1Received.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApiWithMac F mac) u
            let receivingCt2 ← decoderFromPbStateDecode spqrPolyApi s.receivingCt2
            Except.ok { uc := uc, receiving_ct2 := receivingCt2 }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucEkSentCt1Received_from_pb_raw_le_weight huc'; have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        unfold States.send at hsend'; dsimp only [] at hsend'
        have hsinj := (Prod.mk.inj (Except.ok.inj hsend')).1; injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckEkSentCt1ReceivedW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.NoHeaderReceived.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.NoHeaderReceived.from_pb (spqrAuthApiWithMac F mac) u
            let receivingHdr ← decoderFromPbStateDecode spqrPolyApi s.receivingHdr
            Except.ok { uc := uc, receiving_hdr := receivingHdr }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucNoHeaderReceived_from_pb_raw_le_weight huc'; have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        unfold States.send at hsend'; dsimp only [] at hsend'
        have hsinj := (Prod.mk.inj (Except.ok.inj hsend')).1; injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckNoHeaderReceivedW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | headerReceived s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.HeaderReceived.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApiWithMac F mac) u
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucHeaderReceived_from_pb_raw_le_weight huc'; have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk, sec, tape1⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        have hst1_eq : st1 = .ct1Sampled state' := by injection hsinj with _ _ h; exact h.symm
        subst hst1_eq
        unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk Unchunked.SendCt.HeaderReceived.send_ct1 at hs1
        dsimp only [] at hs1; rcases except_bind_eq_ok hs1 with ⟨⟨uc1, ct1, sec1, tape2⟩, huc1, hs1b⟩
        rcases except_bind_eq_ok huc1 with ⟨⟨⟨ct1', es, ss⟩, tape3⟩, henc1, huc2⟩
        rcases except_bind_eq_ok huc2 with ⟨secret, _, huc3⟩; rcases except_bind_eq_ok huc3 with ⟨auth, hauth, huc4⟩
        unfold spqrAuthApiWithMac at hauth; dsimp only [liftM, monadLift, MonadLift.monadLift, liftSpqrPanic] at hauth
        have hauth_eq := Except.ok.inj hauth; subst hauth_eq
        have huc_inj := Prod.mk.inj (Except.ok.inj huc4)
        have huc_eq := huc_inj.1; have hct1_eq := (Prod.mk.inj huc_inj.2).1; subst huc_eq hct1_eq
        rcases except_bind_eq_ok hs1b with ⟨enc0, henc0, hs1c⟩; rcases except_bind_eq_ok hs1c with ⟨⟨enc1, chunk1⟩, hnext, hs1d⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1d)).1; subst hst_eq
        rcases encaps1_lengths henc1 with ⟨hct1_len, hes_len, _⟩
        have hauth_le := Authenticator.update_rawAuth_le F uc.auth uc.epoch secret
        have henc0_le := expectEncodeBytes_raw_le_msg henc0; rw [hct1_len] at henc0_le
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        simp only [v1Weight, innerStateW, ckHeaderReceivedW, hinner, huc] at h1 h2 ⊢; simp [hct1_len, hes_len] at h1 h2 ⊢; omega
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.Ct1Sampled.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) u
            let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi s.sendingCt1
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
        have h1 := ucCt1Sent_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
        have h3 := decoderFromPbStateDecode_raw_le_weight hdec
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        unfold Chunked.SendCt.Ct1Sampled.send_ct1_chunk at hs1; dsimp only [] at hs1
        rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckCt1SampledW, hinner, huc] at h1 h2 h3 ⊢; simp at h1 h2 h3 ⊢; omega
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt1SentEkReceived_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        unfold Chunked.SendCt.EkReceivedCt1Sampled.send_ct1_chunk at hs1; dsimp only [] at hs1
        rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckEkReceivedCt1SampledW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) u
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt1Sent_from_pb_raw_le_weight huc'; have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        unfold States.send at hsend'; dsimp only [] at hsend'
        have hsinj := (Prod.mk.inj (Except.ok.inj hsend')).1; injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckCt1AcknowledgedW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at hfrom; split at hfrom <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj hfrom; subst hinj
      unfold Chunked.SendCt.Ct2Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt2Sent_from_pb_raw_le_weight huc'; have h2 := encoderFromPbStateDecode_raw_le_weight henc
        unfold States.send at hsend'; dsimp only [] at hsend'
        rcases except_bind_eq_ok hsend' with ⟨⟨state', chunk⟩, hs1, hs2⟩
        rw [statesResult_ofPanic_eq_ok] at hs1; have hsinj := (Prod.mk.inj (Except.ok.inj hs2)).1
        unfold Chunked.SendCt.Ct2Sampled.send_ct2_chunk at hs1; dsimp only [] at hs1
        rcases except_bind_eq_ok hs1 with ⟨⟨enc1, chunk1⟩, hnext, hs1b⟩
        have hst_eq := (Prod.mk.inj (Except.ok.inj hs1b)).1; subst hst_eq
        have hnext_le := PolyEncoder.nextChunk_raw_le _ (poly_nextChunk_liftM_eq_ok hnext)
        injection hsinj with _ _ hst1; subst hst1
        simp only [v1Weight, innerStateW, ckCt2SampledW, hinner, huc] at h1 h2 ⊢; simp at h1 h2 ⊢; omega

theorem sendAfterStates_chainWeight_le (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (msg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (out : Send)
    (h : sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F) statePb msg key st1 = .ok out) :
    ∃ chainPb : Option ChainPB, optChainWeight chainPb ≤ optChainWeight statePb.chain + 576 ∧
      out.state = (spqrDepsWithMac F K mac).encodeState {
        inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
        versionNegotiation := statePb.versionNegotiation, chain := chainPb } := by
  unfold sendAfterStates at h; simp only [pure_bind_except] at h
  have hchain? : ∃ chain? : Option Chain,
      (∀ c0, chain? = some c0 → chainWeight c0.intoPb ≤ optChainWeight statePb.chain + 206) ∧
      ((do
        let (index, msgKey, chainPb) ← match chain? with
          | none =>
            if key.isNone then pure (0#32, ([] : Bytes), (none : Option ChainPB))
            else Except.error (SpqrApiError.panic SpqrApiPanic.sendKeySomeWithoutChain)
          | some chain0 => do
            let chain1 ← match key with
              | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
              | none => pure chain0
            let epoch := (spqrDepsWithMac F K mac).msgEpoch msg
            if epoch == 0#64 then Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
            else do
              let (chain2, (idx, mk)) ← SpqrApiResult.ofChainResult (chain1.sendKey (spqrHkdfWith F) (epoch - 1#64))
              pure (idx, mk, some chain2.intoPb)
        let msgBytes := (spqrDepsWithMac F K mac).msgSerialize msg index
        match msgBytes with
        | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
        | b0 :: _ =>
          if b0 != Version.v1.toU8 then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
          else
            let newStateBytes := (spqrDepsWithMac F K mac).encodeState {
              inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1),
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
          unfold chainFromVersionNegotiation at hc
          cases hdir : Direction.fromI32? vn.direction with
          | none => rw [hdir] at hc; contradiction
          | some dir =>
            rw [hdir] at hc; cases hcp : vn.chainParams with
            | none => rw [hcp] at hc; contradiction
            | some cp =>
              rw [hcp] at hc; dsimp only [Bind.bind, Except.bind, pure, Except.pure] at hc
              have hnew := chain_new_weight_le hc
              refine ⟨some c, ?_, h1⟩; intro c0 hc0; have heq := Option.some.inj hc0; subst heq; omega
        · refine ⟨none, ?_, h⟩; intro _ hc; nomatch hc
    | some pb =>
      rw [hch_opt] at h; dsimp only [] at h; rcases except_bind_eq_ok h with ⟨c, hc, h1⟩
      rw [SpqrApiResult.ofError_eq_ok] at hc; have heq := chain_fromPb_weight_eq hc
      refine ⟨some c, ?_, h1⟩; intro c0 hc0; have hc_eq := Option.some.inj hc0; subst hc_eq
      simp only [optChainWeight, optWeight]; omega
  rcases hchain? with ⟨chain?, hch_le, h1⟩; simp only [pure_bind_except] at h1; cases chain? with
  | none =>
    dsimp only [] at h1; split at h1
    · split at h1 <;> [contradiction; skip]; split at h1 <;> [contradiction; skip]
      have hinj := Except.ok.inj h1; subst hinj; exact ⟨none, by simp [optChainWeight, optWeight], rfl⟩
    · dsimp only [Bind.bind, Except.bind] at h1; contradiction
  | some chain0 =>
    have hc0_le := hch_le chain0 rfl
    have htail : ∀ (chain1 : Chain),
        chainWeight chain1.intoPb ≤ optChainWeight statePb.chain + 412 →
        (if ((spqrDepsWithMac F K mac).msgEpoch msg == 0#64) = true then do
          let __x : BitVec 32 × Bytes × Option ChainPB ←
            Except.error (SpqrApiError.panic SpqrApiPanic.sendEpochUnderflow)
          match (spqrDepsWithMac F K mac).msgSerialize msg __x.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDepsWithMac F K mac).encodeState {
                inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1),
                versionNegotiation := statePb.versionNegotiation, chain := __x.2.2 },
              msg := (spqrDepsWithMac F K mac).msgSerialize msg __x.1,
              key := if __x.2.1.isEmpty = true then none else some __x.2.1 } : Send)
        else do
          let __x ← SpqrApiResult.ofChainResult (chain1.sendKey (spqrHkdfWith F) ((spqrDepsWithMac F K mac).msgEpoch msg - 1#64))
          match (spqrDepsWithMac F K mac).msgSerialize msg __x.2.1 with
          | [] => Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgEmpty)
          | b0 :: _ =>
            if (b0 != Version.v1.toU8) = true then Except.error (SpqrApiError.panic SpqrApiPanic.sendMsgBadVersion)
            else Except.ok ({
              state := (spqrDepsWithMac F K mac).encodeState {
                inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1),
                versionNegotiation := statePb.versionNegotiation, chain := some __x.1.intoPb },
              msg := (spqrDepsWithMac F K mac).msgSerialize msg __x.2.1,
              key := if List.isEmpty __x.2.2 = true then none else some __x.2.2 } : Send)) = .ok out →
        ∃ chainPb : Option ChainPB, optChainWeight chainPb ≤ optChainWeight statePb.chain + 576 ∧
          out.state = (spqrDepsWithMac F K mac).encodeState {
            inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1),
            versionNegotiation := statePb.versionNegotiation, chain := chainPb } := by
      intro chain1 hc1_le hstep2; split at hstep2
      · dsimp only [Bind.bind, Except.bind] at hstep2; contradiction
      · rcases except_bind_eq_ok hstep2 with ⟨⟨chain2, idx, mk⟩, hc2, h2⟩
        rw [SpqrApiResult.ofChainResult_eq_ok] at hc2; have hsend := chain_sendKey_weight_le hc2
        have hchainPb_le : optChainWeight (some chain2.intoPb) ≤ optChainWeight statePb.chain + 576 := by
          change chainWeight chain2.intoPb ≤ optChainWeight statePb.chain + 576; omega
        dsimp only [] at h2; split at h2 <;> [contradiction; skip]; split at h2 <;> [contradiction; skip]
        have hinj2 := Except.ok.inj h2; subst hinj2; exact ⟨some chain2.intoPb, hchainPb_le, rfl⟩
    cases key with
    | none => exact htail chain0 (by omega) h1
    | some es =>
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨chain1, hc1, hstep2⟩
      rw [SpqrApiResult.ofChainPanic_eq_ok] at hc1; have hadd := chain_addEpoch_weight_le hc1
      exact htail chain1 (by omega) hstep2

theorem optChainPB_encodeOptMessage_length_le (opt : Option ChainPB) :
    (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt).length ≤ optChainWeight opt + 176 := by
  cases opt with
  | none => simp [Proto.encodeOptMessage, optChainWeight, optWeight]
  | some c => have := chainPB_encodeOptMessage_length_le c; simp only [optChainWeight, optWeight]; omega

theorem spqr_sendAfterStates_length_le (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st coins : Bytes)
    (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB) (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (st0 st1 : (spqrDepsWithMac F K mac).States) (msg : (spqrDepsWithMac F K mac).MessageV1)
    (key : Option EpochSecret) (tape' : Bytes) (out : Send)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = Except.ok st0)
    (hstep : (spqrDepsWithMac F K mac).statesSend st0 coins = (Except.ok (msg, key, st1), tape'))
    (hafter : sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F) statePb msg key st1 = .ok out) :
    out.state.length ≤ st.length + 2^14 := by
  have hdec_w := decodeState_weight_le F K mac st statePb hdec; rw [hinner] at hdec_w; dsimp only [] at hdec_w
  unfold spqrDepsWithMac liftStatesResult at hfrom; dsimp only [] at hfrom
  cases hs0 : States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb with
  | error e => rw [hs0] at hfrom; cases e <;> contradiction
  | ok st0' =>
    have hfrom' := hfrom; rw [hs0] at hfrom'; have hst0_eq := Except.ok.inj hfrom'; subst hst0_eq
    have hstep1 : ((spqrDepsWithMac F K mac).statesSend st0' coins).1 = .ok (msg, key, st1) := by rw [hstep]
    unfold spqrDepsWithMac at hstep1; dsimp only [] at hstep1
    cases hsend0 : st0'.send K coins with
    | error se => rw [hsend0] at hstep1; cases se <;> contradiction
    | ok p =>
      rcases p with ⟨sOut, tape0⟩; rw [hsend0] at hstep1
      have hst1_eq : sOut.state = st1 := (Prod.mk.inj (Prod.mk.inj (Except.ok.inj hstep1)).2).2; subst hst1_eq
      have hv1_w := states_from_pb_and_send_raw_le hs0 hsend0
      rcases sendAfterStates_chainWeight_le F K mac statePb msg key sOut.state out hafter with ⟨chainPb, hch_w, hout⟩
      rw [hout]
      change (PqRatchetState.encodeRaw {
        versionNegotiation := statePb.versionNegotiation
        chain := chainPb
        inner := some (.v1 sOut.state.into_pb)
      }).length ≤ st.length + 2^14
      unfold PqRatchetState.encodeRaw PqRatchetState.Inner.encode
      dsimp only []
      rw [List.length_append, List.length_append]
      have hvn_enc := vnPB_encodeOptMessage_length_le statePb.versionNegotiation
      have hch_enc := optChainPB_encodeOptMessage_length_le chainPb
      have hv1_enc := encodeMessage_length_le V1State.encodeRaw 3#32 sOut.state.into_pb
      have hv1_raw := v1State_encodeRaw_length_le sOut.state.into_pb
      omega

theorem spqr_sendAfterStates_oooBounded (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (msg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (out : Send)
    (hb : SpqrOooBounded st) (hlen : st.length < 2 ^ 32)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb)
    (hsend : sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F) statePb msg key st1 = .ok out)
    (hle : out.state.length ≤ st.length + 2^14) :
    SpqrOooBounded out.state := by
  exact GrowthOoo.spqr_sendAfterStates_oooBounded_fold F K mac st statePb msg key st1 out hb hdec hsend (by omega)

theorem spqr_send_growth (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st coins st' k m : Bytes)
    (hb : SpqrOooBounded st) (hlen : st.length < 2 ^ 32)
    (h : spqrSendB F K mac st coins = some (st', k, m)) :
    SpqrOooBounded st' ∧ st'.length ≤ st.length + 2^14 := by
  unfold spqrSendB spqrV1WithMac toSpqrModel send at h
  cases hdec : decodeState (spqrDepsWithMac F K mac) st with
  | error e =>
    simp [hdec] at h
  | ok statePb =>
    cases hinner : statePb.inner with
    | none =>
      simp [hdec, hinner, messageKeyToSalt?] at h
      rcases h with ⟨rfl, _, _⟩
      exact spqr_send_inner_none_growth st
    | some pb =>
      cases hfrom : (spqrDepsWithMac F K mac).statesFromPb pb with
      | error e =>
        simp [hdec, hinner, hfrom] at h
      | ok st0 =>
        cases hstep : (spqrDepsWithMac F K mac).statesSend st0 coins with
        | mk sendRes tape' =>
          cases sendRes with
          | error e =>
            simp [hdec, hinner, hfrom, hstep] at h
          | ok triple =>
            rcases triple with ⟨msg, key, st1⟩
            cases hafter : sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F) statePb msg key st1 with
            | error e =>
              simp [hdec, hinner, hfrom, hstep, hafter] at h
            | ok out =>
              cases hsalt : messageKeyToSalt? out.key with
              | none =>
                simp [hdec, hinner, hfrom, hstep, hafter, hsalt] at h
              | some salt =>
                simp [hdec, hinner, hfrom, hstep, hafter, hsalt] at h
                rcases h with ⟨rfl, _, _⟩
                have hlen_le := spqr_sendAfterStates_length_le F K mac st coins statePb pb st0 st1 msg key tape' out
                  hdec hinner hfrom hstep hafter
                exact ⟨spqr_sendAfterStates_oooBounded F K mac st statePb msg key st1 out hb hlen hdec hafter hlen_le,
                       hlen_le⟩

end Symbolic.Swarm.TRREF
