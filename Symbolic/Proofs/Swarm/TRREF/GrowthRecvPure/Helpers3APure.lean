/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvB.Defs
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers2BPure
public import Symbolic.Proofs.Swarm.SHARED.StateSizePure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1APure

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr

@[scoped simp] theorem spqrPolyApi_encoder_into_pb (enc : spqrPolyApi.PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[scoped simp] theorem spqrPolyApi_encoder_into_pb' (enc : PolyEncoder) :
    spqrPolyApi.encoder_into_pb enc = protoPolyEncoderToPb (PolyEncoder.intoPb enc) := rfl
@[scoped simp] theorem spqrPolyApi_decoder_into_pb (dec : spqrPolyApi.PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[scoped simp] theorem spqrPolyApi_decoder_into_pb' (dec : PolyDecoder) :
    spqrPolyApi.decoder_into_pb dec = protoPolyDecoderToPb (PolyDecoder.intoPb dec) := rfl
@[scoped simp] theorem spqrAuthApiWithMac_into_pb {F : ShaCompress} {mac : HmacFn}
    (a : (spqrAuthApiWithMac F mac).Authenticator) :
    (spqrAuthApiWithMac F mac).into_pb a = Authenticator.intoPb a := rfl
@[scoped simp] theorem spqrAuthApiWithMac_into_pb' {F : ShaCompress} {mac : HmacFn}
    (a : Authenticator) :
    (spqrAuthApiWithMac F mac).into_pb a = Authenticator.intoPb a := rfl
@[scoped simp] theorem spqrAuthApiWithMac_from_pb {F : ShaCompress} {mac : HmacFn}
    (pb : ProtoAuthenticator) :
    (spqrAuthApiWithMac F mac).from_pb pb = Authenticator.fromPb pb := rfl

attribute [scoped simp]
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
  rw [heq]
  unfold Unchunked.SendEk.HeaderSent.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, ENCAPSULATION_KEY_SIZE, DECAPSULATION_KEY_SIZE] at hlen
  simp only [rawUcHeaderSent, rawOptAuth_eq_optAuthWeight, hlen.1, hlen.2]
  omega

theorem ucEkSent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.EkSent}
    {s : Unchunked.SendEk.EkSent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.EkSent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcEkSent s.into_pb ≤ optAuthWeight pb.auth + 2400 := by
  have heq : rawUcEkSent s.into_pb = rawUcEkSent pb := by
    unfold Unchunked.SendEk.EkSent.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSent.into_pb, rawUcEkSent, hauth]
  rw [heq]
  unfold Unchunked.SendEk.EkSent.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [beq_iff_eq, DECAPSULATION_KEY_SIZE] at hlen
  simp only [rawUcEkSent, rawOptAuth_eq_optAuthWeight, hlen]
  omega

theorem ucEkSentCt1Received_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.EkSentCt1Received}
    {s : Unchunked.SendEk.EkSentCt1Received (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendEk.EkSentCt1Received.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcEkSentCt1Received s.into_pb ≤ optAuthWeight pb.auth + 3360 := by
  have heq : rawUcEkSentCt1Received s.into_pb = rawUcEkSentCt1Received pb := by
    unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendEk.EkSentCt1Received.into_pb, rawUcEkSentCt1Received, hauth]
  rw [heq]
  unfold Unchunked.SendEk.EkSentCt1Received.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, DECAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcEkSentCt1Received, rawOptAuth_eq_optAuthWeight, hlen.1, hlen.2]
  omega

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
  rw [heq]
  unfold Unchunked.SendCt.HeaderReceived.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [beq_iff_eq, HEADER_SIZE] at hlen
  simp only [rawUcHeaderReceived, rawOptAuth_eq_optAuthWeight, hlen]
  omega

theorem ucCt1Sent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1Sent}
    {s : Unchunked.SendCt.Ct1Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1Sent s.into_pb ≤ optAuthWeight pb.auth + 3104 := by
  have heq : rawUcCt1Sent s.into_pb = rawUcCt1Sent pb := by
    unfold Unchunked.SendCt.Ct1Sent.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1Sent.into_pb, rawUcCt1Sent, hauth]
  rw [heq]
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, HEADER_SIZE, ENCAPSULATION_STATE_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcCt1Sent, rawOptAuth_eq_optAuthWeight, hlen.1.1, hlen.1.2, hlen.2]
  omega

theorem ucCt1SentEkReceived_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1SentEkReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1SentEkReceived s.into_pb ≤ optAuthWeight pb.auth + 4192 := by
  have heq : rawUcCt1SentEkReceived s.into_pb = rawUcCt1SentEkReceived pb := by
    unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h; split at h <;> [skip; contradiction]
    cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawUcCt1SentEkReceived, hauth]
  rw [heq]
  unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h
  split at h <;> [skip; contradiction]
  rename_i hlen
  simp only [Bool.and_eq_true, beq_iff_eq, ENCAPSULATION_STATE_SIZE, ENCAPSULATION_KEY_SIZE, CIPHERTEXT1_SIZE] at hlen
  simp only [rawUcCt1SentEkReceived, rawOptAuth_eq_optAuthWeight, hlen.1.1, hlen.1.2, hlen.2]
  omega

theorem ucCt2Sent_from_pb_raw_le_weight {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct2Sent}
    {s : Unchunked.SendCt.Ct2Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct2Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt2Sent s.into_pb ≤ optAuthWeight pb.auth := by
  have heq : rawUcCt2Sent s.into_pb = rawUcCt2Sent pb := by
    unfold Unchunked.SendCt.Ct2Sent.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
    have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct2Sent.into_pb, rawUcCt2Sent, hauth]
  rw [heq]; simp [rawUcCt2Sent, rawOptAuth_eq_optAuthWeight]

theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl; omega

def pointRaw' (pt : Point) : Nat := 2 * pt.value.length + 22

theorem map_intoPb_encoder_pts' (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map (fun b => b.length + 22)) =
    pts.map pointRaw' := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]; simp only [pointRaw', flatMap_u16ToBeBytes_length]

theorem sum_map_set_le' {α : Type} (f : α → Nat) (xs : List α) (idx : Nat) (x x' : α) (c : Nat)
    (hget : xs[idx]? = some x) (hle : f x' ≤ f x + c) :
    ((xs.set idx x').map f).sum ≤ (xs.map f).sum + c := by
  induction xs generalizing idx with
  | nil => simp at hget
  | cons a rest ih =>
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget; subst hget
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]; omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at hget
      have hih := ih i hget
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]; omega

theorem distributeMsgChunks_sum_le' (i : Nat) (msg : List (BitVec 8)) (pts : List Point)
    {pts' : List Point} (h : PolyEncoder.distributeMsgChunks i msg pts = .ok pts') :
    (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length := by
  suffices ∀ n i (msg : List (BitVec 8)) (pts : List Point), msg.length ≤ n →
      PolyEncoder.distributeMsgChunks i msg pts = .ok pts' →
      (pts'.map pointRaw').sum ≤ (pts.map pointRaw').sum + msg.length from
    this msg.length i msg pts (Nat.le_refl _) h
  intro n; induction n with
  | zero =>
    intro i msg pts hn h; cases msg with
    | nil => unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    | cons _ _ => simp at hn
  | succ n ih =>
    intro i msg pts hn h
    rcases msg with _ | ⟨c0, _ | ⟨c1, rest⟩⟩
    · unfold PolyEncoder.distributeMsgChunks at h; simp only [Except.ok.injEq] at h; subst h; omega
    · unfold PolyEncoder.distributeMsgChunks at h; contradiction
    · unfold PolyEncoder.distributeMsgChunks at h; dsimp only [] at h; split at h
      · rename_i pt hpt
        have hih := ih (i + 1) rest _ (by simp only [List.length_cons] at hn; omega) h
        have hset := sum_map_set_le' pointRaw' pts (i % pts.length) pt
          { value := pt.value ++ [GF16.new ((c0.zeroExtend 16 <<< 8) + c1.zeroExtend 16)] } 2 hpt
          (by simp only [pointRaw', List.length_append, List.length_singleton]; omega)
        simp only [List.length_cons]; omega
      · contradiction

theorem polyEncoder_encodeBytes_raw_le_msg {msg : List (BitVec 8)} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h; split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · rcases hpts : PolyEncoder.distributeMsgChunks 0 msg (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h
        have hsum := distributeMsgChunks_sum_le' 0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw').sum = 352 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc,
          map_intoPb_encoder_pts', List.map_nil, List.sum_nil]; omega

theorem expectEncodeBytes_raw_le_msg {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold expectEncodeBytes spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1); cases res with
  | error _ => contradiction
  | ok enc' => have hinj := Except.ok.inj h2; subst hinj; exact polyEncoder_encodeBytes_raw_le_msg h1'

theorem poly_addChunk_liftM_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.add_chunk dec chunk) : Except StatesPanic spqrPolyApi.PolyDecoder) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
theorem poly_addChunk_ofPanic_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk dec chunk) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)
theorem poly_decodedMessage_liftM_eq_ok {dec : PolyDecoder} {msg? : Option Bytes}
    (h : (liftM (spqrPolyApi.decoded_message dec) : Except StatesPanic (Option Bytes)) = .ok msg?) :
    dec.decodedMessage = .ok msg? := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
theorem poly_decoderNew_liftM_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : (liftM (spqrPolyApi.decoder_new lenBytes) :
      Except StatesPanic (Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder)) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)
theorem poly_decoderNew_ofPanic_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : StatesResult.ofPanic (spqrPolyApi.decoder_new lenBytes) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only at h; exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

theorem linkToPb_modify_recv_le (link : ChainEpoch) (recv' : ChainEpochDirection) (K : Nat)
    (h : (EpochDirectionPB.encodeRaw recv'.intoPb).length ≤
         (EpochDirectionPB.encodeRaw link.recv.intoPb).length + K) :
    (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb { link with recv := recv' })).length ≤
      (Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)).length + K + 44 := by
  have hm' := encodeMessage_length_le ChainEpochPB.encodeRaw 3#32 (linkToPb { link with recv := recv' })
  have hm := encodeRaw_le_encodeMessage ChainEpochPB.encodeRaw 3#32 (linkToPb link)
  simp only [ChainEpochPB.encodeRaw, linkToPb, Proto.encodeOptMessage, List.length_append] at hm' hm ⊢
  have hr' := encodeMessage_length_le EpochDirectionPB.encodeRaw 2#32 recv'.intoPb
  have hr := encodeRaw_le_encodeMessage EpochDirectionPB.encodeRaw 2#32 link.recv.intoPb
  omega

theorem chain_recvKey_weight_le {hkdf : HkdfFn} {c1 c2 : Chain} {ep : Epoch} {idx : BitVec 32} {out : Bytes}
    (hooo : c1.params.maxOooKeysOrDefault.toNat ≤ 2000)
    (h : c1.recvKey hkdf ep idx = .ok (c2, out)) :
    chainWeight c2.intoPb ≤ chainWeight c1.intoPb + 72156 := by
  unfold Chain.recvKey at h
  split at h
  · injection h with hp; rcases Prod.mk.inj hp with ⟨rfl, _⟩; omega
  · rcases except_bind_eq_ok h with ⟨epochIndex, _, h⟩
    dsimp only at h
    cases hget : c1.links[epochIndex]? with
    | none => simp [hget] at h
    | some link =>
      rw [hget] at h
      dsimp only [Bind.bind, Except.bind] at h
      rcases except_bind_eq_ok h with ⟨⟨recv', out'⟩, hkey, h⟩
      injection h with hp; rcases Prod.mk.inj hp with ⟨hc2, _⟩
      subst hc2
      have hk_len := key_ooo_encodeRaw_le hkdf link.recv idx c1.params hooo hkey
      have hmod := linkToPb_modify_recv_le link recv' 72112 hk_len
      have hget_map : (c1.links.map linkToPb)[epochIndex]? = some (linkToPb link) := by
        rw [List.getElem?_map, hget]; rfl
      have hset := encodeRepeatedMessage_set_le ChainEpochPB.encodeRaw 3#32 72156
        (c1.links.map linkToPb) epochIndex (linkToPb link) (linkToPb { link with recv := recv' })
        hget_map (by omega)
      have hmap_set : (c1.links.set epochIndex { link with recv := recv' }).map linkToPb =
          (c1.links.map linkToPb).set epochIndex (linkToPb { link with recv := recv' }) := by
        rw [List.map_set]
      change (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32
        ((c1.links.set epochIndex { link with recv := recv' }).map linkToPb)).length +
        c1.nextRoot.length ≤
        (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 (c1.links.map linkToPb)).length +
        c1.nextRoot.length + 72156
      rw [hmap_set]
      omega

theorem chainFrom_weight_and_ooo {hkdf : HkdfFn} {chPb : Option ChainPB} {vnPb : Option VersionNegotiationPB}
    {c : Chain}
    (hc_ooo : ∀ cpb ∈ chPb, ∀ p ∈ cpb.params, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (hv_ooo : ∀ vpb ∈ vnPb, ∀ p ∈ vpb.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (h : chainFrom hkdf chPb vnPb = .ok c) :
    chainWeight c.intoPb ≤ optChainWeight chPb + optVnWeight vnPb + 206 ∧
      c.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
  unfold chainFrom at h
  cases hch : chPb with
  | some cpb =>
    rw [hch] at h
    have hw := chain_fromPb_weight_eq h
    have hp := chain_fromPb_params cpb c h
    have hooo := hc_ooo cpb (by simp [Option.mem_def, hch]) c.params (by simp [Option.mem_def, hp])
    simp only [optChainWeight, optWeight]
    exact ⟨by omega, hooo⟩
  | none =>
    rw [hch] at h
    cases hvn : vnPb with
    | none => rw [hvn] at h; contradiction
    | some vpb =>
      rw [hvn] at h
      have hp := chainFromVersionNegotiation_params hkdf vpb c h
      have hooo := hv_ooo vpb (by simp [Option.mem_def, hvn]) c.params (by simp [Option.mem_def, hp])
      unfold chainFromVersionNegotiation at h
      cases hd : Direction.fromI32? vpb.direction with
      | none => simp [hd, Bind.bind, Except.bind] at h
      | some dir =>
        cases hcp : vpb.chainParams with
        | none => simp [hd, hcp, Bind.bind, Except.bind] at h
        | some cp =>
          simp only [hd, hcp, Bind.bind, Except.bind] at h
          have hw := chain_new_weight_le h
          simp only [optChainWeight, optVnWeight, optWeight]
          exact ⟨by omega, hooo⟩

theorem decWeight_le_rawPolyDec (d : PolynomialDecoder) :
    decWeight d ≤ rawPolyDec d := by
  simp only [rawPolyDec, decWeight, sum_map_add_const]
  omega

theorem authWeight_le_rawAuth (a : ProtoAuthenticator) :
    authWeight a ≤ rawAuth a := by
  simp only [authWeight, rawAuth]
  omega

theorem initInner_v1Weight_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {v : Version} {dir : Direction} {authKey : Bytes} {pb : V1State}
    (h : initInner (spqrDepsWithMac F K mac) v dir authKey = .ok (some pb)) :
    v1Weight pb ≤ 488 := by
  unfold initInner at h
  cases v with
  | v0 => simp at h
  | v1 =>
    dsimp only [Functor.map, Except.map] at h
    split at h <;> try contradiction
    rename_i v1pb hv1
    have hinj := Option.some.inj (Except.ok.inj h); subst hinj
    unfold spqrDepsWithMac liftStatesResult at hv1; dsimp only [Functor.map, Except.map] at hv1
    cases dir with
    | a2b =>
      cases ha : States.init_a spqrPolyApi (spqrAuthApiWithMac F mac) authKey with
      | error _ => rw [ha] at hv1; contradiction
      | ok st =>
        rw [ha] at hv1; dsimp only [] at hv1; have hinj := Except.ok.inj hv1; subst hinj
        unfold States.init_a Chunked.SendEk.KeysUnsampled.new Unchunked.SendEk.KeysUnsampled.new spqrAuthApiWithMac at ha
        dsimp only [Bind.bind, Except.bind] at ha
        have hst := Except.ok.inj ha; subst hst
        have hauth := Authenticator.new_rawAuth_le F authKey 1#64
        have haw := authWeight_le_rawAuth (Authenticator.new F authKey 1#64).intoPb
        simp only [States.into_pb, Chunked.SendEk.KeysUnsampled.into_pb, Unchunked.SendEk.KeysUnsampled.into_pb,
          spqrAuthApiWithMac, v1Weight, innerStateW, ckKeysUnsampledW, optAuthWeight, optWeight]
        omega
    | b2a =>
      cases hb : States.init_b spqrPolyApi (spqrAuthApiWithMac F mac) authKey with
      | error _ => rw [hb] at hv1; contradiction
      | ok st =>
        rw [hb] at hv1; dsimp only [] at hv1; have hinj := Except.ok.inj hv1; subst hinj
        unfold States.init_b at hb
        rcases except_bind_eq_ok hb with ⟨s, hs, hst⟩
        have hst_eq := Except.ok.inj hst; subst hst_eq
        unfold Chunked.SendCt.NoHeaderReceived.new Unchunked.SendCt.NoHeaderReceived.new at hs
        rcases except_bind_eq_ok hs with ⟨decRes, hdec, hs1⟩
        rcases except_bind_eq_ok hs1 with ⟨uc, huc, h2⟩
        unfold spqrAuthApiWithMac at huc; dsimp only [Bind.bind, Except.bind] at huc
        have huc_eq := Except.ok.inj huc; subst huc_eq
        have hdec' := poly_decoderNew_liftM_eq_ok hdec
        cases decRes with
        | error _ => contradiction
        | ok dec =>
          have hinj := Except.ok.inj h2; subst hinj
          have hauth := Authenticator.new_rawAuth_le F authKey 1#64
          have haw := authWeight_le_rawAuth (Authenticator.new F authKey 1#64).intoPb
          have hpoly := PolyDecoder.new_raw_le hdec'
          have hdw := decWeight_le_rawPolyDec (protoPolyDecoderToPb dec.intoPb)
          simp only [States.into_pb, Chunked.SendCt.NoHeaderReceived.into_pb, Unchunked.SendCt.NoHeaderReceived.into_pb,
            spqrAuthApiWithMac, spqrPolyApi_decoder_into_pb, v1Weight, innerStateW, ckNoHeaderReceivedW,
            optAuthWeight, optDecWeight, optWeight]
          omega

theorem recv_chain_and_pre_weight_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (key : Option EpochSecret) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    v1Weight pb + chainWeight chain2.intoPb ≤ st.length + 73200 := by
  have hdec_w := decodeState_weight_le F K mac st prenegotiatedStatePb hdec
  have hbo := statePbOooBounded_of_decodeState F K mac st prenegotiatedStatePb hb hdec
  have hc0 : v1Weight pb + chainWeight chain0.intoPb ≤ st.length + 700 ∧
      chain0.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
    cases hpre with
    | equal =>
      rw [hinner] at hdec_w; dsimp only [] at hdec_w
      rcases chainFrom_weight_and_ooo hbo.1 hbo.2 hcf with ⟨hcw, hcooo⟩
      exact ⟨by omega, hcooo⟩
    | less vn v dir inner' chain' hvn hdir hinit hcf_pre =>
      dsimp only [] at hinner hcf
      subst hinner
      have hv1 := initInner_v1Weight_le hinit
      have hv_ooo : ∀ vpb ∈ (some vn : Option VersionNegotiationPB),
          ∀ p ∈ vpb.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000 := by
        intro vpb hvpb p hp
        simp only [Option.mem_def, Option.some.injEq] at hvpb; subst hvpb
        exact hbo.2 vn (by simp [Option.mem_def, hvn]) p hp
      rcases chainFrom_weight_and_ooo hbo.1 hv_ooo hcf_pre with ⟨hc'w, hc'ooo⟩
      unfold chainFrom at hcf
      have hc0_w := chain_fromPb_weight_eq hcf
      have hc0_p := chain_fromPb_params chain'.intoPb chain0 hcf
      rw [chain_intoPb_params] at hc0_p
      have hc0_peq := Option.some.inj hc0_p.symm
      rw [hvn] at hdec_w
      simp only [optVnWeight, optWeight] at hc'w hdec_w
      exact ⟨by omega, by rw [hc0_peq]; exact hc'ooo⟩
  rcases hc0 with ⟨hc0_w, hc0_ooo⟩
  have hc1 : chainWeight chain1.intoPb ≤ chainWeight chain0.intoPb + 206 ∧
      chain1.params.maxOooKeysOrDefault.toNat ≤ 2000 := by
    unfold recvAddEpochOpt at hadd
    cases key with
    | none =>
      injection hadd with h1; subst h1
      exact ⟨by omega, hc0_ooo⟩
    | some es =>
      have hadd' : chain0.addEpoch (spqrHkdfWith F) es = .ok chain1 :=
        SpqrApiResult.ofChainPanic_eq_ok.mp hadd
      have hw := chain_addEpoch_weight_le hadd'
      have hp := chain_addEpoch_params (spqrHkdfWith F) chain0 es chain1 hadd'
      exact ⟨hw, by rw [hp]; exact hc0_ooo⟩
  rcases hc1 with ⟨hc1_w, hc1_ooo⟩
  have hc2_w := chain_recvKey_weight_le hc1_ooo hrk
  omega

end Symbolic.Swarm.TRREF.GrowthRecvPureB
