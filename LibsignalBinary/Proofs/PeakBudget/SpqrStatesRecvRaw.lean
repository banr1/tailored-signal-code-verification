/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeStep

/-!
# Tight `rawV1State` Step Bound for SPQR `<States>::recv`

Tightens the `rawV1State` growth bound across `<spqr::v1::chunked::states::States>::recv` to
`+ 1,152` bytes (and hence `+ 2,976`) using `rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤
msg.length + 352` on `PolyEncoder.encodeBytes`: across all 11 constructors, `PolyEncoder` creation
occurs only in `KeysSampled.recv_ct1_chunk` (`- ek.length + (ek.length + 352) + 416 = + 768`) and
`send_ct2_encoder` (`160 + 352 = 512`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Chunk Ciphertext2 EncapsulationKey EncapsulationState Epoch GF16
   HEADER_SIZE Mac Message MlKem NUM_POLYS Point PolyDecoder PolyEncoder ProtoAuthenticator
   SpqrPanic States StatesPanic StatesResult ToStatesPanic V1Recv encaps2 expectEncodeBytes
   liftSpqrPanic protoPolyDecoderToPb protoPolyEncoderToPb spqrAuthApi spqrPolyApi u16ToBeBytes)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (send_ct2_encoder)
open CryptoVerification.SpqrV1.Top.StateSize
  (StatesPtsNeededBound ek_matches_header_length except_bind_eq_ok expectDecoderNew_raw_le
   optRaw_none optRaw_some pointRaw rawChCt1Acknowledged rawChCt1Received rawChCt1Sampled
   rawChCt2Sampled rawChEkReceivedCt1Sampled rawChEkSentCt1Received rawChHeaderReceived
   rawChHeaderSent rawChKeysSampled rawChKeysUnsampled rawChNoHeaderReceived rawInnerState
   rawPolyDec rawPolyEnc rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent rawUcEkSent
   rawUcEkSentCt1Received rawUcHeaderReceived rawUcHeaderSent rawUcKeysUnsampled
   rawUcNoHeaderReceived rawV1State)

@[local simp] private theorem pure_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (pure x >>= f) = f x := rfl
@[local simp] private theorem ok_bind_except {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl
@[local simp] private theorem except_mapError_eq_ok_iff {ε ε' α : Type} {f : ε → ε'}
    {m : Except ε α} {a : α} : m.mapError f = .ok a ↔ m = .ok a := by
  cases m <;> simp [Except.mapError]
@[local simp] private theorem liftSpqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    liftSpqrPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [liftSpqrPanic]
@[local simp] private theorem liftM_spqrPanic_eq_ok {α : Type} {r : Except SpqrPanic α} {v : α} :
    (liftM r : Except StatesPanic α) = .ok v ↔ r = .ok v :=
  liftSpqrPanic_eq_ok
@[local simp] private theorem statesResult_ofPanic_eq_ok {ε α : Type} [ToStatesPanic ε]
    {r : Except ε α} {v : α} : StatesResult.ofPanic r = .ok v ↔ r = .ok v := by
  cases r <;> simp [StatesResult.ofPanic]

private theorem poly_addChunk_liftM_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : (liftM (spqrPolyApi.add_chunk dec chunk) :
      Except StatesPanic spqrPolyApi.PolyDecoder) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)

private theorem poly_addChunk_ofPanic_eq_ok {dec dec' : PolyDecoder} {chunk : Chunk}
    (h : StatesResult.ofPanic (spqrPolyApi.add_chunk dec chunk) = .ok dec') :
    dec.addChunk chunk = .ok dec' := by
  unfold spqrPolyApi at h; dsimp only at h
  exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

private theorem poly_decodedMessage_liftM_eq_ok {dec : PolyDecoder} {msg? : Option Bytes}
    (h : (liftM (spqrPolyApi.decoded_message dec) : Except StatesPanic (Option Bytes)) = .ok msg?) :
    dec.decodedMessage = .ok msg? := by
  unfold spqrPolyApi at h; dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  exact except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h)

private theorem poly_decoderNew_ofPanic_eq_ok {lenBytes : Nat}
    {res : Except spqrPolyApi.EncodingError spqrPolyApi.PolyDecoder}
    (h : StatesResult.ofPanic (spqrPolyApi.decoder_new lenBytes) = .ok res) :
    PolyDecoder.new lenBytes = .ok res := by
  unfold spqrPolyApi at h; dsimp only at h
  exact except_mapError_eq_ok_iff.mp (statesResult_ofPanic_eq_ok.mp h)

private theorem flatMap_u16ToBeBytes_length (l : List GF16) :
    (l.flatMap (fun g => u16ToBeBytes g.value)).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    have : (u16ToBeBytes g.value).length = 2 := rfl
    omega

private theorem map_intoPb_encoder_pts (pts : List Point) :
    ((pts.map (fun pt => pt.value.flatMap (fun g => u16ToBeBytes g.value))).map
      (fun b => b.length + 22)) = pts.map pointRaw := by
  induction pts with
  | nil => rfl
  | cons pt ps ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]
    simp only [pointRaw, flatMap_u16ToBeBytes_length]

/-- Bounds `rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352` for `PolyEncoder.encodeBytes`.
-/
theorem encodeBytes_raw_le_msg {msg : Bytes} {enc : PolyEncoder}
    (h : PolyEncoder.encodeBytes msg = .ok (.ok enc)) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold PolyEncoder.encodeBytes PolyEncoder.encodeBytesBase at h
  split at h
  · simp [pure, Except.pure] at h
  · split at h
    · simp [pure, Except.pure] at h
    · rcases hpts : PolyEncoder.distributeMsgChunks 0 msg
          (List.replicate NUM_POLYS { value := [] }) with e | pts
      · simp [hpts, Bind.bind, Except.bind] at h
      · simp only [hpts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        have hsum := CryptoVerification.SpqrV1.Top.StateSize.PolyEncoder.distributeMsgChunks_sum_le
          0 msg (List.replicate NUM_POLYS { value := [] }) hpts
        have hinit : ((List.replicate NUM_POLYS ({ value := [] } : Point)).map pointRaw).sum = 352 := rfl
        simp only [PolyEncoder.intoPb, protoPolyEncoderToPb, rawPolyEnc,
          map_intoPb_encoder_pts, List.map_nil, List.sum_nil]
        omega

theorem expectEncodeBytes_raw_le_msg {site : String} {msg : Bytes} {enc : PolyEncoder}
    (h : expectEncodeBytes spqrPolyApi site msg = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ msg.length + 352 := by
  unfold expectEncodeBytes spqrPolyApi at h
  dsimp only [liftM, monadLift, MonadLift.monadLift] at h
  rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
  have h1' := except_mapError_eq_ok_iff.mp (liftSpqrPanic_eq_ok.mp h1)
  cases res with
  | error _ => contradiction
  | ok enc' =>
    have hinj := Except.ok.inj h2; subst hinj
    exact encodeBytes_raw_le_msg h1'

theorem encaps2_length {K : MlKem} {ek : EncapsulationKey} {es : EncapsulationState}
    {ct2 : Ciphertext2} (h : encaps2 K ek es = .ok ct2) : ct2.length = 128 := by
  unfold encaps2 at h
  rcases except_bind_eq_ok h with ⟨_, _, h2⟩
  dsimp only [] at h2
  split at h2
  · have hinj := Except.ok.inj h2; subst hinj
    exact List.Vector.toList_length _
  · contradiction

theorem spqrAuthApi_macCt_length {F : ShaCompress} {auth : Authenticator}
    {ep : Epoch} {ct : Bytes} {mac : Mac}
    (h : (spqrAuthApi F).mac_ct auth ep ct = .ok mac) : mac.length = 32 := by
  unfold spqrAuthApi Authenticator.macCt at h
  dsimp only [] at h
  split at h
  · have hinj := Except.ok.inj h; subst hinj
    exact Authenticator.length_macCtUnchecked F auth ep ct
  · contradiction

theorem send_ct2_lengths {F : ShaCompress} {K : MlKem}
    {self : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    {uc2 : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent (spqrAuthApi F)} {ct2 : Ciphertext2} {mac : Mac}
    (h : self.send_ct2 K = .ok (uc2, ct2, mac)) :
    uc2 = { epoch := self.epoch, auth := self.auth } ∧ ct2.length = 128 ∧ mac.length = 32 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.send_ct2 at h
  dsimp only [] at h
  rcases except_bind_eq_ok h with ⟨ct2', hct2, hb⟩
  rcases except_bind_eq_ok hb with ⟨mac', hmac, hc⟩
  have hinj := Except.ok.inj hc
  rcases Prod.mk.inj hinj with ⟨huc, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hct_eq, hmac_eq⟩
  subst huc; subst hct_eq; subst hmac_eq
  exact ⟨rfl, encaps2_length hct2, spqrAuthApi_macCt_length (liftM_spqrPanic_eq_ok.mp hmac)⟩

theorem send_ct2_encoder_raw_le {ct2 mac : Bytes} {enc : PolyEncoder}
    (hct2 : ct2.length = 128) (hmac : mac.length = 32)
    (h : send_ct2_encoder spqrPolyApi ct2 mac = .ok enc) :
    rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ 512 := by
  unfold send_ct2_encoder at h
  have hle := expectEncodeBytes_raw_le_msg h
  rw [List.length_append, hct2, hmac] at hle
  omega

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
  States.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysUnsampled.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.into_pb
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.into_pb
  CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.into_pb
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.HeaderReceived.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.into_pb
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.into_pb CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.into_pb
  CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.into_pb
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.KeysUnsampled.into_pb CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.into_pb
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent.into_pb CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived.into_pb CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.HeaderReceived.into_pb
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived.into_pb
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent.into_pb
  rawV1State rawInnerState rawChKeysUnsampled rawChKeysSampled
  rawChHeaderSent rawChCt1Received rawChEkSentCt1Received rawChNoHeaderReceived rawChHeaderReceived
  rawChCt1Sampled rawChEkReceivedCt1Sampled rawChCt1Acknowledged rawChCt2Sampled
  rawUcKeysUnsampled rawUcHeaderSent rawUcEkSent rawUcEkSentCt1Received
  rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent rawUcCt1SentEkReceived rawUcCt2Sent
  Option.map optRaw_none optRaw_some
  CryptoVerification.SpqrV1.Top.StateSize.Authenticator.rawAuth_intoPb_fromPb

set_option maxHeartbeats 400000 in
/-- Bounds `rawV1State` growth by `+ 1,152` bytes across all 11 constructors of `States.recv`. -/
theorem states_recv_raw_le_1152 {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.recv K msg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State self.into_pb + 1152 := by
  unfold States.recv at h; cases self with
  | keysUnsampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | keysSampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.KeysSampled.recv_ct1_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      rcases except_bind_eq_ok h1c with ⟨enc0, henc0, h1d⟩
      have hs' := Except.ok.inj h1d; subst hs'
      have hdec0_le := (expectDecoderNew_raw_le hdec0).1
      have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
        (poly_addChunk_liftM_eq_ok hadd)
      have henc0_le := expectEncodeBytes_raw_le_msg henc0
      simp [CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.HeaderSent.send_ek] at henc0_le ⊢
      omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | headerSent state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.HeaderSent.recv_ct1_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, hmsg, h1c⟩
      have hadd' := poly_addChunk_liftM_eq_ok hadd
      have hmsg' := poly_decodedMessage_liftM_eq_ok hmsg
      have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le hadd'
      have hadd_pts := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_ptsNeeded hadd'
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj
        simp; omega
      | some decoded =>
        rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
        have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSent.recv_ct1 at huc; split at huc <;> [contradiction; skip]
        have huc_eq := Except.ok.inj huc; subst huc_eq
        have hdec_len := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.decodedMessage_length hmsg'
        simp only [StatesPtsNeededBound] at hpts
        simp [hdec_len, hadd_pts]; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ct1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
      have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.Ct1Received.recv_ct2_chunk at h1; split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
      have hs' := Except.ok.inj h1c; subst hs'
      have hdec0_le := (expectDecoderNew_raw_le hdec0).1
      have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
        (poly_addChunk_liftM_eq_ok hadd)
      simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ekSentCt1Received state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h1; dsimp only [] at h1
      split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
        (poly_addChunk_ofPanic_eq_ok hadd)
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj
        simp; omega
      | some ct2Full =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨⟨uc, sec⟩, huc, h1d⟩
        rcases except_bind_eq_ok h1d with ⟨receivingHdr, hdec0, h1e⟩
        rw [statesResult_ofPanic_eq_ok] at hdec0
        have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
        unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.recv_ct2 at huc; dsimp only [] at huc
        rcases except_bind_eq_ok huc with ⟨ss0, _, huc1⟩
        rcases except_bind_eq_ok huc1 with ⟨ss, _, huc2⟩
        rcases except_bind_eq_ok huc2 with ⟨auth, hauth, huc3⟩
        rcases except_bind_eq_ok huc3 with ⟨verifyRes, _, huc4⟩
        unfold spqrAuthApi at hauth; dsimp only [StatesResult.ofPanic] at hauth
        have hauth_eq := Except.ok.inj hauth; subst hauth_eq
        cases verifyRes with
        | error _ => contradiction
        | ok u =>
          cases u; dsimp only [] at huc4; split at huc4 <;> [contradiction; skip]
          have huc_eq := (Prod.mk.inj (Except.ok.inj huc4)).1; subst huc_eq
          have hauth_le := CryptoVerification.SpqrV1.Top.StateSize.Authenticator.update_rawAuth_le
            F state.uc.auth state.uc.epoch ss
          have hdec0_le := (expectDecoderNew_raw_le hdec0).1
          simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | noHeaderReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h
    · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h1; dsimp only [] at h1
      split at h1 <;> [contradiction; skip]
      rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩
      rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
      have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
        (poly_addChunk_ofPanic_eq_ok hadd)
      cases decoded? with
      | none =>
        have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj
        simp; omega
      | some hdrFull =>
        dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
        rcases except_bind_eq_ok h1c with ⟨receivingEkRes, hek0, h1d⟩
        rcases except_bind_eq_ok h1d with ⟨uc, huc, h1e⟩
        have hek0' := poly_decoderNew_ofPanic_eq_ok hek0
        cases receivingEkRes with
        | error _ => contradiction
        | ok receivingEk =>
          have hres := Except.ok.inj h1e; subst hres; have hinj := Except.ok.inj h2; subst hinj
          unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.NoHeaderReceived.recv_header at huc; split at huc <;> [contradiction; skip]
          rcases except_bind_eq_ok huc with ⟨verifyRes, _, huc2⟩
          cases verifyRes with
          | error _ => contradiction
          | ok u =>
            cases u; have huc_eq := Except.ok.inj huc2; subst huc_eq
            have hek_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.new_raw_le hek0'
            simp [HEADER_SIZE]; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | headerReceived state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega
  | ct1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
      (poly_addChunk_ofPanic_eq_ok hadd)
    cases decoded? with
    | none =>
      dsimp only [] at h1c; split at h1c <;>
        (have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj; simp; omega)
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; rename_i hek_match
      have huc_eq := Except.ok.inj huc; subst huc_eq
      have hek_len := ek_matches_header_length hek_match; split at h1d
      · rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
        rw [statesResult_ofPanic_eq_ok] at hct2 henc2
        have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
        rcases send_ct2_lengths hct2 with ⟨rfl, hct2_len, hmac_len⟩
        have henc2_le := send_ct2_encoder_raw_le hct2_len hmac_len henc2
        simp; omega
      · have hres := Except.ok.inj h1d; subst hres; have hinj := Except.ok.inj h2; subst hinj
        simp [hek_len]; omega
  | ekReceivedCt1Sampled state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    have hisAck : ∀ b : Bool, (if b = true then do
        let s' ← StatesResult.ofPanic (state.recv_ct1_ack K msg.epoch)
        Except.ok ({ state := States.ct2Sampled s', key := none } : V1Recv spqrPolyApi (spqrAuthApi F))
      else Except.ok { state := States.ekReceivedCt1Sampled state, key := none }) = .ok recvOut →
      rawV1State recvOut.state.into_pb ≤ rawV1State (States.ekReceivedCt1Sampled state).into_pb + 1152 := by
      intro b hb; cases b
      · have hinj := Except.ok.inj hb; subst hinj; dsimp only []; omega
      · simp only [ite_true] at hb; rcases except_bind_eq_ok hb with ⟨s', h1, h2⟩
        rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
        unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
        dsimp only [] at h1; split at h1 <;> [contradiction; skip]
        rcases except_bind_eq_ok h1 with ⟨⟨uc2, ct2, mac⟩, hct2, h1b⟩
        rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩
        have hs' := Except.ok.inj h1c; subst hs'
        rcases send_ct2_lengths hct2 with ⟨rfl, hct2_len, hmac_len⟩
        have henc2_le := send_ct2_encoder_raw_le hct2_len hmac_len henc2
        simp; omega
    exact hisAck _ h
  | ct1Acknowledged state =>
    dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd, h1b⟩
    rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := CryptoVerification.SpqrV1.Top.StateSize.PolyDecoder.addChunk_raw_le
      (poly_addChunk_ofPanic_eq_ok hadd)
    cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres; have hinj := Except.ok.inj h2; subst hinj
      simp; omega
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, mac⟩, hct2, h1e⟩
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩
      rw [statesResult_ofPanic_eq_ok] at hct2 henc2
      have hres := Except.ok.inj h1f; subst hres; have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; have huc_eq := Except.ok.inj huc; subst huc_eq
      rcases send_ct2_lengths hct2 with ⟨rfl, hct2_len, hmac_len⟩
      have henc2_le := send_ct2_encoder_raw_le hct2_len hmac_len henc2
      simp; omega
  | ct2Sampled state =>
    dsimp only [] at h; split at h
    · split at h <;> [skip; contradiction]; rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1; have hinj := Except.ok.inj h2; subst hinj
      unfold CryptoVerification.LibsignalSpqrV1.Chunked.SendCt.Ct2Sampled.recv_next_epoch CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct2Sent.recv_next_epoch at h1
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨uc, huc, h1b⟩
      have hs' := Except.ok.inj h1b; subst hs'
      split at huc <;> [contradiction; skip]; split at huc <;> [contradiction; skip]
      have huc_eq := Except.ok.inj huc; subst huc_eq; simp; omega
    · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem states_recv_raw_le_2976 {F : ShaCompress} {K : MlKem}
    {self : States spqrPolyApi (spqrAuthApi F)} {msg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApi F)}
    (hpts : StatesPtsNeededBound self) (h : self.recv K msg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State self.into_pb + 2976 := by
  have h1 := states_recv_raw_le_1152 hpts h
  omega

end LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvRaw
