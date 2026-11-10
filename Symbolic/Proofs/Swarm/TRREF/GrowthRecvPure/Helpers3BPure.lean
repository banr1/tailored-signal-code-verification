/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers3APure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers1APure

/-!
# SPQR V1 State Decoding Weight and Per-Constructor Receive Growth Lemmas

Bounds `rawV1State st0.into_pb` in terms of `v1Weight pb` across `statesFromPb`, and bounds raw
state growth across `States.recv` for the first six V1 state constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPureB

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open CryptoVerification.SpqrV1.ProtoRepr

theorem encodeState_v1_chain_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st1 : (spqrDepsWithMac F K mac).States) (chain2 : Chain) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ rawV1State st1.into_pb + chainWeight chain2.intoPb + 800 := by
  change (PqRatchetState.encodeRaw {
    versionNegotiation := none
    chain := some chain2.intoPb
    inner := some (.v1 st1.into_pb)
  }).length ≤ rawV1State st1.into_pb + chainWeight chain2.intoPb + 800
  unfold PqRatchetState.encodeRaw PqRatchetState.Inner.encode
  dsimp only []
  rw [List.length_append, List.length_append]
  have hvn_enc := vnPB_encodeOptMessage_length_le none
  have hch_enc := chainPB_encodeOptMessage_length_le chain2.intoPb
  have hv1_enc := encodeMessage_length_le V1State.encodeRaw 3#32 st1.into_pb
  have hv1_raw := v1State_encodeRaw_length_le st1.into_pb
  simp only [optVnWeight, optWeight] at hvn_enc
  omega

theorem statesFromPb_eq_ok {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (spqrDepsWithMac F K mac).statesFromPb pb = .ok st0) :
    States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb = .ok st0 := by
  unfold spqrDepsWithMac liftStatesResult at h; dsimp only [] at h
  cases hs : States.from_pb spqrPolyApi (spqrAuthApiWithMac F mac) pb with
  | error e => rw [hs] at h; cases e <;> contradiction
  | ok s => rw [hs] at h; injection h with h; subst h; rfl

set_option maxHeartbeats 400000 in
theorem statesFromPb_raw_le_v1Weight {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {pb : V1State} {st0 : States spqrPolyApi (spqrAuthApiWithMac F mac)}
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok st0) :
    rawV1State st0.into_pb ≤ v1Weight pb + 4800 := by
  have h := statesFromPb_eq_ok hfrom
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    cases inner with
    | keysUnsampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.KeysUnsampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', h2⟩; have hinj2 := Except.ok.inj h2; subst hinj2
        have h1 := ucKeysUnsampled_from_pb_raw_le_weight huc'
        simp only [v1Weight, innerStateW, ckKeysUnsampledW, hinner, huc] at h1 ⊢
        simp at h1 ⊢; omega
    | keysSampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.KeysSampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucHeaderSent_from_pb_raw_le_weight huc'
        have h2 := encoderFromPbStateDecode_raw_le_weight henc
        simp only [v1Weight, innerStateW, ckKeysSampledW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.HeaderSent.from_pb at hv
      cases hrec : s.receivingCt1 with
      | none =>
        rw [hrec] at hv; dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩
          rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩; contradiction
      | some d0 =>
        rw [hrec] at hv; dsimp only [] at hv; split at hv <;> [contradiction; skip]
        cases huc : s.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
          have h1 := ucEkSent_from_pb_raw_le_weight huc'
          have h2 := encoderFromPbStateDecode_raw_le_weight henc
          have h3 := decoderFromPbStateDecode_raw_le_weight (pb? := some d0) hdec
          simp only [v1Weight, innerStateW, ckHeaderSentW, hinner, huc, hrec] at h1 h2 h3 ⊢
          simp at h1 h2 h3 ⊢; omega
    | ct1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.Ct1Received.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucEkSentCt1Received_from_pb_raw_le_weight huc'
        have h2 := encoderFromPbStateDecode_raw_le_weight henc
        simp only [v1Weight, innerStateW, ckCt1ReceivedW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | ekSentCt1Received s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendEk.EkSentCt1Received.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
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
        have h1 := ucEkSentCt1Received_from_pb_raw_le_weight huc'
        have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        simp only [v1Weight, innerStateW, ckEkSentCt1ReceivedW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | noHeaderReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.NoHeaderReceived.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
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
        have h1 := ucNoHeaderReceived_from_pb_raw_le_weight huc'
        have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        simp only [v1Weight, innerStateW, ckNoHeaderReceivedW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | headerReceived s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.HeaderReceived.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
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
        have h1 := ucHeaderReceived_from_pb_raw_le_weight huc'
        have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        simp only [v1Weight, innerStateW, ckHeaderReceivedW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | ct1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct1Sampled.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv
      cases huc : s.uc with
      | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
      | some u =>
        rw [huc] at hv
        have hbody : (do
            let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) u
            let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi s.sendingCt1
            let receivingEk ← decoderFromPbStateDecode spqrPolyApi s.receivingEk
            Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) =
              Except.ok v := by
          split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
        rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        rcases except_bind_eq_ok hv3 with ⟨dec, hdec, hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
        have h1 := ucCt1Sent_from_pb_raw_le_weight huc'
        have h2 := encoderFromPbStateDecode_raw_le_weight henc
        have h3 := decoderFromPbStateDecode_raw_le_weight hdec
        simp only [v1Weight, innerStateW, ckCt1SampledW, hinner, huc] at h1 h2 h3 ⊢
        simp at h1 h2 h3 ⊢; omega
    | ekReceivedCt1Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt1SentEkReceived_from_pb_raw_le_weight huc'
        have h2 := encoderFromPbStateDecode_raw_le_weight henc
        simp only [v1Weight, innerStateW, ckEkReceivedCt1SampledW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | ct1Acknowledged s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv
      dsimp only [Bind.bind, Except.bind] at hv; cases huc : s.uc with
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
        have h1 := ucCt1Sent_from_pb_raw_le_weight huc'
        have h2 := decoderFromPbStateDecode_raw_le_weight hdec
        simp only [v1Weight, innerStateW, ckCt1AcknowledgedW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega
    | ct2Sampled s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := Except.ok.inj h; subst hinj
      unfold Chunked.SendCt.Ct2Sampled.from_pb at hv; cases huc : s.uc with
      | none => rw [huc] at hv; contradiction
      | some u =>
        rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
        rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
        have hinj2 := Except.ok.inj hv3; subst hinj2
        have h1 := ucCt2Sent_from_pb_raw_le_weight huc'
        have h2 := encoderFromPbStateDecode_raw_le_weight henc
        simp only [v1Weight, innerStateW, ckCt2SampledW, hinner, huc] at h1 h2 ⊢
        simp at h1 h2 ⊢; omega

/-! ## Per-Constructor `States.recv` Raw Size Bounds -/

theorem statesRecv_eq_ok {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    (st0 st1 : States spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : Message spqrPolyApi) (key : Option EpochSecret)
    (hstep : (spqrDepsWithMac F K mac).statesRecv st0 sckaMsg = .ok (key, st1)) :
    ∃ recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac),
      st0.recv K sckaMsg = .ok recvOut ∧ st1 = recvOut.state := by
  unfold spqrDepsWithMac liftStatesResult at hstep; dsimp only [] at hstep
  cases h : st0.recv K sckaMsg with
  | error e => rw [h] at hstep; cases e <;> contradiction
  | ok recvOut =>
    rw [h] at hstep
    exact ⟨recvOut, rfl, (Prod.mk.inj (Except.ok.inj hstep)).2.symm⟩

theorem recv_keysUnsampled_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (States.keysUnsampled s0 : States spqrPolyApi (spqrAuthApiWithMac F mac)).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.keysUnsampled s0 : States spqrPolyApi (spqrAuthApiWithMac F mac)).into_pb := by
  unfold States.recv at h; dsimp only [] at h
  split at h <;> [contradiction; skip]
  have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem recv_keysSampled_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (States.keysSampled s0).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.keysSampled s0).into_pb + 800 := by
  unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
  split at h
  · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := Except.ok.inj h2; subst hinj
    unfold Chunked.SendEk.KeysSampled.recv_ct1_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
    rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
    rcases except_bind_eq_ok h1c with ⟨enc0, henc0, h1d⟩; have hs' := Except.ok.inj h1d; subst hs'
    have hdec0_le := (expectDecoderNew_raw_le hdec0).1
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_liftM_eq_ok hadd)
    have henc0_le := expectEncodeBytes_raw_le_msg henc0
    simp [Unchunked.SendEk.HeaderSent.send_ek] at henc0_le ⊢; omega
  · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem statesFromPb_headerSent_ptsNeeded {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {pb : V1State} {s0 : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApiWithMac F mac)}
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.headerSent s0)) :
    s0.receiving_ct1.ptsNeeded ≤ 480 := by
  have h := statesFromPb_eq_ok hfrom
  unfold States.from_pb at h
  cases hinner : pb.innerState with
  | none => rw [hinner] at h; contradiction
  | some inner =>
    rw [hinner] at h
    cases inner with
    | headerSent s =>
      dsimp only [Functor.map, Except.map] at h; split at h <;> try contradiction
      rename_i v hv; have hinj := States.headerSent.inj (Except.ok.inj h); subst hinj
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
          rcases decoderFromPbStateDecode_raw_le hdec with ⟨_, d, hd, hpts⟩
          have hd_eq := Option.some.inj hd; subst hd_eq
          simp only [hpts, hd_pts, CIPHERTEXT1_SIZE]; omega
    | _ => dsimp only [Functor.map, Except.map] at h; split at h <;> nomatch h

theorem recv_headerSent_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (hpts : s0.receiving_ct1.ptsNeeded ≤ 480)
    (h : (States.headerSent s0).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.headerSent s0).into_pb + 1000 := by
  unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
  split at h
  · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
    unfold Chunked.SendEk.HeaderSent.recv_ct1_chunk at h1; split at h1 <;> [contradiction; skip]
    rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, hmsg, h1c⟩
    have hadd' := poly_addChunk_liftM_eq_ok hadd
    have hadd_le := PolyDecoder.addChunk_raw_le hadd'
    have hadd_pts := PolyDecoder.addChunk_ptsNeeded hadd'
    cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      simp; omega
    | some decoded =>
      rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      have hres := Except.ok.inj h1d; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      unfold Unchunked.SendEk.EkSent.recv_ct1 at huc; split at huc <;> [contradiction; skip]
      have huc_eq := Except.ok.inj huc; subst huc_eq
      have hdec_len := PolyDecoder.decodedMessage_length (poly_decodedMessage_liftM_eq_ok hmsg)
      simp [hdec_len, hadd_pts]; omega
  · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem recv_ct1Received_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (States.ct1Received s0).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.ct1Received s0).into_pb + 500 := by
  unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
  split at h
  · rcases except_bind_eq_ok h with ⟨s', h1, h2⟩; rw [statesResult_ofPanic_eq_ok] at h1
    have hinj := Except.ok.inj h2; subst hinj
    unfold Chunked.SendEk.Ct1Received.recv_ct2_chunk at h1; split at h1 <;> [contradiction; skip]
    rcases except_bind_eq_ok h1 with ⟨dec0, hdec0, h1b⟩; rcases except_bind_eq_ok h1b with ⟨dec1, hadd, h1c⟩
    have hs' := Except.ok.inj h1c; subst hs'
    have hdec0_le := (expectDecoderNew_raw_le hdec0).1
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_liftM_eq_ok hadd)
    simp; omega
  · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem recv_ekSentCt1Received_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (States.ekSentCt1Received s0).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.ekSentCt1Received s0).into_pb + 500 := by
  unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
  split at h
  · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendEk.EkSentCt1Received.recv_ct2_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
    rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd)
    cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      simp; omega
    | some ct2Full =>
      dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
      rcases except_bind_eq_ok h1c with ⟨⟨uc, sec⟩, huc, h1d⟩; rcases except_bind_eq_ok h1d with ⟨receivingHdr, hdec0, h1e⟩
      rw [statesResult_ofPanic_eq_ok] at hdec0; have hres := Except.ok.inj h1e; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      unfold Unchunked.SendEk.EkSentCt1Received.recv_ct2 at huc; dsimp only [] at huc
      rcases except_bind_eq_ok huc with ⟨ss0, _, huc1⟩; rcases except_bind_eq_ok huc1 with ⟨ss, _, huc2⟩
      rcases except_bind_eq_ok huc2 with ⟨auth, hauth, huc3⟩; rcases except_bind_eq_ok huc3 with ⟨verifyRes, _, huc4⟩
      unfold spqrAuthApiWithMac at hauth; dsimp only [StatesResult.ofPanic] at hauth
      have hauth_eq := Except.ok.inj hauth; subst hauth_eq; cases verifyRes with
      | error _ => contradiction
      | ok u =>
        cases u; dsimp only [] at huc4; split at huc4 <;> [contradiction; skip]
        have huc_eq := (Prod.mk.inj (Except.ok.inj huc4)).1; subst huc_eq
        have hauth_le := Authenticator.update_rawAuth_le F s0.uc.auth s0.uc.epoch ss
        have hdec0_le := (expectDecoderNew_raw_le hdec0).1
        simp; omega
  · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

theorem recv_noHeaderReceived_raw_le {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {s0 : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApiWithMac F mac)}
    {sckaMsg : Message spqrPolyApi}
    {recvOut : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac)}
    (h : (States.noHeaderReceived s0).recv K sckaMsg = .ok recvOut) :
    rawV1State recvOut.state.into_pb ≤ rawV1State (States.noHeaderReceived s0).into_pb + 500 := by
  unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
  split at h; · (have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega)
  split at h
  · rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.NoHeaderReceived.recv_hdr_chunk at h1; dsimp only [] at h1; split at h1 <;> [contradiction; skip]
    rcases except_bind_eq_ok h1 with ⟨dec1, hadd, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd)
    cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres
      have hinj := Except.ok.inj h2; subst hinj
      simp; omega
    | some hdrFull =>
      dsimp only [] at h1c; split at h1c <;> [contradiction; skip]
      rcases except_bind_eq_ok h1c with ⟨receivingEkRes, hek0, h1d⟩; rcases except_bind_eq_ok h1d with ⟨uc, huc, h1e⟩
      have hek0' := poly_decoderNew_ofPanic_eq_ok hek0; cases receivingEkRes with
      | error _ => contradiction
      | ok receivingEk =>
        have hres := Except.ok.inj h1e; subst hres
        have hinj := Except.ok.inj h2; subst hinj
        unfold Unchunked.SendCt.NoHeaderReceived.recv_header at huc; split at huc <;> [contradiction; skip]
        rcases except_bind_eq_ok huc with ⟨verifyRes, _, huc2⟩; cases verifyRes with
        | error _ => contradiction
        | ok u =>
          cases u; have huc_eq := Except.ok.inj huc2; subst huc_eq
          have hek_le := PolyDecoder.new_raw_le hek0'
          simp [HEADER_SIZE]; omega
  · have hinj := Except.ok.inj h; subst hinj; dsimp only []; omega

end Symbolic.Swarm.TRREF.GrowthRecvPureB
