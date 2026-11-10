/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvB.Defs
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesAPure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesBPure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.StatesPure

/-!
# SPQR V1 `spqrRecvB` OOO-Bound Preservation and Byte-Length Growth

Proves `spqr_recv_growth`: for any `st msg st' : Bytes` and `k? : Option Bytes` with
`SpqrOooBounded st`, `st.length < 2^32`, and `spqrRecvB F K mac st msg = some (st', k?)`,
`SpqrOooBounded st'` holds and `st'.length ≤ st.length + 2^17`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthRecvPure

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf
open CryptoVerification.SpqrV1.Top.StateSize.SymP3
open Symbolic.Swarm.TRREF.GrowthRecv
open BranchHelpers

namespace BranchHelpers

theorem spqrOooBounded_nil : SpqrOooBounded [] := by
  intro st hdec
  have hdec0 : PqRatchetState.decode [] =
      .ok { versionNegotiation := none, chain := none, inner := none } := rfl
  rw [hdec0] at hdec
  injection hdec with hst
  subst hst
  exact ⟨(by intro c hc; cases hc), (by intro v hv; cases hv)⟩

end BranchHelpers
open BranchHelpers

theorem spqr_recv_nil_growth (st : Bytes) :
    SpqrOooBounded ([] : Bytes) ∧ ([] : Bytes).length ≤ st.length + 2^17 :=
  ⟨BranchHelpers.spqrOooBounded_nil, Nat.zero_le _⟩

theorem spqr_recv_ekReceivedCt1Sampled_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.EkReceivedCt1Sampled spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ekReceivedCt1Sampled s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ekReceivedCt1Sampled s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ekReceivedCt1Sampled s0)) ≤ v1FullWeight pb + 704 := by
    have hf := statesFromPb_eq_ok hfrom
    unfold States.from_pb at hf
    cases his : pb.innerState with
    | none => rw [his] at hf; contradiction
    | some is =>
      rw [his] at hf
      cases is with
      | ekReceivedCt1Sampled ck =>
        dsimp only [Functor.map, Except.map] at hf; split at hf <;> try contradiction
        rename_i v hv; have hinj := (States.ekReceivedCt1Sampled.inj (Except.ok.inj hf)).symm; subst hinj
        unfold Chunked.SendCt.EkReceivedCt1Sampled.from_pb at hv; cases huc : ck.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          have hinj2 := Except.ok.inj hv3; subst hinj2
          have h1 := ucCt1SentEkReceived_from_pb_raw_eq_withMac huc'
          have h2 := encoderFromPbStateDecode_raw_le_fullW henc
          simp only [v1FullWeight, innerStateFullW, ckEkReceivedCt1SampledFullW, his, huc, optWeight] at *
          dsimp only [States.into_pb, Chunked.SendCt.EkReceivedCt1Sampled.into_pb, rawV1State, optRaw_some,
            rawInnerState, rawChEkReceivedCt1Sampled, spqrPolyApi_encoder_into_pb] at *
          rw [h1]; omega
      | _ => dsimp only [Functor.map, Except.map] at hf; split at hf <;> nomatch hf
  have hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ekReceivedCt1Sampled s0)) + 1200 := by
    have h := statesRecv_eq_recv_ok hstep
    unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp)
    have hisAck : ∀ b : Bool, (if b = true then do
        let s' ← StatesResult.ofPanic (s0.recv_ct1_ack K sckaMsg.epoch)
        Except.ok ({ state := States.ct2Sampled s', key := none } : V1Recv spqrPolyApi (spqrAuthApiWithMac F mac))
      else Except.ok { state := States.ekReceivedCt1Sampled s0, key := none }) = .ok { state := st1, key := key } →
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
        rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ekReceivedCt1Sampled s0)) + 1200 := by
      intro b hb_ack; cases b
      · have hinj := congrArg V1Recv.state (Except.ok.inj hb_ack); subst hinj; simp
      · simp only [ite_true] at hb_ack; rcases except_bind_eq_ok hb_ack with ⟨s', h1, h2⟩
        rw [statesResult_ofPanic_eq_ok] at h1; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj
        unfold Chunked.SendCt.EkReceivedCt1Sampled.recv_ct1_ack at h1
        dsimp only [] at h1; split at h1 <;> [contradiction; skip]
        rcases except_bind_eq_ok h1 with ⟨⟨uc2, ct2, macB⟩, hct2, h1b⟩
        rcases except_bind_eq_ok h1b with ⟨sendingCt2, henc2, h1c⟩; have hs' := Except.ok.inj h1c; subst hs'
        rcases send_ct2_encode_raw_le hct2 henc2 with ⟨rfl, henc2_le⟩
        simp; omega
    exact hisAck _ h
  exact v1_recv_finish_length_le F K mac st prenegotiatedStatePb statePb pb (.ekReceivedCt1Sampled s0) st1
    key chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom_le hstep_le hcf hadd hrk

theorem spqr_recv_ct1Acknowledged_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ct1Acknowledged s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ct1Acknowledged s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct1Acknowledged s0)) ≤ v1FullWeight pb + 704 := by
    have hf := statesFromPb_eq_ok hfrom
    unfold States.from_pb at hf
    cases his : pb.innerState with
    | none => rw [his] at hf; contradiction
    | some is =>
      rw [his] at hf
      cases is with
      | ct1Acknowledged ck =>
        dsimp only [Functor.map, Except.map] at hf; split at hf <;> try contradiction
        rename_i v hv; have hinj := (States.ct1Acknowledged.inj (Except.ok.inj hf)).symm; subst hinj
        unfold Chunked.SendCt.Ct1Acknowledged.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv
        cases huc : ck.uc with
        | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
        | some u =>
          rw [huc] at hv
          have hbody : (do
              let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) u
              let receivingEk ← decoderFromPbStateDecode spqrPolyApi ck.receivingEk
              Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok s0 := by
            split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
          rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec', hv3⟩
          have hinj2 := Except.ok.inj hv3; subst hinj2
          have h1 := ucCt1Sent_from_pb_raw_eq_withMac huc'
          have h2 := decoderFromPbStateDecode_raw_le_fullW hdec'
          simp only [v1FullWeight, innerStateFullW, ckCt1AcknowledgedFullW, his, huc, optWeight] at *
          dsimp only [States.into_pb, Chunked.SendCt.Ct1Acknowledged.into_pb, rawV1State, optRaw_some,
            rawInnerState, rawChCt1Acknowledged, spqrPolyApi_decoder_into_pb] at *
          rw [h1]; omega
      | _ => dsimp only [Functor.map, Except.map] at hf; split at hf <;> nomatch hf
  have hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct1Acknowledged s0)) + 1200 := by
    have h := statesRecv_eq_recv_ok hstep
    unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp)
    split at h; · (have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Acknowledged.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd_c, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd_c); cases decoded? with
    | none =>
      have hres := Except.ok.inj h1c; subst hres; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj; simp; omega
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, macB⟩, hct2, h1e⟩
      rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
      have hres := Except.ok.inj h1f; subst hres; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; have huc_eq := Except.ok.inj huc; subst huc_eq
      rcases send_ct2_encode_raw_le hct2 henc2 with ⟨rfl, henc2_le⟩
      simp; omega
  exact v1_recv_finish_length_le F K mac st prenegotiatedStatePb statePb pb (.ct1Acknowledged s0) st1
    key chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom_le hstep_le hcf hadd hrk

theorem spqr_recv_ct2Sampled_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.Ct2Sampled spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ct2Sampled s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ct2Sampled s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct2Sampled s0)) ≤ v1FullWeight pb + 704 := by
    have hf := statesFromPb_eq_ok hfrom
    unfold States.from_pb at hf
    cases his : pb.innerState with
    | none => rw [his] at hf; contradiction
    | some is =>
      rw [his] at hf
      cases is with
      | ct2Sampled ck =>
        dsimp only [Functor.map, Except.map] at hf; split at hf <;> try contradiction
        rename_i v hv; have hinj := (States.ct2Sampled.inj (Except.ok.inj hf)).symm; subst hinj
        unfold Chunked.SendCt.Ct2Sampled.from_pb at hv; cases huc : ck.uc with
        | none => rw [huc] at hv; contradiction
        | some u =>
          rw [huc] at hv; dsimp only [Bind.bind, Except.bind] at hv
          rcases except_bind_eq_ok hv with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          have hinj2 := Except.ok.inj hv3; subst hinj2
          have h1 := ucCt2Sent_from_pb_raw_eq_withMac huc'
          have h2 := encoderFromPbStateDecode_raw_le_fullW henc
          simp only [v1FullWeight, innerStateFullW, ckCt2SampledFullW, his, huc, optWeight] at *
          dsimp only [States.into_pb, Chunked.SendCt.Ct2Sampled.into_pb, rawV1State, optRaw_some,
            rawInnerState, rawChCt2Sampled, spqrPolyApi_encoder_into_pb] at *
          rw [h1]; omega
      | _ => dsimp only [Functor.map, Except.map] at hf; split at hf <;> nomatch hf
  have hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct2Sampled s0)) + 1200 := by
    have h := statesRecv_eq_recv_ok hstep
    unfold States.recv at h; dsimp only [] at h; split at h
    · split at h <;> [skip; contradiction]; rcases except_bind_eq_ok h with ⟨s', h1, h2⟩
      rw [statesResult_ofPanic_eq_ok] at h1; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj
      unfold Chunked.SendCt.Ct2Sampled.recv_next_epoch Unchunked.SendCt.Ct2Sent.recv_next_epoch at h1
      dsimp only [] at h1; rcases except_bind_eq_ok h1 with ⟨uc, huc, h1b⟩
      have hs' := Except.ok.inj h1b; subst hs'; split at huc <;> [contradiction; skip]; split at huc <;> [contradiction; skip]
      have huc_eq := Except.ok.inj huc; subst huc_eq; simp; omega
    · have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp
  exact v1_recv_finish_length_le F K mac st prenegotiatedStatePb statePb pb (.ct2Sampled s0) st1
    key chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom_le hstep_le hcf hadd hrk

/-- Encoded state growth bound (`≤ st.length + 2^17`) across all 11 V1 states in `States.recv`. -/
theorem spqr_recv_v1_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (st0 st1 : (spqrDepsWithMac F K mac).States)
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (chain0 chain1 chain2 : Chain) (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok st0)
    (hstep : (spqrDepsWithMac F K mac).statesRecv st0 sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  cases st0 with
  | keysUnsampled s0 =>
    exact spqr_recv_keysUnsampled_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | keysSampled s0 =>
    exact spqr_recv_keysSampled_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | headerSent s0 =>
    exact spqr_recv_headerSent_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ct1Received s0 =>
    exact spqr_recv_ct1Received_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ekSentCt1Received s0 =>
    exact spqr_recv_ekSentCt1Received_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | noHeaderReceived s0 =>
    exact spqr_recv_noHeaderReceived_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | headerReceived s0 =>
    exact spqr_recv_headerReceived_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ct1Sampled s0 =>
    exact spqr_recv_ct1Sampled_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ekReceivedCt1Sampled s0 =>
    exact spqr_recv_ekReceivedCt1Sampled_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ct1Acknowledged s0 =>
    exact spqr_recv_ct1Acknowledged_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk
  | ct2Sampled s0 =>
    exact spqr_recv_ct2Sampled_length_le F K mac st prenegotiatedStatePb statePb pb s0 sckaMsg
      key st1 chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom hstep hcf hadd hrk

namespace BranchHelpers

theorem topResult_ofError_ok {α : Type} (x : α) :
    SpqrApiResult.ofError (.ok x) = .ok x := rfl

theorem except_bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    Bind.bind (Except.ok x) f = f x := rfl

theorem except_pure_eq {ε α : Type} (x : α) :
    (pure x : Except ε α) = Except.ok x := rfl

theorem except_ite_error_eq_ok {ε α : Type} {c : Prop} [Decidable c]
    {e : ε} {b : Except ε α} {y : α}
    (h : (if c then Except.error e else b) = Except.ok y) :
    b = Except.ok y := by
  split at h
  · cases h
  · exact h

theorem except_ite_or {ε α : Type} {c : Prop} [Decidable c]
    {a b : Except ε α} {y : α}
    (h : (if c then a else b) = Except.ok y) :
    a = Except.ok y ∨ b = Except.ok y := by
  split at h
  · exact Or.inl h
  · exact Or.inr h

theorem except_ite_bind_error_eq_ok {ε α β : Type} {c : Prop} [Decidable c]
    {e : ε} {f : α → Except ε β} {b : Except ε β} {y : β}
    (h : (if c then Bind.bind (Except.error e) f else b) = Except.ok y) :
    b = Except.ok y := by
  split at h
  · cases h
  · exact h

end BranchHelpers
open BranchHelpers

local macro "step_recv_v1_cont"
    "[" F:ident K:ident mac:ident st:ident prePb:ident deps:ident hkdf:ident mp:ident
        hb:ident hdec:ident hdeps:ident hhkdf:ident hrecv:ident "]"
    statePb:term "," hpre:term : tactic => `(tactic| (
    cases hinner : ($statePb).inner with
    | none =>
      rw [hinner] at $hrecv:ident
      change (Except.ok _ = Except.ok _) at $hrecv:ident
      injection $hrecv:ident with hrec
      injection hrec with hst _
      subst hst
      exact spqr_recv_nil_growth $st
    | some pb =>
      rw [hinner] at $hrecv:ident
      change (Bind.bind (($deps).msgDeserialize ($mp).epoch ($mp).remaining) _ = _) at $hrecv:ident
      cases hdes : ($deps).msgDeserialize ($mp).epoch ($mp).remaining with
      | error e => rw [hdes] at $hrecv:ident; cases $hrecv:ident
      | ok sckaMsg =>
        rw [hdes, except_bind_ok] at $hrecv:ident
        cases hfrom : ($deps).statesFromPb pb with
        | error e => rw [hfrom] at $hrecv:ident; cases $hrecv:ident
        | ok st0 =>
          rw [hfrom, except_bind_ok] at $hrecv:ident
          cases hstep : ($deps).statesRecv st0 sckaMsg with
          | error e => rw [hstep] at $hrecv:ident; cases $hrecv:ident
          | ok pair =>
            rcases pair with ⟨key, st1⟩
            rw [hstep, except_bind_ok] at $hrecv:ident
            apply except_ite_error_eq_ok at $hrecv:ident
            cases hcf : chainFrom $hkdf ($statePb).chain ($statePb).versionNegotiation with
            | error e => rw [hcf] at $hrecv:ident; cases $hrecv:ident
            | ok chain0 =>
              rw [hcf, topResult_ofError_ok, except_bind_ok] at $hrecv:ident
              cases hkey : key with
              | none =>
                rw [hkey] at $hrecv:ident
                change (Bind.bind (pure chain0) _ = _) at $hrecv:ident
                rw [except_pure_eq, except_bind_ok] at $hrecv:ident
                cases hrk : chain0.recvKey $hkdf (($mp).epoch - 1#64) ($mp).index with
                | error e => rw [hrk] at $hrecv:ident; cases $hrecv:ident
                | ok rkPair =>
                  rcases rkPair with ⟨chain2, msgKey⟩
                  rw [hrk] at $hrecv:ident
                  change (Except.ok _ = Except.ok _) at $hrecv:ident
                  injection $hrecv:ident with hrec
                  injection hrec with hst _
                  subst hst
                  rw [hkey] at hstep
                  subst $hdeps:ident $hhkdf:ident
                  have hlen_le := spqr_recv_v1_length_le $F $K $mac $st $prePb $statePb pb st0 st1
                    sckaMsg none chain0 chain0 chain2 (($mp).epoch - 1#64) ($mp).index msgKey
                    $hb $hdec ($hpre) hinner hfrom hstep hcf rfl hrk
                  exact ⟨spqr_recv_v1_oooBounded $F $K $mac $st $prePb $statePb st1 none
                          chain0 chain0 chain2 (($mp).epoch - 1#64) ($mp).index msgKey $hb $hdec ($hpre) hcf rfl hrk (by omega),
                         hlen_le⟩
              | some epochSecret =>
                rw [hkey] at $hrecv:ident
                change (Bind.bind (SpqrApiResult.ofChainPanic (chain0.addEpoch $hkdf epochSecret)) _ = _) at $hrecv:ident
                cases hadd : SpqrApiResult.ofChainPanic (chain0.addEpoch $hkdf epochSecret) with
                | error e => rw [hadd] at $hrecv:ident; cases $hrecv:ident
                | ok chain1 =>
                  rw [hadd, except_bind_ok] at $hrecv:ident
                  cases hrk : chain1.recvKey $hkdf (($mp).epoch - 1#64) ($mp).index with
                  | error e => rw [hrk] at $hrecv:ident; cases $hrecv:ident
                  | ok rkPair =>
                    rcases rkPair with ⟨chain2, msgKey⟩
                    rw [hrk] at $hrecv:ident
                    change (Except.ok _ = Except.ok _) at $hrecv:ident
                    injection $hrecv:ident with hrec
                    injection hrec with hst _
                    subst hst
                    rw [hkey] at hstep
                    subst $hdeps:ident $hhkdf:ident
                    have hlen_le := spqr_recv_v1_length_le $F $K $mac $st $prePb $statePb pb st0 st1
                      sckaMsg (some epochSecret) chain0 chain1 chain2 (($mp).epoch - 1#64) ($mp).index msgKey
                      $hb $hdec ($hpre) hinner hfrom hstep hcf hadd hrk
                    exact ⟨spqr_recv_v1_oooBounded $F $K $mac $st $prePb $statePb st1 (some epochSecret)
                            chain0 chain1 chain2 (($mp).epoch - 1#64) ($mp).index msgKey $hb $hdec ($hpre) hcf hadd hrk (by omega),
                           hlen_le⟩))

/-- `spqrRecvB` preserves `SpqrOooBounded` and grows the serialized SPQR state by at most `2^17`
bytes. -/
theorem spqr_recv_growth (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st msg st' : Bytes) (k? : Option Bytes)
    (hb : SpqrOooBounded st) (hlen : st.length < 2 ^ 32)
    (h : spqrRecvB F K mac st msg = some (st', k?)) :
    SpqrOooBounded st' ∧ st'.length ≤ st.length + 2^17 := by
  unfold spqrRecvB spqrV1RecvWithMac toSpqrRecvModel at h
  cases hrecv : recv (spqrDepsWithMac F K mac) (spqrHkdfWith F) st msg with
  | error e =>
    cases e <;> simp [hrecv] at h
  | ok r =>
    rcases r with ⟨r_state, r_key⟩
    simp [hrecv] at h
    rcases h with ⟨rfl, rfl⟩
    generalize hdeps : spqrDepsWithMac F K mac = deps at hrecv
    generalize hhkdf : spqrHkdfWith F = hkdf at hrecv
    unfold recv at hrecv
    cases hpre : msgPreamble msg with
    | error e => rw [hpre] at hrecv; cases hrecv
    | ok mp =>
      cases hdec : decodeState deps st with
      | error e => rw [hpre, topResult_ofError_ok, except_bind_ok, hdec] at hrecv; cases hrecv
      | ok prenegotiatedStatePb =>
        rw [hpre, topResult_ofError_ok, except_bind_ok,
            hdec, topResult_ofError_ok, except_bind_ok] at hrecv
        cases hvn_top : prenegotiatedStatePb.versionNegotiation <;> {
          rw (occs := .pos [1]) [hvn_top] at hrecv
          dsimp only at hrecv
          apply except_ite_error_eq_ok at hrecv
          apply except_ite_error_eq_ok at hrecv
          rcases except_ite_or hrecv with hrecv | hrecv
          · injection hrecv with hr
            injection hr with hst _
            subst hst
            exact spqr_recv_nil_growth st
          · rcases except_ite_or hrecv with hrecv | hrecv
            ·
              cases hcf : chainFrom hkdf prenegotiatedStatePb.chain prenegotiatedStatePb.versionNegotiation with
              | error e => rw [hcf] at hrecv; cases hrecv
              | ok chain0 =>
                rw [hcf, topResult_ofError_ok, except_bind_ok] at hrecv
                cases hrk : chain0.recvKey hkdf 0#64 mp.index with
                | error e => rw [hrk] at hrecv; cases hrecv
                | ok rkPair =>
                  rcases rkPair with ⟨chain1, rawKey⟩
                  rw [hrk] at hrecv
                  change (Except.ok _ = Except.ok _) at hrecv
                  injection hrecv with hr
                  injection hr with hst _
                  subst hst
                  subst hdeps hhkdf
                  exact ⟨spqr_recv_greater_oooBounded F K mac st prenegotiatedStatePb chain0 chain1 rawKey mp.index hb hlen hdec hcf hrk,
                         spqr_recv_greater_length_le F K mac st prenegotiatedStatePb chain0 chain1 rawKey mp.index hb hdec hcf hrk⟩
            ·
              rcases except_ite_or hrecv with hrecv | hrecv
              ·
                rw [except_pure_eq, except_bind_ok] at hrecv
                step_recv_v1_cont
                  [F K mac st prenegotiatedStatePb deps hkdf mp hb hdec hdeps hhkdf hrecv]
                  prenegotiatedStatePb, PrenegotiatedStep.equal
              ·
                apply except_ite_bind_error_eq_ok at hrecv
                cases hvn : prenegotiatedStatePb.versionNegotiation with
                | none => rw [hvn] at hrecv; cases hrecv
                | some vn =>
                  rw [hvn] at hrecv
                  change (Bind.bind (pure vn) _ = _) at hrecv
                  rw [except_pure_eq, except_bind_ok] at hrecv
                  cases hv : Version.fromU8? mp.version with
                  | none => rw [hv] at hrecv; cases hrecv
                  | some v =>
                    rw [hv] at hrecv
                    change (Bind.bind (pure v) _ = _) at hrecv
                    rw [except_pure_eq, except_bind_ok] at hrecv
                    cases hdir : Direction.fromI32? vn.direction with
                    | none => rw [hdir] at hrecv; cases hrecv
                    | some dir =>
                      rw [hdir] at hrecv
                      change (Bind.bind (pure dir) _ = _) at hrecv
                      rw [except_pure_eq, except_bind_ok] at hrecv
                      cases hinit : initInner deps v dir vn.authKey with
                      | error e => rw [hinit] at hrecv; cases hrecv
                      | ok inner' =>
                        rw [hinit] at hrecv
                        change (Bind.bind (Except.ok inner') _ = _) at hrecv
                        rw [except_bind_ok] at hrecv
                        cases hcf_less : chainFrom hkdf prenegotiatedStatePb.chain (some vn) with
                        | error e => rw [hcf_less] at hrecv; cases hrecv
                        | ok chain' =>
                          rw [hcf_less, topResult_ofError_ok, except_bind_ok, except_pure_eq, except_bind_ok] at hrecv
                          step_recv_v1_cont
                            [F K mac st prenegotiatedStatePb deps hkdf mp hb hdec hdeps hhkdf hrecv]
                            ({ inner := inner', versionNegotiation := none, chain := some chain'.intoPb } :
                              PqRatchetStatePB _),
                            (PrenegotiatedStep.less vn v dir inner' chain' hvn hdir hinit hcf_less)
        }

end Symbolic.Swarm.TRREF.GrowthRecvPure
