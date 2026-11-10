/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.TRREF.GrowthRecv.HelpersB
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers3APure
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.BranchesAPure

/-!
# SPQR V1 Receive Growth Bounds: `headerReceived` and `ct1Sampled` States

Proves `≤ st.length + 2^17` encoded state growth for `States.headerReceived` and
`States.ct1Sampled` under `statesRecv`, via the common V1 post-state wrapper
`v1_recv_finish_length_le`.
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
@[scoped simp] theorem spqrAuthApi_into_pb' {F : ShaCompress} (a : Authenticator) :
    (spqrAuthApi F).into_pb a = Authenticator.intoPb a := rfl

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

theorem ucHeaderReceived_from_pb_raw_eq_withMac {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.HeaderReceived}
    {s : Unchunked.SendCt.HeaderReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcHeaderReceived s.into_pb = rawUcHeaderReceived pb := by
  unfold Unchunked.SendCt.HeaderReceived.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.HeaderReceived.into_pb, rawUcHeaderReceived, hauth]

theorem ucCt1Sent_from_pb_raw_eq_withMac {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1Sent}
    {s : Unchunked.SendCt.Ct1Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1Sent s.into_pb = rawUcCt1Sent pb := by
  unfold Unchunked.SendCt.Ct1Sent.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1Sent.into_pb, rawUcCt1Sent, hauth]

theorem ucCt1SentEkReceived_from_pb_raw_eq_withMac {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct1SentEkReceived}
    {s : Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct1SentEkReceived.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt1SentEkReceived s.into_pb = rawUcCt1SentEkReceived pb := by
  unfold Unchunked.SendCt.Ct1SentEkReceived.from_pb at h; split at h <;> [skip; contradiction]
  cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct1SentEkReceived.into_pb, rawUcCt1SentEkReceived, hauth]

theorem ucCt2Sent_from_pb_raw_eq_withMac {F : ShaCompress} {mac : HmacFn} {pb : V1State.Unchunked.Ct2Sent}
    {s : Unchunked.SendCt.Ct2Sent (spqrAuthApiWithMac F mac)}
    (h : Unchunked.SendCt.Ct2Sent.from_pb (spqrAuthApiWithMac F mac) pb = .ok s) :
    rawUcCt2Sent s.into_pb = rawUcCt2Sent pb := by
  unfold Unchunked.SendCt.Ct2Sent.from_pb at h; cases hauth : pb.auth <;> rw [hauth] at h; · contradiction
  have hinj := Except.ok.inj h; subst hinj; simp [Unchunked.SendCt.Ct2Sent.into_pb, rawUcCt2Sent, hauth]

theorem statesRecv_eq_recv_ok {F : ShaCompress} {K : MlKem} {mac : HmacFn}
    {st0 st1 : (spqrDepsWithMac F K mac).States}
    {sckaMsg : (spqrDepsWithMac F K mac).MessageV1} {key : Option EpochSecret}
    (h : (spqrDepsWithMac F K mac).statesRecv st0 sckaMsg = .ok (key, st1)) :
    States.recv K st0 sckaMsg = .ok { state := st1, key := key } := by
  unfold spqrDepsWithMac at h; dsimp only at h
  cases hrec : States.recv K st0 sckaMsg with
  | error e => rw [hrec] at h; cases e <;> contradiction
  | ok r =>
    rw [hrec] at h; dsimp only at h
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, rfl⟩; rfl

theorem encFullW_le_rawPolyEnc (m : PolynomialEncoder) : encFullW m ≤ rawPolyEnc m := by
  have h1 := encodeRepeatedBytes_length_le 2#32 m.pts
  have h2 := encodeRepeatedBytes_length_le 3#32 m.polys
  unfold encFullW rawPolyEnc; omega

theorem decFullW_le_rawPolyDec (m : PolynomialDecoder) : decFullW m ≤ rawPolyDec m :=
  encodeRepeatedBytes_length_le 3#32 m.pts

theorem optWeight_le_optRaw {M : Type} {w r : M → Nat} (h : ∀ x, w x ≤ r x) (o : Option M) :
    optWeight w o ≤ optRaw r o := by
  cases o with
  | none => rfl
  | some x => exact h x

theorem v1FullWeight_le_rawV1State (pb : V1State) : v1FullWeight pb ≤ rawV1State pb := by
  unfold v1FullWeight rawV1State
  cases his : pb.innerState with
  | none => simp [innerStateFullW]
  | some is =>
    dsimp only [innerStateFullW, optRaw_some, rawInnerState]
    cases is with
    | keysUnsampled v => simp [ckKeysUnsampledFullW]
    | keysSampled v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingHdr
      simp only [ckKeysSampledFullW, rawChKeysSampled, optRaw_eq_optWeight] at *; omega
    | headerSent v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingEk
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingCt1
      simp only [ckHeaderSentFullW, rawChHeaderSent, optRaw_eq_optWeight] at *; omega
    | ct1Received v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingEk
      simp only [ckCt1ReceivedFullW, rawChCt1Received, optRaw_eq_optWeight] at *; omega
    | ekSentCt1Received v =>
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingCt2
      simp only [ckEkSentCt1ReceivedFullW, rawChEkSentCt1Received, optRaw_eq_optWeight] at *; omega
    | noHeaderReceived v =>
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingHdr
      simp only [ckNoHeaderReceivedFullW, rawChNoHeaderReceived, optRaw_eq_optWeight] at *; omega
    | headerReceived v =>
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingEk
      simp only [ckHeaderReceivedFullW, rawChHeaderReceived, optRaw_eq_optWeight] at *; omega
    | ct1Sampled v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingCt1
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingEk
      simp only [ckCt1SampledFullW, rawChCt1Sampled, optRaw_eq_optWeight] at *; omega
    | ekReceivedCt1Sampled v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingCt1
      simp only [ckEkReceivedCt1SampledFullW, rawChEkReceivedCt1Sampled, optRaw_eq_optWeight] at *; omega
    | ct1Acknowledged v =>
      have := optWeight_le_optRaw decFullW_le_rawPolyDec v.receivingEk
      simp only [ckCt1AcknowledgedFullW, rawChCt1Acknowledged, optRaw_eq_optWeight] at *; omega
    | ct2Sampled v =>
      have := optWeight_le_optRaw encFullW_le_rawPolyEnc v.sendingCt2
      simp only [ckCt2SampledFullW, rawChCt2Sampled, optRaw_eq_optWeight] at *; omega

theorem v1_recv_finish_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (st0 st1 : (spqrDepsWithMac F K mac).States)
    (key : Option EpochSecret)
    (chain0 chain1 chain2 : Chain) (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st0) ≤ v1FullWeight pb + 704)
    (hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st0) + 1200)
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hd := decodeState_fullWeight_le F K mac st prenegotiatedStatePb hdec
  rcases statePbOooBounded_of_decodeState F K mac st prenegotiatedStatePb hb hdec with ⟨hc_ooo, hvn_ooo⟩
  have hpre_bound :
      optChainWeight statePb.chain + rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st0) ≤ st.length + 1334 ∧
      StatePbOooBounded statePb := by
    cases hpre with
    | equal =>
      rw [hinner] at hd; simp only [optWeight] at hd
      exact ⟨by omega, ⟨hc_ooo, hvn_ooo⟩⟩
    | less vn v dir inner' chain' hvn hdir hinit hcf_less =>
      dsimp only at hinner; subst hinner
      have hvn_ooo' : ∀ v0 ∈ (some vn : Option VersionNegotiationPB), ∀ p ∈ v0.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000 := by
        intro v0 hv0; rw [← hvn] at hv0; exact hvn_ooo v0 hv0
      rcases chainFrom_weight_and_ooo hc_ooo hvn_ooo' hcf_less with ⟨hcf_w, hooo'⟩
      have hinit' : initInner (spqrDeps F K) v dir vn.authKey = .ok (some pb) := hinit
      have hraw_pb := initInner_spqrDeps_raw_le hinit'
      simp only [Option.map, optRaw_some, rawPqInner] at hraw_pb
      have hfw_le := v1FullWeight_le_rawV1State pb
      refine ⟨by dsimp only [optChainWeight, optWeight]; omega, ⟨?_, by intro v0 hv0; cases hv0⟩⟩
      intro ch hch p hp
      simp only [Option.mem_def, Option.some.injEq] at hch; subst hch
      simp only [Chain.intoPb, Option.mem_def, Option.some.injEq] at hp; subst hp
      exact hooo'
  rcases hpre_bound with ⟨hpre_w, hc_ooo1, hvn_ooo1⟩
  rcases chainFrom_weight_and_ooo hc_ooo1 hvn_ooo1 hcf with ⟨hcf_w, hooo0⟩
  rcases recvAddEpochOpt_weight_and_ooo hooo0 hadd with ⟨hadd_w, hooo1⟩
  have hrk_w := chain_recvKey_weight_le hooo1 hrk
  change (PqRatchetState.encodeRaw (pbToPqRatchetState {
    inner := some (States.into_pb (Au := spqrAuthApiWithMac F mac) st1)
    versionNegotiation := none
    chain := some chain2.intoPb
  })).length ≤ st.length + 2^17
  unfold PqRatchetState.encodeRaw pbToPqRatchetState
  simp only [List.length_append, Proto.encodeOptMessage, List.nil_append, Option.map, PqRatchetState.Inner.encode]
  have h2 := chainPB_encodeOptMessage_length_le chain2.intoPb
  have hm := encodeMessage_length_le V1State.encodeRaw 3#32 (States.into_pb (Au := spqrAuthApiWithMac F mac) st1)
  have hv := v1State_encodeRaw_length_le (States.into_pb (Au := spqrAuthApiWithMac F mac) st1)
  dsimp only [Proto.encodeOptMessage] at h2
  omega

end BranchHelpers
open BranchHelpers

theorem spqr_recv_headerReceived_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.headerReceived s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.headerReceived s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.headerReceived s0)) ≤ v1FullWeight pb + 704 := by
    have hf := statesFromPb_eq_ok hfrom
    unfold States.from_pb at hf
    cases his : pb.innerState with
    | none => rw [his] at hf; contradiction
    | some is =>
      rw [his] at hf
      cases is with
      | headerReceived ck =>
        dsimp only [Functor.map, Except.map] at hf; split at hf <;> try contradiction
        rename_i v hv; have hinj := (States.headerReceived.inj (Except.ok.inj hf)).symm; subst hinj
        unfold Chunked.SendCt.HeaderReceived.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv
        cases huc : ck.uc with
        | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
        | some u =>
          rw [huc] at hv
          have hbody : (do
              let uc ← Unchunked.SendCt.HeaderReceived.from_pb (spqrAuthApiWithMac F mac) u
              let receivingEk ← decoderFromPbStateDecode spqrPolyApi ck.receivingEk
              Except.ok { uc := uc, receiving_ek := receivingEk }) = Except.ok s0 := by
            split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
          rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨dec, hdec', hv3⟩
          have hinj2 := Except.ok.inj hv3; subst hinj2
          have h1 := ucHeaderReceived_from_pb_raw_eq_withMac huc'
          have h2 := decoderFromPbStateDecode_raw_le_fullW hdec'
          simp only [v1FullWeight, innerStateFullW, ckHeaderReceivedFullW, his, huc, optWeight] at *
          dsimp only [States.into_pb, Chunked.SendCt.HeaderReceived.into_pb, rawV1State, optRaw_some,
            rawInnerState, rawChHeaderReceived, spqrPolyApi_decoder_into_pb] at *
          rw [h1]; omega
      | _ => dsimp only [Functor.map, Except.map] at hf; split at hf <;> nomatch hf
  have hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.headerReceived s0)) + 1200 := by
    have h := statesRecv_eq_recv_ok hstep
    unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
    have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp
  exact v1_recv_finish_length_le F K mac st prenegotiatedStatePb statePb pb (.headerReceived s0) st1
    key chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom_le hstep_le hcf hadd hrk

theorem spqr_recv_ct1Sampled_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ct1Sampled s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ct1Sampled s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hfrom_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct1Sampled s0)) ≤ v1FullWeight pb + 704 := by
    have hf := statesFromPb_eq_ok hfrom
    unfold States.from_pb at hf
    cases his : pb.innerState with
    | none => rw [his] at hf; contradiction
    | some is =>
      rw [his] at hf
      cases is with
      | ct1Sampled ck =>
        dsimp only [Functor.map, Except.map] at hf; split at hf <;> try contradiction
        rename_i v hv; have hinj := (States.ct1Sampled.inj (Except.ok.inj hf)).symm; subst hinj
        unfold Chunked.SendCt.Ct1Sampled.from_pb at hv; dsimp only [Bind.bind, Except.bind] at hv
        cases huc : ck.uc with
        | none => rw [huc] at hv; split at hv <;> [split at hv <;> contradiction; contradiction]
        | some u =>
          rw [huc] at hv
          have hbody : (do
              let uc ← Unchunked.SendCt.Ct1Sent.from_pb (spqrAuthApiWithMac F mac) u
              let sendingCt1 ← encoderFromPbStateDecode spqrPolyApi ck.sendingCt1
              let receivingEk ← decoderFromPbStateDecode spqrPolyApi ck.receivingEk
              Except.ok { uc := uc, sending_ct1 := sendingCt1, receiving_ek := receivingEk }) =
                Except.ok s0 := by
            split at hv <;> [split at hv <;> [contradiction; exact hv]; exact hv]
          rcases except_bind_eq_ok hbody with ⟨uc, huc', hv2⟩; rcases except_bind_eq_ok hv2 with ⟨enc, henc, hv3⟩
          rcases except_bind_eq_ok hv3 with ⟨dec, hdec', hv4⟩; have hinj2 := Except.ok.inj hv4; subst hinj2
          have h1 := ucCt1Sent_from_pb_raw_eq_withMac huc'
          have h2 := encoderFromPbStateDecode_raw_le_fullW henc
          have h3 := decoderFromPbStateDecode_raw_le_fullW hdec'
          simp only [v1FullWeight, innerStateFullW, ckCt1SampledFullW, his, huc, optWeight] at *
          dsimp only [States.into_pb, Chunked.SendCt.Ct1Sampled.into_pb, rawV1State, optRaw_some,
            rawInnerState, rawChCt1Sampled, spqrPolyApi_encoder_into_pb, spqrPolyApi_decoder_into_pb] at *
          rw [h1]; omega
      | _ => dsimp only [Functor.map, Except.map] at hf; split at hf <;> nomatch hf
  have hstep_le : rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) st1) ≤
      rawV1State (States.into_pb (Au := spqrAuthApiWithMac F mac) (.ct1Sampled s0)) + 1200 := by
    have h := statesRecv_eq_recv_ok hstep
    unfold States.recv at h; dsimp only [] at h; split at h <;> [contradiction; skip]
    split at h; · (have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp)
    split at h; · (have hinj := congrArg V1Recv.state (Except.ok.inj h); subst hinj; simp)
    rcases except_bind_eq_ok h with ⟨res, h1, h2⟩
    unfold Chunked.SendCt.Ct1Sampled.recv_ek_chunk at h1; dsimp only [] at h1
    rcases except_bind_eq_ok h1 with ⟨receivingEk, hadd_c, h1b⟩; rcases except_bind_eq_ok h1b with ⟨decoded?, _, h1c⟩
    have hadd_le := PolyDecoder.addChunk_raw_le (poly_addChunk_ofPanic_eq_ok hadd_c); cases decoded? with
    | none =>
      dsimp only [] at h1c; split at h1c <;>
        (have hres := Except.ok.inj h1c; subst hres; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj; simp; omega)
    | some decoded =>
      dsimp only [] at h1c; rcases except_bind_eq_ok h1c with ⟨uc, huc, h1d⟩
      unfold Unchunked.SendCt.Ct1Sent.recv_ek at huc; split at huc <;> [contradiction; skip]
      split at huc <;> [skip; contradiction]; rename_i hek_match; have huc_eq := Except.ok.inj huc; subst huc_eq
      have hek_len := ek_matches_header_length hek_match; split at h1d
      · rcases except_bind_eq_ok h1d with ⟨⟨uc2, ct2, macB⟩, hct2, h1e⟩
        rcases except_bind_eq_ok h1e with ⟨sendingCt2, henc2, h1f⟩; rw [statesResult_ofPanic_eq_ok] at hct2 henc2
        have hres := Except.ok.inj h1f; subst hres; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj
        rcases send_ct2_encode_raw_le hct2 henc2 with ⟨rfl, henc2_le⟩
        simp; omega
      · have hres := Except.ok.inj h1d; subst hres; have hinj := congrArg V1Recv.state (Except.ok.inj h2); subst hinj
        simp [hek_len]; omega
  exact v1_recv_finish_length_le F K mac st prenegotiatedStatePb statePb pb (.ct1Sampled s0) st1
    key chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hfrom_le hstep_le hcf hadd hrk

end Symbolic.Swarm.TRREF.GrowthRecvPure
