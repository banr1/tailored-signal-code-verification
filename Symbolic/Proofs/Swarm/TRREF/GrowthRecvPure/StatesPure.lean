/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.TRREF.GrowthRecvB.Defs
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.Helpers3BPure

/-!
# SPQR V1 Receive Growth Bounds: First Six V1 States

Proves `≤ st.length + 2^17` encoded state growth under `statesRecv` for `keysUnsampled`,
`keysSampled`, `headerSent`, `ct1Received`, `ekSentCt1Received`, and `noHeaderReceived`.
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
open GrowthRecvPureB

theorem spqr_recv_keysUnsampled_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendEk.KeysUnsampled (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.keysUnsampled s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.keysUnsampled s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_keysUnsampled_raw_le hrecv
  omega

theorem spqr_recv_keysSampled_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.keysSampled s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.keysSampled s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_keysSampled_raw_le hrecv
  omega

theorem spqr_recv_headerSent_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendEk.HeaderSent spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.headerSent s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.headerSent s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  have hpts := statesFromPb_headerSent_ptsNeeded hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_headerSent_raw_le hpts hrecv
  omega

theorem spqr_recv_ct1Received_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendEk.Ct1Received spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ct1Received s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ct1Received s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_ct1Received_raw_le hrecv
  omega

theorem spqr_recv_ekSentCt1Received_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.ekSentCt1Received s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.ekSentCt1Received s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_ekSentCt1Received_raw_le hrecv
  omega

theorem spqr_recv_noHeaderReceived_length_le
    (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (prenegotiatedStatePb statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (pb : (spqrDepsWithMac F K mac).V1StatePB)
    (s0 : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApiWithMac F mac))
    (sckaMsg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (chain0 chain1 chain2 : Chain)
    (msgKeyEpoch : Epoch) (idx : BitVec 32) (msgKey : Bytes) (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok prenegotiatedStatePb)
    (hpre : PrenegotiatedStep F K mac prenegotiatedStatePb statePb)
    (hinner : statePb.inner = some pb)
    (hfrom : (spqrDepsWithMac F K mac).statesFromPb pb = .ok (.noHeaderReceived s0))
    (hstep : (spqrDepsWithMac F K mac).statesRecv (.noHeaderReceived s0) sckaMsg = .ok (key, st1))
    (hcf : chainFrom (spqrHkdfWith F) statePb.chain statePb.versionNegotiation = .ok chain0)
    (hadd : recvAddEpochOpt (spqrHkdfWith F) chain0 key = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) msgKeyEpoch idx = .ok (chain2, msgKey)) :
    ((spqrDepsWithMac F K mac).encodeState {
      inner := some ((spqrDepsWithMac F K mac).statesIntoPb st1)
      versionNegotiation := none
      chain := some chain2.intoPb
    }).length ≤ st.length + 2^17 := by
  have hpre_w := recv_chain_and_pre_weight_le F K mac st prenegotiatedStatePb statePb pb key
    chain0 chain1 chain2 msgKeyEpoch idx msgKey hb hdec hpre hinner hcf hadd hrk
  have henc := encodeState_v1_chain_length_le F K mac st1 chain2
  have hfrom_w := statesFromPb_raw_le_v1Weight hfrom
  rcases statesRecv_eq_ok _ st1 sckaMsg key hstep with ⟨recvOut, hrecv, rfl⟩
  have hstep_w := recv_noHeaderReceived_raw_le hrecv
  omega

end Symbolic.Swarm.TRREF.GrowthRecvPure
