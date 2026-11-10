/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.CREF.Initiate.InitRej
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SpecLemmas.Model.PQXDH.StateMachine
import all Init.Data.String.Defs
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.SHARED.SpqrX.Prost.MessageMerge.AppendX

/-!
# SPQR State-Size Bounds and Root-Chain Gamma Lemmas

Upper bounds on encoded protobuf byte lengths for SPQR v1 state messages
(`encodeState_length_le_rawPqState`), together with Alice session constructors and `gamma`
correspondence for `rootCreateChain` (`rootCreateChain_eq_gamma_createChain_aliceLit`).
Checked by Lean.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Top.StateSize.SymP3

open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

theorem encodeVarintAux_length_le (fuel : Nat) (v : BitVec 64) :
    (Proto.encodeVarintAux fuel v).length ≤ fuel + 1 := by
  induction fuel generalizing v with
  | zero => simp [Proto.encodeVarintAux]
  | succ fuel ih =>
    simp only [Proto.encodeVarintAux]
    split
    · simp
    · simp only [List.length_cons]; have h := ih (v >>> 7); omega
theorem encodeVarint_length_le (v : BitVec 64) : (Proto.encodeVarint v).length ≤ 11 :=
  encodeVarintAux_length_le 10 v
theorem encodeKey_length_le (tag : BitVec 32) (wt : Proto.WireType) :
    (Proto.encodeKey tag wt).length ≤ 11 :=
  encodeVarint_length_le _
theorem encodeUint32Field_length_le (tag : BitVec 32) (v : BitVec 32) :
    (Proto.encodeUint32Field tag v).length ≤ 22 := by
  unfold Proto.encodeUint32Field
  split
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.zeroExtend 64)
    omega
theorem encodeUint64Field_length_le (tag : BitVec 32) (v : BitVec 64) :
    (Proto.encodeUint64Field tag v).length ≤ 22 := by
  unfold Proto.encodeUint64Field
  split
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le v
    omega
theorem encodeInt32Field_length_le (tag : BitVec 32) (v : BitVec 32) :
    (Proto.encodeInt32Field tag v).length ≤ 22 := by
  unfold Proto.encodeInt32Field
  split
  · simp
  · rw [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.signExtend 64)
    omega
theorem encodeBoolField_length_le (tag : BitVec 32) (v : Bool) :
    (Proto.encodeBoolField tag v).length ≤ 12 := by
  unfold Proto.encodeBoolField
  split
  · rw [List.length_append]; have h1 := encodeKey_length_le tag .varint; simp; omega
  · simp
theorem encodeBytesUncond_length_le (tag : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesUncond tag v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesUncond
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 v.length)
  omega
theorem encodeBytesField_length_le (tag : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesField tag v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesField
  split
  · simp
  · exact encodeBytesUncond_length_le tag v
theorem encodeRepeatedBytes_length_le (tag : BitVec 32) (vs : List Bytes) :
    (Proto.encodeRepeatedBytes tag vs).length ≤
      (vs.map (fun v => v.length + 22)).sum := by
  induction vs with
  | nil => simp [Proto.encodeRepeatedBytes]
  | cons v rest ih =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_cons, List.length_append, List.map_cons,
      List.sum_cons]
    have h1 := encodeBytesUncond_length_le tag v
    have h2 : (List.foldr (fun v acc => Proto.encodeBytesUncond tag v ++ acc) [] rest).length ≤
        (rest.map (fun v => v.length + 22)).sum := ih
    omega
theorem encodeMessage_length_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (Proto.encodeMessage encodeRaw tag m).length ≤ (encodeRaw m).length + 22 := by
  unfold Proto.encodeMessage
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 (encodeRaw m).length)
  omega
def optRaw {α : Type} (f : α → Nat) : Option α → Nat
  | none => 0
  | some x => f x
@[simp] theorem optRaw_none {α : Type} (f : α → Nat) : optRaw f none = 0 := rfl
@[simp] theorem optRaw_some {α : Type} (f : α → Nat) (x : α) : optRaw f (some x) = f x := rfl
theorem encodeOptMessage_length_le {M : Type} (encodeRaw : M → Bytes) (f : M → Nat) (C : Nat)
    (hle : ∀ m, (encodeRaw m).length ≤ f m + C) (tag : BitVec 32) (opt : Option M) :
    (Proto.encodeOptMessage encodeRaw tag opt).length ≤ optRaw f opt + (C + 22) := by
  cases opt with
  | none => simp [Proto.encodeOptMessage]
  | some m =>
    simp only [Proto.encodeOptMessage, optRaw_some]
    have h1 := encodeMessage_length_le encodeRaw tag m
    have h2 := hle m
    omega
theorem encodeRepeatedMessage_length_le {M : Type} (encodeRaw : M → Bytes) (f : M → Nat) (C : Nat)
    (hle : ∀ m, (encodeRaw m).length + 22 ≤ f m + C) (tag : BitVec 32) (ms : List M) :
    (Proto.encodeRepeatedMessage encodeRaw tag ms).length ≤
      (ms.map (fun m => f m + C)).sum := by
  induction ms with
  | nil => simp [Proto.encodeRepeatedMessage]
  | cons m rest ih =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_cons, List.length_append, List.map_cons,
      List.sum_cons]
    have h1 := encodeMessage_length_le encodeRaw tag m
    have h2 := hle m
    have h3 : (List.foldr (fun m acc => Proto.encodeMessage encodeRaw tag m ++ acc) [] rest).length ≤
        (rest.map (fun m => f m + C)).sum := ih
    omega
def rawEpochDir (ed : EpochDirectionPB) : Nat := ed.next.length + ed.prev.length
def rawChainEpoch (ep : ChainEpochPB) : Nat := optRaw rawEpochDir ep.send + optRaw rawEpochDir ep.recv
def rawChain (ch : ChainPB) : Nat :=
  (ch.links.map (fun ep => rawChainEpoch ep + 200)).sum + ch.nextRoot.length
def rawAuth (a : ProtoAuthenticator) : Nat := a.rootKey.length + a.macKey.length
def rawPolyEnc (pe : PolynomialEncoder) : Nat :=
  (pe.pts.map (fun b => b.length + 22)).sum + (pe.polys.map (fun b => b.length + 22)).sum
def rawPolyDec (pd : PolynomialDecoder) : Nat := (pd.pts.map (fun b => b.length + 22)).sum
def rawUcKeysUnsampled (m : V1State.Unchunked.KeysUnsampled) : Nat := optRaw rawAuth m.auth
def rawUcHeaderSent (m : V1State.Unchunked.HeaderSent) : Nat :=
  optRaw rawAuth m.auth + m.ek.length + m.dk.length
def rawUcEkSent (m : V1State.Unchunked.EkSent) : Nat := optRaw rawAuth m.auth + m.dk.length
def rawUcEkSentCt1Received (m : V1State.Unchunked.EkSentCt1Received) : Nat :=
  optRaw rawAuth m.auth + m.dk.length + m.ct1.length
def rawUcNoHeaderReceived (m : V1State.Unchunked.NoHeaderReceived) : Nat := optRaw rawAuth m.auth
def rawUcHeaderReceived (m : V1State.Unchunked.HeaderReceived) : Nat :=
  optRaw rawAuth m.auth + m.hdr.length
def rawUcCt1Sent (m : V1State.Unchunked.Ct1Sent) : Nat :=
  optRaw rawAuth m.auth + m.hdr.length + m.es.length + m.ct1.length
def rawUcCt1SentEkReceived (m : V1State.Unchunked.Ct1SentEkReceived) : Nat :=
  optRaw rawAuth m.auth + m.es.length + m.ek.length + m.ct1.length
def rawUcCt2Sent (m : V1State.Unchunked.Ct2Sent) : Nat := optRaw rawAuth m.auth
def rawChKeysUnsampled (m : V1State.Chunked.KeysUnsampled) : Nat := optRaw rawUcKeysUnsampled m.uc
def rawChKeysSampled (m : V1State.Chunked.KeysSampled) : Nat :=
  optRaw rawUcHeaderSent m.uc + optRaw rawPolyEnc m.sendingHdr
def rawChHeaderSent (m : V1State.Chunked.HeaderSent) : Nat :=
  optRaw rawUcEkSent m.uc + optRaw rawPolyEnc m.sendingEk + optRaw rawPolyDec m.receivingCt1
def rawChCt1Received (m : V1State.Chunked.Ct1Received) : Nat :=
  optRaw rawUcEkSentCt1Received m.uc + optRaw rawPolyEnc m.sendingEk
def rawChEkSentCt1Received (m : V1State.Chunked.EkSentCt1Received) : Nat :=
  optRaw rawUcEkSentCt1Received m.uc + optRaw rawPolyDec m.receivingCt2
def rawChNoHeaderReceived (m : V1State.Chunked.NoHeaderReceived) : Nat :=
  optRaw rawUcNoHeaderReceived m.uc + optRaw rawPolyDec m.receivingHdr
def rawChHeaderReceived (m : V1State.Chunked.HeaderReceived) : Nat :=
  optRaw rawUcHeaderReceived m.uc + optRaw rawPolyDec m.receivingEk
def rawChCt1Sampled (m : V1State.Chunked.Ct1Sampled) : Nat :=
  optRaw rawUcCt1Sent m.uc + optRaw rawPolyEnc m.sendingCt1 + optRaw rawPolyDec m.receivingEk
def rawChEkReceivedCt1Sampled (m : V1State.Chunked.EkReceivedCt1Sampled) : Nat :=
  optRaw rawUcCt1SentEkReceived m.uc + optRaw rawPolyEnc m.sendingCt1
def rawChCt1Acknowledged (m : V1State.Chunked.Ct1Acknowledged) : Nat :=
  optRaw rawUcCt1Sent m.uc + optRaw rawPolyDec m.receivingEk
def rawChCt2Sampled (m : V1State.Chunked.Ct2Sampled) : Nat :=
  optRaw rawUcCt2Sent m.uc + optRaw rawPolyEnc m.sendingCt2
def rawInnerState : V1State.InnerState → Nat
  | .keysUnsampled v        => rawChKeysUnsampled v
  | .keysSampled v          => rawChKeysSampled v
  | .headerSent v           => rawChHeaderSent v
  | .ct1Received v          => rawChCt1Received v
  | .ekSentCt1Received v    => rawChEkSentCt1Received v
  | .noHeaderReceived v     => rawChNoHeaderReceived v
  | .headerReceived v       => rawChHeaderReceived v
  | .ct1Sampled v           => rawChCt1Sampled v
  | .ekReceivedCt1Sampled v => rawChEkReceivedCt1Sampled v
  | .ct1Acknowledged v      => rawChCt1Acknowledged v
  | .ct2Sampled v           => rawChCt2Sampled v
def rawV1State (m : V1State) : Nat := optRaw rawInnerState m.innerState
def rawPqInner : PqRatchetState.Inner → Nat | .v1 v => rawV1State v
def rawVN (m : VersionNegotiationPB) : Nat := m.authKey.length
def rawPqState (m : PqRatchetState) : Nat :=
  optRaw rawVN m.versionNegotiation + optRaw rawChain m.chain + optRaw rawPqInner m.inner
theorem chainParamsPB_encodeRaw_length_le (m : ChainParamsPB) :
    (ChainParamsPB.encodeRaw m).length ≤ 44 := by
  unfold ChainParamsPB.encodeRaw; rw [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.maxJump
  have h2 := encodeUint32Field_length_le 2#32 m.maxOooKeys; omega
theorem encodeOptChainParams_length_le (tag : BitVec 32) (opt : Option ChainParamsPB) :
    (Proto.encodeOptMessage ChainParamsPB.encodeRaw tag opt).length ≤ 66 := by
  cases opt with
  | none => simp [Proto.encodeOptMessage]
  | some m =>
    simp only [Proto.encodeOptMessage]
    have h1 := encodeMessage_length_le ChainParamsPB.encodeRaw tag m
    have h2 := chainParamsPB_encodeRaw_length_le m; omega
theorem epochDirectionPB_encodeRaw_length_le (m : EpochDirectionPB) :
    (EpochDirectionPB.encodeRaw m).length ≤ rawEpochDir m + 66 := by
  unfold EpochDirectionPB.encodeRaw rawEpochDir; simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.ctr
  have h2 := encodeBytesField_length_le 2#32 m.next
  have h3 := encodeBytesField_length_le 3#32 m.prev; omega
theorem chainEpochPB_encodeRaw_length_le (m : ChainEpochPB) :
    (ChainEpochPB.encodeRaw m).length ≤ rawChainEpoch m + 176 := by
  unfold ChainEpochPB.encodeRaw rawChainEpoch; rw [List.length_append]
  have h1 := encodeOptMessage_length_le EpochDirectionPB.encodeRaw rawEpochDir 66
    epochDirectionPB_encodeRaw_length_le 1#32 m.send
  have h2 := encodeOptMessage_length_le EpochDirectionPB.encodeRaw rawEpochDir 66
    epochDirectionPB_encodeRaw_length_le 2#32 m.recv; omega
theorem chainPB_encodeRaw_length_le (m : ChainPB) :
    (ChainPB.encodeRaw m).length ≤ rawChain m + 154 := by
  unfold ChainPB.encodeRaw rawChain; simp only [List.length_append]
  have h1 := encodeInt32Field_length_le 1#32 m.direction
  have h2 := encodeUint64Field_length_le 2#32 m.currentEpoch
  have h3 := encodeRepeatedMessage_length_le ChainEpochPB.encodeRaw rawChainEpoch 200
    (fun ep => by have := chainEpochPB_encodeRaw_length_le ep; omega) 3#32 m.links
  have h4 := encodeBytesField_length_le 4#32 m.nextRoot
  have h5 := encodeUint64Field_length_le 5#32 m.sendEpoch
  have h6 := encodeOptChainParams_length_le 6#32 m.params; omega
theorem versionNegotiationPB_encodeRaw_length_le (m : VersionNegotiationPB) :
    (VersionNegotiationPB.encodeRaw m).length ≤ rawVN m + 132 := by
  unfold VersionNegotiationPB.encodeRaw rawVN; simp only [List.length_append]
  have h1 := encodeBytesField_length_le 1#32 m.authKey
  have h2 := encodeInt32Field_length_le 2#32 m.direction
  have h3 := encodeInt32Field_length_le 3#32 m.minVersion
  have h4 := encodeOptChainParams_length_le 4#32 m.chainParams; omega
theorem protoAuthenticator_encodeRaw_length_le (m : ProtoAuthenticator) :
    (ProtoAuthenticator.encodeRaw m).length ≤ rawAuth m + 44 := by
  unfold ProtoAuthenticator.encodeRaw rawAuth; rw [List.length_append]
  have h1 := encodeBytesField_length_le 1#32 m.rootKey
  have h2 := encodeBytesField_length_le 2#32 m.macKey; omega
theorem polynomialEncoder_encodeRaw_length_le (m : PolynomialEncoder) :
    (PolynomialEncoder.encodeRaw m).length ≤ rawPolyEnc m + 22 := by
  unfold PolynomialEncoder.encodeRaw rawPolyEnc; simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.idx
  have h2 := encodeRepeatedBytes_length_le 2#32 m.pts
  have h3 := encodeRepeatedBytes_length_le 3#32 m.polys; omega
theorem polynomialDecoder_encodeRaw_length_le (m : PolynomialDecoder) :
    (PolynomialDecoder.encodeRaw m).length ≤ rawPolyDec m + 56 := by
  unfold PolynomialDecoder.encodeRaw rawPolyDec; simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.ptsNeeded
  have h2 := encodeUint32Field_length_le 2#32 m.polys
  have h3 := encodeRepeatedBytes_length_le 3#32 m.pts
  have h4 := encodeBoolField_length_le 4#32 m.isComplete; omega
theorem ucKeysUnsampled_encodeRaw_length_le (m : V1State.Unchunked.KeysUnsampled) :
    (V1State.Unchunked.KeysUnsampled.encodeRaw m).length ≤ rawUcKeysUnsampled m + 88 := by
  unfold V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega
theorem ucHeaderSent_encodeRaw_length_le (m : V1State.Unchunked.HeaderSent) :
    (V1State.Unchunked.HeaderSent.encodeRaw m).length ≤ rawUcHeaderSent m + 132 := by
  unfold V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.ek
  have h4 := encodeBytesField_length_le 4#32 m.dk; omega
theorem ucEkSent_encodeRaw_length_le (m : V1State.Unchunked.EkSent) :
    (V1State.Unchunked.EkSent.encodeRaw m).length ≤ rawUcEkSent m + 110 := by
  unfold V1State.Unchunked.EkSent.encodeRaw rawUcEkSent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.dk; omega
theorem ucEkSentCt1Received_encodeRaw_length_le (m : V1State.Unchunked.EkSentCt1Received) :
    (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length ≤ rawUcEkSentCt1Received m + 132 := by
  unfold V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received
  simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.dk
  have h4 := encodeBytesField_length_le 4#32 m.ct1; omega
theorem ucNoHeaderReceived_encodeRaw_length_le (m : V1State.Unchunked.NoHeaderReceived) :
    (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length ≤ rawUcNoHeaderReceived m + 88 := by
  unfold V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega
theorem ucHeaderReceived_encodeRaw_length_le (m : V1State.Unchunked.HeaderReceived) :
    (V1State.Unchunked.HeaderReceived.encodeRaw m).length ≤ rawUcHeaderReceived m + 110 := by
  unfold V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.hdr; omega
theorem ucCt1Sent_encodeRaw_length_le (m : V1State.Unchunked.Ct1Sent) :
    (V1State.Unchunked.Ct1Sent.encodeRaw m).length ≤ rawUcCt1Sent m + 154 := by
  unfold V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.hdr
  have h4 := encodeBytesField_length_le 4#32 m.es
  have h5 := encodeBytesField_length_le 5#32 m.ct1; omega
theorem ucCt1SentEkReceived_encodeRaw_length_le (m : V1State.Unchunked.Ct1SentEkReceived) :
    (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length ≤ rawUcCt1SentEkReceived m + 154 := by
  unfold V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived
  simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.es
  have h4 := encodeBytesField_length_le 4#32 m.ek
  have h5 := encodeBytesField_length_le 5#32 m.ct1; omega
theorem ucCt2Sent_encodeRaw_length_le (m : V1State.Unchunked.Ct2Sent) :
    (V1State.Unchunked.Ct2Sent.encodeRaw m).length ≤ rawUcCt2Sent m + 88 := by
  unfold V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega
theorem chKeysUnsampled_encodeRaw_length_le (v : V1State.Chunked.KeysUnsampled) :
    (V1State.Chunked.KeysUnsampled.encodeRaw v).length ≤ rawChKeysUnsampled v + 110 :=
  encodeOptMessage_length_le _ rawUcKeysUnsampled 88 ucKeysUnsampled_encodeRaw_length_le 1#32 v.uc
theorem chKeysSampled_encodeRaw_length_le (v : V1State.Chunked.KeysSampled) :
    (V1State.Chunked.KeysSampled.encodeRaw v).length ≤ rawChKeysSampled v + 198 := by
  unfold V1State.Chunked.KeysSampled.encodeRaw rawChKeysSampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcHeaderSent 132 ucHeaderSent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingHdr
  omega
theorem chHeaderSent_encodeRaw_length_le (v : V1State.Chunked.HeaderSent) :
    (V1State.Chunked.HeaderSent.encodeRaw v).length ≤ rawChHeaderSent v + 254 := by
  unfold V1State.Chunked.HeaderSent.encodeRaw rawChHeaderSent; simp only [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSent 110 ucEkSent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingEk
  have h3 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingCt1; omega
theorem chCt1Received_encodeRaw_length_le (v : V1State.Chunked.Ct1Received) :
    (V1State.Chunked.Ct1Received.encodeRaw v).length ≤ rawChCt1Received v + 198 := by
  unfold V1State.Chunked.Ct1Received.encodeRaw rawChCt1Received; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingEk; omega
theorem chEkSentCt1Received_encodeRaw_length_le (v : V1State.Chunked.EkSentCt1Received) :
    (V1State.Chunked.EkSentCt1Received.encodeRaw v).length ≤ rawChEkSentCt1Received v + 232 := by
  unfold V1State.Chunked.EkSentCt1Received.encodeRaw rawChEkSentCt1Received; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingCt2; omega
theorem chNoHeaderReceived_encodeRaw_length_le (v : V1State.Chunked.NoHeaderReceived) :
    (V1State.Chunked.NoHeaderReceived.encodeRaw v).length ≤ rawChNoHeaderReceived v + 188 := by
  unfold V1State.Chunked.NoHeaderReceived.encodeRaw rawChNoHeaderReceived; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcNoHeaderReceived 88 ucNoHeaderReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingHdr; omega
theorem chHeaderReceived_encodeRaw_length_le (v : V1State.Chunked.HeaderReceived) :
    (V1State.Chunked.HeaderReceived.encodeRaw v).length ≤ rawChHeaderReceived v + 210 := by
  unfold V1State.Chunked.HeaderReceived.encodeRaw rawChHeaderReceived; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcHeaderReceived 110 ucHeaderReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingEk; omega
theorem chCt1Sampled_encodeRaw_length_le (v : V1State.Chunked.Ct1Sampled) :
    (V1State.Chunked.Ct1Sampled.encodeRaw v).length ≤ rawChCt1Sampled v + 298 := by
  unfold V1State.Chunked.Ct1Sampled.encodeRaw rawChCt1Sampled; simp only [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt1
  have h3 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingEk; omega
theorem chEkReceivedCt1Sampled_encodeRaw_length_le (v : V1State.Chunked.EkReceivedCt1Sampled) :
    (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw v).length ≤ rawChEkReceivedCt1Sampled v + 220 := by
  unfold V1State.Chunked.EkReceivedCt1Sampled.encodeRaw rawChEkReceivedCt1Sampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1SentEkReceived 154 ucCt1SentEkReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt1; omega
theorem chCt1Acknowledged_encodeRaw_length_le (v : V1State.Chunked.Ct1Acknowledged) :
    (V1State.Chunked.Ct1Acknowledged.encodeRaw v).length ≤ rawChCt1Acknowledged v + 254 := by
  unfold V1State.Chunked.Ct1Acknowledged.encodeRaw rawChCt1Acknowledged; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingEk; omega
theorem chCt2Sampled_encodeRaw_length_le (v : V1State.Chunked.Ct2Sampled) :
    (V1State.Chunked.Ct2Sampled.encodeRaw v).length ≤ rawChCt2Sampled v + 154 := by
  unfold V1State.Chunked.Ct2Sampled.encodeRaw rawChCt2Sampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt2Sent 88 ucCt2Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt2; omega
theorem innerState_encode_length_le (is : V1State.InnerState) :
    (V1State.InnerState.encode is).length ≤ rawInnerState is + 400 := by
  cases is with
  | keysUnsampled v =>
    have h0 := encodeMessage_length_le V1State.Chunked.KeysUnsampled.encodeRaw 1#32 v
    have h1 := chKeysUnsampled_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | keysSampled v =>
    have h0 := encodeMessage_length_le V1State.Chunked.KeysSampled.encodeRaw 2#32 v
    have h1 := chKeysSampled_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | headerSent v =>
    have h0 := encodeMessage_length_le V1State.Chunked.HeaderSent.encodeRaw 3#32 v
    have h1 := chHeaderSent_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ct1Received v =>
    have h0 := encodeMessage_length_le V1State.Chunked.Ct1Received.encodeRaw 4#32 v
    have h1 := chCt1Received_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ekSentCt1Received v =>
    have h0 := encodeMessage_length_le V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 v
    have h1 := chEkSentCt1Received_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | noHeaderReceived v =>
    have h0 := encodeMessage_length_le V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 v
    have h1 := chNoHeaderReceived_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | headerReceived v =>
    have h0 := encodeMessage_length_le V1State.Chunked.HeaderReceived.encodeRaw 7#32 v
    have h1 := chHeaderReceived_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ct1Sampled v =>
    have h0 := encodeMessage_length_le V1State.Chunked.Ct1Sampled.encodeRaw 8#32 v
    have h1 := chCt1Sampled_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ekReceivedCt1Sampled v =>
    have h0 := encodeMessage_length_le V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 v
    have h1 := chEkReceivedCt1Sampled_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ct1Acknowledged v =>
    have h0 := encodeMessage_length_le V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 v
    have h1 := chCt1Acknowledged_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
  | ct2Sampled v =>
    have h0 := encodeMessage_length_le V1State.Chunked.Ct2Sampled.encodeRaw 11#32 v
    have h1 := chCt2Sampled_encodeRaw_length_le v; dsimp only [V1State.InnerState.encode, rawInnerState]; omega
theorem v1State_encodeRaw_length_le (m : V1State) :
    (V1State.encodeRaw m).length ≤ rawV1State m + 400 := by
  unfold V1State.encodeRaw rawV1State
  cases m.innerState with
  | none => simp
  | some is => simp only [optRaw_some]; exact innerState_encode_length_le is
theorem pqInner_encode_length_le (i : PqRatchetState.Inner) :
    (PqRatchetState.Inner.encode i).length ≤ rawPqInner i + 422 := by
  cases i with
  | v1 v =>
    have h1 := encodeMessage_length_le V1State.encodeRaw 3#32 v
    have h2 := v1State_encodeRaw_length_le v; dsimp only [PqRatchetState.Inner.encode, rawPqInner]; omega
theorem encodeState_length_le_rawPqState (m : PqRatchetState) :
    (Proto.encodeState m).length ≤ rawPqState m + 752 := by
  show (PqRatchetState.encodeRaw m).length ≤ rawPqState m + 752
  unfold PqRatchetState.encodeRaw rawPqState; simp only [List.length_append]
  have h1 := encodeOptMessage_length_le VersionNegotiationPB.encodeRaw rawVN 132
    versionNegotiationPB_encodeRaw_length_le 1#32 m.versionNegotiation
  have h2 := encodeOptMessage_length_le ChainPB.encodeRaw rawChain 154
    chainPB_encodeRaw_length_le 2#32 m.chain
  cases minner : m.inner with
  | none => simp only [optRaw_none, List.length_nil]; omega
  | some i => simp only [optRaw_some]; have h3 := pqInner_encode_length_le i; omega

end CryptoVerification.SpqrV1.Top.StateSize.SymP3

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF

cref_open

open DY
open DY.Libsignal.PQXDH (
  HandshakeKeys
  aliceAgreement agree hkdfBlock1
  createChain
)
open DY.Libsignal.Refinement (
  ExternCryptoLawsHold sha256CompressFunction
)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

def aliceInitiatedStateV1 (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : CryptoGames.LibsignalSession.KeyPair) (ck1 : ChainKey)
    (pqBytes : List (BitVec 8)) : SessionState (List (BitVec 8)) :=
  { sessionVersion := 4#32
    localIdentity := ourIdentity
    remoteIdentity := some theirIdentity
    rootKey := rk1
    previousCounter := 0#32
    senderChain := some ⟨sendingKeyPair, ck1⟩
    receiverChains := [⟨theirRatchetKey, some ⟨ck0, 0#32⟩, []⟩]
    pendingPreKey := true
    pqRatchetState := pqBytes }

def aliceInitiatedSessionV1 (ourIdentity theirIdentity : IdentityKey)
    (theirRatchetKey baseKey : PublicKey) (rk1 : RootKey) (ck0 : BitVec 256)
    (sendingKeyPair : CryptoGames.LibsignalSession.KeyPair) (ck1 : ChainKey) (opkId? : Option (BitVec 32))
    (spkId kyberPreKeyId remoteRegId localRegId : BitVec 32)
    (kemCtSer pqBytes : List (BitVec 8)) : Session (List (BitVec 8)) :=
  { state :=
      aliceInitiatedStateV1 ourIdentity theirIdentity theirRatchetKey rk1 ck0 sendingKeyPair ck1 pqBytes
    pendingPreKey := some
      { preKeyId := opkId?
        signedPreKeyId := spkId
        baseKey := baseKey
        timestamp := 0#64 }
    pendingKyberPreKey := some
      { preKeyId := kyberPreKeyId
        ciphertext := kemCtSer }
    localRegistrationId := localRegId
    remoteRegistrationId := remoteRegId
    aliceBaseKey := baseKey.serialize }

abbrev hwLit (bs : HwBytes) : DY.Bytes := compHwLit bs

@[simp] theorem gamma_hwLit (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (bs : HwBytes) :
    gamma i S g (hwLit bs) = bs :=
  gamma_compHwLit i S g bs

def aliceLitAgreement (r : ProtocolSetup) (bundle : HwBytes) (ds : List HwBytes) :
    DY.Bytes × HandshakeKeys :=
  aliceAgreement
    (hwLit (secretBytes r 0))
    (hwLit (ds.getD 0 []))
    (DY.DiffieHellman.dhPk (hwLit (secretBytes r 1)))
    (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
    (hwLit (r.opaqueBytes (setupPublic r 6)))
    (if bundle[4]? = some 1#8 then some (hwLit (slice bundle 10 32)) else none)
    (hwLit (entropyBytes ds))

abbrev createChainRootBytes (interpretation : ExternInterpretation)
    (rk theirPk ourSk : HwBytes) : HwBytes :=
  let F := sha256CompressFunction interpretation
  TR.hkdfBlock1Bytes F
    (ByteSpecs.hmacWith F rk (TR.dhAgreeBytes interpretation ourSk theirPk))
    TR.whisperRatchetBytes

theorem gamma_createChain_fst (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (rk theirPk ourSk : DY.Bytes) :
    gamma interpretation S g (createChain rk theirPk ourSk).1 =
      createChainRootBytes interpretation
        (gamma interpretation S g rk)
        (gamma interpretation S g theirPk)
        (gamma interpretation S g ourSk) := by
  have hcc : (createChain rk theirPk ourSk).1 =
      hkdfBlock1 (DY.Libsignal.PQXDH.hmac rk (agree theirPk ourSk))
        (DY.Libsignal.PQXDH.lit "WhisperRatchet") := rfl
  rw [hcc, TR.gamma_hkdfBlock1, TR.gamma_hmac,
      TR.gamma_agree interpretation hEq, TR.gamma_whisperRatchet]
  rfl

theorem gamma_pqxdh_createChain_snd (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (rk theirPk ourSk : DY.Bytes) :
    gamma interpretation S g (createChain rk theirPk ourSk).2 =
      TR.createChainKeyBytes interpretation
        (gamma interpretation S g rk)
        (gamma interpretation S g theirPk)
        (gamma interpretation S g ourSk) :=
  TR.gamma_createChain_snd interpretation hEq S g rk theirPk ourSk

section RootCreateChainBridge

open CryptoVerification
open Proofs.libsignal.Hooks2 (cryptoOf' vec32_toList_of_length_32')

private theorem clampByte_idem_ph (b : BitVec 8) :
    (b &&& 248#8) &&& 248#8 = b &&& 248#8 := by
  revert b; decide

private theorem clampByte_hi_idem_ph (b : BitVec 8) :
    (((b &&& 127#8) ||| 64#8) &&& 127#8) ||| 64#8 = (b &&& 127#8) ||| 64#8 := by
  revert b; decide

private theorem clampByte_idem_at_ph (i : Nat) (b : BitVec 8) :
    clampByte i (clampByte i b) = clampByte i b := by
  unfold clampByte
  split_ifs
  · exact clampByte_idem_ph b
  · exact clampByte_hi_idem_ph b
  · rfl

theorem clamp_clamp (bs : HwBytes) : clamp (clamp bs) = clamp bs := by
  unfold clamp
  by_cases hlen : bs.length = 32
  · simp only [hlen, ↓reduceIte, List.length_mapIdx]
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.getElem_mapIdx, clampByte_idem_at_ph]
  · simp only [hlen, ↓reduceIte]

private theorem toBEBytes_length_apr (n : Nat) (w : BitVec (8 * n)) :
    (ByteSpecs.toBEBytes n w).length = n := by
  simp [ByteSpecs.toBEBytes]

private theorem shaState_flatMap_length_apr (h : ByteSpecs.ShaState) :
    (h.toList.flatMap (ByteSpecs.toBEBytes 4)).length = 32 := by
  rcases h with ⟨l, hl⟩
  have h4 : ∀ x : BitVec 32, (ByteSpecs.toBEBytes 4 x).length = 4 := toBEBytes_length_apr 4
  simp [List.length_flatMap, h4, hl]

private theorem nck_length_hmacWith_apr
    (F : ByteSpecs.ShaState → List (BitVec 8) → ByteSpecs.ShaState)
    (key msg : List (BitVec 8)) :
    (CryptoGames.HMAC.hmacWith F key msg).length = 32 := by
  unfold CryptoGames.HMAC.hmacWith CryptoGames.HMAC.sha256With
  exact shaState_flatMap_length_apr _

private theorem extractLsb'_zero_bytesToKey32_cons_ph (b : BitVec 8) (acc : BitVec 256) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' 0 8 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h256 : i < 256 := by omega
  simp [hi, h256]

private theorem extractLsb'_succ_bytesToKey32_cons_ph (b : BitVec 8) (acc : BitVec 256) (j : Nat)
    (hj : j + 1 < 32) :
    ((acc <<< 8) ||| b.zeroExtend 256).extractLsb' (8 * (j + 1)) 8 =
      acc.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  have h1 : ¬ (8 * (j + 1) + i < 8) := by omega
  have h2 : 8 * (j + 1) + i < 256 := by omega
  have h3 : 8 * (j + 1) + i - 8 = 8 * j + i := by omega
  have hb : b.getLsbD (8 * (j + 1) + i) = false := by
    unfold BitVec.getLsbD
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [h1, h2, h3, hb]

private theorem extractLsb'_bytesToKey32_ph (bs : List (BitVec 8)) (j : Nat)
    (hj : j < bs.length) (h32 : j < 32) :
    (bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j] := by
  induction bs generalizing j with
  | nil => simp at hj
  | cons b rest ih =>
    cases j with
    | zero => simpa [bytesToKey32] using extractLsb'_zero_bytesToKey32_cons_ph b (bytesToKey32 rest)
    | succ j =>
      have hcons : bytesToKey32 (b :: rest) = (bytesToKey32 rest <<< 8) ||| b.zeroExtend 256 := rfl
      rw [hcons, extractLsb'_succ_bytesToKey32_cons_ph b (bytesToKey32 rest) j h32, List.getElem_cons_succ]
      exact ih j (by simpa using hj) (by omega)

private theorem keyToBytes32_bytesToKey32_ph (b : List (BitVec 8)) (hb : b.length = 32) :
    keyToBytes32 (bytesToKey32 b) = b := by
  refine List.ext_getElem (by simp [keyToBytes32, hb]) fun j h1 h2 => ?_
  simp only [keyToBytes32, List.getElem_ofFn]
  exact extractLsb'_bytesToKey32_ph b j h2 (by omega)

private theorem hkdf_64_whisperRatchet_ph (F : ShaCompress) (salt : Salt) (ikm : List (BitVec 8)) :
    let prk := hkdfExtract F salt ikm
    let t1 := CryptoGames.HMAC.hmacWith F prk ([] ++ Ratchet.whisperRatchetInfo ++ [1#8])
    let t2 := CryptoGames.HMAC.hmacWith F prk (t1 ++ Ratchet.whisperRatchetInfo ++ [2#8])
    hkdf F salt ikm Ratchet.whisperRatchetInfo 64 = t1 ++ t2 ∧
    (hkdf F salt ikm Ratchet.whisperRatchetInfo 64).take 32 = t1 ∧
    ((hkdf F salt ikm Ratchet.whisperRatchetInfo 64).drop 32).take 32 = t2 := by
  intro prk t1 t2
  have h2 : (64 + 31) / 32 = 2 := rfl
  have hblocks : (hkdfBlocks F prk Ratchet.whisperRatchetInfo 2).flatten = t1 ++ t2 := by
    simp [hkdfBlocks, t1, t2, List.append_assoc]
  have ht1_len : t1.length = 32 := nck_length_hmacWith_apr F _ _
  have ht2_len : t2.length = 32 := nck_length_hmacWith_apr F _ _
  have h64 : hkdf F salt ikm Ratchet.whisperRatchetInfo 64 = t1 ++ t2 := by
    dsimp only [hkdf, hkdfExpand]
    rw [h2, hblocks, List.take_of_length_le (by simp [ht1_len, ht2_len])]
  refine ⟨h64, ?_, ?_⟩
  · rw [h64, List.take_left' ht1_len]
  · rw [h64, List.drop_left' ht1_len, List.take_of_length_le (by omega)]

private theorem clampScalar_toList_cons32_ph
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8)
    (hl : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31].length = 32) :
    (Ratchet.clampScalar ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩).toList =
      [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
       b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
       (b31 &&& 0x7f#8) ||| 0x40#8] := rfl

private theorem clamp_cons32_ph
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15
     b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : BitVec 8) :
    clamp [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
           b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
      [b0 &&& 0xf8#8, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
       b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30,
       (b31 &&& 0x7f#8) ||| 0x40#8] := by
  simp [clamp, clampByte]

private theorem clampScalar_toList_eq_clamp_toList_ph (v : List.Vector (BitVec 8) 32) :
    (Ratchet.clampScalar v).toList = clamp v.toList := by
  rcases v with ⟨l, hl⟩
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23,
    _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp at hl; done)
  change (Ratchet.clampScalar ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
    b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], hl⟩).toList =
    clamp [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
      b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31]
  rw [clampScalar_toList_cons32_ph, clamp_cons32_ph]

private theorem clampScalar_idem_ph (v : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar v) = Ratchet.clampScalar v := by
  apply Subtype.ext
  change (Ratchet.clampScalar (Ratchet.clampScalar v)).toList = (Ratchet.clampScalar v).toList
  rw [clampScalar_toList_eq_clamp_toList_ph, clampScalar_toList_eq_clamp_toList_ph, clamp_clamp]

theorem rootCreateChain_eq_gamma_createChain_aliceLit
    (interpretation : ExternInterpretation)
    (hEq : ExternCryptoLawsHold interpretation)
    (r : ProtocolSetup) (bundle : HwBytes) (ds : List HwBytes)
    {E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block}
    (rkBytes : HwBytes) (theirRatchetKey : PublicKey)
    (ephACoins : List.Vector (BitVec 8) 32)
    (rk1 : RootKey) (ck1 : ChainKey)
    (hrk : rkBytes = gamma interpretation (compSemOf interpretation r)
      { σ := fun _ _ => [], addr := fun _ => [] }
      (aliceLitAgreement r bundle ds).2.rk)
    (hrk_len : rkBytes.length = 32)
    (htheir : theirRatchetKey.bytes.toList = pubBytes interpretation (secretBytes r 2))
    (heph : (Ratchet.clampScalar ephACoins).toList = clamp (ds.getD 33 []))
    (hcc : rootCreateChain (cryptoOf' interpretation E D)
      (bytesToKey32 rkBytes) theirRatchetKey ⟨Ratchet.clampScalar ephACoins⟩ = .ok (rk1, ck1)) :
    let S := compSemOf interpretation r
    let g0 : Ghost := { σ := fun _ _ => [], addr := fun _ => [] }
    let agr0 := aliceLitAgreement r bundle ds
    let ccSym := createChain agr0.2.rk
      (DY.DiffieHellman.dhPk (hwLit (secretBytes r 2)))
      (hwLit (ds.getD 33 []))
    ck1.index = 0#32 ∧
    keyToBytes32 rk1 = gamma interpretation S g0 ccSym.1 ∧
    keyToBytes32 ck1.key = gamma interpretation S g0 ccSym.2 := by
  intro S g0 agr0 ccSym
  unfold rootCreateChain Ratchet.createChain at hcc
  dsimp only at hcc
  split_ifs at hcc
  dsimp only at hcc
  injection hcc with hpair
  injection hpair with hrk1_eq hck1_eq
  subst hrk1_eq hck1_eq
  let F := sha256CompressFunction interpretation
  let dhBytes := ((cryptoOf' interpretation E D).X
    (Ratchet.clampScalar (⟨Ratchet.clampScalar ephACoins⟩ : PrivateKey).bytes)
    theirRatchetKey.bytes).toList
  obtain ⟨_, htake1, htake2⟩ :=
    hkdf_64_whisperRatchet_ph F (Ratchet.rootSalt (bytesToKey32 rkBytes)) dhBytes
  have hdh_eq : dhBytes =
      TR.dhAgreeBytes interpretation (ds.getD 33 [])
        (pubBytes interpretation (secretBytes r 2)) := by
    dsimp only [dhBytes, cryptoOf', TR.dhAgreeBytes]
    have hlen := hEq.x25519_agreement_length
      (Ratchet.clampScalar (Ratchet.clampScalar ephACoins)).toList
      theirRatchetKey.bytes.toList
    rw [vec32_toList_of_length_32' _ hlen, clampScalar_idem_ph, heph, htheir]
  have hprk_eq :
      hkdfExtract F (Ratchet.rootSalt (bytesToKey32 rkBytes)) dhBytes =
        ByteSpecs.hmacWith F rkBytes dhBytes := by
    dsimp only [hkdfExtract, Ratchet.rootSalt, Option.getD]
    change CryptoGames.HMAC.hmacWith F (keyToBytes32 (bytesToKey32 rkBytes)) dhBytes = _
    rw [keyToBytes32_bytesToKey32_ph rkBytes hrk_len]
    rfl
  have hwr : Ratchet.whisperRatchetInfo = TR.whisperRatchetBytes := by decide
  refine ⟨rfl, ?_, ?_⟩
  · have hrk_bytes :
        keyToBytes32 (Ratchet.rootKdf F (bytesToKey32 rkBytes) dhBytes).1 =
          CryptoGames.HMAC.hmacWith F (hkdfExtract F (Ratchet.rootSalt (bytesToKey32 rkBytes)) dhBytes)
            ([] ++ Ratchet.whisperRatchetInfo ++ [1#8]) := by
      dsimp only [Ratchet.rootKdf]
      rw [htake1, keyToBytes32_bytesToKey32_ph _ (nck_length_hmacWith_apr F _ _)]
    change keyToBytes32 (Ratchet.rootKdf F (bytesToKey32 rkBytes) dhBytes).1 = _
    dsimp only [ccSym]
    rw [hrk_bytes, hprk_eq, hdh_eq, List.nil_append, hwr,
        gamma_createChain_fst interpretation hEq S g0,
        ← hrk, TR.gamma_dhPk, gamma_hwLit, gamma_hwLit]
    rfl
  · have hck_bytes :
        keyToBytes32 (Ratchet.rootKdf F (bytesToKey32 rkBytes) dhBytes).2 =
          CryptoGames.HMAC.hmacWith F (hkdfExtract F (Ratchet.rootSalt (bytesToKey32 rkBytes)) dhBytes)
            (CryptoGames.HMAC.hmacWith F (hkdfExtract F (Ratchet.rootSalt (bytesToKey32 rkBytes)) dhBytes)
              ([] ++ Ratchet.whisperRatchetInfo ++ [1#8]) ++ Ratchet.whisperRatchetInfo ++ [2#8]) := by
      dsimp only [Ratchet.rootKdf]
      rw [htake2, keyToBytes32_bytesToKey32_ph _ (nck_length_hmacWith_apr F _ _)]
    change keyToBytes32 (Ratchet.rootKdf F (bytesToKey32 rkBytes) dhBytes).2 = _
    dsimp only [ccSym]
    rw [hck_bytes, hprk_eq, hdh_eq, List.nil_append, List.append_assoc, hwr,
        gamma_pqxdh_createChain_snd interpretation hEq S g0,
        ← hrk, TR.gamma_dhPk, gamma_hwLit, gamma_hwLit]
    rfl

end RootCreateChainBridge

end Symbolic.Swarm.CREF

namespace CryptoVerification.SpqrV1.ProtoRepr
end CryptoVerification.SpqrV1.ProtoRepr
