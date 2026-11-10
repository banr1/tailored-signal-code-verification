/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.TopInSync
public import LibsignalBinary.Proofs.SpqrV1Sync.RunTight
public import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeBase
public import LibsignalBinary.Proofs.SpqrV1Sync.ChainSync
public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Init
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec
public import ProofLib

set_option autoImplicit false

/-!
# Serialized State Size Bound for Honest SPQR V1 Parties

Proves `partyTop_length_lt`: the serialized `PqRatchetState` of an honest party (`TopSync.PartyTop`)
along a tight braid run (`RunT`) has byte length strictly below `2 ^ 64`, discharging the `hsize`
premise of `TopSync.top_send`, `top_recv`, and `top_recv_err`:
* Version negotiation size is bounded in terms of `authKey.length`.
* `chainOk_rawChain_le` bounds the `Chain` encoding linearly in `currentEpoch` and the sum of
  per-epoch receive high-water counters `(recvSet e).sup id`, using `SendPrevNil`.
* `runT_rawV1State_le` bounds every reachable `V1State` protobuf encoding by `2 ^ 40`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.TopSync

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.InSync
open CryptoVerification.SpqrV1Sync.Braid
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.SpqrV1.Top.StateSize (optRaw rawVN rawChain rawChainEpoch rawEpochDir
  rawV1State rawInnerState rawAuth rawPolyEnc rawPolyDec rawUcKeysUnsampled rawUcHeaderSent
  rawUcEkSent rawUcEkSentCt1Received rawUcNoHeaderReceived rawUcHeaderReceived rawUcCt1Sent
  rawUcCt1SentEkReceived rawUcCt2Sent rawChKeysUnsampled rawChKeysSampled rawChHeaderSent
  rawChCt1Received rawChEkSentCt1Received rawChNoHeaderReceived rawChHeaderReceived
  rawChCt1Sampled rawChEkReceivedCt1Sampled rawChCt1Acknowledged rawChCt2Sampled
  encodeVarint_length_le encodeKey_length_le)

private theorem u32Field_le (tag : BitVec 32) (v : BitVec 32) :
    (Proto.encodeUint32Field tag v).length ≤ 22 := by
  unfold Proto.encodeUint32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.zeroExtend 64)
    omega

private theorem u64Field_le (tag : BitVec 32) (v : BitVec 64) :
    (Proto.encodeUint64Field tag v).length ≤ 22 := by
  unfold Proto.encodeUint64Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le v
    omega

private theorem i32Field_le (tag : BitVec 32) (v : BitVec 32) :
    (Proto.encodeInt32Field tag v).length ≤ 22 := by
  unfold Proto.encodeInt32Field
  split
  · simp
  · simp only [List.length_append]
    have h1 := encodeKey_length_le tag .varint
    have h2 := encodeVarint_length_le (v.signExtend 64)
    omega

private theorem boolField_le (tag : BitVec 32) (v : Bool) :
    (Proto.encodeBoolField tag v).length ≤ 12 := by
  unfold Proto.encodeBoolField
  split
  · simp only [List.length_append, List.length_singleton]
    have h1 := encodeKey_length_le tag .varint
    omega
  · simp

private theorem bytesUncond_le (tag : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesUncond tag v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesUncond
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 v.length)
  omega

private theorem bytesField_le (tag : BitVec 32) (v : Bytes) :
    (Proto.encodeBytesField tag v).length ≤ v.length + 22 := by
  unfold Proto.encodeBytesField
  split
  · simp
  · exact bytesUncond_le tag v

private theorem repeatedBytes_le (tag : BitVec 32) (vs : List Bytes) :
    (Proto.encodeRepeatedBytes tag vs).length ≤ (vs.map fun b => b.length + 22).sum := by
  induction vs with
  | nil => simp [Proto.encodeRepeatedBytes]
  | cons b bs ih =>
    simp only [Proto.encodeRepeatedBytes, List.foldr_cons, List.length_append, List.map_cons,
      List.sum_cons]
    have hb := bytesUncond_le tag b
    have hbs : (bs.foldr (fun v acc => Proto.encodeBytesUncond tag v ++ acc) []).length ≤
        (bs.map fun x => x.length + 22).sum := ih
    omega

private theorem msgField_le {M : Type} (encodeRaw : M → Bytes) (tag : BitVec 32) (m : M) :
    (Proto.encodeMessage encodeRaw tag m).length ≤ (encodeRaw m).length + 22 := by
  unfold Proto.encodeMessage
  simp only [List.length_append]
  have h1 := encodeKey_length_le tag .lengthDelimited
  have h2 := encodeVarint_length_le (BitVec.ofNat 64 (encodeRaw m).length)
  omega

private theorem optMsgField_le {M : Type} (encodeRaw : M → Bytes) (rawM : M → Nat) (c : Nat)
    (tag : BitVec 32) (opt : Option M)
    (h : ∀ m, (encodeRaw m).length ≤ rawM m + c) :
    (Proto.encodeOptMessage encodeRaw tag opt).length ≤ optRaw rawM opt + (c + 22) := by
  cases opt with
  | none => simp [Proto.encodeOptMessage, optRaw]
  | some m =>
    simp only [Proto.encodeOptMessage, optRaw]
    have hm := msgField_le encodeRaw tag m
    have hr := h m
    omega

private theorem chainParams_encodeRaw_le (m : ChainParamsPB) :
    (ChainParamsPB.encodeRaw m).length ≤ 44 := by
  unfold ChainParamsPB.encodeRaw
  simp only [List.length_append]
  have h1 := u32Field_le 1#32 m.maxJump
  have h2 := u32Field_le 2#32 m.maxOooKeys
  omega

private theorem vn_encodeRaw_le (m : VersionNegotiationPB) :
    (VersionNegotiationPB.encodeRaw m).length ≤ rawVN m + 132 := by
  unfold VersionNegotiationPB.encodeRaw rawVN
  simp only [List.length_append]
  have h1 := bytesField_le 1#32 m.authKey
  have h2 := i32Field_le 2#32 m.direction
  have h3 := i32Field_le 3#32 m.minVersion
  have h4 := optMsgField_le ChainParamsPB.encodeRaw (fun _ => 0) 44 4#32 m.chainParams
    (fun cp => by have := chainParams_encodeRaw_le cp; omega)
  have h4' : optRaw (fun _ => 0) m.chainParams = 0 := by cases m.chainParams <;> rfl
  omega

private theorem epochDir_encodeRaw_le (m : EpochDirectionPB) :
    (EpochDirectionPB.encodeRaw m).length ≤ rawEpochDir m + 66 := by
  unfold EpochDirectionPB.encodeRaw rawEpochDir
  simp only [List.length_append]
  have h1 := u32Field_le 1#32 m.ctr
  have h2 := bytesField_le 2#32 m.next
  have h3 := bytesField_le 3#32 m.prev
  omega

private theorem chainEpoch_encodeRaw_le (m : ChainEpochPB) :
    (ChainEpochPB.encodeRaw m).length ≤ rawChainEpoch m + 176 := by
  unfold ChainEpochPB.encodeRaw rawChainEpoch
  simp only [List.length_append]
  have h1 := optMsgField_le EpochDirectionPB.encodeRaw rawEpochDir 66 1#32 m.send epochDir_encodeRaw_le
  have h2 := optMsgField_le EpochDirectionPB.encodeRaw rawEpochDir 66 2#32 m.recv epochDir_encodeRaw_le
  omega

private theorem links_encode_le (links : List ChainEpochPB) :
    (Proto.encodeRepeatedMessage ChainEpochPB.encodeRaw 3#32 links).length ≤
      (links.map fun ep => rawChainEpoch ep + 200).sum := by
  induction links with
  | nil => simp [Proto.encodeRepeatedMessage]
  | cons ep rest ih =>
    simp only [Proto.encodeRepeatedMessage, List.foldr_cons, List.length_append, List.map_cons,
      List.sum_cons]
    have h1 := msgField_le ChainEpochPB.encodeRaw 3#32 ep
    have h2 := chainEpoch_encodeRaw_le ep
    have h3 : (rest.foldr (fun m acc => Proto.encodeMessage ChainEpochPB.encodeRaw 3#32 m ++ acc) []).length ≤
        (rest.map fun x => rawChainEpoch x + 200).sum := ih
    omega

private theorem chainPB_encodeRaw_le (m : ChainPB) :
    (ChainPB.encodeRaw m).length ≤ rawChain m + 154 := by
  unfold ChainPB.encodeRaw rawChain
  simp only [List.length_append]
  have h1 := i32Field_le 1#32 m.direction
  have h2 := u64Field_le 2#32 m.currentEpoch
  have h3 := links_encode_le m.links
  have h4 := bytesField_le 4#32 m.nextRoot
  have h5 := u64Field_le 5#32 m.sendEpoch
  have h6 := optMsgField_le ChainParamsPB.encodeRaw (fun _ => 0) 44 6#32 m.params
    (fun cp => by have := chainParams_encodeRaw_le cp; omega)
  have h6' : optRaw (fun _ => 0) m.params = 0 := by cases m.params <;> rfl
  omega

private theorem auth_encodeRaw_le (a : ProtoAuthenticator) :
    (ProtoAuthenticator.encodeRaw a).length ≤ rawAuth a + 44 := by
  unfold ProtoAuthenticator.encodeRaw rawAuth
  simp only [List.length_append]
  have h1 := bytesField_le 1#32 a.rootKey
  have h2 := bytesField_le 2#32 a.macKey
  omega

private theorem polyEnc_encodeRaw_le (pe : PolynomialEncoder) :
    (PolynomialEncoder.encodeRaw pe).length ≤ rawPolyEnc pe + 22 := by
  unfold PolynomialEncoder.encodeRaw rawPolyEnc
  simp only [List.length_append]
  have h1 := u32Field_le 1#32 pe.idx
  have h2 := repeatedBytes_le 2#32 pe.pts
  have h3 := repeatedBytes_le 3#32 pe.polys
  omega

private theorem polyDec_encodeRaw_le (pd : PolynomialDecoder) :
    (PolynomialDecoder.encodeRaw pd).length ≤ rawPolyDec pd + 56 := by
  unfold PolynomialDecoder.encodeRaw rawPolyDec
  simp only [List.length_append]
  have h1 := u32Field_le 1#32 pd.ptsNeeded
  have h2 := u32Field_le 2#32 pd.polys
  have h3 := repeatedBytes_le 3#32 pd.pts
  have h4 := boolField_le 4#32 pd.isComplete
  omega

private theorem v1Inner_encode_le (is : V1State.InnerState) :
    (V1State.InnerState.encode is).length ≤ rawInnerState is + 320 := by
  cases is with
  | keysUnsampled v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.KeysUnsampled.encodeRaw 1#32 v
    have hraw : (V1State.Chunked.KeysUnsampled.encodeRaw v).length ≤ rawChKeysUnsampled v + 298 := by
      unfold V1State.Chunked.KeysUnsampled.encodeRaw rawChKeysUnsampled
      have huc := optMsgField_le V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled 88 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          omega)
      omega
    omega
  | keysSampled v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.KeysSampled.encodeRaw 2#32 v
    have hraw : (V1State.Chunked.KeysSampled.encodeRaw v).length ≤ rawChKeysSampled v + 298 := by
      unfold V1State.Chunked.KeysSampled.encodeRaw rawChKeysSampled
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent 132 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.ek
          have := bytesField_le 4#32 u.dk
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingHdr polyEnc_encodeRaw_le
      omega
    omega
  | headerSent v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.HeaderSent.encodeRaw 3#32 v
    have hraw : (V1State.Chunked.HeaderSent.encodeRaw v).length ≤ rawChHeaderSent v + 298 := by
      unfold V1State.Chunked.HeaderSent.encodeRaw rawChHeaderSent
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.EkSent.encodeRaw rawUcEkSent 110 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.EkSent.encodeRaw rawUcEkSent
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.dk
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingEk polyEnc_encodeRaw_le
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 3#32 v.receivingCt1 polyDec_encodeRaw_le
      omega
    omega
  | ct1Received v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.Ct1Received.encodeRaw 4#32 v
    have hraw : (V1State.Chunked.Ct1Received.encodeRaw v).length ≤ rawChCt1Received v + 298 := by
      unfold V1State.Chunked.Ct1Received.encodeRaw rawChCt1Received
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.dk
          have := bytesField_le 4#32 u.ct1
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingEk polyEnc_encodeRaw_le
      omega
    omega
  | ekSentCt1Received v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.EkSentCt1Received.encodeRaw 5#32 v
    have hraw : (V1State.Chunked.EkSentCt1Received.encodeRaw v).length ≤ rawChEkSentCt1Received v + 298 := by
      unfold V1State.Chunked.EkSentCt1Received.encodeRaw rawChEkSentCt1Received
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received 132 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.dk
          have := bytesField_le 4#32 u.ct1
          omega)
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 3#32 v.receivingCt2 polyDec_encodeRaw_le
      omega
    omega
  | noHeaderReceived v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.NoHeaderReceived.encodeRaw 6#32 v
    have hraw : (V1State.Chunked.NoHeaderReceived.encodeRaw v).length ≤ rawChNoHeaderReceived v + 298 := by
      unfold V1State.Chunked.NoHeaderReceived.encodeRaw rawChNoHeaderReceived
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived 88 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          omega)
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 2#32 v.receivingHdr polyDec_encodeRaw_le
      omega
    omega
  | headerReceived v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.HeaderReceived.encodeRaw 7#32 v
    have hraw : (V1State.Chunked.HeaderReceived.encodeRaw v).length ≤ rawChHeaderReceived v + 298 := by
      unfold V1State.Chunked.HeaderReceived.encodeRaw rawChHeaderReceived
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived 110 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.hdr
          omega)
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 2#32 v.receivingEk polyDec_encodeRaw_le
      omega
    omega
  | ct1Sampled v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.Ct1Sampled.encodeRaw 8#32 v
    have hraw : (V1State.Chunked.Ct1Sampled.encodeRaw v).length ≤ rawChCt1Sampled v + 298 := by
      unfold V1State.Chunked.Ct1Sampled.encodeRaw rawChCt1Sampled
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.hdr
          have := bytesField_le 4#32 u.es
          have := bytesField_le 5#32 u.ct1
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingCt1 polyEnc_encodeRaw_le
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 3#32 v.receivingEk polyDec_encodeRaw_le
      omega
    omega
  | ekReceivedCt1Sampled v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.EkReceivedCt1Sampled.encodeRaw 9#32 v
    have hraw : (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw v).length ≤ rawChEkReceivedCt1Sampled v + 298 := by
      unfold V1State.Chunked.EkReceivedCt1Sampled.encodeRaw rawChEkReceivedCt1Sampled
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived 154 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.es
          have := bytesField_le 4#32 u.ek
          have := bytesField_le 5#32 u.ct1
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingCt1 polyEnc_encodeRaw_le
      omega
    omega
  | ct1Acknowledged v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.Ct1Acknowledged.encodeRaw 10#32 v
    have hraw : (V1State.Chunked.Ct1Acknowledged.encodeRaw v).length ≤ rawChCt1Acknowledged v + 298 := by
      unfold V1State.Chunked.Ct1Acknowledged.encodeRaw rawChCt1Acknowledged
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent 154 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          have := bytesField_le 3#32 u.hdr
          have := bytesField_le 4#32 u.es
          have := bytesField_le 5#32 u.ct1
          omega)
      have hdec := optMsgField_le PolynomialDecoder.encodeRaw rawPolyDec 56 2#32 v.receivingEk polyDec_encodeRaw_le
      omega
    omega
  | ct2Sampled v =>
    simp only [V1State.InnerState.encode, rawInnerState]
    have hm := msgField_le V1State.Chunked.Ct2Sampled.encodeRaw 11#32 v
    have hraw : (V1State.Chunked.Ct2Sampled.encodeRaw v).length ≤ rawChCt2Sampled v + 298 := by
      unfold V1State.Chunked.Ct2Sampled.encodeRaw rawChCt2Sampled
      simp only [List.length_append]
      have huc := optMsgField_le V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent 88 1#32 v.uc
        (fun u => by
          unfold V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent
          simp only [List.length_append]
          have := u64Field_le 1#32 u.epoch
          have := optMsgField_le ProtoAuthenticator.encodeRaw rawAuth 44 2#32 u.auth auth_encodeRaw_le
          omega)
      have henc := optMsgField_le PolynomialEncoder.encodeRaw rawPolyEnc 22 2#32 v.sendingCt2 polyEnc_encodeRaw_le
      omega
    omega

/-- `topBytes` is bounded by the sum of the `StateSize` measures of its components plus `752`. -/
theorem topBytes_length_le (F : ShaCompress) (K : MlKem) (st : St F)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) :
    (topBytes F K st vn? ch?).length ≤
      optRaw rawVN vn? + optRaw rawChain (ch?.map Chain.intoPb) + rawV1State st.into_pb + 752 := by
  have heq : topBytes F K st vn? ch? = Proto.encodeState (pbToPqRatchetState (topPb st vn? ch?)) := rfl
  rw [heq]
  unfold Proto.encodeState PqRatchetState.encode PqRatchetState.encodeRaw pbToPqRatchetState topPb
  simp only [Option.map_some, List.length_append]
  have hvn := optMsgField_le VersionNegotiationPB.encodeRaw rawVN 132 1#32 vn? vn_encodeRaw_le
  have hch := optMsgField_le ChainPB.encodeRaw rawChain 154 2#32 (ch?.map Chain.intoPb)
    chainPB_encodeRaw_le
  have hin : (PqRatchetState.Inner.encode (.v1 st.into_pb)).length ≤ rawV1State st.into_pb + 342 := by
    simp only [PqRatchetState.Inner.encode]
    have hm := msgField_le V1State.encodeRaw 3#32 st.into_pb
    have hraw : (V1State.encodeRaw st.into_pb).length ≤ rawV1State st.into_pb + 320 := by
      unfold V1State.encodeRaw rawV1State
      cases st.into_pb.innerState with
      | none => simp [optRaw]
      | some is =>
        simp only [optRaw]
        exact v1Inner_encode_le is
    omega
  omega

private theorem flatten_histEntry_length (F : ShaCompress) (seed : Bytes) :
    ∀ L : List ℕ, ((L.map fun j => histEntry j (keyAt F seed (j - 1))).flatten).length = 36 * L.length
  | [] => rfl
  | j :: rest => by
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have hent : (histEntry j (keyAt F seed (j - 1))).length = 36 := by
      simp [histEntry, toBEBytes, length_keyAt]
    have hrest := flatten_histEntry_length F seed rest
    omega

/-- A `KeyHistory` satisfying `HistRepr F seed S` has exact byte length `36 * S.card`. -/
theorem histRepr_length (F : ShaCompress) (seed : Bytes) (S : Finset ℕ) (h : KeyHistory)
    (hr : HistRepr F seed S h) : h.data.length = 36 * S.card := by
  rcases hr with ⟨L, hnodup, hfin, hdata⟩
  rw [hdata, flatten_histEntry_length, ← hfin, List.toFinset_card_of_nodup hnodup]

/-- Per-link raw protobuf size bound under `ChainOk` and `SendPrevNil`. -/
theorem chainOk_link_le (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsp : SendPrevNil ch) (i : ℕ)
    (l : ChainEpoch) (hl : ch.links[i]? = some l) :
    rawEpochDir l.send.intoPb + rawEpochDir l.recv.intoPb ≤
      64 + 36 * (recvSet (ch.sendEpoch.toNat - 1 + i)).sup id := by
  have hi_lt : i < ch.links.length := (List.getElem?_eq_some_iff.mp hl).1
  have hlen := h.hlen
  have hsend_le := h.hsend_le
  let e := ch.sendEpoch.toNat - 1 + i
  have he_lo : ch.sendEpoch.toNat - 1 ≤ e := Nat.le_add_right _ _
  have he_hi : e ≤ ch.currentEpoch.toNat := by omega
  have he_sub : e - (ch.sendEpoch.toNat - 1) = i := Nat.add_sub_cancel_left _ _
  have hsend_prev : l.send.prev.data = [] := hsp l (List.mem_of_getElem? hl)
  have hsend_next : l.send.next.length ≤ 32 := by
    by_cases hge : ch.sendEpoch.toNat ≤ e
    · obtain ⟨l₀, hl₀, hsd⟩ := h.hsendDir e hge he_hi
      rw [he_sub, hl] at hl₀
      injection hl₀ with hl₀_eq
      subst hl₀_eq
      rw [hsd.hnext, length_nextAt F _ (length_seedAt F authKey secret dir e)]
    · have hi0 : i = 0 := by omega
      have hpos : 1 ≤ ch.sendEpoch.toNat := by omega
      rw [hi0] at hl
      rw [h.hsendOld l hpos hl]
      simp
  obtain ⟨l₁, hl₁, hrd⟩ := h.hrecvDir e he_lo he_hi
  rw [he_sub, hl] at hl₁
  injection hl₁ with hl₁_eq
  subst hl₁_eq
  have hrecv_next : l.recv.next.length = 32 := by
    rw [hrd.hnext, length_nextAt F _ (length_seedAt F authKey secret dir.switch e)]
  obtain ⟨S, hhist, hS_bounds, _⟩ := hrd.hprev
  have hrecv_prev : l.recv.prev.data.length = 36 * S.card :=
    histRepr_length F _ S l.recv.prev hhist
  have hsub : S ⊆ Finset.range ((recvSet e).sup id) := by
    intro j hj
    rw [Finset.mem_range, ← hrd.hctr]
    exact (hS_bounds j hj).2.1
  have hcard : S.card ≤ (recvSet (ch.sendEpoch.toNat - 1 + i)).sup id :=
    (Finset.card_le_card hsub).trans (by simp [e])
  unfold rawEpochDir ChainEpochDirection.intoPb
  simp only [hsend_prev, List.length_nil, hrecv_next, hrecv_prev]
  omega

private theorem list_sum_map_le_range {α : Type} :
    ∀ (xs : List α) (f : α → ℕ) (g : ℕ → ℕ),
      (∀ i (x : α), xs[i]? = some x → f x ≤ g i) →
      (xs.map f).sum ≤ ∑ i ∈ Finset.range xs.length, g i
  | [], _, _, _ => by simp
  | x :: xs, f, g, hfg => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
    have hx : f x ≤ g 0 := hfg 0 x rfl
    have hxs : (xs.map f).sum ≤ ∑ i ∈ Finset.range xs.length, g (i + 1) :=
      list_sum_map_le_range xs f (fun i => g (i + 1)) (fun i y hy => hfg (i + 1) y hy)
    omega

private theorem sum_shift_le_range (a n m : ℕ) (f : ℕ → ℕ) (h : a + n ≤ m + 1) :
    (∑ i ∈ Finset.range n, f (a + i)) ≤ ∑ e ∈ Finset.range (m + 1), f e := by
  have himg : (∑ i ∈ Finset.range n, f (a + i)) =
      ∑ e ∈ (Finset.range n).image (fun i => a + i), f e := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    dsimp only at hxy
    omega
  rw [himg]
  apply Finset.sum_le_sum_of_subset
  intro e he
  rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
  rw [Finset.mem_range] at hi ⊢
  omega

/-- Total `rawChain` size bound for an honest chain, linear in `currentEpoch` and received
high-water counters. -/
theorem chainOk_rawChain_le (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ) (ch : Chain)
    (h : ChainOk F authKey dir secret sendCtr recvSet ch) (hsp : SendPrevNil ch) :
    rawChain ch.intoPb ≤
      32 + ∑ e ∈ Finset.range (ch.currentEpoch.toNat + 1),
        (264 + 36 * (recvSet e).sup id) := by
  unfold rawChain Chain.intoPb
  simp only [List.map_map, Function.comp_def]
  have hroot_le : ch.nextRoot.length ≤ 32 := by
    rw [h.hroot]
    exact List.length_take_le 32 _
  have hlinks_le :
      ((ch.links.map (fun l =>
          rawChainEpoch { send := some l.send.intoPb, recv := some l.recv.intoPb } + 200)).sum) ≤
        ∑ i ∈ Finset.range ch.links.length,
          (264 + 36 * (recvSet (ch.sendEpoch.toNat - 1 + i)).sup id) := by
    refine list_sum_map_le_range ch.links
      (fun l => rawChainEpoch { send := some l.send.intoPb, recv := some l.recv.intoPb } + 200)
      (fun i => 264 + 36 * (recvSet (ch.sendEpoch.toNat - 1 + i)).sup id) ?_
    intro i l hl
    have hlink := chainOk_link_le F authKey dir secret sendCtr recvSet ch h hsp i l hl
    simp only [rawChainEpoch, optRaw]
    omega
  have hshift := sum_shift_le_range (ch.sendEpoch.toNat - 1) ch.links.length
    ch.currentEpoch.toNat (fun e => 264 + 36 * (recvSet e).sup id)
    (by have := h.hlen; have := h.hsend_le; omega)
  omega

private theorem update_rootKey_le (F : ShaCompress) (a : Authenticator) (ep : Epoch) (k : Bytes) :
    (a.update F ep k).rootKey.length ≤ 32 :=
  List.length_take_le 32 _

private theorem runT_rootKey_le (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) : auth.rootKey.length ≤ 32 := by
  induction hr with
  | init => exact update_rootKey_le F _ _ _
  | sendA _ _ _ _ _ _ _ _ _ ih => exact ih
  | sendB _ _ _ _ _ _ _ _ _ ih => exact ih
  | recvA _ _ _ _ _ _ _ ih => exact ih
  | recvB _ _ _ _ _ _ _ ih => exact ih
  | advanceA => exact update_rootKey_le F _ _ _
  | advanceB => exact update_rootKey_le F _ _ _

private theorem rawAuth_of_wf {F : ShaCompress} (a : Authenticator)
    (hrk : a.rootKey.length ≤ 32) (hwf : AuthWf a) :
    rawAuth ((spqrAuthApi F).into_pb a) ≤ 64 := by
  change a.rootKey.length + a.macKey.length ≤ 64
  rw [AuthWf] at hwf
  omega

private theorem rawAuth_authNext_le (F : ShaCompress) (K : MlKem) (e : Epoch)
    (auth : Authenticator) (s : Seed) (r : EncRand) :
    rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) ≤ 64 :=
  rawAuth_of_wf (authNext F K e auth s r) (update_rootKey_le F auth e _)
    (authWf_update F auth e _)

private theorem flatMap_u16_len :
    ∀ xs : List GF16, (xs.flatMap fun g => u16ToBeBytes g.value).length = 2 * xs.length
  | [] => rfl
  | g :: xs => by
    rw [List.flatMap_cons, List.length_append, flatMap_u16_len xs]
    have hg : (u16ToBeBytes g.value).length = 2 := rfl
    rw [hg, List.length_cons]
    omega

private theorem flatMap_pt_len :
    ∀ xs : List Pt, (xs.flatMap Pt.serialize).length = 4 * xs.length
  | [] => rfl
  | _ :: xs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Pt.serialize,
      u16ToBeBytes, List.length_nil]
    have := flatMap_pt_len xs
    omega

private theorem list_sum_le_mul {α : Type} :
    ∀ (xs : List α) (f : α → ℕ) (B : ℕ), (∀ x ∈ xs, f x ≤ B) → (xs.map f).sum ≤ xs.length * B
  | [], _, _, _ => by simp
  | x :: xs, f, B, h => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have hxs := list_sum_le_mul xs f B (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : (xs.length + 1) * B = xs.length * B + B := Nat.succ_mul xs.length B
    omega

private theorem rawPolyEnc_of_encInv {msg : Bytes} {enc : PolyEncoder}
    (hmsg : msg.length ≤ 2000) (henc : Erasure.EncInv msg enc) :
    rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 70000 := by
  have hneed : ∀ j, Erasure.needed msg.length j ≤ 2000 := by
    intro j
    unfold Erasure.needed
    split <;> omega
  change rawPolyEnc (protoPolyEncoderToPb enc.intoPb) ≤ 70000
  unfold PolyEncoder.intoPb
  rcases henc with hs | ⟨polys, hs, hlen, hcoeff⟩
  · rw [hs]
    unfold protoPolyEncoderToPb rawPolyEnc Erasure.msgPoints
    simp only [List.map_nil, List.sum_nil, Nat.add_zero, List.map_map, Function.comp_def]
    have hsum := list_sum_le_mul (List.range 16)
      (fun j => (((List.range (Erasure.needed msg.length j)).map
        fun k => Erasure.msgVal msg (16 * k + j)).flatMap
          fun g => u16ToBeBytes g.value).length + 22)
      4022
      (fun j _ => by
        rw [flatMap_u16_len, List.length_map, List.length_range]
        have := hneed j
        omega)
    rw [List.length_range] at hsum
    omega
  · rw [hs]
    unfold protoPolyEncoderToPb rawPolyEnc
    simp only [List.map_nil, List.sum_nil, Nat.zero_add, List.map_map, Function.comp_def]
    have hsum := list_sum_le_mul polys
      (fun p => (Poly.serialize p).length + 22)
      4022
      (fun p hp => by
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
        have hc := (hcoeff j hj).1
        unfold Poly.serialize
        rw [flatMap_u16_len, hc]
        have := hneed j
        omega)
    rw [hlen] at hsum
    omega

private theorem rawPolyDec_of_decInv {msg : Bytes} {S : Finset ℕ} {dec : PolyDecoder}
    (hdec : Erasure.DecInv msg S dec) :
    rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 5000000 := by
  change rawPolyDec (protoPolyDecoderToPb dec.intoPb) ≤ 5000000
  unfold PolyDecoder.intoPb protoPolyDecoderToPb rawPolyDec
  simp only [List.map_map, Function.comp_def]
  have hsum := list_sum_le_mul dec.pts
    (fun s => (s.vec.flatMap Pt.serialize).length + 22)
    270000
    (fun s hs => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      have hpair := hdec.sorted j hj
      have hnodup : (dec.pts[j].vec.map fun pt => pt.x.value.toNat).Nodup :=
        hpair.imp (fun hlt => Nat.ne_of_lt hlt)
      have hsub : (dec.pts[j].vec.map fun pt => pt.x.value.toNat).toFinset ⊆
          Finset.range 65536 := by
        intro v hv
        rw [List.mem_toFinset, List.mem_map] at hv
        rcases hv with ⟨pt, _, rfl⟩
        exact Finset.mem_range.mpr pt.x.value.isLt
      have hcard : (dec.pts[j].vec.map fun pt => pt.x.value.toNat).length ≤ 65536 := by
        rw [← List.toFinset_card_of_nodup hnodup]
        exact (Finset.card_le_card hsub).trans (by simp)
      rw [List.length_map] at hcard
      rw [flatMap_pt_len]
      omega)
  rw [hdec.len] at hsum
  omega

private theorem rawPolyDec_freshDec (len : ℕ) :
    rawPolyDec (spqrPolyApi.decoder_into_pb (freshDec len)) ≤ 5000000 := by
  change rawPolyDec (protoPolyDecoderToPb (freshDec len).intoPb) ≤ 5000000
  unfold freshDec PolyDecoder.intoPb protoPolyDecoderToPb rawPolyDec SortedSetPt.new
  simp

private theorem xShape_raw_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (x : St F) (hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64)
    (hx : XShape F K e auth seed? x) : rawV1State x.into_pb ≤ 2 ^ 40 := by
  cases seed? with
  | none =>
    rw [XShape] at hx
    rw [hx]
    change rawAuth ((spqrAuthApi F).into_pb auth) ≤ 2 ^ 40
    omega
  | some s =>
    obtain ⟨enc, henc, hx_eq⟩ := hx
    rw [hx_eq]
    change rawAuth ((spqrAuthApi F).into_pb auth) + (ekOf K s).length + (dkOf K s).length +
      rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 2 ^ 40
    have hek := Codec.ekOf_length K s
    have hdk := Codec.dkOf_length K s
    have hpe := rawPolyEnc_of_encInv (by rw [hdrMsg_length]; omega) henc
    omega

private theorem yShape_raw_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (seed? : Option Seed) (y : St F) (hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64)
    (hy : YShape F K e auth seed? y) : rawV1State y.into_pb ≤ 2 ^ 40 := by
  cases seed? with
  | none =>
    rw [YShape] at hy
    rw [hy]
    change rawAuth ((spqrAuthApi F).into_pb auth) +
      rawPolyDec (spqrPolyApi.decoder_into_pb (freshDec 96)) ≤ 2 ^ 40
    have hpd := rawPolyDec_freshDec 96
    omega
  | some s =>
    rcases hy with ⟨S, dec, hdec, _, hy_eq⟩ | hy_eq
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb auth) +
        rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 2 ^ 40
      have hpd := rawPolyDec_of_decInv hdec
      omega
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb auth) + (hdrOf K s).length +
        rawPolyDec (spqrPolyApi.decoder_into_pb (freshDec 1152)) ≤ 2 ^ 40
      have hhdr := Codec.hdrOf_length K s
      have hpd := rawPolyDec_freshDec 1152
      omega

private theorem xShapeE_raw_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (x : St F) (hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64)
    (hkem : ∀ s r, c = .both s r → KemOk K s r)
    (hx : XShapeE F K e auth c x) : rawV1State x.into_pb ≤ 2 ^ 40 := by
  cases c with
  | init => exact xShape_raw_le F K e auth none x hauth hx
  | seed s => exact xShape_raw_le F K e auth (some s) x hauth hx
  | both s r =>
    have hok : KemOk K s r := hkem s r rfl
    rcases hx with hxs | ⟨enc, S, dec, henc, hdec, _, hx_eq⟩ | ⟨enc, henc, hx_eq⟩ |
        ⟨S, dec, hdec, _, hx_eq⟩ | hx_eq
    · exact xShape_raw_le F K e auth (some s) x hauth hxs
    · rw [hx_eq]
      change rawAuth ((spqrAuthApi F).into_pb auth) + (dkOf K s).length +
        rawPolyEnc (spqrPolyApi.encoder_into_pb enc) +
        rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 2 ^ 40
      have hdk := Codec.dkOf_length K s
      have hpe := rawPolyEnc_of_encInv (by rw [Codec.ekOf_length]; omega) henc
      have hpd := rawPolyDec_of_decInv hdec
      omega
    · rw [hx_eq]
      change rawAuth ((spqrAuthApi F).into_pb auth) + (dkOf K s).length + (ct1Of K s r).length +
        rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 2 ^ 40
      have hdk := Codec.dkOf_length K s
      have hct1 := ct1Of_length_le K s r
      have hpe := rawPolyEnc_of_encInv (by rw [Codec.ekOf_length]; omega) henc
      omega
    · rw [hx_eq]
      change rawAuth ((spqrAuthApi F).into_pb auth) + (dkOf K s).length + (ct1Of K s r).length +
        rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 2 ^ 40
      have hdk := Codec.dkOf_length K s
      have hct1 := ct1Of_length_le K s r
      have hpd := rawPolyDec_of_decInv hdec
      omega
    · rw [XLag] at hx_eq
      rw [hx_eq]
      change rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) +
        rawPolyDec (spqrPolyApi.decoder_into_pb (freshDec 96)) ≤ 2 ^ 40
      have han := rawAuth_authNext_le F K e auth s r
      have hpd := rawPolyDec_freshDec 96
      omega

private theorem yShapeE_raw_le (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (y : St F) (hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64)
    (hkem : ∀ s r, c = .both s r → KemOk K s r)
    (hy : YShapeE F K e auth c y) : rawV1State y.into_pb ≤ 2 ^ 40 := by
  cases c with
  | init => exact yShape_raw_le F K e auth none y hauth hy
  | seed s => exact yShape_raw_le F K e auth (some s) y hauth hy
  | both s r =>
    have hok : KemOk K s r := hkem s r rfl
    have han := rawAuth_authNext_le F K e auth s r
    rcases hy with ⟨enc, S, dec, henc, hdec, _, hy_eq⟩ | ⟨enc, henc, hy_eq⟩ |
        ⟨S, dec, hdec, _, hy_eq⟩ | ⟨enc, henc, hy_eq⟩
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) +
        (hdrOf K s).length + (esOf K s r).length + (ct1Of K s r).length +
        rawPolyEnc (spqrPolyApi.encoder_into_pb enc) +
        rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 2 ^ 40
      have hhdr := Codec.hdrOf_length K s
      have hes := esOf_length K s r hok
      have hct1 := ct1Of_length_le K s r
      have hpe := rawPolyEnc_of_encInv (by have := ct1Of_length_le K s r; omega) henc
      have hpd := rawPolyDec_of_decInv hdec
      omega
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) +
        (esOf K s r).length + (ekOf K s).length + (ct1Of K s r).length +
        rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 2 ^ 40
      have hes := esOf_length K s r hok
      have hek := Codec.ekOf_length K s
      have hct1 := ct1Of_length_le K s r
      have hpe := rawPolyEnc_of_encInv (by have := ct1Of_length_le K s r; omega) henc
      omega
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) +
        (hdrOf K s).length + (esOf K s r).length + (ct1Of K s r).length +
        rawPolyDec (spqrPolyApi.decoder_into_pb dec) ≤ 2 ^ 40
      have hhdr := Codec.hdrOf_length K s
      have hes := esOf_length K s r hok
      have hct1 := ct1Of_length_le K s r
      have hpd := rawPolyDec_of_decInv hdec
      omega
    · rw [hy_eq]
      change rawAuth ((spqrAuthApi F).into_pb (authNext F K e auth s r)) +
        rawPolyEnc (spqrPolyApi.encoder_into_pb enc) ≤ 2 ^ 40
      have hpe := rawPolyEnc_of_encInv (by rw [c2Msg_length F K e auth s r hok]; omega) henc
      omega

/-- Every braid state reachable along a `RunT` trace has `rawV1State` size at most `2 ^ 40`. -/
theorem runT_rawV1State_le (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) :
    rawV1State stA.into_pb ≤ 2 ^ 40 ∧ rawV1State stB.into_pb ≤ 2 ^ 40 := by
  have hrk : auth.rootKey.length ≤ 32 := runT_rootKey_le F K authKey hr
  have hins := runT_inSync F K authKey hr
  unfold InSync at hins
  cases hek : ekSide e <;> rw [hek] at hins
  · have hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64 := rawAuth_of_wf auth hrk hins.hauth
    exact ⟨xShapeE_raw_le F K e auth c stA hauth hins.hkem hins.hx,
      yShapeE_raw_le F K e auth c stB hauth hins.hkem hins.hy⟩
  · have hauth : rawAuth ((spqrAuthApi F).into_pb auth) ≤ 64 := rawAuth_of_wf auth hrk hins.hauth
    exact ⟨yShapeE_raw_le F K e auth c stA hauth hins.hkem hins.hy,
      xShapeE_raw_le F K e auth c stB hauth hins.hkem hins.hx⟩

/-- Serialized state bytes of a `PartyTop` state have length `< 2 ^ 64` under bounded `authKey`,
epoch count, cumulative received indices, and `rawV1State ≤ 2 ^ 40`. -/
theorem partyTop_length_lt (F : ShaCompress) (K : MlKem) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (st : St F) (sendEp : ℕ) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (bytes : Bytes) (h : PartyTop F K authKey dir secret st sendEp sendCtr recvSet bytes)
    (hauth : authKey.length ≤ 2 ^ 40) (hcur : chainCur st ≤ 2 ^ 40)
    (hrecv : ∑ e ∈ Finset.range (chainCur st + 1), (recvSet e).sup id ≤ 2 ^ 40)
    (hbraid : rawV1State st.into_pb ≤ 2 ^ 40) :
    bytes.length < 2 ^ 64 := by
  rcases h with ⟨vn?, ch?, chE, hw⟩
  rw [hw.hbytes]
  have htop := topBytes_length_le F K st vn? ch?
  have hvn_le : optRaw rawVN vn? ≤ authKey.length := by
    rcases hw.hvn with rfl | rfl
    · simp [optRaw]
    · simp [optRaw, rawVN, vnOf]
  have hch_le : optRaw rawChain (ch?.map Chain.intoPb) ≤ rawChain chE.intoPb := by
    rcases hw.hch with rfl | ⟨rfl, _, _⟩
    · simp [optRaw]
    · simp [optRaw]
  have hraw := chainOk_rawChain_le F authKey dir secret sendCtr recvSet chE hw.hok hw.hsendPrev
  rw [hw.hcur] at hraw
  have hsum :
      (∑ e ∈ Finset.range (chainCur st + 1), (264 + 36 * (recvSet e).sup id)) =
        (chainCur st + 1) * 264 + 36 * ∑ e ∈ Finset.range (chainCur st + 1), (recvSet e).sup id := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum]
  omega

end CryptoVerification.SpqrV1Sync.TopSync
