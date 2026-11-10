/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.Append
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
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
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
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs

/-!
# SPQR V1: Proto Wire Size Measures and Decode Growth Bounds

**Checked by Lean.**

Defines linear payload size measures (`rawEpochDir`, `rawChainEpoch`, `rawChain`, `rawAuth`,
`rawPolyEnc`, `rawPolyDec`, `rawV1State`, `rawVN`, `rawPqState`) and proves `.encodeRaw.length` /
`.encodedLen` upper bounds together with `MergeFieldBound` and `rawPqState st ≤ 201 * bs.length`
for `Proto.decodeState` and `Proto.spqrDecodeState`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.StateSize

open CryptoGames.HMAC (toBEBytes)
open CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge
set_option maxHeartbeats 400000

/-! ## Primitive `Proto` Wire Encoding Length Upper Bounds -/

theorem encodeVarintAux_length_le (fuel : Nat) (v : BitVec 64) :
    (Proto.encodeVarintAux fuel v).length ≤ fuel + 1 := by
  induction fuel generalizing v with
  | zero => simp [Proto.encodeVarintAux]
  | succ fuel' ih =>
    simp only [Proto.encodeVarintAux]
    by_cases hv : v < 0x80#64
    · simp [hv]
    · simp only [hv, ↓reduceIte, List.length_cons]
      have h := ih (v >>> 7)
      omega

theorem encodeVarint_length_le (v : BitVec 64) : (Proto.encodeVarint v).length ≤ 11 :=
  encodeVarintAux_length_le 10 v

theorem encodeKey_length_le (tag : BitVec 32) (wt : Proto.WireType) :
    (Proto.encodeKey tag wt).length ≤ 11 :=
  encodeVarint_length_le _

/-- Lift a `Nat`-valued size measure to `Option α` (`0` on `none`). -/
def optRaw {α : Type} (f : α → Nat) : Option α → Nat
  | none => 0
  | some x => f x

@[simp] theorem optRaw_some {α : Type} (f : α → Nat) (x : α) : optRaw f (some x) = f x := rfl

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

def rawVN (m : VersionNegotiationPB) : Nat := m.authKey.length


/-! ## Payload Size Measures and `MergeFieldBound` -/

section MoveCompat
open CryptoVerification.SpqrV1.ProtoRepr

private theorem encodedLenVarint_le (v : BitVec 64) : Proto.encodedLenVarint v ≤ 11 :=
  encodeVarint_length_le v

private theorem keyLen_le (tag : BitVec 32) : Proto.keyLen tag ≤ 11 :=
  encodedLenVarint_le _

private theorem encodeUint32Field_length_le (tag : BitVec 32) (v : BitVec 32) :
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

private theorem encodeBoolField_length_le (tag : BitVec 32) (v : Bool) :
    (Proto.encodeBoolField tag v).length ≤ 12 := by
  unfold Proto.encodeBoolField
  split
  · rw [List.length_append]; have h1 := encodeKey_length_le tag .varint; simp; omega
  · simp

private theorem encodeBytesUncond_length_le (tag : BitVec 32) (v : Bytes) :
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

private theorem encodeRepeatedBytes_length_le (tag : BitVec 32) (vs : List Bytes) :
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

@[simp] theorem optRaw_none {α : Type} (f : α → Nat) : optRaw f none = 0 := rfl

private theorem optRaw_getD_default {α : Type} [Inhabited α] (f : α → Nat) (h0 : f default = 0)
    (opt : Option α) : f (opt.getD default) = optRaw f opt := by
  cases opt with
  | none => exact h0
  | some _ => rfl

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

private theorem encodeRepeatedMessage_length_le {M : Type} (encodeRaw : M → Bytes) (f : M → Nat) (C : Nat)
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

private def rawUcEkReceived (m : V1State.Unchunked.EkReceived) : Nat :=
  optRaw rawAuth m.auth + m.hdr.length + m.ek.length

def rawPqInner : PqRatchetState.Inner → Nat | .v1 v => rawV1State v

def rawPqState (m : PqRatchetState) : Nat :=
  optRaw rawVN m.versionNegotiation + optRaw rawChain m.chain + optRaw rawPqInner m.inner

private theorem chainParamsPB_encodeRaw_length_le (m : ChainParamsPB) :
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

private theorem epochDirectionPB_encodeRaw_length_le (m : EpochDirectionPB) :
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

private theorem chainPB_encodeRaw_length_le (m : ChainPB) :
    (ChainPB.encodeRaw m).length ≤ rawChain m + 154 := by
  unfold ChainPB.encodeRaw rawChain; simp only [List.length_append]
  have h1 := encodeInt32Field_length_le 1#32 m.direction
  have h2 := encodeUint64Field_length_le 2#32 m.currentEpoch
  have h3 := encodeRepeatedMessage_length_le ChainEpochPB.encodeRaw rawChainEpoch 200
    (fun ep => by have := chainEpochPB_encodeRaw_length_le ep; omega) 3#32 m.links
  have h4 := encodeBytesField_length_le 4#32 m.nextRoot
  have h5 := encodeUint64Field_length_le 5#32 m.sendEpoch
  have h6 := encodeOptChainParams_length_le 6#32 m.params; omega

theorem chainPBEncodedLen_le_rawChain (m : ChainPB) :
    chainPBEncodedLen m ≤ rawChain m + 154 := by
  rw [← chainPBEncodedLen_eq_proto]; exact chainPB_encodeRaw_length_le m

private theorem versionNegotiationPB_encodeRaw_length_le (m : VersionNegotiationPB) :
    (VersionNegotiationPB.encodeRaw m).length ≤ rawVN m + 132 := by
  unfold VersionNegotiationPB.encodeRaw rawVN; simp only [List.length_append]
  have h1 := encodeBytesField_length_le 1#32 m.authKey
  have h2 := encodeInt32Field_length_le 2#32 m.direction
  have h3 := encodeInt32Field_length_le 3#32 m.minVersion
  have h4 := encodeOptChainParams_length_le 4#32 m.chainParams; omega

private theorem protoAuthenticator_encodeRaw_length_le (m : ProtoAuthenticator) :
    (ProtoAuthenticator.encodeRaw m).length ≤ rawAuth m + 44 := by
  unfold ProtoAuthenticator.encodeRaw rawAuth; rw [List.length_append]
  have h1 := encodeBytesField_length_le 1#32 m.rootKey
  have h2 := encodeBytesField_length_le 2#32 m.macKey; omega

private theorem polynomialEncoder_encodeRaw_length_le (m : PolynomialEncoder) :
    (PolynomialEncoder.encodeRaw m).length ≤ rawPolyEnc m + 22 := by
  unfold PolynomialEncoder.encodeRaw rawPolyEnc; simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.idx
  have h2 := encodeRepeatedBytes_length_le 2#32 m.pts
  have h3 := encodeRepeatedBytes_length_le 3#32 m.polys; omega

private theorem polynomialDecoder_encodeRaw_length_le (m : PolynomialDecoder) :
    (PolynomialDecoder.encodeRaw m).length ≤ rawPolyDec m + 56 := by
  unfold PolynomialDecoder.encodeRaw rawPolyDec; simp only [List.length_append]
  have h1 := encodeUint32Field_length_le 1#32 m.ptsNeeded
  have h2 := encodeUint32Field_length_le 2#32 m.polys
  have h3 := encodeRepeatedBytes_length_le 3#32 m.pts
  have h4 := encodeBoolField_length_le 4#32 m.isComplete; omega

private theorem ucKeysUnsampled_encodeRaw_length_le (m : V1State.Unchunked.KeysUnsampled) :
    (V1State.Unchunked.KeysUnsampled.encodeRaw m).length ≤ rawUcKeysUnsampled m + 88 := by
  unfold V1State.Unchunked.KeysUnsampled.encodeRaw rawUcKeysUnsampled; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega

private theorem ucHeaderSent_encodeRaw_length_le (m : V1State.Unchunked.HeaderSent) :
    (V1State.Unchunked.HeaderSent.encodeRaw m).length ≤ rawUcHeaderSent m + 132 := by
  unfold V1State.Unchunked.HeaderSent.encodeRaw rawUcHeaderSent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.ek
  have h4 := encodeBytesField_length_le 4#32 m.dk; omega

private theorem ucEkSent_encodeRaw_length_le (m : V1State.Unchunked.EkSent) :
    (V1State.Unchunked.EkSent.encodeRaw m).length ≤ rawUcEkSent m + 110 := by
  unfold V1State.Unchunked.EkSent.encodeRaw rawUcEkSent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.dk; omega

private theorem ucEkSentCt1Received_encodeRaw_length_le (m : V1State.Unchunked.EkSentCt1Received) :
    (V1State.Unchunked.EkSentCt1Received.encodeRaw m).length ≤ rawUcEkSentCt1Received m + 132 := by
  unfold V1State.Unchunked.EkSentCt1Received.encodeRaw rawUcEkSentCt1Received
  simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.dk
  have h4 := encodeBytesField_length_le 4#32 m.ct1; omega

private theorem ucNoHeaderReceived_encodeRaw_length_le (m : V1State.Unchunked.NoHeaderReceived) :
    (V1State.Unchunked.NoHeaderReceived.encodeRaw m).length ≤ rawUcNoHeaderReceived m + 88 := by
  unfold V1State.Unchunked.NoHeaderReceived.encodeRaw rawUcNoHeaderReceived; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega

private theorem ucHeaderReceived_encodeRaw_length_le (m : V1State.Unchunked.HeaderReceived) :
    (V1State.Unchunked.HeaderReceived.encodeRaw m).length ≤ rawUcHeaderReceived m + 110 := by
  unfold V1State.Unchunked.HeaderReceived.encodeRaw rawUcHeaderReceived; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.hdr; omega

private theorem ucCt1Sent_encodeRaw_length_le (m : V1State.Unchunked.Ct1Sent) :
    (V1State.Unchunked.Ct1Sent.encodeRaw m).length ≤ rawUcCt1Sent m + 154 := by
  unfold V1State.Unchunked.Ct1Sent.encodeRaw rawUcCt1Sent; simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.hdr
  have h4 := encodeBytesField_length_le 4#32 m.es
  have h5 := encodeBytesField_length_le 5#32 m.ct1; omega

private theorem ucCt1SentEkReceived_encodeRaw_length_le (m : V1State.Unchunked.Ct1SentEkReceived) :
    (V1State.Unchunked.Ct1SentEkReceived.encodeRaw m).length ≤ rawUcCt1SentEkReceived m + 154 := by
  unfold V1State.Unchunked.Ct1SentEkReceived.encodeRaw rawUcCt1SentEkReceived
  simp only [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth
  have h3 := encodeBytesField_length_le 3#32 m.es
  have h4 := encodeBytesField_length_le 4#32 m.ek
  have h5 := encodeBytesField_length_le 5#32 m.ct1; omega

private theorem ucCt2Sent_encodeRaw_length_le (m : V1State.Unchunked.Ct2Sent) :
    (V1State.Unchunked.Ct2Sent.encodeRaw m).length ≤ rawUcCt2Sent m + 88 := by
  unfold V1State.Unchunked.Ct2Sent.encodeRaw rawUcCt2Sent; rw [List.length_append]
  have h1 := encodeUint64Field_length_le 1#32 m.epoch
  have h2 := encodeOptMessage_length_le ProtoAuthenticator.encodeRaw rawAuth 44
    protoAuthenticator_encodeRaw_length_le 2#32 m.auth; omega

private theorem chKeysUnsampled_encodeRaw_length_le (v : V1State.Chunked.KeysUnsampled) :
    (V1State.Chunked.KeysUnsampled.encodeRaw v).length ≤ rawChKeysUnsampled v + 110 :=
  encodeOptMessage_length_le _ rawUcKeysUnsampled 88 ucKeysUnsampled_encodeRaw_length_le 1#32 v.uc

private theorem chKeysSampled_encodeRaw_length_le (v : V1State.Chunked.KeysSampled) :
    (V1State.Chunked.KeysSampled.encodeRaw v).length ≤ rawChKeysSampled v + 198 := by
  unfold V1State.Chunked.KeysSampled.encodeRaw rawChKeysSampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcHeaderSent 132 ucHeaderSent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingHdr
  omega

private theorem chHeaderSent_encodeRaw_length_le (v : V1State.Chunked.HeaderSent) :
    (V1State.Chunked.HeaderSent.encodeRaw v).length ≤ rawChHeaderSent v + 254 := by
  unfold V1State.Chunked.HeaderSent.encodeRaw rawChHeaderSent; simp only [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSent 110 ucEkSent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingEk
  have h3 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingCt1; omega

private theorem chCt1Received_encodeRaw_length_le (v : V1State.Chunked.Ct1Received) :
    (V1State.Chunked.Ct1Received.encodeRaw v).length ≤ rawChCt1Received v + 198 := by
  unfold V1State.Chunked.Ct1Received.encodeRaw rawChCt1Received; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingEk; omega

private theorem chEkSentCt1Received_encodeRaw_length_le (v : V1State.Chunked.EkSentCt1Received) :
    (V1State.Chunked.EkSentCt1Received.encodeRaw v).length ≤ rawChEkSentCt1Received v + 232 := by
  unfold V1State.Chunked.EkSentCt1Received.encodeRaw rawChEkSentCt1Received; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcEkSentCt1Received 132 ucEkSentCt1Received_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingCt2; omega

private theorem chNoHeaderReceived_encodeRaw_length_le (v : V1State.Chunked.NoHeaderReceived) :
    (V1State.Chunked.NoHeaderReceived.encodeRaw v).length ≤ rawChNoHeaderReceived v + 188 := by
  unfold V1State.Chunked.NoHeaderReceived.encodeRaw rawChNoHeaderReceived; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcNoHeaderReceived 88 ucNoHeaderReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingHdr; omega

private theorem chHeaderReceived_encodeRaw_length_le (v : V1State.Chunked.HeaderReceived) :
    (V1State.Chunked.HeaderReceived.encodeRaw v).length ≤ rawChHeaderReceived v + 210 := by
  unfold V1State.Chunked.HeaderReceived.encodeRaw rawChHeaderReceived; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcHeaderReceived 110 ucHeaderReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingEk; omega

private theorem chCt1Sampled_encodeRaw_length_le (v : V1State.Chunked.Ct1Sampled) :
    (V1State.Chunked.Ct1Sampled.encodeRaw v).length ≤ rawChCt1Sampled v + 298 := by
  unfold V1State.Chunked.Ct1Sampled.encodeRaw rawChCt1Sampled; simp only [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt1
  have h3 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 3#32 v.receivingEk; omega

private theorem chEkReceivedCt1Sampled_encodeRaw_length_le (v : V1State.Chunked.EkReceivedCt1Sampled) :
    (V1State.Chunked.EkReceivedCt1Sampled.encodeRaw v).length ≤ rawChEkReceivedCt1Sampled v + 220 := by
  unfold V1State.Chunked.EkReceivedCt1Sampled.encodeRaw rawChEkReceivedCt1Sampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1SentEkReceived 154 ucCt1SentEkReceived_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt1; omega

private theorem chCt1Acknowledged_encodeRaw_length_le (v : V1State.Chunked.Ct1Acknowledged) :
    (V1State.Chunked.Ct1Acknowledged.encodeRaw v).length ≤ rawChCt1Acknowledged v + 254 := by
  unfold V1State.Chunked.Ct1Acknowledged.encodeRaw rawChCt1Acknowledged; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt1Sent 154 ucCt1Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyDec 56 polynomialDecoder_encodeRaw_length_le 2#32 v.receivingEk; omega

private theorem chCt2Sampled_encodeRaw_length_le (v : V1State.Chunked.Ct2Sampled) :
    (V1State.Chunked.Ct2Sampled.encodeRaw v).length ≤ rawChCt2Sampled v + 154 := by
  unfold V1State.Chunked.Ct2Sampled.encodeRaw rawChCt2Sampled; rw [List.length_append]
  have h1 := encodeOptMessage_length_le _ rawUcCt2Sent 88 ucCt2Sent_encodeRaw_length_le 1#32 v.uc
  have h2 := encodeOptMessage_length_le _ rawPolyEnc 22 polynomialEncoder_encodeRaw_length_le 2#32 v.sendingCt2; omega

private theorem innerState_encode_length_le (is : V1State.InnerState) :
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

private theorem pqRatchetState_encodedLen_le_rawPqState (m : PqRatchetState) :
    PqRatchetState.encodedLen m ≤ rawPqState m + 752 :=
  encodeState_length_le_rawPqState m

def MergeFieldBound {M : Type}
    (mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes))
    (rawM : M → Nat) (K : Nat) : Prop :=
  ∀ (m : M) (tag : BitVec 32) (wt : Proto.WireType) (rest : Bytes) (depth : Nat)
    (m' : M) (rest' : Bytes),
    mergeField m tag wt rest depth = .ok (m', rest') →
    rest'.length ≤ rest.length ∧ rawM m' ≤ rawM m + K * (rest.length - rest'.length + 1)

theorem mergeFieldsLoop_raw_le {M : Type}
    {mergeField : M → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (M × Bytes)}
    {rawM : M → Nat} {K : Nat} (hb : MergeFieldBound mergeField rawM K) :
    ∀ (fuel : Nat) (m : M) (bs : Bytes) (depth : Nat) (m' : M),
      Proto.mergeFieldsLoop mergeField fuel m bs depth = .ok m' →
      rawM m' ≤ rawM m + K * bs.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro m bs depth m' h; cases bs with
    | nil => simp only [Proto.mergeFieldsLoop, Except.ok.injEq] at h; subst h; simp
    | cons _ _ => nomatch h
  | succ fuel ih =>
    intro m bs depth m' h; cases bs with
    | nil => simp only [Proto.mergeFieldsLoop, Except.ok.injEq] at h; subst h; simp
    | cons b tl =>
      simp only [Proto.mergeFieldsLoop] at h
      rcases hdk : Proto.decodeKey (b :: tl) with e | ⟨⟨tag, wt⟩, rest⟩
      · simp [hdk, Bind.bind, Except.bind] at h
      · have hlt1 : rest.length < (b :: tl).length := decodeKey_length_lt hdk
        simp only [hdk, Bind.bind, Except.bind] at h
        rcases hmf : mergeField m tag wt rest depth with e | ⟨m1, rest'⟩
        · simp [hmf] at h
        · simp only [hmf] at h
          obtain ⟨hle2, hraw1⟩ := hb m tag wt rest depth m1 rest' hmf
          have hraw2 := ih m1 rest' depth m' h
          have hmul : K * (rest.length - rest'.length + 1) + K * rest'.length ≤
              K * (b :: tl).length := by
            rw [← Nat.mul_add]; exact Nat.mul_le_mul_left K (by omega)
          omega

theorem skipField_length_le {wt : Proto.WireType} {tag : BitVec 32} {rest : Bytes}
    {depth : Nat} {rest' : Bytes} (h : Proto.skipField wt tag rest depth = .ok rest') :
    rest'.length ≤ rest.length := (skipField_append_of_ok [] h).1

private theorem mergeUint32_length_le {wt : Proto.WireType} {rest : Bytes} {v : BitVec 32} {rest' : Bytes}
    (h : Proto.mergeUint32 wt rest = .ok (v, rest')) : rest'.length ≤ rest.length :=
  (protoPrefixStep_mergeUint32 wt).length_le h

private theorem mergeUint64_length_le {wt : Proto.WireType} {rest : Bytes} {v : BitVec 64} {rest' : Bytes}
    (h : Proto.mergeUint64 wt rest = .ok (v, rest')) : rest'.length ≤ rest.length :=
  (protoPrefixStep_mergeUint64 wt).length_le h

private theorem mergeInt32_length_le {wt : Proto.WireType} {rest : Bytes} {v : BitVec 32} {rest' : Bytes}
    (h : Proto.mergeInt32 wt rest = .ok (v, rest')) : rest'.length ≤ rest.length :=
  (protoPrefixStep_mergeInt32 wt).length_le h

private theorem mergeBool_length_le {wt : Proto.WireType} {rest : Bytes} {v : Bool} {rest' : Bytes}
    (h : Proto.mergeBool wt rest = .ok (v, rest')) : rest'.length ≤ rest.length :=
  (protoPrefixStep_mergeBool wt).length_le h

private theorem mergeBytes_length_le {wt : Proto.WireType} {rest : Bytes} {v rest' : Bytes}
    (h : Proto.mergeBytes wt rest = .ok (v, rest')) :
    rest'.length ≤ rest.length ∧ v.length ≤ rest.length - rest'.length := by
  unfold Proto.mergeBytes Proto.checkWireType at h
  split at h
  · nomatch h
  · simp only [Bind.bind, Except.bind] at h
    rcases hdv : Proto.decodeVarint rest with e | ⟨len, r0⟩
    · simp [hdv] at h
    · have hlt : r0.length < rest.length := decodeVarint_length_lt hdv
      simp only [hdv, takeExact_eq_take_drop] at h
      split at h
      · rename_i hle
        injection h with hpair; injection hpair with hv hr; subst hv hr
        simp only [List.length_take_of_le hle, List.length_drop]; omega
      · nomatch h

private theorem mergeRepeatedBytes_raw_le {wt : Proto.WireType} {vs : List Bytes} {rest : Bytes}
    {vs' : List Bytes} {rest' : Bytes}
    (h : Proto.mergeRepeatedBytes wt vs rest = .ok (vs', rest')) :
    rest'.length ≤ rest.length ∧
      (vs'.map (fun b => b.length + 22)).sum ≤
        (vs.map (fun b => b.length + 22)).sum + 22 * (rest.length - rest'.length + 1) := by
  unfold Proto.mergeRepeatedBytes at h
  rcases hmb : Proto.mergeBytes wt rest with e | ⟨v, r'⟩
  · simp [hmb, Bind.bind, Except.bind] at h
  · simp only [hmb, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨hle, hv⟩ := mergeBytes_length_le hmb
    refine ⟨hle, ?_⟩
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega

theorem mergeMessage_raw_le {S : Type}
    {mergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes)}
    {rawS : S → Nat} {K : Nat} (hb : MergeFieldBound mergeField rawS K)
    {wt : Proto.WireType} {m0 : S} {rest : Bytes} {depth : Nat} {s' : S} {rest' : Bytes}
    (h : Proto.mergeMessage mergeField wt m0 rest depth = .ok (s', rest')) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS m0 + K * (rest.length - rest'.length) := by
  unfold Proto.mergeMessage Proto.checkWireType at h
  split at h
  · nomatch h
  · cases depth with
    | zero => nomatch h
    | succ depth' =>
      simp only [Bind.bind, Except.bind] at h
      rcases hdv : Proto.decodeVarint rest with e | ⟨len, r0⟩
      · simp [hdv] at h
      · have hlt : r0.length < rest.length := decodeVarint_length_lt hdv
        simp only [hdv] at h
        rcases hte : Proto.takeExact len.toNat r0 with e | ⟨sub, after⟩
        · simp [hte] at h
        · simp only [hte] at h
          rcases hloop : Proto.mergeFieldsLoop mergeField sub.length m0 sub depth' with e | s1
          · simp [hloop] at h
          · simp only [hloop, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hraw := mergeFieldsLoop_raw_le hb sub.length m0 sub depth' s1 hloop
            rw [takeExact_eq_take_drop] at hte
            split at hte
            · rename_i hle
              simp only [Except.ok.injEq, Prod.mk.injEq] at hte
              obtain ⟨rfl, rfl⟩ := hte
              simp only [List.length_take_of_le hle, List.length_drop] at hraw ⊢
              refine ⟨by omega, ?_⟩
              have hmul : K * len.toNat ≤ K * (rest.length - (r0.length - len.toNat)) :=
                Nat.mul_le_mul_left K (by omega)
              omega
            · nomatch hte

theorem mergeOptMessage_raw_le {S : Type} [Inhabited S]
    {mergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes)}
    {rawS : S → Nat} {K : Nat} (hb : MergeFieldBound mergeField rawS K) (hdef : rawS default = 0)
    {wt : Proto.WireType} {opt : Option S} {rest : Bytes} {depth : Nat}
    {opt' : Option S} {rest' : Bytes}
    (h : Proto.mergeOptMessage mergeField wt opt rest depth = .ok (opt', rest')) :
    rest'.length ≤ rest.length ∧
      optRaw rawS opt' ≤ optRaw rawS opt + K * (rest.length - rest'.length) := by
  unfold Proto.mergeOptMessage at h
  rcases hmm : Proto.mergeMessage mergeField wt (opt.getD default) rest depth with e | ⟨s', r'⟩
  · simp [hmm, Bind.bind, Except.bind] at h
  · simp only [hmm, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨hle, hraw⟩ := mergeMessage_raw_le hb hmm
    rw [optRaw_getD_default rawS hdef] at hraw
    exact ⟨hle, hraw⟩

private theorem mergeRepeatedMessage_raw_le {S : Type} [Inhabited S]
    {mergeField : S → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (S × Bytes)}
    {rawS : S → Nat} {K : Nat} (hb : MergeFieldBound mergeField rawS K) (hdef : rawS default = 0)
    (C : Nat) {wt : Proto.WireType} {ms : List S} {rest : Bytes} {depth : Nat}
    {ms' : List S} {rest' : Bytes}
    (h : Proto.mergeRepeatedMessage mergeField wt ms rest depth = .ok (ms', rest')) :
    rest'.length ≤ rest.length ∧
      (ms'.map (fun s => rawS s + C)).sum ≤
        (ms.map (fun s => rawS s + C)).sum + (K + C) * (rest.length - rest'.length + 1) := by
  unfold Proto.mergeRepeatedMessage at h
  rcases hmm : Proto.mergeMessage mergeField wt default rest depth with e | ⟨s', r'⟩
  · simp [hmm, Bind.bind, Except.bind] at h
  · simp only [hmm, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hle, hraw⟩ := mergeMessage_raw_le hb hmm
    rw [hdef, Nat.zero_add] at hraw
    refine ⟨hle, ?_⟩
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    have hmul : rawS s' + C ≤ (K + C) * (rest.length - r'.length + 1) := by
      rw [Nat.add_mul]
      have h1 : K * (rest.length - r'.length) ≤ K * (rest.length - r'.length + 1) :=
        Nat.mul_le_mul_left K (by omega)
      have h2 : C ≤ C * (rest.length - r'.length + 1) := by
        simpa using Nat.mul_le_mul_left C (show 1 ≤ rest.length - r'.length + 1 by omega)
      omega
    omega

@[simp, reducible] private def unOk {S : Type} (s : S) : Except Proto.DecodeErr (S × Bytes) → S
  | .ok (s', _) => s'
  | .error _ => s

private theorem branch_ite {S : Type} {R : Prop} {c : Bool} [Decidable (c = true)]
    {a b : Except Proto.DecodeErr (S × Bytes)} {x : S × Bytes}
    (h : (if c then a else b) = .ok x)
    (ha : a = .ok x → R) (hb : b = .ok x → R) : R := by
  split at h
  · exact ha h
  · exact hb h

private theorem bind_pair_ok {S α : Type} {e : Except Proto.DecodeErr (α × Bytes)}
    {k : α × Bytes → Except Proto.DecodeErr (S × Bytes)} {s s' : S} {rest' : Bytes}
    (h : Bind.bind e k = .ok (s', rest'))
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs')) :
    ∃ v, e = .ok (v, rest') ∧ s' = unOk s (k (v, rest')) := by
  rcases he : e with err | ⟨v, bs'⟩
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind] at h
    rw [hk v bs'] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨v, rfl, rfl⟩

private theorem bind_skip_ok {S : Type} {e : Except Proto.DecodeErr Bytes}
    {s s' : S} {rest' : Bytes}
    (h : Bind.bind e (fun bs' => Except.ok (s, bs')) = .ok (s', rest')) :
    e = .ok rest' ∧ s' = s := by
  rcases he : e with err | bs'
  · simp [he, Bind.bind, Except.bind] at h
  · simp only [he, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2 ▸ rfl, h.1.symm⟩

private theorem branch_uint32 {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {k : BitVec 32 × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeUint32 wt rest) k = .ok (s', rest'))
    (hg : ∀ v, rawS (unOk s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  rw [hg]; exact ⟨mergeUint32_length_le he, Nat.le_add_right _ _⟩

private theorem branch_uint64 {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {k : BitVec 64 × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeUint64 wt rest) k = .ok (s', rest'))
    (hg : ∀ v, rawS (unOk s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  rw [hg]; exact ⟨mergeUint64_length_le he, Nat.le_add_right _ _⟩

private theorem branch_int32 {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {k : BitVec 32 × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeInt32 wt rest) k = .ok (s', rest'))
    (hg : ∀ v, rawS (unOk s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  rw [hg]; exact ⟨mergeInt32_length_le he, Nat.le_add_right _ _⟩

private theorem branch_bool {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {k : Bool × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeBool wt rest) k = .ok (s', rest'))
    (hg : ∀ v, rawS (unOk s (k (v, rest'))) = rawS s)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  rw [hg]; exact ⟨mergeBool_length_le he, Nat.le_add_right _ _⟩

private theorem branch_skip {S : Type} {rawS : S → Nat} {K : Nat} {s s' : S}
    {wt : Proto.WireType} {tag : BitVec 32} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.skipField wt tag rest depth) (fun bs' => Except.ok (s, bs')) = .ok (s', rest')) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨he, rfl⟩ := bind_skip_ok h
  exact ⟨skipField_length_le he, Nat.le_add_right _ _⟩

private theorem branch_bytes {S : Type} {rawS : S → Nat} {K : Nat}
    {s s' : S} {k : Bytes × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeBytes wt rest) k = .ok (s', rest'))
    (hK : 1 ≤ K) (hg : ∀ v, rawS (unOk s (k (v, rest'))) ≤ rawS s + v.length)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  obtain ⟨hle, hv⟩ := mergeBytes_length_le he
  refine ⟨hle, ?_⟩
  have hgv := hg v
  have hmul : 1 * (rest.length - rest'.length + 1) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.mul_le_mul_right _ hK
  omega

private theorem branch_repeatedBytes {S : Type} {rawS : S → Nat} {K : Nat}
    {s s' : S} {old : List Bytes}
    {k : List Bytes × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes}
    (h : Bind.bind (Proto.mergeRepeatedBytes wt old rest) k = .ok (s', rest'))
    (hK : 22 ≤ K)
    (hg : ∀ v, (old.map (fun b => b.length + 22)).sum + rawS (unOk s (k (v, rest'))) ≤
      rawS s + (v.map (fun b => b.length + 22)).sum)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  obtain ⟨hle, hv⟩ := mergeRepeatedBytes_raw_le he
  refine ⟨hle, ?_⟩
  have hgv := hg v
  have hmul : 22 * (rest.length - rest'.length + 1) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.mul_le_mul_right _ hK
  omega

private theorem branch_optMessage {S Sub : Type} [Inhabited Sub]
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat} {K : Nat}
    {s s' : S} {old : Option Sub}
    {k : Option Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeOptMessage mergeSub wt old rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hdef : rawSub default = 0) (hK : Ksub ≤ K)
    (hg : ∀ v, optRaw rawSub old + rawS (unOk s (k (v, rest'))) ≤ rawS s + optRaw rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  obtain ⟨hle, hv⟩ := mergeOptMessage_raw_le hb hdef he
  refine ⟨hle, ?_⟩
  have hgv := hg v
  have hmul : Ksub * (rest.length - rest'.length) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hK) (Nat.mul_le_mul_left K (by omega))
  omega

private theorem branch_repeatedMessage {S Sub : Type} [Inhabited Sub]
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat} (C : Nat)
    {rawS : S → Nat} {K : Nat}
    {s s' : S} {old : List Sub}
    {k : List Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeRepeatedMessage mergeSub wt old rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hdef : rawSub default = 0) (hK : Ksub + C ≤ K)
    (hg : ∀ v, (old.map (fun x => rawSub x + C)).sum + rawS (unOk s (k (v, rest'))) ≤
      rawS s + (v.map (fun x => rawSub x + C)).sum)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  obtain ⟨hle, hv⟩ := mergeRepeatedMessage_raw_le hb hdef C he
  refine ⟨hle, ?_⟩
  have hgv := hg v
  have hmul : (Ksub + C) * (rest.length - rest'.length + 1) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.mul_le_mul_right _ hK
  omega

private theorem branch_oneofMessage {S Sub : Type}
    {mergeSub : Sub → BitVec 32 → Proto.WireType → Bytes → Nat → Except Proto.DecodeErr (Sub × Bytes)}
    {rawSub : Sub → Nat} {Ksub : Nat}
    {rawS : S → Nat} {K : Nat}
    {s s' : S} {prev : Sub}
    {k : Sub × Bytes → Except Proto.DecodeErr (S × Bytes)}
    {wt : Proto.WireType} {rest rest' : Bytes} {depth : Nat}
    (h : Bind.bind (Proto.mergeMessage mergeSub wt prev rest depth) k = .ok (s', rest'))
    (hb : MergeFieldBound mergeSub rawSub Ksub) (hK : Ksub ≤ K)
    (hprev : rawSub prev ≤ rawS s) (hg : ∀ v, rawS (unOk s (k (v, rest'))) = rawSub v)
    (hk : ∀ v bs', k (v, bs') = .ok (unOk s (k (v, bs')), bs') := by intro _ _; rfl) :
    rest'.length ≤ rest.length ∧ rawS s' ≤ rawS s + K * (rest.length - rest'.length + 1) := by
  obtain ⟨v, he, rfl⟩ := bind_pair_ok h hk
  obtain ⟨hle, hv⟩ := mergeMessage_raw_le hb he
  refine ⟨hle, ?_⟩
  rw [hg]
  have hmul : Ksub * (rest.length - rest'.length) ≤ K * (rest.length - rest'.length + 1) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hK) (Nat.mul_le_mul_left K (by omega))
  omega

private def rawChainParams (_ : ChainParamsPB) : Nat := 0

private theorem mergeFieldBound_chainParams : MergeFieldBound ChainParamsPB.mergeField rawChainParams 0 := by
  intro s tag wt rest depth s' rest' h
  unfold ChainParamsPB.mergeField at h
  exact branch_ite h (fun h => branch_uint32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_uint32 h (fun _ => rfl)) branch_skip)

private theorem mergeFieldBound_epochDir : MergeFieldBound EpochDirectionPB.mergeField rawEpochDir 1 := by
  intro s tag wt rest depth s' rest' h
  unfold EpochDirectionPB.mergeField at h
  exact branch_ite h (fun h => branch_uint32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawEpochDir]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawEpochDir]))
      branch_skip))

private theorem mergeFieldBound_chainEpoch : MergeFieldBound ChainEpochPB.mergeField rawChainEpoch 1 := by
  intro s tag wt rest depth s' rest' h
  unfold ChainEpochPB.mergeField at h
  exact branch_ite h
    (fun h => branch_optMessage h mergeFieldBound_epochDir rfl (by omega) (fun v => by simp [rawChainEpoch]; omega))
    (fun h => branch_ite h
      (fun h => branch_optMessage h mergeFieldBound_epochDir rfl (by omega) (fun v => by simp [rawChainEpoch]; omega))
      branch_skip)

theorem mergeFieldBound_chain : MergeFieldBound ChainPB.mergeField rawChain 201 := by
  intro s tag wt rest depth s' rest' h
  unfold ChainPB.mergeField at h
  exact branch_ite h (fun h => branch_int32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_repeatedMessage 200 h mergeFieldBound_chainEpoch rfl (by omega) (fun v => by simp [rawChain]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawChain]))
    (fun h => branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_chainParams rfl (by omega)
        (fun v => by cases s.params <;> cases v <;> simp [optRaw, rawChainParams, rawChain]))
      branch_skip)))))

theorem mergeFieldBound_vn : MergeFieldBound VersionNegotiationPB.mergeField rawVN 1 := by
  intro s tag wt rest depth s' rest' h
  unfold VersionNegotiationPB.mergeField at h
  exact branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawVN]))
    (fun h => branch_ite h (fun h => branch_int32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_int32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_chainParams rfl (by omega)
        (fun v => by cases s.chainParams <;> cases v <;> simp [optRaw, rawChainParams, rawVN]))
      branch_skip)))

private theorem mergeFieldBound_auth : MergeFieldBound ProtoAuthenticator.mergeField rawAuth 1 := by
  intro s tag wt rest depth s' rest' h
  unfold ProtoAuthenticator.mergeField at h
  exact branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawAuth]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawAuth]))
      branch_skip)

theorem mergeFieldBound_polyEnc : MergeFieldBound PolynomialEncoder.mergeField rawPolyEnc 22 := by
  intro s tag wt rest depth s' rest' h
  unfold PolynomialEncoder.mergeField at h
  exact branch_ite h (fun h => branch_uint32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_repeatedBytes h (by omega) (fun v => by simp [rawPolyEnc]; omega))
    (fun h => branch_ite h (fun h => branch_repeatedBytes h (by omega) (fun v => by simp [rawPolyEnc]; omega))
      branch_skip))

theorem mergeFieldBound_polyDec : MergeFieldBound PolynomialDecoder.mergeField rawPolyDec 22 := by
  intro s tag wt rest depth s' rest' h
  unfold PolynomialDecoder.mergeField at h
  exact branch_ite h (fun h => branch_uint32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_uint32 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_repeatedBytes h (by omega) (fun v => by simp [rawPolyDec]))
    (fun h => branch_ite h (fun h => branch_bool h (fun _ => rfl))
      branch_skip)))

theorem mergeFieldBound_ucKeysUnsampled :
    MergeFieldBound V1State.Unchunked.KeysUnsampled.mergeField rawUcKeysUnsampled 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.KeysUnsampled.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcKeysUnsampled]))
      branch_skip)

private theorem mergeFieldBound_ucHeaderSent :
    MergeFieldBound V1State.Unchunked.HeaderSent.mergeField rawUcHeaderSent 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.HeaderSent.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcHeaderSent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcHeaderSent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcHeaderSent]))
      branch_skip)))

private theorem mergeFieldBound_ucEkSent :
    MergeFieldBound V1State.Unchunked.EkSent.mergeField rawUcEkSent 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.EkSent.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcEkSent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcEkSent]))
      branch_skip))

private theorem mergeFieldBound_ucEkSentCt1Received :
    MergeFieldBound V1State.Unchunked.EkSentCt1Received.mergeField rawUcEkSentCt1Received 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.EkSentCt1Received.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcEkSentCt1Received]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcEkSentCt1Received]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcEkSentCt1Received]))
      branch_skip)))

private theorem mergeFieldBound_ucNoHeaderReceived :
    MergeFieldBound V1State.Unchunked.NoHeaderReceived.mergeField rawUcNoHeaderReceived 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.NoHeaderReceived.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcNoHeaderReceived]))
      branch_skip)

private theorem mergeFieldBound_ucHeaderReceived :
    MergeFieldBound V1State.Unchunked.HeaderReceived.mergeField rawUcHeaderReceived 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.HeaderReceived.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcHeaderReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcHeaderReceived]))
      branch_skip))

private theorem mergeFieldBound_ucEkReceived :
    MergeFieldBound V1State.Unchunked.EkReceived.mergeField rawUcEkReceived 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.EkReceived.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcEkReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcEkReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcEkReceived]))
      branch_skip)))

theorem mergeFieldBound_ucCt1Sent :
    MergeFieldBound V1State.Unchunked.Ct1Sent.mergeField rawUcCt1Sent 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.Ct1Sent.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcCt1Sent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1Sent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1Sent]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1Sent]))
      branch_skip))))

theorem mergeFieldBound_ucCt1SentEkReceived :
    MergeFieldBound V1State.Unchunked.Ct1SentEkReceived.mergeField rawUcCt1SentEkReceived 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.Ct1SentEkReceived.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcCt1SentEkReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1SentEkReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1SentEkReceived]; omega))
    (fun h => branch_ite h (fun h => branch_bytes h (by omega) (fun v => by simp [rawUcCt1SentEkReceived]))
      branch_skip))))

private theorem mergeFieldBound_ucCt2Sent :
    MergeFieldBound V1State.Unchunked.Ct2Sent.mergeField rawUcCt2Sent 1 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.Unchunked.Ct2Sent.mergeField at h
  exact branch_ite h (fun h => branch_uint64 h (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_auth rfl (by omega) (fun v => by simp [rawUcCt2Sent]))
      branch_skip)

theorem mergeFieldBound_chKeysUnsampled : MergeFieldBound V1State.Chunked.KeysUnsampled.mergeField rawChKeysUnsampled 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.KeysUnsampled.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucKeysUnsampled rfl (by omega) (fun v => by simp [rawChKeysUnsampled])) branch_skip

theorem mergeFieldBound_chKeysSampled : MergeFieldBound V1State.Chunked.KeysSampled.mergeField rawChKeysSampled 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.KeysSampled.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucHeaderSent rfl (by omega) (fun v => by simp [rawChKeysSampled]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChKeysSampled]; omega)) branch_skip)

theorem mergeFieldBound_chHeaderSent : MergeFieldBound V1State.Chunked.HeaderSent.mergeField rawChHeaderSent 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.HeaderSent.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucEkSent rfl (by omega) (fun v => by simp [rawChHeaderSent]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChHeaderSent]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChHeaderSent]; omega)) branch_skip))

theorem mergeFieldBound_chCt1Received : MergeFieldBound V1State.Chunked.Ct1Received.mergeField rawChCt1Received 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct1Received.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucEkSentCt1Received rfl (by omega) (fun v => by simp [rawChCt1Received]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChCt1Received]; omega)) branch_skip)

theorem mergeFieldBound_chEkSentCt1Received : MergeFieldBound V1State.Chunked.EkSentCt1Received.mergeField rawChEkSentCt1Received 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.EkSentCt1Received.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucEkSentCt1Received rfl (by omega) (fun v => by simp [rawChEkSentCt1Received]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChEkSentCt1Received]; omega)) branch_skip)

theorem mergeFieldBound_chNoHeaderReceived : MergeFieldBound V1State.Chunked.NoHeaderReceived.mergeField rawChNoHeaderReceived 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.NoHeaderReceived.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucNoHeaderReceived rfl (by omega) (fun v => by simp [rawChNoHeaderReceived]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChNoHeaderReceived]; omega)) branch_skip)

theorem mergeFieldBound_chHeaderReceived : MergeFieldBound V1State.Chunked.HeaderReceived.mergeField rawChHeaderReceived 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.HeaderReceived.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucHeaderReceived rfl (by omega) (fun v => by simp [rawChHeaderReceived]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChHeaderReceived]; omega)) branch_skip)

theorem mergeFieldBound_chCt1Sampled : MergeFieldBound V1State.Chunked.Ct1Sampled.mergeField rawChCt1Sampled 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct1Sampled.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucCt1Sent rfl (by omega) (fun v => by simp [rawChCt1Sampled]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChCt1Sampled]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChCt1Sampled]; omega)) branch_skip))

theorem mergeFieldBound_chEkReceivedCt1Sampled : MergeFieldBound V1State.Chunked.EkReceivedCt1Sampled.mergeField rawChEkReceivedCt1Sampled 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.EkReceivedCt1Sampled.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucCt1SentEkReceived rfl (by omega) (fun v => by simp [rawChEkReceivedCt1Sampled]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChEkReceivedCt1Sampled]; omega)) branch_skip)

theorem mergeFieldBound_chCt1Acknowledged : MergeFieldBound V1State.Chunked.Ct1Acknowledged.mergeField rawChCt1Acknowledged 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct1Acknowledged.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucCt1Sent rfl (by omega) (fun v => by simp [rawChCt1Acknowledged]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyDec rfl (by omega) (fun v => by simp [rawChCt1Acknowledged]; omega)) branch_skip)

theorem mergeFieldBound_chCt2Sampled : MergeFieldBound V1State.Chunked.Ct2Sampled.mergeField rawChCt2Sampled 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.Chunked.Ct2Sampled.mergeField at h
  exact branch_ite h (fun h => branch_optMessage h mergeFieldBound_ucCt2Sent rfl (by omega) (fun v => by simp [rawChCt2Sampled]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_polyEnc rfl (by omega) (fun v => by simp [rawChCt2Sampled]; omega)) branch_skip)

private theorem mergeFieldBound_innerState : MergeFieldBound V1State.InnerState.merge (optRaw rawInnerState) 22 := by
  intro s tag wt rest depth s' rest' h; unfold V1State.InnerState.merge at h
  exact branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chKeysUnsampled (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chKeysSampled (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chHeaderSent (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chCt1Received (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chEkSentCt1Received (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chNoHeaderReceived (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chHeaderReceived (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chCt1Sampled (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chEkReceivedCt1Sampled (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chCt1Acknowledged (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
    (fun h => branch_ite h (fun h => branch_oneofMessage h mergeFieldBound_chCt2Sampled (by omega) (by cases s with | none => rfl | some is => cases is <;> first | exact Nat.le_refl _ | exact Nat.zero_le _) (fun _ => rfl))
      branch_skip))))))))))

private theorem mergeFieldBound_v1State : MergeFieldBound V1State.mergeField rawV1State 22 := by
  intro s tag wt rest depth s' rest' h
  unfold V1State.mergeField at h
  refine branch_ite h (fun h => ?_) branch_skip
  obtain ⟨is', he, rfl⟩ := bind_pair_ok (s := s) h (fun _ _ => rfl)
  exact mergeFieldBound_innerState s.innerState tag wt rest depth is' rest' he

private theorem mergeFieldBound_pqInner :
    MergeFieldBound PqRatchetState.Inner.merge (optRaw rawPqInner) 22 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.Inner.merge at h
  exact branch_ite h
    (fun h => branch_oneofMessage h mergeFieldBound_v1State (by omega)
      (by cases s with | none => rfl | some is => cases is; exact Nat.le_refl _) (fun _ => rfl))
    branch_skip

private theorem mergeFieldBound_pqState : MergeFieldBound PqRatchetState.mergeField rawPqState 201 := by
  intro s tag wt rest depth s' rest' h
  unfold PqRatchetState.mergeField at h
  refine branch_ite h (fun h => branch_optMessage h mergeFieldBound_vn rfl (by omega) (fun v => by simp [rawPqState]; omega))
    (fun h => branch_ite h (fun h => branch_optMessage h mergeFieldBound_chain rfl (by omega) (fun v => by simp [rawPqState]; omega))
    (fun h => branch_ite h (fun h => ?_) branch_skip))
  obtain ⟨v, he, rfl⟩ := bind_pair_ok (s := s) h (fun _ _ => rfl)
  obtain ⟨hle, hv⟩ := mergeFieldBound_pqInner s.inner tag wt rest depth v rest' he
  refine ⟨hle, ?_⟩
  simp only [rawPqState]
  have hmul : 22 * (rest.length - rest'.length + 1) ≤ 201 * (rest.length - rest'.length + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- Decoding `bs` via `Proto.decodeState` yields `rawPqState st ≤ 201 * bs.length`. -/
theorem decodeState_rawPqState_le {bs : Bytes} {st : PqRatchetState}
    (h : Proto.decodeState bs = .ok st) : rawPqState st ≤ 201 * bs.length := by
  have hraw := mergeFieldsLoop_raw_le mergeFieldBound_pqState bs.length default bs
    Proto.RECURSION_LIMIT st h
  have hdef : rawPqState default = 0 := rfl
  omega

/-- Decoding `bs` via `Proto.spqrDecodeState` yields `rawPqState st ≤ 201 * bs.length`. -/
theorem spqrDecodeState_rawPqState_le {bs : Bytes} {st : PqRatchetState}
    (h : Proto.spqrDecodeState bs = .ok st) : rawPqState st ≤ 201 * bs.length := by
  unfold Proto.spqrDecodeState at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    simp [rawPqState, optRaw]
  · rcases hdec : PqRatchetState.decode bs with e | st'
    · simp [hdec] at h
    · simp only [hdec, Except.ok.injEq] at h
      subst h
      exact decodeState_rawPqState_le hdec

end MoveCompat

end CryptoVerification.SpqrV1.Top.StateSize
