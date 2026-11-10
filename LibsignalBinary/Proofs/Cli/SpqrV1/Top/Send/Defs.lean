/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Decodes
public import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.Decodes

/-!
# Definitions, `.rodata` Bundle, & Callee Contracts for `spqr::send::<signal_session_ratchet::Coins>`

Defines stack-frame constants, `.rodata` table bundles, and callee contract structures
for `spqr::send::<signal_session_ratchet::Coins>` in the CLI image.
-/

@[expose] public section

set_option autoImplicit false

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib

open CryptoGames.LibsignalSession (Crypto ShaCompress)

open CryptoVerification

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalSpqrV1

open CryptoVerification.SpqrV1.Alloc

open CryptoVerification.SpqrV1.Drop

open CryptoVerification.SpqrV1.ProtoRepr

open CryptoVerification.SpqrV1.ChainProofs

open CryptoVerification.SpqrV1.Top.DecodeState

open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation

open CryptoVerification.SpqrV1.Top.ChainFrom

open CryptoVerification.SpqrV1.Top.EncodeVarint

open CryptoVerification.SpqrV1.Top.MessageSerialize

open CryptoVerification.SpqrV1.States

open CryptoVerification.SpqrV1.States.FromPb

open CryptoVerification.SpqrV1.States.IntoPb

open CryptoVerification.SpqrV1.States.Leaves

open CryptoVerification.SpqrV1.Auth

open CryptoVerification.SpqrV1.Kdf

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## 1. Stack Frame Constants & Saved Callee-Saved Registers (`sp + 0x1f20 .. sp + 0x1f80`) -/

/-- Bundle of all `.rodata` tables used by `spqr::send::<signal_session_ratchet::Coins>` and its callees. -/
def _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendRoAt (b : BitVec 64) : SepProp :=
  CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendStatesJumpTableAt b ∗
  CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendEncodeJumpTableAt b ∗
  CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendDropJumpTableAt b ∗
  Prost.MessageMerge.v1StateJumpTablesAt b ∗
  statesFromPbJumpTableAt b ∗
  statesIntoPbJumpTableAt b ∗
  reduceTableAt b

/-- Bundle of all callee contracts and `.rodata` tables required by `spqr::send::<signal_session_ratchet::Coins>`. -/
structure _root_.CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  /-- Base alignment (`img.base &&& 0xfff#64 = 0#64`). -/
  base_aligned : img.base &&& 0xfff#64 = 0#64
  /-- `img` loads `libsignalSessionImage` (so `.rodata` jump tables are present under `ImgCallInv`). -/
  loads : Obj.Loads libsignalSessionImage img
  /-- Bridge between `DecodeState.optProtoInnerStateAt H_inner` and `Drop.optProtoInnerStateAt`. -/
  h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st
  /-- Rust heap allocator + `memcpy` + `memcmp` contracts. -/
  alloc : AllocContracts img.base A ext
  /-- `spqr::decode_state`. -/
  decodeState_ok : DecodeStateOkX H_inner img A ext
  /-- `<States>::from_pb`. -/
  statesFromPb_ok : StatesFromPbOkX img A C.F ext
  /-- `<States>::into_pb`. -/
  statesIntoPb_ok : StatesIntoPbOkX img A C.F ext
  /-- `<Chain>::from_pb` (`0x60074`). -/
  chainFromPb_ok : ChainFromPbOkX img A ext
  /-- `spqr::chain_from_version_negotiation`. -/
  chainFromVn_ok : ChainFromVersionNegotiationOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::add_epoch` (`0x61004`). -/
  chainAddEpoch_ok : ChainAddEpochOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::send_key` (`0x60db0`). -/
  chainSendKey_ok : ChainSendKeyOkX img (spqrHkdfWith C.F) A ext
  /-- `<Chain>::into_pb` (`0x60514`). -/
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  /-- `<Message>::serialize`. -/
  messageSerialize_ok : MessageSerializeOkX spqrPolyApi img A ext
  /-- `spqr::encode_varint`. -/
  encodeVarint_ok : SpqrEncodeVarintOkX img A ext
  /-- `<Authenticator>::mac_hdr` (`0x69b0c`). -/
  authMacHdr_ok : AuthMacHdrOkX img C.F A ext
  /-- `<Authenticator>::update` (`0x69dbc`). -/
  authUpdate_ok : AuthUpdateOkX img C.F A ext
  /-- `spqr::kdf::hkdf_to_vec` (`0x66010`). -/
  hkdfToVec_ok : HkdfToVecOkX img A (spqrHkdfWith C.F) ext
  /-- `<PolyEncoder>::encode_bytes` (`0x6b560`). -/
  encodeBytes_ok : EncodeBytesOkX img A ext
  /-- `<PolyEncoder as Encoder>::next_chunk` (`0x6a384`). -/
  polyNextChunk_ok : PolyNextChunkOkX img A ext
  /-- Leaf `<HeaderSent>::send_ek_chunk`. -/
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkOkX img A C.F ext
  /-- Leaf `<Ct1Received>::send_ek_chunk`. -/
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkOkX img A C.F ext
  /-- Leaf `<Ct1Sampled>::send_ct1_chunk`. -/
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkOkX img A C.F ext
  /-- Leaf `<EkReceivedCt1Sampled>::send_ct1_chunk`. -/
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkOkX img A C.F ext
  /-- Leaf `<Ct2Sampled>::send_ct2_chunk`. -/
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkOkX img A C.F ext
  /-- `drop_glue::<proto::Chain>`. -/
  dropProtoChain_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
    (dropProtoSpqrChainSpec A)
  /-- `drop_glue::<[chain::Epoch]> [local#1]`. -/
  dropChainEpochSlice_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name)
    (dropChainEpochSliceSpec A)

/-- Contract-parameterized (`*Ext`, `+ 16384` B extern-hook stack headroom) callee bundle for
    `spqr::send::<Coins>` on the CLI binary. -/
structure _root_.CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt
    (H_inner : V1InnerHeapPred) (img : Obj.Image) (A : RustAlloc)
    (ctl : BitVec 64) (C : Crypto) (K : MlKem)
    (ext : String → Option (State → State)) : Prop where
  base_aligned : img.base &&& 0xfff#64 = 0#64
  loads : Obj.Loads libsignalSessionImage img
  h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st
  alloc : AllocContracts img.base A ext
  decodeState_ok : DecodeStateOkX H_inner img A ext
  statesFromPb_ok : StatesFromPbOkX img A C.F ext
  statesIntoPb_ok : StatesIntoPbOkX img A C.F ext
  chainFromPb_ok : ChainFromPbOkX img A ext
  chainFromVn_ok : ChainFromVersionNegotiationOkExt img (spqrHkdfWith C.F) A ext
  chainAddEpoch_ok : ChainAddEpochOkExt img (spqrHkdfWith C.F) A ext
  chainSendKey_ok : ChainSendKeyOkExt img (spqrHkdfWith C.F) A ext
  chainIntoPb_ok : ChainIntoPbOkX img A ext
  messageSerialize_ok : MessageSerializeOkX spqrPolyApi img A ext
  encodeVarint_ok : SpqrEncodeVarintOkX img A ext
  authMacHdr_ok : AuthMacHdrOkX img C.F A ext
  authUpdate_ok : AuthUpdateOkExt img C.F A ext
  hkdfToVec_ok : HkdfToVecOkExt img A (spqrHkdfWith C.F) ext
  encodeBytes_ok : EncodeBytesOkX img A ext
  polyNextChunk_ok : PolyNextChunkOkX img A ext
  headerSentSendEkChunk_ok : HeaderSentSendEkChunkOkX img A C.F ext
  ct1ReceivedSendEkChunk_ok : Ct1ReceivedSendEkChunkOkX img A C.F ext
  ct1SampledSendCt1Chunk_ok : Ct1SampledSendCt1ChunkOkX img A C.F ext
  ekReceivedCt1SampledSendCt1Chunk_ok : EkReceivedCt1SampledSendCt1ChunkOkX img A C.F ext
  ct2SampledSendCt2Chunk_ok : Ct2SampledSendCt2ChunkOkX img A C.F ext
  dropProtoChain_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
    (dropProtoSpqrChainSpec A)
  dropChainEpochSlice_ok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name)
    (dropChainEpochSliceSpec A)

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts.toExt
    {H_inner : V1InnerHeapPred} {img : Obj.Image} {A : RustAlloc}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem} {ext : String → Option (State → State)}
    (h : CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts H_inner img A ctl C K ext) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt H_inner img A ctl C K ext where
  base_aligned := h.base_aligned
  loads := h.loads
  h_inner_eq := h.h_inner_eq
  alloc := h.alloc
  decodeState_ok := h.decodeState_ok
  statesFromPb_ok := h.statesFromPb_ok
  statesIntoPb_ok := h.statesIntoPb_ok
  chainFromPb_ok := h.chainFromPb_ok
  chainFromVn_ok := chainFromVnOkExt_of_okX h.chainFromVn_ok
  chainAddEpoch_ok := chainAddEpochOkExt_of_okX h.chainAddEpoch_ok
  chainSendKey_ok := chainSendKeyOkExt_of_okX h.chainSendKey_ok
  chainIntoPb_ok := h.chainIntoPb_ok
  messageSerialize_ok := h.messageSerialize_ok
  encodeVarint_ok := h.encodeVarint_ok
  authMacHdr_ok := h.authMacHdr_ok
  authUpdate_ok := authUpdateOkExt_of_okX h.authUpdate_ok
  hkdfToVec_ok := hkdfToVecOkExt_of_okX h.hkdfToVec_ok
  encodeBytes_ok := h.encodeBytes_ok
  polyNextChunk_ok := h.polyNextChunk_ok
  headerSentSendEkChunk_ok := h.headerSentSendEkChunk_ok
  ct1ReceivedSendEkChunk_ok := h.ct1ReceivedSendEkChunk_ok
  ct1SampledSendCt1Chunk_ok := h.ct1SampledSendCt1Chunk_ok
  ekReceivedCt1SampledSendCt1Chunk_ok := h.ekReceivedCt1SampledSendCt1Chunk_ok
  ct2SampledSendCt2Chunk_ok := h.ct2SampledSendCt2Chunk_ok
  dropProtoChain_ok := h.dropProtoChain_ok
  dropChainEpochSlice_ok := h.dropChainEpochSlice_ok

end CryptoVerification.SpqrV1.Top.Send
