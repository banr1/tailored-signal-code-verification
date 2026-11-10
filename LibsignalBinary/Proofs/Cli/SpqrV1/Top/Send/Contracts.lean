/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Contracts
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Defs
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpoch
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChain
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# Callee Contract & `.rodata` Scaffolding for `spqr::send::<signal_session_ratchet::Coins>`

Assembles `.rodata` extraction/restoration helpers and discharges `SpqrSendContracts`
from `TripleRatchetHooks` and `SpqrHooks` on the CLI image.
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

open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof

open CryptoVerification.SpqrV1.GF.UnacceleratedMul

open CryptoVerification.SpqrV1.Poly

open CryptoVerification.SpqrV1.Poly.EncodeBytes

open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## 1. `.rodata` Bundle Introduction Helpers (`spqrSendRoAt`) -/

/-- `core::ptr::drop_in_place::<spqr::proto::pq_ratchet::Chain>` (`0x4bd00`) meets
    `dropProtoSpqrChainSpec A`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.drop_proto_spqr_chain_ok_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_proto_spqr_chain_ok_ext hA.dealloc

/-- `core::ptr::drop_in_place::<[spqr::proto::pq_ratchet::chain::Epoch]> [local#1]`
    meets `dropChainEpochSliceSpec A`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.drop_chain_epoch_slice_local1_ok_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr CryptoVerification.Cli.SpqrV1.Drop.dropChainEpochSliceLocal1Name)
      (dropChainEpochSliceSpec A) :=
  CryptoVerification.Cli.SpqrV1.Drop.drop_chain_epoch_slice_local1_ok_ext hA.dealloc

/-- Assemble `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K ext` from:
    - `himg : Obj.Loads libsignalSessionImage img`
    - `hC : Stage2Contracts img.base C A ctl uuidTryParse S ext`
    - `hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext`
    - `hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec`
    - `hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)`
    - `hhooks : SpqrHooks C A K ext`
    - `hfrom_pb : StatesFromPbOkX img A C.F ext`
    - `hnc : PolyNextChunkOkX img A ext` -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContracts_of_callees {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hhooks : SpqrHooks C A K ext)
    (hfrom_pb : StatesFromPbOkX img A C.F ext)
    (hnc : PolyNextChunkOkX img A ext := poly_next_chunk_ok_x himg hC.toAllocContracts) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K ext where
  base_aligned := ProofLib.base_aligned_of_loads himg
  loads := himg
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A
  alloc := hC.toAllocContracts
  decodeState_ok := decode_state_ok_x himg hC
  statesFromPb_ok := hfrom_pb
  statesIntoPb_ok := states_into_pb_ok_x hC.toAllocContracts
  chainFromPb_ok := chain_from_pb_ok_x hC.toAllocContracts
  chainFromVn_ok := chain_from_version_negotiation_ok_x himg hhkdf hC.toAllocContracts
  chainAddEpoch_ok := chain_add_epoch_ok_x himg hhkdf hC.toAllocContracts
  chainSendKey_ok := chain_send_key_ok_x himg hhkdf hC.toAllocContracts hRO
  chainIntoPb_ok := chain_into_pb_ok_x hC.toAllocContracts
  messageSerialize_ok := message_serialize_ok_x hC.toAllocContracts hhooks
  encodeVarint_ok := spqr_encode_varint_ok_x hC.toAllocContracts hhooks
  authMacHdr_ok := auth_mac_hdr_ok_x himg hC.toAllocContracts hRO hhooks
  authUpdate_ok := auth_update_ok_x himg hhkdf hC.toAllocContracts hRO hZero
  hkdfToVec_ok := hkdf_to_vec_ok_x hC.toAllocContracts hZero hhkdf
  encodeBytes_ok := encode_bytes_ok_x hC.toAllocContracts
  polyNextChunk_ok := hnc
  headerSentSendEkChunk_ok := headerSent_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1ReceivedSendEkChunk_ok := ct1Received_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1SampledSendCt1Chunk_ok := ct1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ekReceivedCt1SampledSendCt1Chunk_ok := ekReceivedCt1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ct2SampledSendCt2Chunk_ok := ct2Sampled_send_ct2_chunk_ok_x hC.toAllocContracts hnc
  dropProtoChain_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_proto_spqr_chain_ok_x hC.toAllocContracts
  dropChainEpochSlice_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_chain_epoch_slice_local1_ok_x hC.toAllocContracts

/-- Assemble `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs)`
    from `TripleRatchetHooks C A (spqrV1 C.F K) abs`, `SpqrHooks C A K abs`,
    `Obj.Loads libsignalSessionImage img`, and `StatesFromPbOkX`. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContracts_of_hooks {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs)
    (hfrom_pb : StatesFromPbOkX img A C.F (tripleRatchetExterns C ctl abs)) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs) := by
  have hC : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K)
      (tripleRatchetExterns C ctl abs) :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) (tripleRatchetExterns C ctl abs) :=
    hkdf_to_slice_spqr_ok_ext img C himg
      (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs)
  have hRO : HookSat (tripleRatchetExterns C ctl abs) memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_tripleRatchetExterns C ctl abs
  exact CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContracts_of_callees himg hC hhkdf hRO
    (hookSat_allocZeroed_tripleRatchetExterns hTH.allocZeroed)
    (spqrHooks_tripleRatchetExterns hSH)
    hfrom_pb (poly_next_chunk_ok_x himg hC.toAllocContracts)

/-- Assemble `CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt canonicalV1InnerHeap img A ctl C K ext`
    from `*Ext` HKDF / Auth / Chain contracts and local SPQR callees. -/
theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendContractsExt_of_callees
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith C.F) ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hhooks : SpqrHooks C A K ext)
    (hfrom_pb : StatesFromPbOkX img A C.F ext)
    (hnc : PolyNextChunkOkX img A ext := poly_next_chunk_ok_x himg hC.toAllocContracts) :
    CryptoVerification.Cli.SpqrV1.Top.Send.SpqrSendContractsExt canonicalV1InnerHeap img A ctl C K ext where
  base_aligned := ProofLib.base_aligned_of_loads himg
  loads := himg
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A
  alloc := hC.toAllocContracts
  decodeState_ok := decode_state_ok_x himg hC
  statesFromPb_ok := hfrom_pb
  statesIntoPb_ok := states_into_pb_ok_x hC.toAllocContracts
  chainFromPb_ok := chain_from_pb_ok_x hC.toAllocContracts
  chainFromVn_ok := chain_from_version_negotiation_ok_ext' himg hhkdf hC.toAllocContracts
  chainAddEpoch_ok := chain_add_epoch_ok_ext' himg hhkdf hC.toAllocContracts
  chainSendKey_ok := chain_send_key_ok_ext' himg hhkdf hC.toAllocContracts hRO
  chainIntoPb_ok := chain_into_pb_ok_x hC.toAllocContracts
  messageSerialize_ok := message_serialize_ok_x hC.toAllocContracts hhooks
  encodeVarint_ok := spqr_encode_varint_ok_x hC.toAllocContracts hhooks
  authMacHdr_ok := auth_mac_hdr_ok_x himg hC.toAllocContracts hRO hhooks
  authUpdate_ok := auth_update_ok_ext himg hhkdf hC.toAllocContracts hRO hZero
  hkdfToVec_ok := hkdf_to_vec_ok_ext' img A (spqrHkdfWith C.F) ext hC.toAllocContracts hZero hhkdf
  encodeBytes_ok := encode_bytes_ok_x hC.toAllocContracts
  polyNextChunk_ok := hnc
  headerSentSendEkChunk_ok := headerSent_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1ReceivedSendEkChunk_ok := ct1Received_send_ek_chunk_ok_x hC.toAllocContracts hnc
  ct1SampledSendCt1Chunk_ok := ct1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ekReceivedCt1SampledSendCt1Chunk_ok := ekReceivedCt1Sampled_send_ct1_chunk_ok_x hC.toAllocContracts hnc
  ct2SampledSendCt2Chunk_ok := ct2Sampled_send_ct2_chunk_ok_x hC.toAllocContracts hnc
  dropProtoChain_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_proto_spqr_chain_ok_x hC.toAllocContracts
  dropChainEpochSlice_ok := CryptoVerification.Cli.SpqrV1.Top.Send.drop_chain_epoch_slice_local1_ok_x hC.toAllocContracts

end CryptoVerification.SpqrV1.Top.Send
