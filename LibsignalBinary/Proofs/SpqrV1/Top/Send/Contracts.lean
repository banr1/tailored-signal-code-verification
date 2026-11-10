/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Top
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainResolve
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# Callee Contracts and `.rodata` Scaffolding for `spqr::send::<HookRng>` (`0x3085c`)

**Checked by Lean.**

Wires individual callee `OkX` / `OkExt` contracts and `.rodata` jump-table assertions into
`SpqrSendContracts` and `SpqrSendContractsExt` from `TripleRatchetHooks`, `SpqrHooks`, and
`Obj.Loads libsignalSessionImage img`.
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

/-! ## `.rodata` Bundle Introduction (`spqrSendRoAt`) -/

/-- Introduce `spqrSendRoAt img.base` into the precondition of a `SepWPp` obligation
    using `rodata_spqrSendRoAt himg hF`. -/
theorem sepWPp_intro_spqrSendRoAt {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s0 : State} (hF : img.FrozenLoaded s0)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s0 (spqrSendRoAt img.base ∗ P) Q Qp) :
    SepWPp prog ret s0 P Q Qp := by
  intro R0 hm hL
  have hm' : s0.mem ⊨ (spqrSendRoAt img.base ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact rodata_spqrSendRoAt himg hF hm
  exact h R0 hm' hL

/-! ## Leaf `send_*_chunk` `OkX` Wiring -/

theorem sessionMemcpyRegion_ok_of_allocContracts {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
  have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0

theorem headerSent_send_ek_chunk_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hnc : PolyNextChunkOkX img A ext) :
    HeaderSentSendEkChunkOkX img A F ext :=
  header_sent_send_ek_chunk_ok_ext (sessionMemcpyRegion_ok_of_allocContracts hA) hnc

theorem ct1Received_send_ek_chunk_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hnc : PolyNextChunkOkX img A ext) :
    Ct1ReceivedSendEkChunkOkX img A F ext :=
  ct1_received_send_ek_chunk_ok_ext (sessionMemcpyRegion_ok_of_allocContracts hA) hnc

theorem ct1Sampled_send_ct1_chunk_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hnc : PolyNextChunkOkX img A ext) :
    Ct1SampledSendCt1ChunkOkX img A F ext :=
  ct1_sampled_send_ct1_chunk_ok_ext (sessionMemcpyRegion_ok_of_allocContracts hA) hnc

theorem ekReceivedCt1Sampled_send_ct1_chunk_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hnc : PolyNextChunkOkX img A ext) :
    EkReceivedCt1SampledSendCt1ChunkOkX img A F ext :=
  ek_received_ct1_sampled_send_ct1_chunk_ok_ext (sessionMemcpyRegion_ok_of_allocContracts hA) hnc

theorem ct2Sampled_send_ct2_chunk_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hnc : PolyNextChunkOkX img A ext) :
    Ct2SampledSendCt2ChunkOkX img A F ext :=
  ct2_sampled_send_ct2_chunk_ok_ext (sessionMemcpyRegion_ok_of_allocContracts hA) hnc

/-! ## Individual Callee `OkX` Wiring -/

/-- Construct `Prost.MessageMerge.BytesMerge3Contracts img A ext` from `Obj.Loads libsignalSessionImage img`
    and `Stage2Contracts img.base C A ctl uuidTryParse S ext`. -/
theorem bytesMerge3Contracts_of_stage2 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    Prost.MessageMerge.BytesMerge3Contracts img A ext where
  loads := himg
  alloc := hC.toAllocContracts
  decode_error_from := hC.decode_error_from
  decode_varint2 := subroutine_ok_inImage_of_subroutine_ok img (Varint.decodeVarint2_ok_ext hC)
  bytes_from_vec := bytesFromVecOk_ext himg rfl
  reserve7 := do_reserve_7_ok_ext hC.toAllocContracts
  vtable_slot := bytesVtableSlotLoaded
  vtable_drop := fun p v => bytesVtableDropOk_ext p v v.length hC.toAllocContracts himg rfl

theorem decode_state_ok_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts img.base C A ctl uuidTryParse S ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext :=
  spqr_decode_state_ok_of_bytes_contracts
    (ProofLib.base_aligned_of_loads himg) hC
    (bytesMerge3Contracts_of_stage2 himg hC)

theorem chain_from_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    ChainFromPbOkX img A ext :=
  chain_from_pb_ok hA.dealloc

theorem chain_from_version_negotiation_ok_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainFromVersionNegotiationOkX img hkdf A ext :=
  chainFromVersionNegotiation_ok_of_contracts_x
    (chainNew_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA)
      (AllocContractsX.of_AllocContracts hA))

theorem chain_add_epoch_ok_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainAddEpochOkX img hkdf A ext :=
  chainAddEpoch_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA)
    (AllocContractsX.of_AllocContracts hA)

theorem chain_send_key_ok_x {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    ChainSendKeyOkX img hkdf A ext :=
  chainSendKey_ok_ext_x himg (slice_concat_2_ok_x hA hRO) hhkdf
    (AllocContractsX.of_AllocContracts hA)

theorem chain_into_pb_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    ChainIntoPbOkX img A ext :=
  chain_into_pb_ok hA

theorem message_serialize_ok_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hhooks : SpqrHooks C A K ext) :
    MessageSerializeOkX spqrPolyApi img A ext :=
  messageSerialize_ok_of_contracts_x spqrPolyApi img C A K ext hA hhooks

theorem spqr_encode_varint_ok_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hhooks : SpqrHooks C A K ext) :
    SpqrEncodeVarintOkX img A ext :=
  spqrEncodeVarint_ok_of_contracts_x img C A K ext hA hhooks

theorem auth_mac_hdr_ok_x {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hhooks : SpqrHooks C A K ext) :
    AuthMacHdrOkX img C.F A ext :=
  authMacHdr_ok_ext_x himg (slice_concat_3_ok_x hA hRO) hhooks.hmac
    (AllocContractsX.of_AllocContracts hA)

theorem auth_update_ok_x {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith F) ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthUpdateOkX img F A ext :=
  authUpdate_ok_of_hook_x himg (slice_concat_2_ok_x hA hRO) hhkdf
    (AllocContractsX.of_AllocContracts hA) hZero

theorem hkdf_to_vec_ok_x {img : Obj.Image} {A : RustAlloc} {hkdf : HkdfFn}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hhkdf : HkdfToSliceSpqrOkX img hkdf ext) :
    HkdfToVecOkX img A hkdf ext :=
  hkdf_to_vec_ok_ext img A hkdf ext hA hZero hhkdf

theorem states_into_pb_ok_x {img : Obj.Image} {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    StatesIntoPbOkX img A F ext :=
  CryptoVerification.SpqrV1.States.IntoPb.states_into_pb_ok_x hA

theorem encode_bytes_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    EncodeBytesOkX img A ext :=
  CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_ok_x hA

theorem poly_next_chunk_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext) :
    PolyNextChunkOkX img A ext :=
  CryptoVerification.SpqrV1.Poly.NextChunk.poly_next_chunk_ok_x himg A ext hA

theorem drop_proto_spqr_chain_ok_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A) :=
  drop_proto_spqr_chain_ok_ext hA.dealloc

theorem drop_chain_epoch_slice_local1_ok_x {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropChainEpochSliceLocal1Name)
      (dropChainEpochSliceSpec A) :=
  drop_chain_epoch_slice_local1_ok_ext hA.dealloc

theorem optProtoInnerStateAt_canonical_eq_drop_send (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    DecodeState.optProtoInnerStateAt canonicalV1InnerHeap A a opt =
      Drop.optProtoInnerStateAt A a opt :=
  optProtoInnerStateAt_canonical_eq_drop A a opt

/-! ## `SpqrSendContracts` Assembly -/

/-- Assemble `SpqrSendContracts canonicalV1InnerHeap img A ctl C K ext` from `Stage2Contracts`,
    `HkdfToSliceSpqrOkX`, `SpqrHooks`, `StatesFromPbOkX`, and `PolyNextChunkOkX`. -/
theorem spqrSendContracts_of_callees {img : Obj.Image} {C : Crypto} {A : RustAlloc}
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
    SpqrSendContracts canonicalV1InnerHeap img A ctl C K ext where
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
  dropProtoChain_ok := drop_proto_spqr_chain_ok_x hC.toAllocContracts
  dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_ok_x hC.toAllocContracts

theorem spqrHooks_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (tripleRatchetExterns C ctl abs) where
  fromSeed := hSH.fromSeed
  pk1 := hSH.pk1
  pk2 := hSH.pk2
  encaps1 := hSH.encaps1
  encaps2 := hSH.encaps2
  decaps := hSH.decaps
  validatePk := hSH.validatePk
  hmac := hSH.hmac

theorem hookSat_allocZeroed_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (tripleRatchetExterns C ctl abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hZero

/-- Assemble `SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs)`
    from `TripleRatchetHooks C A (spqrV1 C.F K) abs`, `SpqrHooks C A K abs`,
    `Obj.Loads libsignalSessionImage img`, and `StatesFromPbOkX`. -/
theorem spqrSendContracts_of_hooks {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs)
    (hfrom_pb : StatesFromPbOkX img A C.F (tripleRatchetExterns C ctl abs)) :
    SpqrSendContracts canonicalV1InnerHeap img A ctl C K (tripleRatchetExterns C ctl abs) := by
  have hC : Stage2Contracts img.base C A ctl uuidTryParse (spqrV1 C.F K)
      (tripleRatchetExterns C ctl abs) :=
    Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl (spqrV1 C.F K) abs hTH
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) (tripleRatchetExterns C ctl abs) :=
    hkdf_to_slice_spqr_ok_ext img C himg
      (ConsumeMessageKeyTransfer.sessionExterns_le C ctl abs)
  have hRO : HookSat (tripleRatchetExterns C ctl abs) memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_tripleRatchetExterns C ctl abs
  exact spqrSendContracts_of_callees himg hC hhkdf hRO
    (hookSat_allocZeroed_tripleRatchetExterns hTH.allocZeroed)
    (spqrHooks_tripleRatchetExterns hSH)
    hfrom_pb (poly_next_chunk_ok_x himg hC.toAllocContracts)

/-! ## Contract-Parameterized (`*Ext`) Wiring and `SpqrSendContractsExt` -/

theorem chain_from_version_negotiation_ok_ext' {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainFromVersionNegotiationOkExt img hkdf A ext :=
  chainFromVersionNegotiation_ok_of_contracts_ext
    (chainNew_ok_ext_ext himg hhkdf (vec_deque_grow_ok_x hA)
      (AllocContractsX.of_AllocContracts hA))

theorem chain_add_epoch_ok_ext' {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContracts img.base A ext) :
    ChainAddEpochOkExt img hkdf A ext :=
  chainAddEpoch_ok_ext_ext himg hhkdf (vec_deque_grow_ok_x hA)
    (AllocContractsX.of_AllocContracts hA)

theorem chain_send_key_ok_ext' {img : Obj.Image} {hkdf : HkdfFn} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img hkdf ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    ChainSendKeyOkExt img hkdf A ext :=
  chainSendKey_ok_ext_ext himg (slice_concat_2_ok_x hA hRO) hhkdf
    (AllocContractsX.of_AllocContracts hA)

theorem auth_update_ok_ext {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hhkdf : HkdfToSliceSpqrOkExt img (spqrHkdfWith F) ext)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    AuthUpdateOkExt img F A ext :=
  authUpdate_ok_of_hook_ext himg (slice_concat_2_ok_x hA hRO) hhkdf
    (AllocContractsX.of_AllocContracts hA) hZero

theorem spqrSendContractsExt_of_callees {img : Obj.Image} {C : Crypto} {A : RustAlloc}
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
    SpqrSendContractsExt canonicalV1InnerHeap img A ctl C K ext where
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
  dropProtoChain_ok := drop_proto_spqr_chain_ok_x hC.toAllocContracts
  dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_ok_x hC.toAllocContracts

/-! ## Contract-Backed (`*Ext`) Phase 3b–3c Chain Resolution -/

section ChainResolveExt

set_option linter.unusedVariables false
open ProofLib.ProgramReflection CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff

private theorem stackAt_callee_split_ext (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide) :
    stackAt sp spqrSendCalleeStack = memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by have : n ≤ 123008 := hle; change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd; rwa [Nat.add_sub_of_le hle] at h

private theorem of_sepWP_inImage_ext {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (img : Obj.Image) (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  exact SepWPp.of_sepWP_frozen hinv.1 hinv.2 (SepWP.mono h fun _ _ _ _ hnext hfz hsym => hnext ⟨hfz, hsym⟩)

private theorem panic_frame_anyHeap_ext {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) : m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) := Entails.of_eq (by ac_rfl)
  have hm' := Satisfies.mono h1 hm; rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

private theorem panic_not_exited_ext {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False :=
  ((satisfies_pure_sepConj _ _ _).mp h).1

private theorem panic_inImage_calleeStack_anyPanic_ext {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret : BitVec 64} {spec : Spec α} {x : α} {s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp} {φ_pre : Prop} {φ_pan φ_out : State → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜φ_pan sf⌝ ∗ anyHeap))
    (hpan_imp : ∀ sm : State, φ_pan sm → φ_out sm) (hspec_post : ∀ sf, spec.post x s sf = ⌜False⌝)
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  refine SepWPp.call_wpp_frozen (x := x)
    (F := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F)
    hcall hinv.1 hinv.2 hpc hrun hsp_al rfl
    (fun R' hm => by
      change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗
        ((memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) ∗ R')
      rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
      rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
      rw [hP, stackAt_callee_split_ext sp n hle] at hm
      exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)
    (fun sm code R' _ hpost => by
      dsimp only [Spec.inImage] at hpost; rw [hexit_eq code sm] at hpost
      exact panic_not_exited_ext hpost)
    (fun sm _ _ hmFr => by
      dsimp only [Spec.inImage] at hmFr; rw [hpan_eq sm] at hmFr
      exact panic_frame_anyHeap_ext (hpan_imp sm) hmFr)
    (fun sm _ _ _ _ _ _ => by
      have hpeq : (spec.inImage img).post x s sm ∗
          (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) =
          ⌜False⌝ ∗ (memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F) := by
        dsimp only [Spec.inImage]; rw [hspec_post sm]
      exact SepWPp.weaken_pre (Entails.of_eq hpeq) (ProofLib.SepWPp.pure_elim False.elim))
    (fun sm R' _ hpost => by
      dsimp only [Spec.inImage] at hpost; rw [hoom_eq sm] at hpost
      exact (panic_not_exited_ext hpost).elim)

private theorem readReg32_of_readReg64_eq_ext {s1 s2 : State} {r : Reg} (h : s1.readReg64 r = s2.readReg64 r) : s1.readReg32 r = s2.readReg32 r := by unfold State.readReg32; rw [h]
private theorem flag_preserve_ext {s1 s2 : State} (h : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x20 = 0#32)
    (hx20 : s2.readReg64 .x20 = s1.readReg64 .x20) (hx21 : s2.readReg64 .x21 = s1.readReg64 .x21) :
    s2.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s2.readReg32 .x20 = 0#32 :=
  h.imp (hx21.trans ·) ((readReg32_of_readReg64_eq_ext hx20).trans ·)
private theorem flag_of_csinc_ext {s : State} {x21 : BitVec 64} (hx21 : s.readReg64 .x21 = x21)
    (hx20 : s.readReg32 .x20 = (if (x21 + 1#64 != 0#64) = true then 0#32 else 1#32)) :
    s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32 := by
  by_cases h : x21 = LibsignalTripleRatchetRepr.noneCap
  · exact Or.inl (hx21.trans h)
  · refine Or.inr (hx20.trans ?_)
    have hne : (x21 + 1#64 != 0#64) = true := by unfold LibsignalTripleRatchetRepr.noneCap at h; simp only [bne_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [hne]
private theorem memRegion_1260_88_eq_32_56_ext (sp : BitVec 64) : memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 32 ∗ memRegion (sp + 0x1280#64) 56 := ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 32) (k := 56) (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1260_88_eq_40_48_ext (sp : BitVec 64) : memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 40 ∗ memRegion (sp + 0x1288#64) 48 := ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 40) (k := 48) (b' := sp + 0x1288#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_80_8_ext (sp : BitVec 64) : memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 80 ∗ memRegion (sp + 0x5e0#64) 8 := ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 80) (k := 8) (b' := sp + 0x5e0#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_24_64_ext (sp : BitVec 64) : memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 24 ∗ memRegion (sp + 0x5a8#64) 64 := ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 64) (b' := sp + 0x5a8#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1060_80_eq_24_56_ext (sp : BitVec 64) : memRegion (sp + 0x1060#64) 80 = memRegion (sp + 0x1060#64) 24 ∗ memRegion (sp + 0x1078#64) 56 := ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 24) (k := 56) (b' := sp + 0x1078#64) rfl (by bv_omega) (by decide)
private theorem addsPState64_noneCap_z_ext : (addsPState64 LibsignalTripleRatchetRepr.noneCap 1#64).z = true := by unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap; decide
private theorem addsPState64_z_false_of_ne_noneCap_ext {x21 : BitVec 64} (hne : x21 ≠ LibsignalTripleRatchetRepr.noneCap) : (addsPState64 x21 1#64).z = false := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap at *; simp only [Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne]; intro h; apply hne; bv_omega
private theorem setPC_preserves_ext {s1 s : State} {pc : BitVec 64} (h : s1 = s.setPC pc) :
    s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧ (∀ r, s1.readReg64 r = s.readReg64 r) := by subst h; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
private theorem optEpochSecretRegSlotAt_some_ne_ext (A : RustAlloc) (sp x21 x27 : BitVec 64) (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢ ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ optEpochSecretRegSlotAt A sp x21 x27 (some es) := by
  dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne; exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))
private theorem sendChainPost_congr_frame_ext {F : ShaCompress} (A : RustAlloc) (img : Obj.Image) (s0 : State) (sp ret x23 : BitVec 64)
    (st1 : States spqrPolyApi (spqrAuthApi F)) {Fr1 Fr2 : SepProp} (hFr : Fr1 = Fr2) (res : SpqrApiResult (BitVec 32 × Bytes × Option ChainPB)) :
    sendChainPost A img s0 sp ret x23 st1 Fr1 res = sendChainPost A img s0 sp ret x23 st1 Fr2 res := by rw [hFr]

theorem step_chain_5dc_to_7fc_ext {A : RustAlloc} {F : ShaCompress} (img : Obj.Image) (hkdf : HkdfFn)
    {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64) (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hsend_key : ChainSendKeyOkExt img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x23 : BitVec 64) (c1 : Chain) (msgEpoch : Epoch) (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame Fr : SepProp) (φ_out : State → Prop) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3456#64) (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ret) (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendKeyIntoPbChain hkdf c1 msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨ (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendKeyIntoPbChain hkdf c1 msgEpoch)) s
      (chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1 Frame (sendKeyIntoPbChain hkdf c1 msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  by_cases hep0 : msgEpoch = 0#64
  · refine step_panic_epoch_zero_315dc img ext hinv hpc hrun (hx22.trans hep0) fun sf htr_f => ?_
    exact hφ sf (Or.inl ⟨by unfold sendKeyIntoPbChain; simp [hep0]; rfl, htr_f.trans htr⟩)
  · have hep0_beq : (msgEpoch == 0#64) = false := beq_eq_false_iff_ne.mpr hep0
    have hpre_sk := step_pre_send_key_315dc s
      (chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc hrun (by rw [hx22]; exact hep0)
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176248#64) img hinv
    refine SepWP.mono hpre_sk ?_
    rintro s1 P1 hpc1 hrun1 ⟨_, htr1, hsp1, hx8_1, hx0_1, hx1_1, hx30_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, _, _, hx26_1, _, hx28_1, hvregs1, rfl⟩ hinv1
    dsimp only [chainRepr]; rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro G; rw [memRegion_1260_88_eq_40_48_ext s.sp]
    have hcall_sk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176248#64)
        ((chainSendKeySpecExt hkdf A).inImage img) := by rw [spqrSend_chainSendKey_addr]; exact hsend_key
    refine call_inImage_calleeStack_anyPanic (s.sp) chainSendKeyStackExt (by decide)
      (x := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, msgEpoch - 1#64, G, c1⟩)
      (T_pre := memRegion (s.sp + 0x1260#64) 40 ∗ chainAt A (s.sp + 0x590#64) G c1 ∗ A.pool)
      (T_post := fun _ => sendKeyPostAt A (s.sp + 0x590#64) (s.sp + 0x1260#64) c1 (Chain.sendKey hkdf c1 (msgEpoch - 1#64)) ∗ A.pool)
      (F := memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
      hcall_sk hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1
      (by dsimp only [chainSendKeySpecExt]; ac_rfl) (And.intro hx0_1 (And.intro (hx1_1.trans (congrArg (· - 1#64) hx22)) hx8_1))
      (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun sm hpan => by
        rcases hpan with ⟨hpan_sk, htr_sm⟩ | ⟨halloc, hpref⟩
        · refine hφ sm (Or.inl ⟨?_, htr_sm.trans (htr1.trans htr)⟩); unfold sendKeyIntoPbChain; simp only [hep0_beq, Bool.false_eq_true, ↓reduceIte]
          cases h : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
          | ok _ => rw [h] at hpan_sk; contradiction
          | error e => cases e with | err _ => rw [h] at hpan_sk; contradiction | panic _ => rfl
        · exact hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr1, htr] at halloc, by rwa [htr1, htr] at hpref⟩))
      (fun _ => by dsimp only [chainSendKeySpecExt]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 hx20_2 hx21_2 _ hx23_2 _ _ hx26_2 _ hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr); have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19); have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx26_20 : s2.readReg64 .x26 = s.sp + 0x1260#64 := hx26_2.trans (hx26_1.trans hx26); have hx28_20 : s2.readReg64 .x28 = s.sp + 0x1060#64 := hx28_2.trans (hx28_1.trans hx28)
    have hflag2 := flag_preserve_ext (flag_preserve_ext hflag hx20_1 hx21_1) hx20_2 hx21_2
    cases hsk : Chain.sendKey hkdf c1 (msgEpoch - 1#64) with
    | error e =>
      cases e with
      | panic p => dsimp only [sendKeyPostAt]; exact pure_elim_focus_b1 False (fun h => h.elim)
      | err err =>
        have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .error (.err err) := by unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
        rw [hres]; dsimp only [sendChainTargetPC, sendChainPost, sendKeyPostAt]
        apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv2
        have herr_step := step_send_key_err_315f4_to_31a3c hb hdealloc hdrop_slice hdrop_states s2 ret x23 err c1 st1
          (memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
          hpc2 hrun2 hx19_20 hx23_20 hsp2_align
        rw [hsp2] at herr_step; refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono herr_step ?_)
        rintro sf Q hpcf hrunf ⟨_, htrf, hspf, hx23f, hvregsf, hQ⟩ hinvf
        refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
        rw [memRegion_1260_88_eq_40_48_ext s.sp]; exact Entails.trans hQ (Entails.of_eq (by ac_rfl))
    | ok val =>
      rcases val with ⟨c2, idx, msgKey⟩
      have hres : sendKeyIntoPbChain hkdf c1 msgEpoch = .ok (idx, msgKey, some c2.intoPb) := by unfold sendKeyIntoPbChain; simp [hep0_beq, hsk]; rfl
      rw [hres]; dsimp only [sendChainTargetPC, sendChainPost, sendKeyPostAt]
      have hok1 := step_post_send_key_ok_315f4 (A := A) s2 idx msgKey
        (chainRepr A (s.sp + 0x590#64) c2 ∗ memRegion (s.sp + 0x1288#64) 48 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
          memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
          chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc2 hrun2 hsp2_align
      rw [hsp2] at hok1; apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3712#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok1 ?_)
      rintro s3 P3 hpc3 hrun3 ⟨_, htr3, hsp3, hx24_3, hx19_3, hx20_3, hx21_3, _, hx23_3, _, hx26_3, _, hx28_3, hvregs3, hP3⟩ hinv3
      refine SepWPp.weaken_pre hP3 ?_; have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hok2 := step_pre_chain_into_pb_316dc (A := A) s3 idx msgKey c2
        (memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc3 hrun3 hsp3_align
      rw [hsp3] at hok2; apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 174044#64) img hinv3
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok2 ?_)
      rintro s4 P4 hpc4 hrun4 ⟨_, htr4, hsp4, hx0_4, hx8_4, hx30_4, hx22_4, hx19_4, hx20_4, hx21_4, hx23_4, hx24_4, hx26_4, _, hx28_4, hvregs4, hP4⟩ hinv4
      refine SepWPp.weaken_pre hP4 ?_; apply SepWPp.exists_elim; intro G2; apply SepWPp.exists_elim; intro mkCap; apply SepWPp.exists_elim; intro mkPtr
      have hcall_into : subroutine_ok (tripleRatchetProgAtExt img.base ext)
          ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 174044#64) ((chainIntoPbSpecX A).inImage img) := by rw [spqrSend_chainIntoPb_addr]; exact hinto_pb
      have htr4_0 : s4.trace = s0.trace := htr4.trans (htr3.trans htr2_0)
      refine call_inImage_calleeStack_anyPanic (s.sp) chainIntoPbStackX (by decide)
        (x := ⟨s.sp + 0x1060#64, s.sp + 0x1260#64, G2, c2⟩)
        (T_pre := memRegion (s.sp + 0x1060#64) 80 ∗ chainAt A (s.sp + 0x1260#64) G2 c2 ∗ A.pool)
        (T_post := fun _ => ProtoRepr.chainPBAt A (s.sp + 0x1060#64) c2.intoPb ∗ memRegion (s.sp + 0x1260#64) 88 ∗ A.pool)
        (F := ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_into hinv4 hpc4 hrun4 hsp4 hsp_align hx30_4 (by dsimp only [chainIntoPbSpecX]; ac_rfl) (And.intro hx8_4 hx0_4)
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr4_0] at halloc, by rwa [htr4_0] at hpref⟩))
        (fun _ => by dsimp only [chainIntoPbSpecX]; ac_rfl) ?_
      intro s5 hpc5 hrun5 hsp5 htr5 hinv5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 _ hx26_5 _ hx28_5 hvregs5
      have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5]; exact hsp_align
      have hx28_50 : s5.readReg64 .x28 = s5.sp + 0x1060#64 := by rw [hsp5]; exact hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))
      have hflag5 := flag_preserve_ext (flag_preserve_ext (flag_preserve_ext hflag2 hx20_3 hx21_3) hx20_4 hx21_4) hx20_5 hx21_5
      have hok3 := step_post_chain_into_pb_31734 (A := A) s5 c2.intoPb
        (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
          memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc5 hrun5 hx28_50 hsp5_align
      rw [hsp5] at hok3; apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4000#64) img hinv5
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hok3 ?_)
      rintro sf Q hpcf hrunf ⟨_, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx26f, _, hx28f, hvregsf, hQ⟩ hinvf
      refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans (htr5.trans htr4_0), hspf, hinvf,
        hx19f.trans (hx19_5.trans (hx19_4.trans (hx19_3.trans hx19_20))), hx22f.trans (hx22_5.trans hx22_4),
        hx23f.trans (hx23_5.trans (hx23_4.trans (hx23_3.trans hx23_20))), hx24f.trans ((readReg32_of_readReg64_eq_ext hx24_5).trans (hx24_4.trans hx24_3)),
        hx26f.trans (hx26_5.trans (hx26_4.trans (hx26_3.trans hx26_20))), hx28f.trans (hx28_5.trans (hx28_4.trans (hx28_3.trans hx28_20))),
        flag_preserve_ext hflag5 hx20f hx21f, hvregsf.trans (hvregs5.trans (hvregs4.trans (hvregs3.trans hvregs2_0))), ?_⟩
      refine Entails.trans hQ (Entails.trans (Entails.of_eq (show
        optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) =
        (((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey) ∗
          (optChainPBRegSlotAt A (s.sp + 0xd90#64) (sf.readReg64 .x25) (some c2.intoPb) ∗
            memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) by ac_rfl)) ?_)
      have hex_mk : ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey ⊢
          ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ((s.sp + 0x28#64) ↦₆₄ mkCap) ∗ ((s.sp + 0x8#64) ↦₆₄ mkPtr) ∗ DecodeState.vecU8Heap A mkCap mkPtr msgKey :=
        Entails.sepExists_right mkCap (Entails.sepExists_right mkPtr (Entails.refl _))
      exact Entails.trans (sepConj_mono_left hex_mk) (Entails.of_eq (by ac_rfl))

theorem step_chain_5b8_to_7fc_ext {A : RustAlloc} {F : ShaCompress} (img : Obj.Image)
    (hkdf : HkdfFn) {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hadd_epoch : ChainAddEpochOkExt img hkdf A ext)
    (hsend_key : ChainSendKeyOkExt img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x21 x27 x23 : BitVec 64) (c0 : Chain) (hc0_len : c0.links.length ≤ 2 ^ 54)
    (key : Option EpochSecret) (msgEpoch : Epoch) (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame Fr : SepProp) (φ_out : State → Prop) (hinv : ImgCallInv img s)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace) (hpstate : s.pstate = addsPState64 x21 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64) (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64)
    (hflag : s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendStepChain hkdf (some c0) key msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendStepChain hkdf (some c0) key msgEpoch)) s
      (optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ chainRepr A (s.sp + 0x590#64) c0 ∗
        memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) (sendStepChain hkdf (some c0) key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases key with
  | none =>
    have heq_step : sendStepChain hkdf (some c0) none msgEpoch = sendKeyIntoPbChain hkdf c0 msgEpoch := rfl
    rw [heq_step]; dsimp only [optEpochSecretRegSlotAt]; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 = LibsignalTripleRatchetRepr.noneCap); intro hx21_none
    have hz : s.pstate.z = true := by rw [hpstate, hx21_none]; exact addsPState64_noneCap_z_ext
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3456#64) img hinv
    refine SepWP.mono (step_branch_key_none_315b8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves_ext hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hstep := step_chain_5dc_to_7fc_ext img hkdf hb hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
      s0 s1 ret x23 c0 msgEpoch st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out
      hinv1 hpc1 hrun1 (htr1.trans htr) ((hreg1 .x19).trans hx19) ((hreg1 .x22).trans hx22) ((hreg1 .x23).trans hx23)
      (by rw [hsp1]; exact (hreg1 .x26).trans hx26) (by rw [hsp1]; exact (hreg1 .x28).trans hx28)
      (flag_preserve_ext hflag (hreg1 .x20) (hreg1 .x21)) (by rw [hsp1]; exact hsp_align) hφ (hvregs1.trans hvregs)
    rw [hsp1] at hstep; exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hstep
  | some es =>
    refine SepWPp.weaken_pre (sepConj_mono_left (optEpochSecretRegSlotAt_some_ne_ext A s.sp x21 x27 es)) ?_; rw [sepConj_assoc]
    apply pure_elim_focus_b1 (x21 ≠ LibsignalTripleRatchetRepr.noneCap); intro hx21_ne
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap_ext hx21_ne
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3424#64) img hinv
    refine SepWP.mono (step_branch_key_some_315b8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves_ext hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19
    have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22
    have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27
    have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    rw [memRegion_1260_88_eq_32_56_ext s.sp]
    have hpre_ae := step_pre_add_epoch_315bc (A := A) s1 es
      (chainRepr A (s.sp + 0x590#64) c0 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
        memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) hpc1 hrun1 (by rw [hsp1]; exact hsp_align)
    rw [hsp1, hx21_1, hx27_1] at hpre_ae
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176844#64) img hinv1
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_ae ?_)
    rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx0_2, hx1_2, hx30_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
    have hP2' : P2 ⊢ chainRepr A (s.sp + 0x590#64) c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗
        memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame :=
      Entails.trans hP2 (Entails.of_eq (by ac_rfl))
    refine SepWPp.weaken_pre hP2' ?_; dsimp only [chainRepr]; rw [sepExists_sepConj_left]; apply SepWPp.exists_elim; intro G0
    refine SepWPp.weaken_pre (sepConj_mono_left (chainAt_entails_links_grow_ok A (s.sp + 0x590#64) G0 c0 hc0_len)) ?_
    rw [sepConj_assoc]
    apply pure_elim_focus_b1 (c0.links.length < G0.linksCap.toNat ∨ max (2 * G0.linksCap.toNat) 4 * chainEpochSize < 2 ^ 63); intro hgrow
    have hcall_ae : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 176844#64)
        ((chainAddEpochSpecExt hkdf A).inImage img) := by rw [spqrSend_chainAddEpoch_addr]; exact hadd_epoch
    have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
    have hpan_ae : ∀ sm : State, (((Chain.addEpoch hkdf c0 es).isOk = false ∧ sm.trace = s2.trace) ∨
        (allocFailedIn s2 sm ∧ s2.trace <+: sm.trace)) → φ_out sm := by
      intro sm hpan; rcases hpan with ⟨hpan_ae, htr_sm⟩ | ⟨halloc, hpref⟩
      · refine hφ sm (Or.inl ⟨?_, htr_sm.trans htr2_0⟩)
        unfold sendStepChain; dsimp only [Bind.bind, Except.bind]
        cases h : Chain.addEpoch hkdf c0 es with
        | ok _ => rw [h] at hpan_ae; contradiction
        | error p => rfl
      · exact hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr2_0] at halloc, by rwa [htr2_0] at hpref⟩)
    cases hae : Chain.addEpoch hkdf c0 es with
    | error p =>
      exact panic_inImage_calleeStack_anyPanic_ext (s.sp) chainAddEpochStackExt (by decide)
        (x := ⟨s.sp + 0x590#64, s.sp + 0x1260#64, G0, ⟨x21, x27⟩, c0, es⟩)
        (T_pre := chainAt A (s.sp + 0x590#64) G0 c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_ae hinv2 hpc2 hrun2 hsp2 hsp_align (by dsimp only [chainAddEpochSpecExt]; ac_rfl)
        (And.intro hx0_2 (And.intro hx1_2 hgrow)) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecExt]; rw [hae])
    | ok c1 =>
      refine call_inImage_calleeStack_anyPanic (s.sp) chainAddEpochStackExt (by decide)
        (x := ⟨s.sp + 0x590#64, s.sp + 0x1260#64, G0, ⟨x21, x27⟩, c0, es⟩)
        (T_pre := chainAt A (s.sp + 0x590#64) G0 c0 ∗ epochSecretAt A (s.sp + 0x1260#64) ⟨x21, x27⟩ es ∗ A.pool)
        (T_post := fun _ => chainRepr A (s.sp + 0x590#64) c1 ∗ memRegion (s.sp + 0x1260#64) 32 ∗ A.pool)
        (F := memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x1280#64) 56 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
        hcall_ae hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2 (by dsimp only [chainAddEpochSpecExt]; ac_rfl)
        (And.intro hx0_2 (And.intro hx1_2 hgrow)) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl) hpan_ae
        (fun _ => by dsimp only [chainAddEpochSpecExt]; rw [hae]; ac_rfl) ?_
      intro s3 hpc3 hrun3 hsp3 htr3 hinv3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 _ _ hx26_3 _ hx28_3 hvregs3
      have heq_step : sendStepChain hkdf (some c0) (some es) msgEpoch = sendKeyIntoPbChain hkdf c1 msgEpoch := by
        unfold sendStepChain sendKeyIntoPbChain; simp [hae]; rfl
      rw [heq_step]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
      have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1)
      have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1)
      have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
      have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
      have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
      have hflag3 := flag_preserve_ext (flag_preserve_ext (flag_preserve_ext hflag (hreg1 .x20) (hreg1 .x21)) hx20_2 (hx21_2.trans hx21_1.symm)) hx20_3 hx21_3
      have hstep := step_chain_5dc_to_7fc_ext img hkdf hb hdealloc hdrop_slice hdrop_states hsend_key hinto_pb
        s0 s3 ret x23 c1 msgEpoch st1 (memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame) Fr φ_out
        hinv3 hpc3 hrun3 (htr3.trans htr2_0) hx19_30 hx22_30 hx23_30 hx26_30 hx28_30 hflag3 hsp3_align (by rwa [heq_step] at hφ)
        (hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs)))
      rw [hsp3, memRegion_1260_88_eq_32_56_ext s.sp] at hstep
      exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) hstep

theorem step_chain_resolve_314d8_to_7fc_ext {A : RustAlloc} {F : ShaCompress} (img : Obj.Image)
    (hkdf : HkdfFn) {ext : String → Option (State → State)} (hb : img.base &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt img.base A ext)
    (hdrop_slice : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChainEpochSliceLocal1Name) (dropChainEpochSliceSpec A))
    (hdrop_states : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dropChunkedStatesLocal1Name) (dropChunkedStatesLocal1Spec A F img.base))
    (hfrom_pb : ChainFromPbOkX img A ext) (hfrom_vn : ChainFromVersionNegotiationOkExt img hkdf A ext)
    (hadd_epoch : ChainAddEpochOkExt img hkdf A ext)
    (hsend_key : ChainSendKeyOkExt img hkdf A ext) (hinto_pb : ChainIntoPbOkX img A ext)
    (s0 s : State) (ret x21 x27 x23 : BitVec 64)
    (chain : Option ChainPB) (hchain_raw : Top.StateSize.optRaw Top.StateSize.rawChain chain + 296 ≤ 2 ^ 54)
    (vn : Option VersionNegotiationPB) (key : Option EpochSecret) (msgEpoch : Epoch)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame Fr : SepProp) (φ_out : State → Prop)
    (hinv : ImgCallInv img s) (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3196#64)
    (hrun : s.status = .Running) (htr : s.trace = s0.trace)
    (hx23_none : x23 = LibsignalTripleRatchetRepr.noneCap ↔ chain = none) (hpstate : s.pstate = addsPState64 x23 1#64)
    (hx19 : s.readReg64 .x19 = ret) (hx21 : s.readReg64 .x21 = x21)
    (hx22 : s.readReg64 .x22 = msgEpoch) (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = s.sp + 0x550#64) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hx27 : s.readReg64 .x27 = x27) (hx28 : s.readReg64 .x28 = s.sp + 0x1060#64) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hφ : ∀ sf : State, (((sendChainPhase hkdf chain vn key msgEpoch).isPanic = true ∧ sf.trace = s0.trace) ∨
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)) → φ_out sf)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (sendChainTargetPC img.base ext (sendChainPhase hkdf chain vn key msgEpoch)) s
      (ProtoRepr.optChainPBAt A (s.sp + 0x60#64) chain ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
        chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (sendChainPost A img s0 s.sp ret x23 st1
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0x1bc0#64) 16 ∗ Frame)
        (sendChainPhase hkdf chain vn key msgEpoch))
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (⌜φ_out sf⌝ ∗ anyHeap) ∗ Fr)) := by
  cases chain with
  | none =>
    have hx23_eq : x23 = LibsignalTripleRatchetRepr.noneCap := hx23_none.mpr rfl
    have hz : s.pstate.z = true := by rw [hpstate, hx23_eq]; exact addsPState64_noneCap_z_ext
    have horig_eq : ProtoRepr.optChainPBAt A (s.sp + 0x60#64) none = chainOrigSlotAt s.sp x23 := by
      have hx23_eq' : x23 = ChainFromVersionNegotiation.noneCap := hx23_eq
      rw [hx23_eq', chainOrigSlotAt_none]
      dsimp only [ProtoRepr.optChainPBAt, ChainFromVersionNegotiation.noneCap, LibsignalTripleRatchetRepr.noneCap]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    rw [horig_eq]
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3568#64) img hinv
    refine SepWP.mono (step_branch_chain_none_314d8 s _ hpc hrun hz) ?_
    rintro s1 P1 hpc1 hrun1 ⟨hs1, rfl⟩ hinv1
    rcases setPC_preserves_ext hs1 with ⟨hsp1, htr1, hvregs1, hreg1⟩
    have hx19_1 : s1.readReg64 .x19 = ret := (hreg1 .x19).trans hx19; have hx21_1 : s1.readReg64 .x21 = x21 := (hreg1 .x21).trans hx21
    have hx22_1 : s1.readReg64 .x22 = msgEpoch := (hreg1 .x22).trans hx22; have hx23_1 : s1.readReg64 .x23 = x23 := (hreg1 .x23).trans hx23
    have hx25_1 : s1.readReg64 .x25 = s.sp + 0x550#64 := (hreg1 .x25).trans hx25; have hx26_1 : s1.readReg64 .x26 = s.sp + 0x1260#64 := (hreg1 .x26).trans hx26
    have hx27_1 : s1.readReg64 .x27 = x27 := (hreg1 .x27).trans hx27; have hx28_1 : s1.readReg64 .x28 = s.sp + 0x1060#64 := (hreg1 .x28).trans hx28
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    cases vn with
    | none =>
      have heq_ph : sendChainPhase hkdf none none key msgEpoch = .error (.err .chainNotAvailable) := rfl
      rw [heq_ph]
      have hstep := step_vn_none_3164c_to_31a3c hb hdealloc hdrop_states s1 ret x21 x27 x23 st1 key
        (chainOrigSlotAt s.sp x23 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
          memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
          memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
          memRegion (s.sp + 0x8#64) 8 ∗ Frame) hpc1 hrun1 hx19_1 hx21_1 hx23_1 hx27_1 hsp1_align
      rw [hsp1] at hstep
      apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv1
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      exact SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans (htr1.trans htr), hspf, hinvf, hx23f, hvregsf.trans (hvregs1.trans hvregs), Entails.trans hQf (Entails.of_eq (by ac_rfl))⟩
    | some v =>
      by_cases hgt : BitVec.slt 0#32 v.minVersion = true
      · have hpre_vn := step_pre_from_vn_3164c (A := A) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
            memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hgt hsp1_align
        rw [hsp1] at hpre_vn
        apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 125100#64) img hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_vn ?_)
        rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx0_2, hx8_2, hx30_2, hx19_2, _, hx21_2, hx22_2, hx23_2, _, hx25_2, hx26_2, hx27_2, hx28_2, hvregs2, hP2⟩ hinv2
        refine SepWPp.weaken_pre hP2 ?_; apply SepWPp.exists_elim; intro pin
        have hcall_vn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
            ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 125100#64)
            ((chainFromVersionNegotiationSpecExt hkdf A).inImage img) := by rw [spqrSend_chainFromVN_addr]; exact hfrom_vn
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        refine call_inImage_calleeStack_anyPanic (s.sp) chainFromVersionNegotiationStackExt (by decide)
          (x := ⟨s.sp + 0x1260#64, s.sp + 0x30#64, pin, v⟩)
          (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ ChainFromVersionNegotiation.versionNegotiationPBAt A pin (s.sp + 0x30#64) v ∗ A.pool)
          (T_post := fun _ => chainResultAt A (s.sp + 0x1260#64) (chainFromVersionNegotiation hkdf v) ∗
            ChainFromVersionNegotiation.versionNegotiationPBAt A pin (s.sp + 0x30#64) v ∗ A.pool)
          (F := chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
            memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
            memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
          hcall_vn hinv2 hpc2 hrun2 hsp2 hsp_align hx30_2 (by dsimp only [chainFromVersionNegotiationSpecExt]; ac_rfl)
          (And.intro hx8_2 hx0_2) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
          (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr2_0] at halloc, by rwa [htr2_0] at hpref⟩))
          (fun _ => by dsimp only [chainFromVersionNegotiationSpecExt]; ac_rfl) ?_
        intro s3 hpc3 hrun3 hsp3 htr3 hinv3 hx19_3 _ hx21_3 hx22_3 hx23_3 _ hx25_3 hx26_3 hx27_3 hx28_3 hvregs3
        have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
        have htr3_0 : s3.trace = s0.trace := htr3.trans htr2_0
        have hvregs3_0 : calleeSavedVRegs s3 = calleeSavedVRegs s0 := hvregs3.trans (hvregs2.trans (hvregs1.trans hvregs))
        have hx19_30 : s3.readReg64 .x19 = ret := hx19_3.trans (hx19_2.trans hx19_1); have hx21_30 : s3.readReg64 .x21 = x21 := hx21_3.trans (hx21_2.trans hx21_1)
        have hx22_30 : s3.readReg64 .x22 = msgEpoch := hx22_3.trans (hx22_2.trans hx22_1); have hx23_30 : s3.readReg64 .x23 = x23 := hx23_3.trans (hx23_2.trans hx23_1)
        have hx25_30 : s3.readReg64 .x25 = s3.sp + 0x550#64 := by rw [hsp3]; exact hx25_3.trans (hx25_2.trans hx25_1)
        have hx26_30 : s3.readReg64 .x26 = s3.sp + 0x1260#64 := by rw [hsp3]; exact hx26_3.trans (hx26_2.trans hx26_1)
        have hx27_30 : s3.readReg64 .x27 = x27 := hx27_3.trans (hx27_2.trans hx27_1)
        have hx28_30 : s3.readReg64 .x28 = s3.sp + 0x1060#64 := by rw [hsp3]; exact hx28_3.trans (hx28_2.trans hx28_1)
        refine SepWPp.weaken_pre (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (vn_some_pack A pin (s.sp + 0x30#64) v))))) ?_
        cases hfvn : chainFromVersionNegotiation hkdf v with
        | error err =>
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = .error (.err err) := by
            unfold sendChainPhase sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]; rfl
          rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_590_88_eq_24_64_ext s.sp]
          have hstep := step_from_vn_err_31674_to_31a3c hb hdealloc hdrop_states s3 ret x21 x27 x23 err st1 key
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              memRegion (s.sp + 0x5a8#64) 64 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
              memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
              memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
            hpc3 hrun3 hx19_30 hx21_30 hx23_30 hx26_30 hx27_30 hsp3_align
          rw [hsp3] at hstep
          apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
          rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
          refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr3_0, hspf, hinvf, hx23f, hvregsf.trans hvregs3_0, ?_⟩
          rw [memRegion_590_88_eq_24_64_ext s.sp]; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))
        | ok c0 =>
          have hres : sendResolveChain hkdf none (some v) = .ok (some c0) := by unfold sendResolveChain; simp [Version.toI32, hgt, hfvn, SpqrApiResult.ofError]
          have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
          have hc0_len : c0.links.length ≤ 2 ^ 54 :=
            Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf none (some v) hres) hchain_raw)
          rw [heq_ph, sendChainPost_congr_frame_ext A img s0 s.sp ret x23 st1
            (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) (by ac_rfl)]
          dsimp only [chainResultAt]
          have hstep_ok := step_post_from_vn_ok_31674 (A := A) s3 c0
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
              memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
              chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            hpc3 hrun3 hx25_30 hx26_30 hsp3_align
          rw [hsp3] at hstep_ok
          apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64) img hinv3
          refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep_ok ?_)
          rintro s4 P4 hpc4 hrun4 ⟨_, htr4, hsp4, hpst4, hx20_4, hx19_4, hx21_4, hx22_4, hx23_4, _, _, hx26_4, hx27_4, hx28_4, hvregs4, hP4⟩ hinv4
          have hstep_5b8 := step_chain_5b8_to_7fc_ext img hkdf hb hdealloc hdrop_slice hdrop_states hadd_epoch hsend_key hinto_pb
            s0 s4 ret x21 x27 x23 c0 hc0_len key msgEpoch st1
            (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
            Fr φ_out hinv4 hpc4 hrun4 (htr4.trans htr3_0) (by rw [hx21_30] at hpst4; exact hpst4)
            (hx19_4.trans hx19_30) (hx21_4.trans hx21_30) (hx22_4.trans hx22_30) (hx23_4.trans hx23_30)
            (by rw [hsp4, ← hsp3]; exact hx26_4.trans hx26_30) (hx27_4.trans hx27_30)
            (by rw [hsp4, ← hsp3]; exact hx28_4.trans hx28_30)
            (flag_of_csinc_ext (hx21_4.trans hx21_30) (by rw [hx21_30] at hx20_4; exact hx20_4))
            (by rw [hsp4]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs4.trans hvregs3_0)
          rw [hsp4] at hstep_5b8; exact SepWPp.weaken_pre (Entails.trans hP4 (Entails.of_eq (by ac_rfl))) hstep_5b8
      · have hle : BitVec.slt 0#32 v.minVersion = false := Bool.eq_false_iff.mpr hgt
        have hres : sendResolveChain hkdf none (some v) = .ok none := by unfold sendResolveChain; simp [Version.toI32, hle]; rfl
        have heq_ph : sendChainPhase hkdf none (some v) key msgEpoch = sendStepChain hkdf none key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
        rw [heq_ph]
        have hstep_le := step_from_vn_le_zero_3164c (A := A) s1 v
          (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x590#64) 88 ∗
            memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
            memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
            chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
          hpc1 hrun1 hle hsp1_align
        rw [hsp1] at hstep_le
        apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3964#64) img hinv1
        refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep_le ?_)
        rintro s2 P2 hpc2 hrun2 ⟨_, htr2, hsp2, hx19_2, _, hx21_2, _, hx23_2, _, _, hx26_2, _, hx28_2, hvregs2, hP2⟩ hinv2
        have htr2_0 : s2.trace = s0.trace := htr2.trans (htr1.trans htr)
        have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
        have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
        refine SepWPp.weaken_pre hP2 ?_
        cases key with
        | none =>
          have heq_st : sendStepChain hkdf none none msgEpoch = .ok (0#32, [], none) := rfl
          rw [heq_st]; dsimp only [optEpochSecretRegSlotAt]
          have hpull : ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ (⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗ memRegion (s.sp + 0x1bc0#64) 16) ∗
                memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
                memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
                memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
                chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 = LibsignalTripleRatchetRepr.noneCap⌝ ∗
              (memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗
                (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
                  memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
                  memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
                  memRegion (s.sp + 0xde0#64) 80 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
                  chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := Entails.of_eq (by ac_rfl)
          refine SepWPp.weaken_pre hpull ?_; apply pure_elim_focus_b1 (x21 = LibsignalTripleRatchetRepr.noneCap); intro hx21_none
          have hstep_ok := step_min_version_zero_ok_317d8 (A := A) s2
            (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
              memRegion (s.sp + 0x1bc0#64) 16 ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
              memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
              memRegion (s.sp + 0xde0#64) 80 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
              chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
            hpc2 hrun2 (hx21_2.trans (hx21_1.trans hx21_none)) hsp2_align
          rw [hsp2] at hstep_ok
          apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4000#64) img hinv2
          refine SepWP.mono hstep_ok ?_
          rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx24f, hx22f, _, _, hx19f, hx21f, hx23f, hx26f, _, hx28f, hvregsf, hQf⟩ hinvf
          exact SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf,
            hx19f.trans (hx19_2.trans hx19_1), hx22f, hx23f.trans (hx23_2.trans hx23_1),
            hx24f, hx26f.trans (hx26_2.trans hx26_1), hx28f.trans (hx28_2.trans hx28_1),
            Or.inl (hx21f.trans (hx21_2.trans (hx21_1.trans hx21_none))),
            hvregsf.trans hvregs2_0, Entails.trans hQf (Entails.of_eq (by ac_rfl))⟩
        | some es =>
          have hpull : ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗
              (chainOrigSlotAt s.sp x23 ∗ optEpochSecretRegSlotAt A s.sp x21 x27 (some es) ∗
                memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
                memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
                memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
                chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) ⊢
              ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗
              (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) (some v) ∗ chainOrigSlotAt s.sp x23 ∗
                optEpochSecretRegSlotAt A s.sp x21 x27 (some es) ∗ memRegion (s.sp + 0x590#64) 88 ∗ memRegion (s.sp + 0x1260#64) 88 ∗
                memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
                memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
                memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗
                chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame) :=
            Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (optEpochSecretRegSlotAt_some_ne_ext A s.sp x21 x27 es)))) (Entails.of_eq (by ac_rfl))
          refine SepWPp.weaken_pre hpull ?_; apply pure_elim_focus_b1 (x21 ≠ LibsignalTripleRatchetRepr.noneCap); intro hx21_ne
          refine step_panic_key_without_chain_317d8 img ext hinv2 hpc2 hrun2 (by rw [hx21_2, hx21_1]; exact hx21_ne) fun sf htr_f => ?_
          exact hφ sf (Or.inl ⟨by rw [heq_ph]; rfl, htr_f.trans htr2_0⟩)
  | some pb =>
    have hx23_ne : x23 ≠ LibsignalTripleRatchetRepr.noneCap := fun h => by have := hx23_none.mp h; contradiction
    have hz : s.pstate.z = false := by rw [hpstate]; exact addsPState64_z_false_of_ne_noneCap_ext hx23_ne
    dsimp only [ProtoRepr.optChainPBAt]; rw [memRegion_590_88_eq_80_8_ext s.sp]
    have hpre_pb := step_pre_from_pb_314d8 (A := A) s pb
      (ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗ optEpochSecretRegSlotAt A s.sp x21 x27 key ∗
        memRegion (s.sp + 0x5e0#64) 8 ∗ memRegion (s.sp + 0x1260#64) 88 ∗ memRegion (s.sp + 0x1060#64) 80 ∗
        memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
        memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      hpc hrun hz (by rw [hx23]; exact hx23_ne) hsp_align
    apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 172860#64) img hinv
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hpre_pb ?_)
    rintro s1 P1 hpc1 hrun1 ⟨_, htr1, hsp1, hx0_1, hx8_1, hx30_1, hx19_1, _, hx21_1, hx22_1, hx23_1, _, hx25_1, hx26_1, hx27_1, hx28_1, hvregs1, hP1⟩ hinv1
    rw [hx23] at hP1; refine SepWPp.weaken_pre hP1 ?_; apply SepWPp.exists_elim; intro gPb
    have hcall_pb : subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 172860#64)
        ((chainFromPbSpecX A).inImage img) := by rw [spqrSend_chainFromPb_addr]; exact hfrom_pb
    have htr1_0 : s1.trace = s0.trace := htr1.trans htr
    refine call_inImage_calleeStack_anyPanic (s.sp) chainFromPbStackX (by decide)
      (x := ⟨s.sp + 0x1260#64, s.sp + 0x590#64, gPb, pb⟩)
      (T_pre := memRegion (s.sp + 0x1260#64) 88 ∗ chainPBAt A gPb (s.sp + 0x590#64) pb ∗ A.pool)
      (T_post := fun _ => chainResultAt A (s.sp + 0x1260#64) (Chain.fromPb pb) ∗ memRegion (s.sp + 0x590#64) 80 ∗ A.pool)
      (F := chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x5e0#64) 8 ∗
        memRegion (s.sp + 0x1060#64) 80 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗
        memRegion (s.sp + 0xde0#64) 80 ∗ memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗
        memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗ chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ Frame)
      hcall_pb hinv1 hpc1 hrun1 hsp1 hsp_align hx30_1 (by dsimp only [chainFromPbSpecX]; ac_rfl)
      (And.intro hx8_1 hx0_1) (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
      (fun sm ⟨halloc, hpref⟩ => hφ sm (Or.inr ⟨by unfold allocFailedIn at halloc ⊢; rwa [htr1_0] at halloc, by rwa [htr1_0] at hpref⟩))
      (fun _ => by dsimp only [chainFromPbSpecX]; ac_rfl) ?_
    intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hx19_2 _ hx21_2 hx22_2 hx23_2 _ hx25_2 hx26_2 hx27_2 hx28_2 hvregs2
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
    have htr2_0 : s2.trace = s0.trace := htr2.trans htr1_0
    have hvregs2_0 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2.trans (hvregs1.trans hvregs)
    have hx19_20 : s2.readReg64 .x19 = ret := hx19_2.trans (hx19_1.trans hx19); have hx21_20 : s2.readReg64 .x21 = x21 := hx21_2.trans (hx21_1.trans hx21)
    have hx22_20 : s2.readReg64 .x22 = msgEpoch := hx22_2.trans (hx22_1.trans hx22); have hx23_20 : s2.readReg64 .x23 = x23 := hx23_2.trans (hx23_1.trans hx23)
    have hx25_20 : s2.readReg64 .x25 = s2.sp + 0x550#64 := by rw [hsp2]; exact hx25_2.trans (hx25_1.trans hx25)
    have hx26_20 : s2.readReg64 .x26 = s2.sp + 0x1260#64 := by rw [hsp2]; exact hx26_2.trans (hx26_1.trans hx26)
    have hx27_20 : s2.readReg64 .x27 = x27 := hx27_2.trans (hx27_1.trans hx27)
    have hx28_20 : s2.readReg64 .x28 = s2.sp + 0x1060#64 := by rw [hsp2]; exact hx28_2.trans (hx28_1.trans hx28)
    cases hfpb : Chain.fromPb pb with
    | error err =>
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = .error (.err err) := by
        unfold sendChainPhase sendResolveChain; simp [hfpb, SpqrApiResult.ofError]; rfl
      rw [heq_ph]; dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56_ext s.sp]
      have hstep := step_from_pb_err_31510_to_31a3c hb hdealloc hdrop_states s2 ret x21 x27 x23 err st1 key
        (memRegion (s.sp + 0x590#64) 80 ∗ memRegion (s.sp + 0x5e0#64) 8 ∗ chainOrigSlotAt s.sp x23 ∗
          ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗ memRegion (s.sp + 0x1078#64) 56 ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ Frame)
        hpc2 hrun2 hx19_20 hx21_20 hx23_20 hx26_20 hx27_20 hsp2_align
      rw [hsp2] at hstep
      apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 4576#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWP.mono hstep ?_)
      rintro sf Qf hpcf _ ⟨hrunf, htrf, hspf, hx23f, hvregsf, hQf⟩ hinvf
      refine SepWPp.done hpcf hrunf ⟨hrunf, htrf.trans htr2_0, hspf, hinvf, hx23f, hvregsf.trans hvregs2_0, ?_⟩
      rw [memRegion_590_88_eq_80_8_ext s.sp, memRegion_1060_80_eq_24_56_ext s.sp]; exact Entails.trans hQf (Entails.of_eq (by ac_rfl))
    | ok c0 =>
      have hres : sendResolveChain hkdf (some pb) vn = .ok (some c0) := by unfold sendResolveChain; simp [hfpb, SpqrApiResult.ofError]
      have heq_ph : sendChainPhase hkdf (some pb) vn key msgEpoch = sendStepChain hkdf (some c0) key msgEpoch := by unfold sendChainPhase; rw [hres]; rfl
      have hc0_len : c0.links.length ≤ 2 ^ 54 :=
        Nat.le_trans (chain_links_length_le_rawChain c0) (Nat.le_trans (sendResolveChain_raw_le hkdf (some pb) vn hres) hchain_raw)
      rw [heq_ph, sendChainPost_congr_frame_ext A img s0 s.sp ret x23 st1
        (Fr2 := memRegion (s.sp + 0x1bc0#64) 16 ∗ (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)) (by ac_rfl)]
      dsimp only [chainResultAt]; rw [memRegion_1060_80_eq_24_56_ext s.sp]
      have hstep_ok := step_post_from_pb_ok_31510 (A := A) s2 c0
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          optEpochSecretRegSlotAt A s.sp x21 x27 key ∗ memRegion (s.sp + 0x1078#64) 56 ∗ memRegion (s.sp + 0xcf0#64) 80 ∗
          memRegion (s.sp + 0xd90#64) 72 ∗ memRegion (s.sp + 0x28#64) 8 ∗ memRegion (s.sp + 0x8#64) 8 ∗ memRegion ret 72 ∗
          chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ chunkedStatesLocal1JumpTableAt img.base ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        hpc2 hrun2 hx25_20 hx26_20 hsp2_align
      rw [hsp2] at hstep_ok
      apply of_sepWP_inImage_ext (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 3420#64) img hinv2
      refine SepWP.weaken_pre (Entails.of_eq (by rw [memRegion_590_88_eq_80_8_ext s.sp]; ac_rfl)) (SepWP.mono hstep_ok ?_)
      rintro s3 P3 hpc3 hrun3 ⟨_, htr3, hsp3, hpst3, hx20_3, hx19_3, hx21_3, hx22_3, hx23_3, _, _, hx26_3, hx27_3, hx28_3, hvregs3, hP3⟩ hinv3
      have hstep_5b8 := step_chain_5b8_to_7fc_ext img hkdf hb hdealloc hdrop_slice hdrop_states hadd_epoch hsend_key hinto_pb
        s0 s3 ret x21 x27 x23 c0 hc0_len key msgEpoch st1
        (chainOrigSlotAt s.sp x23 ∗ ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
          memRegion (s.sp + 0xcf0#64) 80 ∗ memRegion (s.sp + 0xd40#64) 80 ∗ memRegion (s.sp + 0xde0#64) 80 ∗ Frame)
        Fr φ_out hinv3 hpc3 hrun3 (htr3.trans htr2_0) (by rw [hx21_20] at hpst3; exact hpst3)
        (hx19_3.trans hx19_20) (hx21_3.trans hx21_20) (hx22_3.trans hx22_20) (hx23_3.trans hx23_20)
        (by rw [hsp3, ← hsp2]; exact hx26_3.trans hx26_20) (hx27_3.trans hx27_20)
        (by rw [hsp3, ← hsp2]; exact hx28_3.trans hx28_20)
        (flag_of_csinc_ext (hx21_3.trans hx21_20) (by rw [hx21_20] at hx20_3; exact hx20_3))
        (by rw [hsp3]; exact hsp_align) (by rwa [heq_ph] at hφ) (hvregs3.trans hvregs2_0)
      rw [hsp3, memRegion_1060_80_eq_24_56_ext s.sp] at hstep_5b8; exact SepWPp.weaken_pre (Entails.trans hP3 (Entails.of_eq (by ac_rfl))) hstep_5b8

end ChainResolveExt

end CryptoVerification.SpqrV1.Top.Send
