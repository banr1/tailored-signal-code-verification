/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.Callees
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.ProofX
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Acknowledged
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedCt2Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkReceivedCt1Sampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedHeaderSent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysSampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedKeysUnsampled
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedNoHeaderReceived
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.EpochDirection
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedCt1Sent
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.UnchunkedEkSentCt1Received
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.V1StateProof
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Top
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Ct1AcknowledgedRecvEkChunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DecodedMessageBridge
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.KeysSampledRecvCt1Chunk
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.Ct1Received
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvCt2Chunk.RecvCt1Ack
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.RecvHdrChunkProof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.UnchunkedRecvEk
import LibsignalBinary.Proofs.SpqrV1.States.Recv.Top
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserialize
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Contracts
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Final
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Proof
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From

/-!
# Trap-at-RNG `spqr::recv` Proof for SPQR v1 on the CLI Image

Assembles `SpqrRecvContracts canonicalV1InnerHeap img A C.F K (trTrapExterns C abs)` from
`Stage2Contracts_trap`, `TripleRatchetHooks`, `SpqrHooks`, and `Obj.Loads`, yielding
`spqr_recv_ok_trap` on `tripleRatchetProg_trap img C abs`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Prost.BytesMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Unchunked
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## 1. Hook Lifts to `trTrapExterns C abs` -/

private theorem hookSat_memcpy_ro_trTrapExterns (C : Crypto)
    (abs : String → Option (State → State)) :
    HookSat (trTrapExterns C abs) memcpyName sessionMemcpyRegionROSpec := by
  have heq := trTrapExterns_eq_tripleRatchetExterns C 0#64 abs (by decide : memcpyName ≠ rngFillName)
  rcases hookSat_memcpy_ro_tripleRatchetExterns C 0#64 abs with ⟨fn, hfn, hok⟩
  exact ⟨fn, heq.trans hfn, hok⟩

private theorem hookSat_allocZeroed_trTrapExterns {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (trTrapExterns C abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hookSat_trTrapExterns (by decide) (by decide) hZero

private theorem spqrHooks_trTrapExterns {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (trTrapExterns C abs) where
  fromSeed := hookSat_trTrapExterns (by decide) (by decide) hSH.fromSeed
  pk1 := hookSat_trTrapExterns (by decide) (by decide) hSH.pk1
  pk2 := hookSat_trTrapExterns (by decide) (by decide) hSH.pk2
  encaps1 := hookSat_trTrapExterns (by decide) (by decide) hSH.encaps1
  encaps2 := hookSat_trTrapExterns (by decide) (by decide) hSH.encaps2
  decaps := hookSat_trTrapExterns (by decide) (by decide) hSH.decaps
  validatePk := hookSat_trTrapExterns (by decide) (by decide) hSH.validatePk
  hmac := hookSat_trTrapExterns (by decide) (by decide) hSH.hmac

/-! ## 2. `DecodeStateOkX` under `Stage2Contracts_trap` -/

private theorem decodeVarint2_ok_ext_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap b C A uuidTryParse S ext) :
    Varint.DecodeVarint2OkExt b A ext := by
  refine Varint.decodeVarint2_ok_of_contracts ?_ ?_
  · rw [Varint.decodeVarint2_add_from_eq_fnAddr]
    exact hC.decode_error_from
  · exact Prost.decodeVarintSlow_ok_at_of_contract Varint.decodeVarint2_fnOff
      (k := num% (ls_off% "prost::encoding::varint::decode_varint_slow::<&mut &[u8]>" -
        ls_off% "prost::encoding::varint::decode_varint::<&mut &[u8]> [local#2]"))
      (by decide)
      (Prost.decodeVarintSlow_ok_of_session2 hC.decode_varint_slow)

private theorem skipField3_ok_ext_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Varint.skipField3Name)
      (Varint.skipField3Spec A) := by
  refine Varint.skipField3_ok_of_contracts ?_ (decodeVarint2_ok_ext_trap hC)
  rw [Varint.skipField3_add_from_eq_fnAddr]
  exact hC.decode_error_from

private theorem bytesMerge3Contracts_of_stage2_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    BytesMerge3Contracts img A ext where
  loads := himg
  alloc := hC.toAllocContracts
  decode_error_from := hC.decode_error_from
  decode_varint2 := subroutine_ok_inImage_of_subroutine_ok img (decodeVarint2_ok_ext_trap hC)
  bytes_from_vec := bytesFromVecOk_ext himg rfl
  reserve7 := do_reserve_7_ok_ext hC.toAllocContracts
  vtable_slot := bytesVtableSlotLoaded
  vtable_drop := fun p v => bytesVtableDropOk_ext p v v.length hC.toAllocContracts himg rfl

private theorem chainParamsMerge_canonical_ok_trap {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap b C A uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr DecodeState.chainParamsMergeName)
      (DecodeState.chainParamsMergeSpec A) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr Prost.MessageMerge.chainParamsMergeName)
      (Prost.MessageMerge.chainParamsMergeSpec A) := by
    refine Prost.MessageMerge.chainParamsMerge_ok_of_contracts ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorFromName)]
      exact hC.decode_error_from
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName) (callee := decodeErrorPushName)]
      exact hC.decode_error_push
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName) (callee := Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_ext_trap hC
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.chainParamsMergeName) (callee := skipField3Name)]
      exact skipField3_ok_ext_trap hC
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : Prost.MessageMerge.ChainParamsMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout

private theorem epochDirectionMerge_canonical_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DecodeState.epochDirectionMergeName)
      ((DecodeState.epochDirectionMergeSpec A).inImage img) := by
  have hok : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr Prost.MessageMerge.epochDirectionMergeName)
      ((Prost.MessageMerge.epochDirectionMergeSpec A).inImage img) := by
    refine Prost.MessageMerge.epochDirectionMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorFromName)]
      exact hC.decode_error_from
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName) (callee := decodeErrorPushName)]
      exact hC.decode_error_push
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName) (callee := Varint.decodeVarint2Name)]
      exact decodeVarint2_ok_ext_trap hC
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName) (callee := skipField3Name)]
      exact skipField3_ok_ext_trap hC
    · rw [fnAddr_offset_eq_H (name := Prost.MessageMerge.epochDirectionMergeName)
        (callee := bytesMerge3Name)]
      exact hBytes
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre halign => ?_
  let x' : Prost.MessageMerge.EpochDirectionMergeGhost :=
    ⟨x.wt, x.msgPtr, x.msg, x.bufRef, x.slot, x.ptr, x.bs⟩
  exact hok.mono_outcome x' R s0 hpc hrun hpre halign fun _ hout => hout

private theorem polyEncoderMerge_ok_ext_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName)
      ((polyEncoderMergeSpec A).inImage img) := by
  refine polyEncoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorFromName)]
    exact hC.decode_error_from
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := decodeErrorPushName)]
    exact hC.decode_error_push
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_ext_trap hC
  · rw [fnAddr_offset_eq_H (name := polyEncoderMergeName) (callee := skipField3Name)]
    exact skipField3_ok_ext_trap hC
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyEncoderMergeName)) +
          bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
            "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
          (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyEncoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyEncoderMergeName)) +
          bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
            ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff growOneVecU8Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialEncoder, &mut &[u8]>"),
          (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]
      bv_omega
    rw [h_off]; exact hGrow

private theorem polyDecoderMerge_ok_ext_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrow : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName)
      ((polyDecoderMergeSpec A).inImage img) := by
  refine polyDecoderMerge_ok_of_contracts ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorFromName)]
    exact hC.decode_error_from
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := decodeErrorPushName)]
    exact hC.decode_error_push
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := Varint.decodeVarint2Name)]
    exact decodeVarint2_ok_ext_trap hC
  · rw [fnAddr_offset_eq_H (name := polyDecoderMergeName) (callee := skipField3Name)]
    exact skipField3_ok_ext_trap hC
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
          "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) +
          bv% (2 ^ 64 - ls_rel% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]"
            "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff bytesMerge3Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
          (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#3]")]
      bv_omega
    rw [h_off]; exact hBytes
  · have h_off : (tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderMergeName +
        bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
          ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        (tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name := by
      change (img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff polyDecoderMergeName)) +
          bv% (ls_off% "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one" -
            ls_off% "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>") =
        img.base + BitVec.ofNat 64 (libsignalSessionCode.fnOff growOneVecU8Name)
      rw [(ls_lemma% fnOff "prost::encoding::message::merge::<spqr::proto::pq_ratchet::PolynomialDecoder, &mut &[u8]>"),
          (ls_lemma% fnOff "<alloc::raw_vec::RawVec<alloc::vec::Vec<u8>>>::grow_one")]
      bv_omega
    rw [h_off]; exact hGrow

private theorem v1StateMerge_canonical_ok_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext)
    (hBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr bytesMerge3Name)
      ((bytesMerge3RawSpec A).inImage img))
    (hGrowVecU8 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneVecU8Name)
      (growOneVecU8Spec A)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr v1StateMergeName)
      ((Prost.MessageMerge.v1StateMergeSpec A img.base).inImage img) := by
  have hFrom := hC.decode_error_from
  have hPush := hC.decode_error_push
  have hVarint := decodeVarint2_ok_ext_trap hC
  have hSkip := skipField3_ok_ext_trap hC
  have hAuth : CryptoVerification.SpqrV1.Auth.AuthMergeOkX img A ext :=
    CryptoVerification.SpqrV1.Auth.auth_merge_ok_ext hFrom hPush hVarint hSkip hBytes
  have hAuthPb := auth_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes
  have hUcEk := unchunkedEkSentCt1ReceivedMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthPb
  have hUcCt1 := unchunkedCt1SentMerge_ok_of_fnAddr hFrom hPush hVarint hSkip hBytes hAuthPb
  have hPolyEnc := polyEncoderMerge_ok_ext_trap hC hBytes hGrowVecU8
  have hPolyDec := polyDecoderMerge_ok_ext_trap hC hBytes hGrowVecU8
  exact v1State_merge_ok_of_fnAddr
    hFrom hPush hVarint hSkip hC.dealloc
    (CryptoVerification.SpqrV1.Drop.drop_opt_proto_inner_state_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ct1_received_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_sent_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_ek_sent_ct1_received_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_no_header_received_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_chunked_header_received_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_proto_unchunked_ct1_sent_ek_received_ok_ext hC.dealloc)
    (CryptoVerification.SpqrV1.Drop.drop_glue_proto_poly_encoder_ok_ext hC.dealloc)
    (chunked_keys_unsampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth)
    (chunked_keys_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunked_header_sent_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc hPolyDec)
    (chunkedCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyEnc)
    (chunkedEkSentCt1Received_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcEk hPolyDec)
    (chunked_no_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyDec)
    (chunked_header_received_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hBytes hPolyDec)
    (chunkedCt1Sampled_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyEnc hPolyDec)
    (chunked_ek_received_ct1_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hBytes hAuth hPolyEnc)
    (chunkedCt1Acknowledged_merge_ok_of_fnAddr hFrom hPush hVarint hSkip hUcCt1 hPolyDec)
    (chunked_ct2_sampled_merge_ok_ext_x hFrom hPush hVarint hSkip hAuth hPolyEnc)

private theorem decode_state_ok_x_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hC : Stage2Contracts_trap img.base C A uuidTryParse S ext) :
    DecodeStateOkX canonicalV1InnerHeap img A ext := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.base_aligned_of_loads himg
  let hAlloc : AllocContracts img.base A ext := hC.toAllocContracts
  have hBytes := (bytesMerge3Contracts_of_stage2_trap himg hC).ok_ext
  have hGrow := growOneVecU8_ok_ext img.base A ext hAlloc
  have hBase : DecodeStateCalleeContracts canonicalV1InnerHeap img.base A ext :=
    { b_page_aligned := hb
      of_drop_inner := of_drop_inner_canonical A
      of_cap_inner := of_cap_inner_ok A
      alloc := hAlloc
      decodeErrorFrom := hC.decode_error_from
      decodeErrorPush := hC.decode_error_push
      decodeVarint2 := decodeVarint2_ok_ext_trap hC
      skipField3 := skipField3_ok_ext_trap hC
      chainParamsMerge := chainParamsMerge_canonical_ok_trap hC
      growOneChainEpoch := Alloc.grow_one_chain_epoch_full_ok_ext hAlloc
      dropOptProtoInnerState := dropOptProtoInnerState_canonical_ok hb hC.dealloc
      dropProtoPqRatchetState := dropProtoPqRatchetState_canonical_ok hb hC.dealloc }
  exact decodeState_ok
    { hBase with
      bytesMerge3 := hBytes
      epochDirectionMerge := epochDirectionMerge_canonical_ok_trap hC hBytes
      v1StateMerge := v1StateMerge_canonical_ok_trap hC hBytes hGrow }

/-! ## 3. `StatesRecvOkX` and `SpqrRecvContracts` on `trTrapExterns C abs` -/

private theorem statesRecvContracts_of_hooks_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    StatesRecvContracts img A C.F K (trTrapExterns C abs) := by
  let ext := trTrapExterns C abs
  have hStage2 : Stage2Contracts_trap img.base C A uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hStage2.toAllocContracts
  have hAx : AllocContractsX img A ext := AllocContractsX.of_AllocContracts hA
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    have h0 := hA.session_memcpy_region_ok_at memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_trTrapExterns C abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_trTrapExterns hTH.allocZeroed
  have hSH' : SpqrHooks C A K ext := spqrHooks_trTrapExterns hSH
  have hle := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.sessionExterns_le_trTrap C abs
  have : HkdfHooks C.F ext := HkdfHooks.of_le_sessionExterns hle
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg hle
  have hconcat2 : SliceConcat2OkX img A ext := slice_concat_2_ok_x hA hRO
  have hconcat3 : SliceConcat3OkX img A ext := slice_concat_3_ok_x hA hRO
  have hadd : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addChunkName) (addChunkSpec A) :=
    add_chunk_ok_ext hA
  have haddX : AddChunkOkX img A ext := add_chunk_ok_x hA
  have hencBytes : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr encodeBytesName) (encodeBytesSpec A) :=
    encode_bytes_ok_ext hA
  have hdecMsg : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr polyDecoderDecodedMessageName)
      (polyDecoderDecodedMessageSpec A img.base) :=
    polyDecoderDecodedMessage_ok_ext hA
  have hdecMsgX : PolyDecodedMessageOkX img A ext := polyDecodedMessageOkX_of_alloc hA
  have hvalPk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr mlkemValidatePkName) (mlkemValidatePkSpec K) :=
    mlkemValidatePk_ok_of_hookSat hSH'.validatePk
  have hrecvEk : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentRecvEkName)
      (unchunkedCt1SentRecvEkSpec A C.F K) :=
    unchunked_ct1_sent_recv_ek_ok_ext hA.dealloc hvalPk
  have hsendCt2 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name)
      (unchunkedCt1SentEkReceivedSendCt2Spec A C.F K img.base) :=
    unchunked_ct1_sent_ek_received_send_ct2_ok_ext hA hRO hSH'.encaps2 hSH'.hmac
  have hsendCt2Enc : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sendCt2EncoderName) (sendCt2EncoderSpec A) :=
    send_ct2_encoder_ok_ext hA hencBytes
  exact
    { keysSampledRecvCt1Chunk_ok :=
        keys_sampled_recv_ct1_chunk_ok_ext hA.dealloc hmemcpy hadd hencBytes
      headerSentRecvCt1Chunk_ok :=
        header_sent_recv_ct1_chunk_ok_alloc hA
      ct1ReceivedRecvCt2Chunk_ok :=
        ct1_received_recv_ct2_chunk_ok_ext hA.dealloc hmemcpy hadd
      ekSentCt1ReceivedRecvCt2Chunk_ok :=
        recv_ct2_chunk_ok_x_of_decodedMessage himg hA hAx
          (allocZeroedWithStackOkX_of_hook hZero)
          hSH'.decaps hconcat2 hconcat3
          hhkdf (authUpdate_ok_of_hook_x himg hconcat2 hhkdf hAx hZero)
          (do_reserve_7_ok_ext_x hA) hSH'.hmac
      noHeaderReceivedRecvHdrChunk_ok :=
        noHeaderReceived_recv_hdr_chunk_okX himg hAx hA.dealloc haddX hdecMsgX
          hconcat3 hSH'.hmac
      polyAddChunk_ok := haddX
      polyDecodedMessage_ok := hdecMsg
      unchunkedCt1SentRecvEk_ok := hrecvEk
      unchunkedCt1SentEkReceivedSendCt2_ok := hsendCt2
      sendCt2Encoder_ok := hsendCt2Enc
      ekReceivedCt1SampledRecvCt1Ack_ok :=
        ek_received_ct1_sampled_recv_ct1_ack_ok_ext hA.dealloc hsendCt2 hsendCt2Enc
      ct1AcknowledgedRecvEkChunk_ok :=
        ct1_acknowledged_recv_ek_chunk_ok_ext hA.dealloc hmemcpy hadd hdecMsg
          hrecvEk hsendCt2 hsendCt2Enc
      ct2SampledRecvNextEpoch_ok :=
        ct2_sampled_recv_next_epoch_ok_ext (drop_glue_poly16_ok_ext hA.dealloc) }

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks_canonical_trap
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {K : MlKem}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hTH : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSH : SpqrHooks C A K abs) :
    SpqrRecvContracts canonicalV1InnerHeap img A C.F K (trTrapExterns C abs) := by
  let ext := trTrapExterns C abs
  have hStage2 : Stage2Contracts_trap img.base C A uuidTryParse (spqrV1 C.F K) ext :=
    Stage2Contracts_trap.of_tripleRatchetProgAt_trap img.base C A (spqrV1 C.F K) abs hTH
  have hA : AllocContracts img.base A ext := hStage2.toAllocContracts
  have hle := CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPqAssembly.sessionExterns_le_trTrap C abs
  have : HkdfHooks C.F ext := HkdfHooks.of_le_sessionExterns hle
  have hhkdf : HkdfToSliceSpqrOkX img (spqrHkdfWith C.F) ext :=
    hkdf_to_slice_spqr_ok_ext img C himg hle
  have hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec :=
    hookSat_memcpy_ro_trTrapExterns C abs
  have hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A) :=
    hookSat_allocZeroed_trTrapExterns hTH.allocZeroed
  exact CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_okX himg hA
    (decode_state_ok_x_trap himg hStage2)
    (auth_new_ok_x himg hhkdf hA hRO hZero)
    (chainNew_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) (AllocContractsX.of_AllocContracts hA))
    (chainAddEpoch_ok_ext_x himg hhkdf (vec_deque_grow_ok_x hA) (AllocContractsX.of_AllocContracts hA))
    (chainRecvKey_ok_alloc_x himg (slice_concat_2_ok_x hA hRO) hhkdf hA)
    (messageDeserialize_spqrPolyApi_ok_of_contracts_x img A ext hA hStage2.format_inner)
    (states_from_pb_ok_x hA)
    (states_recv_ok_x hA (statesRecvContracts_of_hooks_trap himg hTH hSH))

theorem _root_.CryptoVerification.Cli.SpqrV1.Top.Recv.spqr_recv_ok_trap
    (C : Crypto) (A : RustAlloc) (K : MlKem)
    (abs : String → Option (State → State)) (img : Obj.Image)
    (hHooks : TripleRatchetHooks C A (spqrV1 C.F K) abs)
    (hSpqr : SpqrHooks C A K abs)
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg_trap img C abs) (entryOf img spqrRecvName)
      (spqrRecvSpecExactKeyBounded A (spqrV1Recv C.F K) img) :=
  spqrRecv_ok_of_contracts
    (CryptoVerification.Cli.SpqrV1.Top.Recv.spqrRecvContracts_of_hooks_canonical_trap
      himg hHooks hSpqr)

end CryptoVerification.SpqrV1.Top.Recv
