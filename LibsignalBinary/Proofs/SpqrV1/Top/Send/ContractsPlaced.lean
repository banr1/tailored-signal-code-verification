/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed

/-!
# Relocatable Callee Contracts and `.rodata` Scaffolding for `spqr::send::<HookRng>` (Block 124)

Provides `spqrSendRoPlacedAt` introduction/restoration helpers, `StatesPlacedSeams` wiring
for the five leaf `send_*_chunk` contracts, and `spqrSendPlacedContracts_of_okX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Placed
open CryptoVerification.SpqrV1.States.IntoPb.Placed
open CryptoVerification.SpqrV1.Top.Recv.Placed
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `.rodata` Bundle Introduction and Restoration -/

/-- Introduce `spqrSendRoPlacedAt` into the precondition of a `SepWPp` obligation from
    `GF.Mul2U16.tokenInitPlacedAt ∗ P` under `LibsignalRoLoaded lsmpl s0.mem`. -/
theorem sepWPp_intro_spqrSendRoPlacedAt
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s0 (spqrSendRoPlacedAt ∗ P) Q Qp) :
    SepWPp prog ret s0 (GF.Mul2U16.tokenInitPlacedAt ∗ P) Q Qp := by
  intro R0 hm hL
  have hm_assoc : s0.mem ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ (P ∗ R0) := by
    rwa [← sepConj_assoc]
  have hm' : s0.mem ⊨ (spqrSendRoPlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact lsro_spqrSendRoPlacedAt hro hm_assoc
  exact h R0 hm' hL

/-- Discard the read-only `.rodata` slices in `spqrSendRoPlacedAt`, recovering
    `GF.Mul2U16.tokenInitPlacedAt ∗ P`. -/
theorem spqrSendRoPlacedAt_restore {m : Memory} {P : SepProp}
    (hm : m ⊨ spqrSendRoPlacedAt ∗ P) :
    m ⊨ GF.Mul2U16.tokenInitPlacedAt ∗ P := by
  have hm' :
      m ⊨ (spqrSendStatesJumpTablePlacedAt ∗
           spqrSendEncodeJumpTablePlacedAt ∗
           spqrSendDropJumpTablePlacedAt ∗
           Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗
           Top.Recv.statesFromPbJumpTablePlacedAt ∗
           States.IntoPb.statesIntoPbJumpTablePlacedAt ∗
           GF.UnacceleratedMul.reduceTablePlacedAt) ∗
          (GF.Mul2U16.tokenInitPlacedAt ∗ P) := by
    refine Satisfies.mono (Entails.of_eq ?_) hm
    dsimp only [spqrSendRoPlacedAt]
    ac_rfl
  exact Satisfies.of_sep_right hm'

/-! ## Leaf `send_*_chunk` `PlacedOkX` Wiring -/

theorem headerSent_send_ek_chunk_placed_ok_x {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hSeams : StatesPlacedSeams A F K ext) :
    HeaderSentSendEkChunkPlacedOkX A F ext :=
  hSeams.headerSentSendEkChunk_on

theorem ct1Received_send_ek_chunk_placed_ok_x {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hSeams : StatesPlacedSeams A F K ext) :
    Ct1ReceivedSendEkChunkPlacedOkX A F ext :=
  hSeams.ct1ReceivedSendEkChunk_on

theorem ct1Sampled_send_ct1_chunk_placed_ok_x {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hSeams : StatesPlacedSeams A F K ext) :
    Ct1SampledSendCt1ChunkPlacedOkX A F ext :=
  hSeams.ct1SampledSendCt1Chunk_on

theorem ekReceivedCt1Sampled_send_ct1_chunk_placed_ok_x {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hSeams : StatesPlacedSeams A F K ext) :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext :=
  hSeams.ekReceivedCt1SampledSendCt1Chunk_on

theorem ct2Sampled_send_ct2_chunk_placed_ok_x {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hSeams : StatesPlacedSeams A F K ext) :
    Ct2SampledSendCt2ChunkPlacedOkX A F ext :=
  hSeams.ct2SampledSendCt2Chunk_on

/-! ## `SpqrSendPlacedContracts` Assembly -/

/-- Assemble `SpqrSendPlacedContracts canonicalV1InnerHeap A ctl C K ext` from placed callee contracts
    and `StatesPlacedSeams A C.F K ext`. -/
theorem spqrSendPlacedContracts_of_okX
    {A : RustAlloc} {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hDecodeState : DecodeStatePlacedOkX canonicalV1InnerHeap A ext)
    (hStatesIntoPb : subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base (States.IntoPb.statesIntoPbPlacedRoSpecX A C.F))
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (blkPl_364).base (chainFromPbSpecX A))
    (hChainFromVn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith C.F) A)))
    (hChainAddEpoch : subroutine_ok ((blkPC_368).rebase (blkPl_368).base (Rust.withPanics ext))
      (blkPl_368).base (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) A)))
    (hChainSendKey : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) A)))
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (blkPl_365).base (chainIntoPbSpecX A))
    (hMsgSer : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi A)))
    (hEncodeVarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A)))
    (hAuthMacHdr : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F A)))
    (hAuthUpdate : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F A)))
    (hHkdfToVec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec A (spqrHkdfWith C.F))))
    (hEncodeBytes : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 417)
      (withLsCodeRoLoaded lsmpl (encodeBytesSpecX A)))
    (hPolyNextChunk : PolyNextChunkPlacedOkX A ext)
    (hDropProtoChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (hDropChainEpochSlice : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 143)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec A)))
    (hSeams : StatesPlacedSeams A C.F K ext) :
    SpqrSendPlacedContracts canonicalV1InnerHeap A ctl C K ext where
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A
  alloc := hA
  decodeState_ok := Top.Recv.ls_subroutine_ok_cro_of_cro hDecodeState
  statesFromPb_ok := hSeams.statesFromPb_on
  statesIntoPb_ok := Top.Recv.ls_subroutine_ok_cro_of_plain hStatesIntoPb
  chainFromPb_ok := Top.Recv.ls_subroutine_ok_cro_of_plain hChainFromPb
  chainFromVn_ok := hChainFromVn
  chainAddEpoch_ok := Top.Recv.ls_subroutine_ok_cro_of_callInv hChainAddEpoch
  chainSendKey_ok := hChainSendKey
  chainIntoPb_ok := Top.Recv.ls_subroutine_ok_cro_of_plain hChainIntoPb
  messageSerialize_ok := hMsgSer
  encodeVarint_ok := hEncodeVarint
  authMacHdr_ok := hAuthMacHdr
  authUpdate_ok := hAuthUpdate
  hkdfToVec_ok := hHkdfToVec
  encodeBytes_ok := hEncodeBytes
  polyNextChunk_ok := hPolyNextChunk
  headerSentSendEkChunk_ok := hSeams.headerSentSendEkChunk_on
  ct1ReceivedSendEkChunk_ok := hSeams.ct1ReceivedSendEkChunk_on
  ct1SampledSendCt1Chunk_ok := hSeams.ct1SampledSendCt1Chunk_on
  ekReceivedCt1SampledSendCt1Chunk_ok := hSeams.ekReceivedCt1SampledSendCt1Chunk_on
  ct2SampledSendCt2Chunk_ok := hSeams.ct2SampledSendCt2Chunk_on
  dropProtoChain_ok := hDropProtoChain
  dropChainEpochSlice_ok := hDropChainEpochSlice

end CryptoVerification.SpqrV1.Top.Send
