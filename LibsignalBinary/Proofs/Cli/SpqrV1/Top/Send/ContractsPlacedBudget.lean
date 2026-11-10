/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Callee Contract & `.rodata` Scaffolding (Block `427`)

Provides panic-polymorphic `.rodata` extraction helpers and discharges budget-threaded
`SpqrSendPlacedContracts` for `spqr::send::<signal_session_ratchet::Coins>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
  (LibsignalPlacement LibsignalRoLoaded ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Top.Send (ls_subroutine_ok_of_blockProgram_cro)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrHkdfWith spqrPolyApi)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.Top.DecodeState
  (canonicalV1InnerHeap optProtoInnerStateAt_canonical_eq_drop)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ChainEpochPlacedBudget
  (drop_chain_epoch_slice_local1_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Drop.ProtoChainPlacedBudget
  (drop_proto_spqr_chain_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX Ct1ReceivedSendEkChunkPlacedOkX
   Ct1ReceivedSendEkChunkTightPlacedOkX Ct1SampledSendCt1ChunkPlacedOkX
   Ct1SampledSendCt1ChunkTightPlacedOkX Ct2SampledSendCt2ChunkPlacedOkX
   Ct2SampledSendCt2ChunkTightPlacedOkX EkReceivedCt1SampledSendCt1ChunkPlacedOkX
   EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX EncodeBytesPlacedOkX
   HeaderSentSendEkChunkPlacedOkX HeaderSentSendEkChunkTightPlacedOkX PolyNextChunkPlacedOkX
   SpqrSendPlacedContracts SpqrSendPlacedContractsTight spqrSendPlacedProg spqrSendRoPlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget (lsro_spqrSendRoPlacedAt)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (CliSpqrSendPeerSeams messageSerializeSpecX)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget (authMacHdrSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget (authUpdateSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (chainIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget (chainFromPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.DefsBudget
  (chainFromVersionNegotiationSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.SpecsPlacedBudget (spqrDecodeStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (statesIntoPbPlacedSpecX)

variable [LibsignalPlacement]

/-! ## 1. `.rodata` Helpers & Cross-Block `withLsCodeRoLoaded` Transfer Combinators -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (sepWPp_intro_spqrSendRoPlacedAt spqrSendRoPlacedAt_restore ls_subroutine_ok_cro_of_cro
   ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_callInv)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_cro_of_plain ls_subroutine_ok_of_blockProgram_plain)

/-- `oom`-polymorphic companion of `sepWPp_intro_spqrSendRoPlacedAt`:
    introduces `spqrSendRoPlacedAt` into the precondition of a `SepWPp` obligation from
    `tokenInitPlacedAt ∗ P` under `LibsignalRoLoaded lsmpl s0.mem`. -/
theorem sepWPp_intro_spqrSendRoPlacedAt_oom
    {prog : Program} {ret : BitVec 64} {s0 : State} (hro : LibsignalRoLoaded lsmpl s0.mem)
    {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog ret s0 (spqrSendRoPlacedAt ∗ P) Q Qp oom) :
    SepWPp prog ret s0 (tokenInitPlacedAt ∗ P) Q Qp oom := by
  intro R0 hm hL
  have hm_assoc : s0.mem ⊨ tokenInitPlacedAt ∗ (P ∗ R0) := by
    rwa [← sepConj_assoc]
  have hm' : s0.mem ⊨ (spqrSendRoPlacedAt ∗ P) ∗ R0 := by
    rw [sepConj_assoc]
    exact lsro_spqrSendRoPlacedAt hro hm_assoc
  exact h R0 hm' hL

/-! ## 2. Budget-Threaded CGU-Local Drop Glue (`Block 439`, `Block 446`) & `CliSpqrSendPeerSeams` Wiring -/

/-- `core::ptr::drop_in_place::<spqr::proto::pq_ratchet::Chain>` (`Block 439`) meets
    `withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)` on `spqrSendPlacedProg ext`. -/
theorem drop_proto_spqr_chain_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)) :=
  ls_subroutine_ok_cro_of_plain (drop_proto_spqr_chain_placed hA.dealloc)

/-- `core::ptr::drop_in_place::<[spqr::proto::pq_ratchet::chain::Epoch]> [local#1]` (`Block 446`)
    meets `withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec M A lim)` on `spqrSendPlacedProg ext`. -/
theorem drop_chain_epoch_slice_local1_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeRoLoaded lsmpl (dropChainEpochSliceSpec M A lim)) :=
  ls_subroutine_ok_cro_of_plain (drop_chain_epoch_slice_local1_placed hA.dealloc)

/-- `withLsCodeLoaded`-wrapped companion of `drop_chain_epoch_slice_local1_placed_ok_x` (`Block 446`)
    on `spqrSendPlacedProg ext`. -/
theorem drop_chain_epoch_slice_local1_placed_lscl_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext) :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 446)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := spqrSendPlacedProg ext)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (drop_chain_epoch_slice_local1_placed hA.dealloc))

/-- `<HeaderSent>::send_ek_chunk` (`Block 336`) meets `HeaderSentSendEkChunkPlacedOkX M A lim C.F ext`. -/
theorem headerSent_send_ek_chunk_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    HeaderSentSendEkChunkPlacedOkX M A lim C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.headerSentSendEkChunk_ok

/-- `<Ct1Received>::send_ek_chunk` (`Block 345`) meets `Ct1ReceivedSendEkChunkPlacedOkX M A lim C.F ext`. -/
theorem ct1Received_send_ek_chunk_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    Ct1ReceivedSendEkChunkPlacedOkX M A lim C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct1ReceivedSendEkChunk_ok

/-- `<Ct1Sampled>::send_ct1_chunk` (`Block 335`) meets `Ct1SampledSendCt1ChunkPlacedOkX M A lim C.F ext`. -/
theorem ct1Sampled_send_ct1_chunk_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    Ct1SampledSendCt1ChunkPlacedOkX M A lim C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct1SampledSendCt1Chunk_ok

/-- `<EkReceivedCt1Sampled>::send_ct1_chunk` (`Block 344`) meets
    `EkReceivedCt1SampledSendCt1ChunkPlacedOkX M A lim C.F ext`. -/
theorem ekReceivedCt1Sampled_send_ct1_chunk_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    EkReceivedCt1SampledSendCt1ChunkPlacedOkX M A lim C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ekReceivedCt1SampledSendCt1Chunk_ok

/-- `<Ct2Sampled>::send_ct2_chunk` (`Block 354`) meets `Ct2SampledSendCt2ChunkPlacedOkX M A lim C.F ext`. -/
theorem ct2Sampled_send_ct2_chunk_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    Ct2SampledSendCt2ChunkPlacedOkX M A lim C.F ext :=
  ls_subroutine_ok_of_blockProgram_cro hSeams.ct2SampledSendCt2Chunk_ok

/-- `signal_session_coins_fill` (`Block 618`) meets `CoinsFillPlacedOkX ext`. -/
theorem coins_fill_placed_ok_x
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {C : Crypto}
    {ext : String → Option (State → State)}
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    CoinsFillPlacedOkX ext :=
  ls_subroutine_ok_of_blockProgram_plain hSeams.coinsFill_ok

/-! ## 3. Constructing `SpqrSendPlacedContracts` & `SpqrSendPlacedContractsTight` -/

/-- Assemble `SpqrSendPlacedContracts M canonicalV1InnerHeap A lim ctl C K ext` from placed callee
    contracts and `CliSpqrSendPeerSeams M A lim C ext`. -/
theorem spqrSendPlacedContracts_of_okX
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hChainFromPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hChainAddEpoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) M A lim)))
    (hChainSendKey : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) M A lim)))
    (hChainIntoPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (hAuthMacHdr : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F M A lim)))
    (hAuthUpdate : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F M A lim)))
    (hHkdfToVec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))))
    (hEncodeBytes : EncodeBytesPlacedOkX A lim ext)
    (hPolyNextChunk : PolyNextChunkPlacedOkX M A lim ext)
    (hSeams : CliSpqrSendPeerSeams M A lim C ext) :
    SpqrSendPlacedContracts M canonicalV1InnerHeap A lim ctl C K ext where
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc
  alloc := hA
  coinsFill_ok := coins_fill_placed_ok_x hSeams
  decodeState_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.decodeState_ok
  statesFromPb_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.statesFromPb_ok
  statesIntoPb_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.statesIntoPb_ok
  chainFromPb_ok := hChainFromPb
  chainFromVn_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.chainFromVn_ok
  chainAddEpoch_ok := hChainAddEpoch
  chainSendKey_ok := hChainSendKey
  chainIntoPb_ok := hChainIntoPb
  messageSerialize_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.messageSerialize_ok
  encodeVarint_ok := ls_subroutine_ok_of_blockProgram_cro hSeams.encodeVarint_ok
  authMacHdr_ok := hAuthMacHdr
  authUpdate_ok := hAuthUpdate
  hkdfToVec_ok := hHkdfToVec
  encodeBytes_ok := hEncodeBytes
  polyNextChunk_ok := hPolyNextChunk
  headerSentSendEkChunk_ok := headerSent_send_ek_chunk_placed_ok_x hSeams
  ct1ReceivedSendEkChunk_ok := ct1Received_send_ek_chunk_placed_ok_x hSeams
  ct1SampledSendCt1Chunk_ok := ct1Sampled_send_ct1_chunk_placed_ok_x hSeams
  ekReceivedCt1SampledSendCt1Chunk_ok := ekReceivedCt1Sampled_send_ct1_chunk_placed_ok_x hSeams
  ct2SampledSendCt2Chunk_ok := ct2Sampled_send_ct2_chunk_placed_ok_x hSeams
  dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hA
  dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hA

/-- Assemble tight `SpqrSendPlacedContractsTight M canonicalV1InnerHeap A lim ctl C K ext` from
    exact-envelope placed callee contracts and `AllocContractsPlaced M A lim ext`. -/
theorem spqrSendPlacedContractsTight_of_okX
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {C : Crypto} {K : MlKem}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hCoinsFill : CoinsFillPlacedOkX ext)
    (hDecodeState : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl (spqrDecodeStatePlacedSpec canonicalV1InnerHeap A lim)))
    (hStatesFromPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 333)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget.statesFromPbPlacedSpecX M A lim C.F)))
    (hStatesIntoPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim C.F)))
    (hChainFromPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX M A lim)))
    (hChainFromVn : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 328)
      (withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith C.F) M A lim)))
    (hChainAddEpoch : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith C.F) M A lim)))
    (hChainSendKey : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith C.F) M A lim)))
    (hChainIntoPb : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX M A lim)))
    (hMessageSerialize : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)))
    (hEncodeVarint : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)))
    (hAuthMacHdr : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrSpec C.F M A lim)))
    (hAuthUpdate : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec C.F M A lim)))
    (hHkdfToVec : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith C.F))))
    (hEncodeBytes : EncodeBytesPlacedOkX A lim ext)
    (hPolyNextChunk : PolyNextChunkPlacedOkX M A lim ext)
    (hHsEk : HeaderSentSendEkChunkTightPlacedOkX M A lim C.F ext)
    (hCt1rEk : Ct1ReceivedSendEkChunkTightPlacedOkX M A lim C.F ext)
    (hCt1sCt1 : Ct1SampledSendCt1ChunkTightPlacedOkX M A lim C.F ext)
    (hEkrCt1 : EkReceivedCt1SampledSendCt1ChunkTightPlacedOkX M A lim C.F ext)
    (hCt2sCt2 : Ct2SampledSendCt2ChunkTightPlacedOkX M A lim C.F ext) :
    SpqrSendPlacedContractsTight M canonicalV1InnerHeap A lim ctl C K ext where
  h_inner_eq := optProtoInnerStateAt_canonical_eq_drop A.repAlloc
  alloc := hA
  coinsFill_ok := hCoinsFill
  decodeState_ok := hDecodeState
  statesFromPb_ok := hStatesFromPb
  statesIntoPb_ok := hStatesIntoPb
  chainFromPb_ok := hChainFromPb
  chainFromVn_ok := hChainFromVn
  chainAddEpoch_ok := hChainAddEpoch
  chainSendKey_ok := hChainSendKey
  chainIntoPb_ok := hChainIntoPb
  messageSerialize_ok := hMessageSerialize
  encodeVarint_ok := hEncodeVarint
  authMacHdr_ok := hAuthMacHdr
  authUpdate_ok := hAuthUpdate
  hkdfToVec_ok := hHkdfToVec
  encodeBytes_ok := hEncodeBytes
  polyNextChunk_ok := hPolyNextChunk
  headerSentSendEkChunk_ok := hHsEk
  ct1ReceivedSendEkChunk_ok := hCt1rEk
  ct1SampledSendCt1Chunk_ok := hCt1sCt1
  ekReceivedCt1SampledSendCt1Chunk_ok := hEkrCt1
  ct2SampledSendCt2Chunk_ok := hCt2sCt2
  dropProtoChain_ok := drop_proto_spqr_chain_placed_ok_x hA
  dropChainEpochSlice_ok := drop_chain_epoch_slice_local1_placed_ok_x hA

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
