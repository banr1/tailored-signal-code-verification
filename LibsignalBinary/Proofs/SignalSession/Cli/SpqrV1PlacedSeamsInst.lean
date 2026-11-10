/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.FinalPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState

/-!
# Closed Relocatable SPQR-V1 Seam Bundle Instantiation

Assembles closed `[LibsignalPlacement]` contracts for `spqr::initial_state` (Block 327),
`spqr::send::<Coins>` (Block 427), and `spqr::recv` (Block 329) to discharge
`SpqrV1PlacedSeams mmpl gh W`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

open scoped CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification (IsLsBlockProg LibsignalPlacement libsignalMutatedBlocks libsignalSessionCode libsignalSessionExterns libsignalSessionLib ls_blockPlacement_base ls_subroutine_ok_cl_of_block lsmpl withLsCl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacSpec)
open CryptoVerification.SignalSession.Cli (CliSpqrExt SpqrV1PlacedSeams cliChainAddEpoch_placed_ok cliChainNew_placed_ok cliChainRecvKey_placed_ok cliDealloc_at_block cliEncodeToVec_placed_ok cliFramelessMemcpy_at_block cliMessageDeserialize_placed_ok cliSpqrDecodeState_recv_trTrap_ok cliSpqrDecodeState_sendCoins_ok cliSpqrExt_self cliSpqrExt_trTrap cliSpqrSendCoins_placed_ok cliStatesPlacedSeamsExt instCliSpqrExtWithPanics spqrRecvPlacedInnerSpecX spqrRecvPlacedInnerSpecXT spqrSendCoinsPlacedSpecT)
open CryptoVerification.SpqrV1.Top.Placed (instIsLsBlockProg_351)
open CryptoVerification.SpqrV1.Top.Recv (SpqrRecvPlacedContracts decodeStatePlacedSpecX initInnerPlacedSpecX ls_subroutine_ok_cro_of_callInv ls_subroutine_ok_cro_of_cro spqrRecvPlacedProg spqrRecvPlacedRawSpecX spqrRecvPlacedSpecX spqrRecvPlacedSpecXT spqr_recv_placed_ok_blockProgram_ext_of_contracts)

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1 (spqrV1Recv)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots (CliGhostA0Hooks lsLibcruxHmacSymCli lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStateEncodeToVecSpecX withLsRoLoaded)
open CryptoVerification.SpqrV1.Prost.MessageMerge.ChunkedMerge
  (unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst (cliDrop_288_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInst
  (cliDrop_266_cl cliDrop_267_cl cliDrop_269_cl cliDrop_270_cl cliDrop_273_cl
   cliDrop_281_cl cliDrop_282_cl cliInitInner_callInv_placed_ok
   cliSpqrInitialState_placed_ok_closed)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInst
  (cliSpqrSend_chainFromPb_ok cliSpqrSend_chainIntoPb_ok
   cliSpqrRecv_chainFrom_ok_trTrap cliSpqrRecv_chainFromPb_ok_trTrap
   cliSpqrRecv_chainIntoPb_ok_trTrap)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInst
  (cliStatesIntoPb_sendCoins_ok cliStatesIntoPb_recv_trTrap_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
  (cliDecodeErrorFrom_blockProgram_cl cliDecodeErrorPush_blockProgram_cl
   cliDecodeVarint2_blockProgram_cl cliSkipField3_blockProgram_cl
   cliBytesMerge3_blockProgram_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInst
  (cliAuthMerge_blockProgram_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInst
  (cliChainParamsMerge_294_cl cliEpochDirectionMerge_299_cro
   cliPolyDecoderMerge_296_cro cliPolyEncoderMerge_297_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInst
  (cliUnchunkedCt1SentMerge_312_cro cliUnchunkedEkSentCt1ReceivedMerge_311_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInst
  (cliChunkedCt1SampledMerge_300_cl cliChunkedCt2SampledMerge_301_cl
   cliChunkedHeaderSentMerge_302_cl cliChunkedCt1ReceivedMerge_303_cl
   cliChunkedKeysSampledMerge_304_cl cliChunkedKeysUnsampledMerge_305_cl
   cliChunkedHeaderReceivedMerge_306_cl cliChunkedCt1AcknowledgedMerge_307_cl
   cliChunkedNoHeaderReceivedMerge_308_cl cliChunkedEkSentCt1ReceivedMerge_309_cl
   cliChunkedEkReceivedCt1SampledMerge_310_cl)

attribute [local irreducible]
  libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup

/-!
### 1. Closed Own-Block `MessageMerge` Contracts (`Blocks 294, 296, 297, 299, 311, 312, 300..310`)
-/

private theorem cliPolyDec_296_closed [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (CryptoVerification.SpqrV1.Prost.MessageMerge.polyDecoderMergeSpec CryptoVerification.E2E.HooksE.A0)) :=
  cliPolyDecoderMerge_296_cro W
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)

private theorem cliPolyEnc_297_closed [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (CryptoVerification.SpqrV1.Prost.MessageMerge.polyEncoderMergeSpec CryptoVerification.E2E.HooksE.A0)) :=
  cliPolyEncoderMerge_297_cro W
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)

private theorem cliUc311_closed [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec CryptoVerification.E2E.HooksE.A0)) :=
  cliUnchunkedEkSentCt1ReceivedMerge_311_cro W
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliAuthMerge_blockProgram_cro W)

private theorem cliUc312_closed [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec CryptoVerification.E2E.HooksE.A0)) :=
  cliUnchunkedCt1SentMerge_312_cro W
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliAuthMerge_blockProgram_cro W)

/-! ### 2. Closed `spqr::decode_state` (`Block 325`) for `send::<Coins>` and `recv` -/

theorem cliSpqrDecodeState_sendCoins_ok_closed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.decodeStatePlacedSpecX
          CryptoVerification.SpqrV1.Top.DecodeState.canonicalV1InnerHeap CryptoVerification.E2E.HooksE.A0)) := by
  have : CliSpqrExt W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact cliSpqrDecodeState_sendCoins_ok mmpl gh W hG hMs hMc hHmac
    (cliDrop_267_cl W) (cliDrop_270_cl W) (cliDrop_281_cl W) (cliDrop_282_cl W)
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliChainParamsMerge_294_cl
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W))
    (cliEpochDirectionMerge_299_cro
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W))
    (cliChunkedCt1SampledMerge_300_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc312_closed W) (cliPolyEnc_297_closed W) (cliPolyDec_296_closed W))
    (cliChunkedCt2SampledMerge_301_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W) (cliPolyEnc_297_closed W))
    (cliChunkedHeaderSentMerge_302_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W) (cliPolyDec_296_closed W))
    (cliChunkedCt1ReceivedMerge_303_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc311_closed W) (cliPolyEnc_297_closed W))
    (cliChunkedKeysSampledMerge_304_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W))
    (cliChunkedKeysUnsampledMerge_305_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W))
    (cliChunkedHeaderReceivedMerge_306_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyDec_296_closed W))
    (cliChunkedCt1AcknowledgedMerge_307_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc312_closed W) (cliPolyDec_296_closed W))
    (cliChunkedNoHeaderReceivedMerge_308_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W) (cliPolyDec_296_closed W))
    (cliChunkedEkSentCt1ReceivedMerge_309_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc311_closed W) (cliPolyDec_296_closed W))
    (cliChunkedEkReceivedCt1SampledMerge_310_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W))

theorem cliSpqrDecodeState_recv_trTrap_ok_closed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX
          CryptoVerification.SpqrV1.Top.DecodeState.canonicalV1InnerHeap CryptoVerification.E2E.HooksE.A0)) := by
  have : CliSpqrExt W (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliSpqrDecodeState_recv_trTrap_ok mmpl gh W hG hMs hMc hHmac
    (cliDrop_267_cl W) (cliDrop_270_cl W) (cliDrop_281_cl W) (cliDrop_282_cl W)
    (cliDecodeErrorPush_blockProgram_cl W)
    (cliDecodeErrorFrom_blockProgram_cl W)
    (cliSkipField3_blockProgram_cl W)
    (cliBytesMerge3_blockProgram_cro W)
    (cliDecodeVarint2_blockProgram_cl W)
    (cliChainParamsMerge_294_cl
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W))
    (cliEpochDirectionMerge_299_cro
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W))
    (cliChunkedCt1SampledMerge_300_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc312_closed W) (cliPolyEnc_297_closed W) (cliPolyDec_296_closed W))
    (cliChunkedCt2SampledMerge_301_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W) (cliPolyEnc_297_closed W))
    (cliChunkedHeaderSentMerge_302_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W) (cliPolyDec_296_closed W))
    (cliChunkedCt1ReceivedMerge_303_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc311_closed W) (cliPolyEnc_297_closed W))
    (cliChunkedKeysSampledMerge_304_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W))
    (cliChunkedKeysUnsampledMerge_305_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W))
    (cliChunkedHeaderReceivedMerge_306_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyDec_296_closed W))
    (cliChunkedCt1AcknowledgedMerge_307_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc312_closed W) (cliPolyDec_296_closed W))
    (cliChunkedNoHeaderReceivedMerge_308_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliAuthMerge_blockProgram_cro W) (cliPolyDec_296_closed W))
    (cliChunkedEkSentCt1ReceivedMerge_309_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliUc311_closed W) (cliPolyDec_296_closed W))
    (cliChunkedEkReceivedCt1SampledMerge_310_cl W
      (cliDecodeErrorFrom_blockProgram_cl W) (cliDecodeErrorPush_blockProgram_cl W)
      (cliDecodeVarint2_blockProgram_cl W) (cliSkipField3_blockProgram_cl W)
      (cliBytesMerge3_blockProgram_cro W) (cliAuthMerge_blockProgram_cro W)
      (cliPolyEnc_297_closed W))

/-! ### 3. Closed `spqr::send::<Coins>` (`Block 427`) -/

theorem cliSpqrSendCoins_placed_ok_closed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT CryptoVerification.E2E.HooksE.A0 0#64 (CryptoVerification.E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) :=
  cliSpqrSendCoins_placed_ok mmpl gh W hG hMs hMc hHmac
    (cliSpqrSend_chainFromPb_ok mmpl gh W hG hMs hMc hHmac)
    (cliSpqrSend_chainIntoPb_ok mmpl gh W hG hMs hMc hHmac)
    (cliSpqrDecodeState_sendCoins_ok_closed mmpl gh W hG hMs hMc hHmac)
    (cliStatesIntoPb_sendCoins_ok mmpl gh W hG hMs hMc hHmac)

/-! ### 4. Closed `SpqrRecvPlacedContracts` & `spqr::recv` (`Block 329`) -/

private theorem lift_rebase_cl_to_recv [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {ext : String → Option (State → State)}
    [IsLsBlockProg calleeProg j (Rust.withPanics ext)]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCodeLoaded lsmpl spec) := by
  have hcl : subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCl lsmpl spec) :=
    ls_subroutine_ok_cl_of_block (callerProg := spqrRecvPlacedProg ext)
      (i := 329) (j := j) hcallee (by decide) hj hj_unmut
  exact subroutine_ok_mono hcl
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem lift_blockProgram_cl_to_recv [LibsignalPlacement] {α : Type}
    {j : Nat} {ext : String → Option (State → State)}
    {entry : BitVec 64} {spec : Spec α}
    (hext_j : (libsignalSessionLib.blockLib j).text.externs = libsignalSessionExterns := by decide)
    (hcallee : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j (Rust.withPanics ext))
      entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (spqrRecvPlacedProg ext) entry (withLsCodeLoaded lsmpl spec) := by
  let _ : IsLsBlockProg (libsignalSessionLib.blockProgram lsmpl j (Rust.withPanics ext))
      j (Rust.withPanics ext) := ⟨rfl, hext_j⟩
  exact lift_rebase_cl_to_recv hcallee hj hj_unmut

private theorem trTrapExternsPlaced_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym = some Rust.panicked := by
  intro sym hsym
  have hp := congrFun (CryptoVerification.SignalSession.Cli.RunGlue.withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at hp
  have hne : sym ≠ lsRngFillSym := by
    intro heq
    subst heq
    rw [CryptoVerification.SignalSession.Cli.Slots.cliExternsPlaced_rngFill mmpl gh W] at hp
    exact absurd hp (by simp)
  have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
  simp only [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq, Bool.false_eq_true, ↓reduceIte]
  exact hp.symm

theorem cliSpqrRecvPlacedContracts [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    SpqrRecvPlacedContracts
      CryptoVerification.SpqrV1.Top.DecodeState.canonicalV1InnerHeap
      CryptoVerification.E2E.HooksE.A0 W.C.F W.Q.K
      (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  let extTrap := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have : CliSpqrExt W extTrap := cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact
    { dealloc_ok := cliDealloc_at_block W (i := 329)
      memcpy_ok := cliFramelessMemcpy_at_block W (i := 329)
      dropEpochSlice_ok :=
        lift_rebase_cl_to_recv (j := 288) (cliDrop_288_cl W)
      dropOptProtoInnerState_ok :=
        lift_blockProgram_cl_to_recv (j := 267) (hcallee := cliDrop_267_cl W)
      dropOptProtoChain_ok :=
        lift_blockProgram_cl_to_recv (j := 266) (hcallee := cliDrop_266_cl W)
      dropChain_ok :=
        lift_blockProgram_cl_to_recv (j := 269) (hcallee := cliDrop_269_cl W)
      dropPqRatchetState_ok :=
        lift_blockProgram_cl_to_recv (j := 270) (hcallee := cliDrop_270_cl W)
      dropStates_ok :=
        lift_blockProgram_cl_to_recv (j := 273) (hcallee := cliDrop_273_cl W)
      decodeState_ok := cliSpqrDecodeState_recv_trTrap_ok_closed mmpl gh W hG hMs hMc hHmac
      initInner_ok := by
        have h0 := cliInitInner_callInv_placed_ok W (ext := extTrap)
        conv at h0 => arg 2; rw [ls_blockPlacement_base (i := 324)]
        have h1 := ls_subroutine_ok_cro_of_callInv
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 324) h0
        exact subroutine_ok_mono h1
          (fun _ _ _ hpre => by
            dsimp only [withLsCodeRoLoaded, CryptoVerification.SpqrV1.Top.InitInner.initInnerPlacedSpecX,
              initInnerPlacedSpecX] at hpre ⊢
            exact hpre)
          (fun _ _ _ _ hpost => hpost)
      chainFrom_ok := cliSpqrRecv_chainFrom_ok_trTrap mmpl gh W hG hMs hMc hHmac
      chainFromPb_ok := cliSpqrRecv_chainFromPb_ok_trTrap mmpl gh W hG hMs hMc hHmac
      chainNew_ok := by
        have h0 := cliChainNew_placed_ok W (H := Rust.withPanics extTrap)
        conv at h0 => arg 2; rw [ls_blockPlacement_base (i := 363)]
        exact ls_subroutine_ok_cro_of_callInv
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 363) h0
      chainAddEpoch_ok := by
        have h0 := cliChainAddEpoch_placed_ok W (H := Rust.withPanics extTrap)
        conv at h0 => arg 2; rw [ls_blockPlacement_base (i := 368)]
        exact ls_subroutine_ok_cro_of_callInv
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 368) h0
      chainRecvKey_ok := by
        have h0 := cliChainRecvKey_placed_ok W (H := Rust.withPanics extTrap)
        conv at h0 => arg 2; rw [ls_blockPlacement_base (i := 366)]
        exact ls_subroutine_ok_cro_of_callInv
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 366) h0
      chainIntoPb_ok := cliSpqrRecv_chainIntoPb_ok_trTrap mmpl gh W hG hMs hMc hHmac
      messageDeserialize_ok := by
        let _ := instIsLsBlockProg_351 (Rust.withPanics extTrap)
        have h0 := cliMessageDeserialize_placed_ok W (ext := extTrap)
        dsimp only [CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializePlacedOkX] at h0
        exact ls_subroutine_ok_cro_of_callInv
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 351) h0
      statesFromPb_ok :=
        (cliStatesPlacedSeamsExt W (ext := extTrap)).statesFromPb_on
      statesRecv_ok :=
        (cliStatesPlacedSeamsExt W (ext := extTrap)).statesRecv_on
      statesIntoPb_ok := cliStatesIntoPb_recv_trTrap_ok mmpl gh W hG hMs hMc hHmac
      encodeToVec_ok := by
        have h0 := cliEncodeToVec_placed_ok W (ext := extTrap)
        dsimp only [CryptoVerification.SpqrV1.Prost.EncodeToVec.PqRatchetStateEncodeToVecPlacedOkExt] at h0
        have henc_cro :=
          subroutine_ok_mono h0
            (spec' := withLsCodeRoLoaded lsmpl (pqRatchetStateEncodeToVecSpecX CryptoVerification.E2E.HooksE.A0))
            (fun _ _ _ hpre => by
              dsimp only [withLsCodeRoLoaded, CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
                withLsRoLoaded, withLsCodeLoaded, pqRatchetStateEncodeToVecSpecX] at hpre ⊢
              rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
              rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
              refine ⟨hpre.1.2, ?_⟩
              rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
              exact ⟨hpre.1.1, hpre.2⟩)
            (fun _ _ _ _ hpost => hpost)
        exact ls_subroutine_ok_cro_of_cro
          (callerProg := spqrRecvPlacedProg extTrap)
          (i := 329) (j := 426) henc_cro
      h_inner_eq :=
        CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt_canonical_eq_drop CryptoVerification.E2E.HooksE.A0 }

theorem cliSpqrRecv_placed_ok_closed [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 329
        (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 329)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrRecvPlacedInnerSpecXT CryptoVerification.E2E.HooksE.A0 (spqrV1Recv W.C.F W.Q.K))) := by
  have hok := spqr_recv_placed_ok_blockProgram_ext_of_contracts
    (trTrapExternsPlaced_isPanic mmpl gh W)
    (cliSpqrRecvPlacedContracts mmpl gh W hG hMs hMc hHmac)
  have heq_cro (m : Memory) :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m =
        LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  exact subroutine_ok_mono hok
    (fun _ _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, spqrRecvPlacedInnerSpecXT,
        spqrRecvPlacedInnerSpecX, spqrRecvPlacedSpecXT, spqrRecvPlacedSpecX, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecX, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff] at hpre ⊢
      rw [heq_cro s.mem] at hpre
      simpa only [sepConj_assoc] using hpre)
    (fun _ _ _ _ hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, spqrRecvPlacedInnerSpecXT,
        spqrRecvPlacedInnerSpecX, spqrRecvPlacedSpecXT, spqrRecvPlacedSpecX, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecX, CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.lsLogOff] at hpost ⊢
      exact hpost)
    (fun _ _ _ _ hpanic => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, spqrRecvPlacedInnerSpecXT,
        spqrRecvPlacedInnerSpecX, spqrRecvPlacedSpecXT, spqrRecvPlacedSpecX, withLsCodeRoLoaded,
        spqrRecvPlacedRawSpecX] at hpanic ⊢
      exact hpanic)

/-! ### 5. Complete SPQR-V1 Seam Bundle (`SpqrV1PlacedSeams mmpl gh W`) -/

/-- Closed instantiation of `SpqrV1PlacedSeams mmpl gh W` under `[LibsignalPlacement]`. -/
theorem spqrV1PlacedSeams_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks CryptoVerification.E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsLibcruxHmacSymCli
      (libcruxHmacSpec W.C.F CryptoVerification.E2E.HooksE.A0)) :
    SpqrV1PlacedSeams mmpl gh W :=
  { spqrInitialState := cliSpqrInitialState_placed_ok_closed mmpl gh W hG hMs hMc hHmac
    spqrRecv         := cliSpqrRecv_placed_ok_closed mmpl gh W hG hMs hMc hHmac
    spqrSendCoins    := cliSpqrSendCoins_placed_ok_closed mmpl gh W hG hMs hMc hHmac }

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsInst
