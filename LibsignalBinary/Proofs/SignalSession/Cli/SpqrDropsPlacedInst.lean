/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlaced
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochPlaced
import LibsignalBinary.Proofs.SpqrV1.Drop.Chunked
import LibsignalBinary.Proofs.SpqrV1.Drop.Poly
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyDecoder
import LibsignalBinary.Proofs.SpqrV1.Drop.PolyEncoder
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChain
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked1
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChunked2
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoPoly
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPt
import LibsignalBinary.Proofs.SpqrV1.Drop.States2
import LibsignalBinary.Proofs.SpqrV1.Drop.Unchunked
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Placed Drop & Chain Callee Instantiations for `SpqrV1PlacedSeams`

Code-loaded placed contracts for SPQR drop and chain callees under `[CliSpqrExt W ext]`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl libsignalSessionLib withLsCodeLoaded
   subroutine_ok_withLsCodeLoaded_of_plain ls_blockPlacement_base)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli
  (CliSpqrExt instCliSpqrExtWithPanics cliSpqrExt_dealloc_sat
   cliDealloc_at_block cliDrop_287 cliDrop_288)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Drop
  (dropGlueSortedSetPt16Spec dropGluePoly16Spec
   dropChainEpochSliceSpec dropProtoEpochSliceSpec)
open CryptoVerification.SpqrV1.States.Recv
  (drop_glue_sorted_set_pt16_cl_blockProgram drop_glue_poly16_cl_blockProgram)

theorem cliDrop_264_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 264 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A0)) :=
  drop_glue_sorted_set_pt16_cl_blockProgram
    (cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext))

theorem cliDrop_265_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext)) (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A0)) :=
  drop_glue_poly16_cl_blockProgram
    (cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext))

theorem cliDrop_287_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_287).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base H)
      (lsmpl.base 287)
      (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 287)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (cliDrop_287 W)

theorem cliDrop_288_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((CryptoVerification.blkPC_288).rebase
        (CryptoVerification.blkPl_288).base H)
      (lsmpl.base 288)
      (withLsCodeLoaded lsmpl (dropProtoEpochSliceSpec A0)) := by
  rw [← ls_blockPlacement_base (i := 288)]
  exact subroutine_ok_withLsCodeLoaded_of_plain (cliDrop_288 W)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
