/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbClPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Code-Loaded Placed `spqr::chain::Chain` (Blocks `364, 365, 323`) CLI Instantiations

Establishes code-loaded `[LibsignalPlacement]` contracts under `[CliSpqrExt W H]` for
`<spqr::chain::Chain>::from_pb` (Block `364`), `<spqr::chain::Chain>::into_pb` (Block `365`), and
`Chain::from` (Block `323`), discharging the chain conversion hypotheses of `spqrSendPlacedProg` and
`SpqrRecvPlacedContracts` on `spqrRecvPlacedProg` (including `trTrapExternsPlaced`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement lsmpl libsignalSessionLib libsignalMutatedBlocks lsρ
   IsLsBlockProg withLsCodeLoaded
   ls_blockPlacement_base ls_subroutine_ok_of_block ls_externAt?_of_mem
   blkPC_364 blkPl_364 instIsLsBlockProg_364
   blkPC_365 blkPl_365 instIsLsBlockProg_365)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1 (spqrHkdfWith libcruxHmacSpec)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded sessionShimSpec)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (CliSpqrExt instCliSpqrExtWithPanics
   cliSpqrExt_self cliSpqrExt_trTrap
   cliSpqrExt_shim_sat cliSpqrExt_panic_handle_error
   cliAlloc_at_block cliDealloc_at_block cliChainNew_placed_ok cliSpqrSendCoins_placed_ok)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (CliGhostA0Hooks lsLibcruxHmacSymCli trTrapExternsPlaced)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ChainProofs
  (chainIntoPbSpecX chainNewSpecX
   chain_from_pb_cl_placed_ok chain_into_pb_cl_placed_ok_X)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (withLsCallInv subroutine_ok_withLsCallInv_of_withLsCodeLoaded)
open CryptoVerification.SpqrV1.Top.ChainFrom
  (chainFromPbSpecX chainFromSpecX chainFrom_placed_ok_of_contracts_x)
open CryptoVerification.SpqrV1.Top.DecodeState (canonicalV1InnerHeap decodeStatePlacedSpecX)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_323 blkPl_323 instIsLsBlockProg_323)
open CryptoVerification.SpqrV1.Top.Recv
  (spqrRecvPlacedProg ls_subroutine_ok_cro_of_cl
   ls_subroutine_ok_cro_of_callInv ls_subroutine_ok_callInv_of_callInv)
open CryptoVerification.SpqrV1.Top.Recv.Placed (instIsLsBlockProg_329)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (spqrSendPlacedProg spqrSendCoinsPlacedSpecT statesIntoPbPlacedSpecX)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (instIsLsBlockProg_427)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
  (cliDrop_287_cl cliDrop_288_cl)

private theorem cliSessionShim_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      sessionShimSpec :=
  spqr_hook_ok_of_mem
    (cliSpqrExt_shim_sat W)
    (by decide) hi hunmut

/-! ## Own-block `withLsCodeLoaded` contracts for Blocks `364` and `365` -/

/-- Block `364` (`<spqr::chain::Chain>::from_pb`) with `withLsCodeLoaded lsmpl` under `[CliSpqrExt W H]`. -/
theorem cliChainFromPb_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_364).rebase (blkPl_364).base H)
      (lsmpl.base 364)
      (withLsCodeLoaded lsmpl (chainFromPbSpecX A0)) := by
  rw [← ls_blockPlacement_base (i := 364)]
  exact chain_from_pb_cl_placed_ok
    (cliDealloc_at_block W)
    (ls_subroutine_ok_of_block (i := 364) (j := 287) (cliDrop_287_cl W))
    (ls_subroutine_ok_of_block (i := 364) (j := 288) (cliDrop_288_cl W))

/-- Block `365` (`<spqr::chain::Chain>::into_pb`) with `withLsCodeLoaded lsmpl` under `[CliSpqrExt W H]`. -/
theorem cliChainIntoPb_cl [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 365)
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX A0)) := by
  rw [← ls_blockPlacement_base (i := 365)]
  exact chain_into_pb_cl_placed_ok_X
    (cliSessionShim_at_block W)
    (cliAlloc_at_block W)
    (cliDealloc_at_block W)
    (ls_subroutine_ok_of_block (i := 365) (j := 287) (cliDrop_287_cl W))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W))

theorem cliChainFromPb_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 364 (Rust.withPanics ext))
      (lsmpl.base 364)
      (withLsCodeLoaded lsmpl (chainFromPbSpecX A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))]
  exact cliChainFromPb_cl W

theorem cliChainIntoPb_blockProgram_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 365 (Rust.withPanics ext))
      (lsmpl.base 365)
      (withLsCodeLoaded lsmpl (chainIntoPbSpecX A0)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))]
  exact cliChainIntoPb_cl W

/-! ## `spqrSendPlacedProg` contracts -/

theorem cliSpqrSend_chainFromPb_ok_ext [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A0)) :=
  ls_subroutine_ok_cro_of_cl (i := 427) (j := 364)
    (cliChainFromPb_cl W (H := Rust.withPanics ext))

theorem cliSpqrSend_chainIntoPb_ok_ext [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A0)) :=
  ls_subroutine_ok_cro_of_cl (i := 427) (j := 365)
    (cliChainIntoPb_cl W (H := Rust.withPanics ext))

theorem cliSpqrSend_chainFromPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 364)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (chainFromPbSpecX CryptoVerification.E2E.HooksE.A0)) := by
  have : CliSpqrExt W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact cliSpqrSend_chainFromPb_ok_ext W

theorem cliSpqrSend_chainIntoPb_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 365)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (chainIntoPbSpecX CryptoVerification.E2E.HooksE.A0)) := by
  have : CliSpqrExt W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact cliSpqrSend_chainIntoPb_ok_ext W

/-- Specializes `cliSpqrSendCoins_placed_ok` by discharging `hChainFromPb` (Block `364`) and `hChainIntoPb` (Block `365`). -/
theorem cliSpqrSendCoins_placed_ok_of_decode_intoPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0))
    (hDecodeState : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX canonicalV1InnerHeap CryptoVerification.E2E.HooksE.A0)))
    (hStatesIntoPb : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (statesIntoPbPlacedSpecX CryptoVerification.E2E.HooksE.A0 W.C.F))) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT CryptoVerification.E2E.HooksE.A0 0#64
          (pqxdhSpqrModel ⟨W.C, W.Q⟩))) :=
  cliSpqrSendCoins_placed_ok mmpl gh W hG hMs hMc hHmac
    (cliSpqrSend_chainFromPb_ok mmpl gh W hG hMs hMc hHmac)
    (cliSpqrSend_chainIntoPb_ok mmpl gh W hG hMs hMc hHmac)
    hDecodeState hStatesIntoPb

/-! ## `spqrRecvPlacedProg` contracts (`SpqrRecvPlacedContracts`) -/

theorem spqrRecv_chainFromPb_ok_of_cl [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hChainFromPb : subroutine_ok ((blkPC_364).rebase (blkPl_364).base (Rust.withPanics ext))
      (lsmpl.base 364) (withLsCodeLoaded lsmpl (chainFromPbSpecX A))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A)) :=
  ls_subroutine_ok_cro_of_cl (i := 329) (j := 364) hChainFromPb

theorem spqrRecv_chainIntoPb_ok_of_cl [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hChainIntoPb : subroutine_ok ((blkPC_365).rebase (blkPl_365).base (Rust.withPanics ext))
      (lsmpl.base 365) (withLsCodeLoaded lsmpl (chainIntoPbSpecX A))) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A)) :=
  ls_subroutine_ok_cro_of_cl (i := 329) (j := 365) hChainIntoPb

/-- Discharges `SpqrRecvPlacedContracts.chainFromPb_ok` (Block `364`) on `spqrRecvPlacedProg ext`. -/
theorem cliSpqrRecv_chainFromPb_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A0)) :=
  spqrRecv_chainFromPb_ok_of_cl (cliChainFromPb_cl W)

/-- Discharges `SpqrRecvPlacedContracts.chainIntoPb_ok` (Block `365`) on `spqrRecvPlacedProg ext`. -/
theorem cliSpqrRecv_chainIntoPb_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A0)) :=
  spqrRecv_chainIntoPb_ok_of_cl (cliChainIntoPb_cl W)

/-- Discharges `SpqrRecvPlacedContracts.chainFrom_ok` (Block `323`) on `spqrRecvPlacedProg ext`. -/
theorem cliSpqrRecv_chainFrom_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) A0)) := by
  have h_fpb_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 364) (withLsCallInv lsmpl (chainFromPbSpecX A0)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 364)
      (subroutine_ok_withLsCallInv_of_withLsCodeLoaded
        (cliChainFromPb_cl W (H := Rust.withPanics ext)))
  have h_new_323 : subroutine_ok ((blkPC_323).rebase (blkPl_323).base (Rust.withPanics ext))
      (lsmpl.base 363) (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) A0)) :=
    ls_subroutine_ok_callInv_of_callInv (i := 323) (j := 363)
      (cliChainNew_placed_ok W (H := Rust.withPanics ext))
  exact ls_subroutine_ok_cro_of_callInv (i := 329) (j := 323)
    (chainFrom_placed_ok_of_contracts_x h_fpb_323 h_new_323)

theorem cliSpqrRecv_chainFromPb_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 364) (withLsCodeRoLoaded lsmpl (chainFromPbSpecX A0)) := by
  have : CliSpqrExt W (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliSpqrRecv_chainFromPb_ok W

theorem cliSpqrRecv_chainIntoPb_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 365) (withLsCodeRoLoaded lsmpl (chainIntoPbSpecX A0)) := by
  have : CliSpqrExt W (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliSpqrRecv_chainIntoPb_ok W

theorem cliSpqrRecv_chainFrom_ok_trTrap [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 323) (withLsCodeRoLoaded lsmpl (chainFromSpecX (spqrHkdfWith W.C.F) A0)) := by
  have : CliSpqrExt W (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliSpqrRecv_chainFrom_ok W

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInst
