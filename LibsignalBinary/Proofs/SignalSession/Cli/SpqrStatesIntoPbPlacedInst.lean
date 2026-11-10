/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.IntoPbClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbClPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Placed `PolyEncoder::into_pb`, `PolyDecoder::into_pb`, and `States::into_pb`

Code-loaded (`withLsCodeLoaded` / `withLsCodeRoLoaded`) contracts under `[CliSpqrExt W ext]` for
`PolyEncoder::into_pb` (Block 375), `PolyDecoder::into_pb` (Block 377), and all 11 arms of
`States::into_pb` (Block 334), lifted to `spqr::send::<Coins>` (Block 427) and `spqr::recv`
(Block 329).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInst

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl lsρ libsignalSessionLib
   libsignalMutatedBlocks withLsCl withLsCodeLoaded
   ls_blockPlacement_base ls_subroutine_ok_cl_of_block
   lsProg_264 lsProg_265 blkPC_375 blkPl_375 blkPC_377 blkPl_377)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1 (libcruxHmacSpec)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded sessionMemcpyRegionSpec)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli
  (CliSpqrExt instCliSpqrExtWithPanics
   cliSpqrExt_self cliSpqrExt_trTrap cliSpqrExt_sessionMemcpyRegion_sat
   cliSpqrSendAllocContractsPlacedExt cliNoAllocShim_at_block cliAlloc_at_block
   cliDealloc_at_block cliFramelessMemcpy_at_block
   spqrSendCoinsPlacedSpecT cliSpqrSendCoins_placed_ok)
open CryptoVerification.SignalSession.Cli.RunGlue (CliGhostHooks cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (CliGhostA0Hooks lsLibcruxHmacSymCli trTrapExternsPlaced)
open CryptoVerification.E2E.HooksE (A0)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (dropGlueSortedSetPt16Spec dropGluePoly16Spec)
open CryptoVerification.SpqrV1.Poly.EncoderIntoPb
  (encoderIntoPbSpec encoderIntoPbSpecX
   encoder_into_pb_cl_placed_ok_ext encoder_into_pb_cl_placed_ok_x)
open CryptoVerification.SpqrV1.Poly.DecoderPb
  (decoderIntoPbSpec decoder_into_pb_cl_placed_ok_ext)
open CryptoVerification.SpqrV1.States.IntoPb
  (StatesIntoPbAllocPlaced StatesIntoPbPlacedOkExt StatesIntoPbPlacedOkX
   statesIntoPbPlacedSpec statesIntoPbPlacedRoSpecX
   states_into_pb_cl_placed_ok_ext states_into_pb_cl_placed_ro_ok_x
   states_into_pb_cl_placed_ro_cro_ok_x states_into_pb_cl_placed_ok_x)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.Top.Recv (spqrRecvPlacedProg ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDropsPlacedInst
  (cliDrop_264_cl cliDrop_265_cl)

private theorem rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

private theorem withLsCodeLoaded_of_withLsCl [LibsignalPlacement] {α : Type}
    {P : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P entry (withLsCl lsmpl spec)) :
    subroutine_ok P entry (withLsCodeLoaded lsmpl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)

private theorem lift_264_cl [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 264 (Rust.withPanics ext))
      264 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_264 (Rust.withPanics ext))
      264 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (cliDrop_264_cl W (ext := ext)) hi (by decide) (by decide))

private theorem lift_265_cl [LibsignalPlacement]
    {callerProg : Program} {i : Nat} (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec A0)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext))
      265 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_265 (Rust.withPanics ext))
      265 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (cliDrop_265_cl W (ext := ext)) hi (by decide) (by decide))

/-! ### 1. Block `375` (`PolyEncoder::into_pb`) and Block `377` (`PolyDecoder::into_pb`) -/

/-- Block `375` (`<PolyEncoder>::into_pb`) on `(blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext)`
    with `withLsCodeLoaded`. -/
theorem cliEncoderIntoPb_375_rebase_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (blkPl_375).base (withLsCodeLoaded lsmpl (encoderIntoPbSpec A0)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  exact encoder_into_pb_cl_placed_ok_ext hA.handle_error hA.shim hA.alloc
    (lift_265_cl (i := 375) W (ext := ext))

/-- own-block code-loaded Block `375` (`<PolyEncoder>::into_pb`),
    generic in `[CliSpqrExt W ext]`. -/
theorem cliEncoderIntoPb_375_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 375 (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A0)) :=
  rebase_to_blockProgram (j := 375) (cliEncoderIntoPb_375_rebase_cl W (ext := ext))

/-- Extended-stack variant (`encoderIntoPbSpecX`) of own-block code-loaded Block `375`. -/
theorem cliEncoderIntoPb_375_cl_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 375 (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpecX A0)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  exact rebase_to_blockProgram (j := 375)
    (encoder_into_pb_cl_placed_ok_x hA.handle_error hA.shim hA.alloc
      (lift_265_cl (i := 375) W (ext := ext)))

/-- Block `377` (`<PolyDecoder>::into_pb`) on `(blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext)`
    with `withLsCodeLoaded`. -/
theorem cliDecoderIntoPb_377_rebase_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (blkPl_377).base (withLsCodeLoaded lsmpl (decoderIntoPbSpec A0)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  exact decoder_into_pb_cl_placed_ok_ext hA.handle_error hA.shim hA.alloc
    (lift_264_cl (i := 377) W (ext := ext))

/-- Own-block code-loaded Block `377` (`<PolyDecoder>::into_pb`), generic in `[CliSpqrExt W ext]`. -/
theorem cliDecoderIntoPb_377_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 377 (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A0)) :=
  rebase_to_blockProgram (j := 377) (cliDecoderIntoPb_377_rebase_cl W (ext := ext))

private theorem lift_375_to_334 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec A0)) := by
  have h := cliEncoderIntoPb_375_rebase_cl W (ext := ext)
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 375)]
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (i := 334) (j := 375) h)

private theorem lift_377_to_334 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec A0)) := by
  have h := cliDecoderIntoPb_377_rebase_cl W (ext := ext)
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 377)]
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (i := 334) (j := 377) h)

/-! ### 2. Block `334` (`States::into_pb`, All 11 Arms) -/

/-- `StatesIntoPbAllocPlaced A0 ext` discharged from `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPbAllocPlaced [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    StatesIntoPbAllocPlaced A0 ext where
  shim_ok := cliNoAllocShim_at_block W
  alloc_ok := cliAlloc_at_block W
  dealloc_ok := cliDealloc_at_block W
  memcpy_ok := cliFramelessMemcpy_at_block W
  panic_ok := (cliSpqrSendAllocContractsPlacedExt W (ext := ext)).handle_error

/-- `sessionMemcpyRegionSpec` on `memcpy` inside Block `334`, discharged from `[CliSpqrExt W ext]`. -/
theorem cliSessionMemcpyRegion_at_334 [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionSpec :=
  spqr_hook_ok_of_mem
    (cliSpqrExt_sessionMemcpyRegion_sat W (ext := Rust.withPanics ext))
    (by decide) (by decide) (by decide)

/-- `StatesIntoPbPlacedOkExt A0 W.C.F ext` (code-loaded Block `334`, all 11 arms),
    generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_placed_ok_ext [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    StatesIntoPbPlacedOkExt A0 W.C.F ext :=
  states_into_pb_cl_placed_ok_ext
    (cliStatesIntoPbAllocPlaced W (ext := ext))
    (lift_375_to_334 W (ext := ext))
    (lift_377_to_334 W (ext := ext))
    (cliSessionMemcpyRegion_at_334 W (ext := ext))

/-- own-block code-loaded Block `334` (`<States>::into_pb`, all 11 arms),
    generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_cl [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedSpec A0 W.C.F)) :=
  rebase_to_blockProgram (j := 334)
    (cliStatesIntoPb_334_placed_ok_ext W (ext := ext))

/-- Extended-stack `statesIntoPbPlacedRoSpecX` on `blockProgram lsmpl 334` with `withLsCodeLoaded`. -/
theorem cliStatesIntoPb_334_ro_cl_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbPlacedRoSpecX A0 W.C.F)) :=
  rebase_to_blockProgram (j := 334)
    (states_into_pb_cl_placed_ro_ok_x (F := W.C.F)
      (cliStatesIntoPbAllocPlaced W (ext := ext))
      (lift_375_to_334 W (ext := ext))
      (lift_377_to_334 W (ext := ext))
      (cliSessionMemcpyRegion_at_334 W (ext := ext)))

/-- `InitInner.StatesIntoPbPlacedOkX A0 W.C.F ext` for Block `324` (`spqr::init_inner`). -/
theorem cliStatesIntoPb_initInner_ok_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CryptoVerification.SpqrV1.Top.InitInner.StatesIntoPbPlacedOkX A0 W.C.F ext :=
  cliStatesIntoPb_334_ro_cl_x W (ext := ext)

/-! ### 3. `spqr::send::<Coins>` (`427`) and `spqr::recv` (`329`) -/

/-- `StatesIntoPbPlacedOkX A0 W.C.F ext` (`withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX A0 W.C.F)`
    on `(blkPC_334).rebase`), generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_placed_ok_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    StatesIntoPbPlacedOkX A0 W.C.F ext :=
  states_into_pb_cl_placed_ok_x
    (cliStatesIntoPbAllocPlaced W (ext := ext))
    (lift_375_to_334 W (ext := ext))
    (lift_377_to_334 W (ext := ext))
    (cliSessionMemcpyRegion_at_334 W (ext := ext))

/-- Rebase form: `statesIntoPbPlacedRoSpecX` in `withLsCodeRoLoaded` form
    on `(blkPC_334).rebase`, generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_ro_cro_rebase [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (blkPl_334).base
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecX A0 W.C.F)) :=
  states_into_pb_cl_placed_ro_cro_ok_x
    (cliStatesIntoPbAllocPlaced W (ext := ext))
    (lift_375_to_334 W (ext := ext))
    (lift_377_to_334 W (ext := ext))
    (cliSessionMemcpyRegion_at_334 W (ext := ext))

/-- Own-block `blockprogram` form: `statesIntoPbPlacedRoSpecX` in `withLsCodeRoLoaded`
    form on `libsignalSessionLib.blockProgram lsmpl 334`, generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_ro_cro_ok_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedRoSpecX A0 W.C.F)) :=
  rebase_to_blockProgram (j := 334)
    (cliStatesIntoPb_334_ro_cro_rebase W (ext := ext))

/-- Own-block `withLsCodeRoLoaded` contract for `Cli.SpqrV1.Top.Send.statesIntoPbPlacedSpecX`,
    generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_334_cro_ok_x [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbPlacedSpecX A0 W.C.F)) :=
  cliStatesIntoPb_334_ro_cro_ok_x W (ext := ext)

/-- exact `hStatesIntoPb` hypothesis of `cliSpqrSendCoins_placed_ok` (`Block 427`). -/
theorem cliStatesIntoPb_sendCoins_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.SpqrV1.Top.Send.statesIntoPbPlacedSpecX A0 W.C.F)) := by
  have : CliSpqrExt W (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact cliStatesIntoPb_334_cro_ok_x W (ext := cliGhostExterns gh (cliExternsPlaced mmpl W))

/-- Block `427` (`cliSpqrSendCoins_placed_ok`) with `hStatesIntoPb` discharged directly by
    `cliStatesIntoPb_sendCoins_ok`. -/
theorem cliSpqrSendCoins_with_statesIntoPb [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0))
    (hChainFromPb : subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendPlacedProg
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 364)
      (withLsCodeRoLoaded lsmpl (CryptoVerification.SpqrV1.Top.ChainFrom.chainFromPbSpecX A0)))
    (hChainIntoPb : subroutine_ok
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrSendPlacedProg
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 365)
      (withLsCodeRoLoaded lsmpl (CryptoVerification.SpqrV1.ChainProofs.chainIntoPbSpecX A0)))
    (hDecodeState : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.decodeStatePlacedSpecX
          CryptoVerification.SpqrV1.Top.DecodeState.canonicalV1InnerHeap A0))) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT A0 0#64
          (CryptoVerification.E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) :=
  cliSpqrSendCoins_placed_ok mmpl gh W hG hMs hMc hHmac hChainFromPb hChainIntoPb hDecodeState
    (cliStatesIntoPb_sendCoins_ok mmpl gh W hG hMs hMc hHmac)

/-- `spqr: :recv` (`Block 329`) caller form: exact `statesIntoPb_ok` field type of
    `SpqrRecvPlacedContracts`, generic in `[CliSpqrExt W ext]`. -/
theorem cliStatesIntoPb_recv_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.Recv.statesIntoPbPlacedSpecX A0 W.C.F)) := by
  have h := cliStatesIntoPb_334_ro_cro_rebase W (ext := ext)
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 334)]
  exact ls_subroutine_ok_cro_of_cro (i := 329) (j := 334) h

/-- Exact `statesIntoPb_ok` field of `SpqrRecvPlacedContracts` specialized to
    `ext = trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))` (`SpqrV1PlacedSeams.spqrRecv`). -/
theorem cliStatesIntoPb_recv_trTrap_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostA0Hooks A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W))
      lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F A0)) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.Recv.statesIntoPbPlacedSpecX A0 W.C.F)) := by
  have : CliSpqrExt W (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    cliSpqrExt_trTrap mmpl gh W hG hMs hMc hHmac
  exact cliStatesIntoPb_recv_ok W
    (ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInst
