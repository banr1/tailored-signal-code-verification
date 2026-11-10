/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeams
public import LibsignalBinary.Proofs.SpecLemmas.LibsignalE2E.PqxdhCorrectModelProofDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CoinsBridgePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlaced
public import LibsignalBinary.Proofs.Placed.SubsetA4
public import LibsignalBinary.Proofs.Placed.SubsetA4b
public import LibsignalBinary.Proofs.Placed.SubsetA4c
public import LibsignalBinary.Proofs.Placed.SubsetA4d
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlaced
import LibsignalBinary.Proofs.SignalSession.Coins.Fill
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKey
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKey
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.MessageDeserializePlaced
import LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.ContractsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoin

/-!
# Placed `spqr::send::<Coins>` & SPQR-V1 Peer Leaf Instantiations

Integrates `spqr::send::<Coins>` (Block 427), `spqr::initial_state` (Block 327), and their
placed allocator, chain, authenticator, drop, and message-codec callees on `cliGhostExterns`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Keys
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook)
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.SignalSession.Coins
open CryptoVerification.SignalSession.Coins.Placed
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send (spqrSendCalleeStack)
open CryptoVerification.Cli.SpqrV1.Top.Send

private theorem cliGhostExterns_eq_of_base (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) {sym : String} {v : Option (State → State)}
    (h : cliExternsPlaced mmpl W sym = v)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym = v :=
  (RunGlue.cliGhostExterns_other gh (cliExternsPlaced mmpl W) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans h

theorem spqrCoinsFillSpecPlaced_eq_coinsFillSpecPlaced [LibsignalPlacement] :
    CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillSpecPlaced =
      CryptoVerification.SignalSession.Coins.coinsFillSpecPlaced := rfl

theorem cliSpqrSend_coinsFill_ok_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 618
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 618)
      (CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillSpecPlaced spqrSendCalleeStack) := by
  rw [RunGlue.withPanics_cliGhostExterns mmpl gh W,
    (Placed.instIsLsBlockProg_618
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))).eq_blockProgram.symm,
    spqrCoinsFillSpecPlaced_eq_coinsFillSpecPlaced]
  exact CryptoVerification.SignalSession.Coins.coinsFillPlaced_ok
    (Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG)
    (Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG)
    spqrSendCalleeStack (by decide) (by decide)

private theorem instHkdfPlacedHooks_cli
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook) :
    HkdfPlacedHooks W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  memset := RunGlue.cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hMs
  memcpy := RunGlue.cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hMc
  compress256 := cliGhostExterns_eq_of_base mmpl gh W
    (RunGlue.cliExternsPlaced_row mmpl W (Slots.compress256_row_placed mmpl W))

private theorem instHkdfPlacedHooks_withPanics_cli
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook) :
    HkdfPlacedHooks W.C.F (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  (RunGlue.withPanics_cliGhostExterns mmpl gh W).symm ▸ instHkdfPlacedHooks_cli mmpl gh W hMs hMc

theorem cliRecvCt2PlacedAlloc [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    CryptoVerification.SpqrV1.States.RecvCt2Chunk.RecvCt2PlacedAlloc E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { handleError := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_panic_handle_error mmpl gh W
    assertFailedU64 := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_assert_yy mmpl W)
    sliceIndexFail := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_slice_index_fail mmpl W)
    unwrapFailed := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_result_unwrap_failed mmpl W)
    panicBoundsCheck := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_bounds_check mmpl W)
    panicConstAddOverflow := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_add_overflow mmpl W)
    shim := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq
    alloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_alloc_sat mmpl gh W hG
    allocZeroed := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_allocZeroed_sat mmpl gh W hG
    dealloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG
    realloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_realloc_sat mmpl gh W hG
    memcpy := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG
    memcpyRO := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_memcpyRegionRO_sat mmpl gh W hG }

theorem cliStatesPlacedSeams [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    CryptoVerification.SpqrV1.StatesPlacedSeams E2E.HooksE.A0 W.C.F W.Q.K
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  letI := instHkdfPlacedHooks_withPanics_cli mmpl gh W hMs hMc
  LibsignalBinary.Proofs.Placed.SubsetA4c.statesPlacedSeams_of_hooks
    (cliRecvCt2PlacedAlloc mmpl gh W hG)
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W 0))
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG)
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_mlkemValidatePk_sat mmpl W))
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_mlkemEncaps2_sat mmpl W))
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (Slots.cliExternsPlaced_mlkemDecaps_sat mmpl W))
    (by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_libcruxHmac_sat mmpl gh W hHmac)

theorem cliSpqrSendPeerSeams_of_peers [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hDecodeState : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)))
    (hEncodeVarint : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 326
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 326)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX E2E.HooksE.A0)))
    (hChainFromVn : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 328
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 328)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)))
    (hStatesIntoPb : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX E2E.HooksE.A0 W.C.F)))
    (hMessageSerialize : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 352)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi E2E.HooksE.A0))) :
    CliSpqrSendPeerSeams E2E.HooksE.A0 W.C (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  let hS := cliStatesPlacedSeams mmpl gh W hG hMs hMc hHmac
  { decodeState_ok := hDecodeState
    encodeVarint_ok := hEncodeVarint
    chainFromVn_ok := hChainFromVn
    statesFromPb_ok := hS.statesFromPb_ok
    statesIntoPb_ok := hStatesIntoPb
    messageSerialize_ok := hMessageSerialize
    headerSentSendEkChunk_ok := hS.headerSentSendEkChunk_ok
    ct1ReceivedSendEkChunk_ok := hS.ct1ReceivedSendEkChunk_ok
    ct1SampledSendCt1Chunk_ok := hS.ct1SampledSendCt1Chunk_ok
    ekReceivedCt1SampledSendCt1Chunk_ok := hS.ekReceivedCt1SampledSendCt1Chunk_ok
    ct2SampledSendCt2Chunk_ok := hS.ct2SampledSendCt2Chunk_ok
    coinsFill_ok := cliSpqrSend_coinsFill_ok_cli mmpl gh W hG }

theorem cliSpqrSendAllocContractsPlaced
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    AllocContractsPlaced E2E.HooksE.A0 (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  { handle_error := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliGhostExterns_panic_handle_error mmpl gh W
    shim := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq
    alloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_alloc_sat mmpl gh W hG
    dealloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG
    realloc := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_realloc_sat mmpl gh W hG
    session_memcpy stk := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_sessionMemcpy_sat mmpl gh W hG stk
    session_memset_region := by
      rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
      exact Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG }

theorem cliPolyNextChunkPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    CryptoVerification.Cli.SpqrV1.Top.Send.PolyNextChunkPlacedOkX E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  CryptoVerification.Cli.SpqrV1.Top.Send.ls_subroutine_ok_of_blockProgram_cro
    (CryptoVerification.Cli.SpqrV1.Top.Send.ls_subroutine_ok_to_blockProgram
      (CryptoVerification.SpqrV1.Poly.NextChunk.poly_next_chunk_placed_ok_ext
        (cliSpqrSendAllocContractsPlaced mmpl gh W hG)))

theorem cliEncodeBytesPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    CryptoVerification.Cli.SpqrV1.Top.Send.EncodeBytesPlacedOkX E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hA := cliSpqrSendAllocContractsPlaced mmpl gh W hG
  have hraw := CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_placed_ok_x
    hA.handle_error hA.shim hA.alloc (hA.session_memcpy _)
  exact @CryptoVerification.Cli.SpqrV1.Top.Send.ls_subroutine_ok_cro_of_plain _ _
    (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) _ 427 417
    (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced.instIsLsBlockProg_427
      (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (CryptoVerification.instIsLsBlockProg_417
      (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (lsmpl.base 417) (CryptoVerification.SpqrV1.Poly.EncodeBytes.encodeBytesSpecX E2E.HooksE.A0)
    hraw (by decide) (by decide) (by decide)

theorem cliHkdfToVec_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook) :
    subroutine_ok (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 378)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (hkdfToVecSpec E2E.HooksE.A0 (spqrHkdfWith W.C.F))) := by
  have := instHkdfPlacedHooks_withPanics_cli mmpl gh W hMs hMc
  have hA := cliRecvCt2PlacedAlloc mmpl gh W hG
  exact CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_vec_spqr_placed_ok_of_other_block
    (i := 427) W.C E2E.HooksE.A0 hA.handleError hA.shim hA.allocZeroed

theorem cliEncodeVarint_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 326
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 326)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX E2E.HooksE.A0)) := by
  have hA := cliRecvCt2PlacedAlloc mmpl gh W hG
  exact LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (spqrEncodeVarint_placed_ok_of_hookSat_x E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      hA.handleError hA.shim hA.alloc hA.realloc)

/-- Block `341` (`<Authenticator>::update`) on
    `spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))` is
    satisfied unconditionally via `Auth.authUpdate_placed_ok`. -/
theorem cliAuthUpdate_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook) :
    subroutine_ok (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 341)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (authUpdateSpec W.C.F E2E.HooksE.A0)) := by
  have := instHkdfPlacedHooks_withPanics_cli mmpl gh W hMs hMc
  have hA := cliRecvCt2PlacedAlloc mmpl gh W hG
  have hconcat_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec E2E.HooksE.A0)) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (ls_subroutine_ok_of_block (i := 341) (j := 386)
          (subroutine_ok_withLsCodeLoaded_of_plain
            (CryptoVerification.SpqrV1.Alloc.slice_concat_2_placed_ok hA.handleError
              hA.shim hA.alloc hA.memcpy hA.memcpyRO))))
  have hhkdf_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 379)
      (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F))) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok_of_other_block W.C)
  have hupd_341 :=
    CryptoVerification.SpqrV1.Auth.authUpdate_placed_ok hconcat_341 hhkdf_341
      (hA.shim_at_block extHookStack)
      hA.alloc_at_block
      hA.allocZeroed_at_block
      hA.dealloc_at_block
      hA.panic_handle_error
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 341)
    (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      hupd_341)

/-- Block `342` (`<Authenticator>::mac_hdr`) on
    `spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))` is
    satisfied unconditionally via `Auth.authMacHdr_placed_ok`. -/
theorem cliAuthMacHdr_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    subroutine_ok (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 342)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (authMacHdrSpec W.C.F E2E.HooksE.A0)) := by
  have hA := cliRecvCt2PlacedAlloc mmpl gh W hG
  have hconcat_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat3Spec E2E.HooksE.A0)) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (ls_subroutine_ok_of_block (i := 342) (j := 386)
          (subroutine_ok_withLsCodeLoaded_of_plain
            (CryptoVerification.SpqrV1.Alloc.slice_concat_3_placed_ok hA.handleError
              hA.shim hA.alloc hA.memcpy hA.memcpyRO))))
  have hhmac_sat : HookSat (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      "_RNvCs65XVORQObL2_12libcrux_hmac4hmac" (libcruxHmacSpec W.C.F E2E.HooksE.A0) := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliExternsPlaced_libcruxHmac_sat mmpl gh W hHmac
  have hhmac_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain
        (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hhmac_sat))
  have hmac_342 :=
    CryptoVerification.SpqrV1.Auth.authMacHdr_placed_ok
      hconcat_342 hhmac_342 hA.dealloc_at_block
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 342)
    (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      hmac_342)

/-- Block `342` (`<Authenticator>::mac_hdr` pinned) on
    `spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))`
    is satisfied unconditionally via `Auth.authMacHdrPinned_placed_ok`. -/
theorem cliAuthMacHdrPinnedPlacedOkX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    AuthMacHdrPinnedPlacedOkX W.C.F E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hA := cliRecvCt2PlacedAlloc mmpl gh W hG
  have hconcat_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat3Spec E2E.HooksE.A0)) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
        (ls_subroutine_ok_of_block (i := 342) (j := 386)
          (subroutine_ok_withLsCodeLoaded_of_plain
            (CryptoVerification.SpqrV1.Alloc.slice_concat_3_placed_ok hA.handleError
              hA.shim hA.alloc hA.memcpy hA.memcpyRO))))
  have hhmac_sat : HookSat (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      "_RNvCs65XVORQObL2_12libcrux_hmac4hmac" (libcruxHmacSpec W.C.F E2E.HooksE.A0) := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliExternsPlaced_libcruxHmac_sat mmpl gh W hHmac
  have hhmac_342 : subroutine_ok
      ((blkPC_342).rebase (blkPl_342).base
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsρ "_RNvCs65XVORQObL2_12libcrux_hmac4hmac")
      (withLsCallInv lsmpl (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_plain
        (CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem hhmac_sat))
  have hmac_342 :=
    CryptoVerification.SpqrV1.Auth.authMacHdrPinned_placed_ok
      hconcat_342 hhmac_342 hA.dealloc_at_block
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 342)
    (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      hmac_342)

theorem spqrSendExtraContractsPlaced_of_cli [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hMacHdrPinned : AuthMacHdrPinnedPlacedOkX W.C.F E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
        cliAuthMacHdrPinnedPlacedOkX mmpl gh W hG hHmac) :
    SpqrSendExtraContractsPlaced E2E.HooksE.A0 0#64 W.C W.Q.K
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  panic_hook := cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_panic mmpl W)
  panicSubOverflow_hook := cliGhostExterns_eq_of_base mmpl gh W
    (Slots.cliExternsPlaced_panic_sub_overflow mmpl W)
  unwrapFailed_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_eq_of_base mmpl gh W
      (Slots.cliExternsPlaced_panic_result_unwrap_failed mmpl W)
  allocZeroed_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliExternsPlaced_allocZeroed_sat mmpl gh W hG
  mlkemFromSeed_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemFromSeed_sat mmpl W)
  mlkemPk1_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemPk1_sat mmpl W)
  mlkemPk2_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemPk2_sat mmpl W)
  mlkemEncaps1_hook := by
    rw [RunGlue.withPanics_cliGhostExterns mmpl gh W]
    exact Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemEncaps1_sat mmpl W)
  fromSeed_pk1_slice := W.Q.K.fromSeed_pk1
  fromSeed_pk2_slice := W.Q.K.fromSeed_pk2
  macHdrPinned_ok := hMacHdrPinned
  doReserve2_ok := CryptoVerification.Cli.SpqrV1.Top.Send.doReserve2_placed_ok_ext_x
    (cliSpqrSendAllocContractsPlaced mmpl gh W hG)
  dropChainEpochSlice_raw_ok := spqrSend_dropChainEpochSlice_raw_ok_of_dealloc
    (cliSpqrSendAllocContractsPlaced mmpl gh W hG).dealloc
  dropChunkedStates_ok := spqrSend_dropChunkedStates_ok_of_dealloc
    (cliSpqrSendAllocContractsPlaced mmpl gh W hG).dealloc

theorem spqrSendCoins_placed_seam_of_contracts [LibsignalPlacement]
    {mmpl : Obj.MultiPlacement} {gh : RunGlue.CliGhostHooks} {W : CliHooks}
    {H_inner : V1InnerHeapPred}
    (hC : SpqrSendPlacedContracts H_inner E2E.HooksE.A0 0#64 W.C W.Q.K
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hE : SpqrSendExtraContractsPlaced E2E.HooksE.A0 0#64 W.C W.Q.K
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SignalSession.Cli.spqrSendCoinsPlacedSpecT
          E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) := by
  have hp : ∀ sym, Rust.isPanicSymbol sym = true →
      RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
    intro sym hsym
    have h := congrFun (RunGlue.withPanics_cliGhostExterns mmpl gh W) sym
    simp only [Rust.withPanics, hsym, ↓reduceIte] at h; exact h.symm
  exact spqrSendCoins_placed_ok_at_prog_ext_of_contracts
    (hcaller := CryptoVerification.CliRatchet.SendPlaced.instIsLsBlockProg_427
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    hp hC hE

theorem spqrSendCoins_placed_seam_of_peer_contracts [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hChainFromPb : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 364)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainFromPbSpecX E2E.HooksE.A0)))
    (hChainAddEpoch : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 368)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)))
    (hChainSendKey : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 367)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)))
    (hChainIntoPb : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 365)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainIntoPbSpecX E2E.HooksE.A0)))
    (hAuthMacHdr : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 342)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (authMacHdrSpec W.C.F E2E.HooksE.A0)))
    (hAuthUpdate : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 341)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (authUpdateSpec W.C.F E2E.HooksE.A0)))
    (hHkdfToVec : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 378)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (hkdfToVecSpec E2E.HooksE.A0 (spqrHkdfWith W.C.F))))
    (hDecodeState : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (decodeStatePlacedSpecX canonicalV1InnerHeap E2E.HooksE.A0)))
    (hEncodeVarint : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 326
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 326)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX E2E.HooksE.A0)))
    (hChainFromVn : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 328
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 328)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)))
    (hStatesIntoPb : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX E2E.HooksE.A0 W.C.F)))
    (hMessageSerialize : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 352)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi E2E.HooksE.A0)))
    (hMacHdrPinned : AuthMacHdrPinnedPlacedOkX W.C.F E2E.HooksE.A0
      (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SignalSession.Cli.spqrSendCoinsPlacedSpecT
          E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) :=
  spqrSendCoins_placed_seam_of_contracts
    (spqrSendPlacedContracts_of_okX
      (cliSpqrSendAllocContractsPlaced mmpl gh W hG)
      hChainFromPb hChainAddEpoch hChainSendKey hChainIntoPb
      hAuthMacHdr hAuthUpdate hHkdfToVec
      (cliEncodeBytesPlacedOkX mmpl gh W hG) (cliPolyNextChunkPlacedOkX mmpl gh W hG)
      (cliSpqrSendPeerSeams_of_peers mmpl gh W hG hMs hMc hHmac
        hDecodeState hEncodeVarint hChainFromVn hStatesIntoPb hMessageSerialize))
    (spqrSendExtraContractsPlaced_of_cli mmpl gh W hG hHmac hMacHdrPinned)

/-- External hook table class matching `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)` on all
non-RNG symbols for some `(mmpl, gh)` satisfying `CliGhostA0Hooks`, stock `memset`/`memcpy` hooks,
and the `libcrux_hmac` contract (satisfied by both `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`
and its `trTrapExternsPlaced` wrap, while keeping `[CliSpqrExt W ext]` 2-argument for downstream SPQR modules). -/
class CliSpqrExt (W : CliHooks) (ext : String → Option (State → State)) : Prop where
  exists_ghost :
    ∃ (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks),
      Slots.CliGhostA0Hooks E2E.HooksE.A0 gh ∧
      gh.memset = some memsetHook ∧
      gh.memcpy = some memcpyHook ∧
      HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
        Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0) ∧
      ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
        ext sym = RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym

theorem cliSpqrExt_self (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    CliSpqrExt W (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ⟨⟨mmpl, gh, hG, hMs, hMc, hHmac, fun _ _ => rfl⟩⟩

theorem cliSpqrExt_trTrap (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0)) :
    CliSpqrExt W (Slots.trTrapExternsPlaced (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
  ⟨⟨mmpl, gh, hG, hMs, hMc, hHmac, fun sym hne => by
    simp [Slots.trTrapExternsPlaced, Slots.lsRngFillSym, trapAt, hne]⟩⟩

instance instCliSpqrExtWithPanics (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CliSpqrExt W (Rust.withPanics ext) where
  exists_ghost := by
    obtain ⟨mmpl, gh, hG, hMs, hMc, hHmac, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := ext)
    refine ⟨mmpl, gh, hG, hMs, hMc, hHmac, fun sym hne => ?_⟩
    have h1 : Rust.withPanics ext sym =
        Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
      simp only [Rust.withPanics, heq sym hne]
    exact h1.trans (congrFun (RunGlue.withPanics_cliGhostExterns mmpl gh W) sym)

private theorem cliSpqrExt_hookSat_of_ghost (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    {α : Type} {sym : String} {spec : Spec α}
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide)
    (hf : ∀ (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks),
      Slots.CliGhostA0Hooks E2E.HooksE.A0 gh →
      HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
        Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0) →
      HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat ext sym spec := by
  obtain ⟨mmpl, gh, hG, _, _, hHmac, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := ext)
  exact RunGlue.hookSat_of_eq (heq sym hne) (hf mmpl gh hG hHmac)

private theorem cliSpqrExt_eq_of_ghost (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext]
    {sym : String} {v : Option (State → State)}
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide)
    (hf : ∀ (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks),
      RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym = v) :
    ext sym = v := by
  obtain ⟨mmpl, gh, _, _, _, _, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := ext)
  exact (heq sym hne).trans (hf mmpl gh)

theorem cliSpqrExt_shim_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustNoAllocShimSymCli sessionShimSpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_shim_sat mmpl gh W hG.shim_eq

theorem cliSpqrExt_noAllocShim_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustNoAllocShimSymCli noAllocShimSpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_noAllocShim_sat mmpl gh W hG.shim_eq

theorem cliSpqrExt_alloc_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustAllocSymCli (rustAllocSpec E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_alloc_sat mmpl gh W hG

theorem cliSpqrExt_allocZeroed_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustAllocZeroedSymCli (rustAllocZeroedSpec E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_allocZeroed_sat mmpl gh W hG

theorem cliSpqrExt_realloc_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustReallocSymCli (rustReallocSpec E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_realloc_sat mmpl gh W hG

theorem cliSpqrExt_dealloc_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsRustDeallocSymCli (rustDeallocSpec E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_dealloc_sat mmpl gh W hG

theorem cliSpqrExt_memcpy_sat (W : CliHooks) (stk : Nat)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memcpy" (libcMemcpySpec stk) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_memcpy_sat mmpl gh W hG stk

theorem cliSpqrExt_sessionMemcpy_sat (W : CliHooks) (stk : Nat)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memcpy" (sessionMemcpySpec stk) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_sessionMemcpy_sat mmpl gh W hG stk

theorem cliSpqrExt_sessionMemcpyRegion_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memcpy" sessionMemcpyRegionSpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_sessionMemcpyRegion_sat mmpl gh W hG

theorem cliSpqrExt_framelessMemcpy_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memcpy" framelessMemcpySpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_framelessMemcpy_sat mmpl gh W hG

theorem cliSpqrExt_memcpyRegionRO_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memcpy" CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_memcpyRegionRO_sat mmpl gh W hG

theorem cliSpqrExt_sessionMemmove_sat (W : CliHooks) (stk : Nat)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memmove" (sessionMemmoveSpec stk) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ _ =>
    Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_sessionMemmove_sat mmpl W stk)

theorem cliSpqrExt_sessionMemsetRegion_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext "memset" sessionMemsetRegionSpec :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh hG _ =>
    Slots.cliExternsPlaced_sessionMemsetRegion_sat mmpl gh W hG

theorem cliSpqrExt_formatInner_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext lsFormatInnerSym (formatInnerSpec E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ _ =>
    Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_formatInner_sat mmpl W)

theorem cliSpqrExt_mlkemValidatePk_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext Slots.lsMlkemValidatePkSymCli (mlkemValidatePkSpec W.Q.K) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ _ =>
    Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemValidatePk_sat mmpl W)

theorem cliSpqrExt_mlkemEncaps2_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext Slots.lsMlkemEncaps2SymCli (mlkemEncaps2Spec W.Q.K) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ _ =>
    Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemEncaps2_sat mmpl W)

theorem cliSpqrExt_mlkemDecaps_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext Slots.lsMlkemDecapsSymCli (mlkemDecapsSpec W.Q.K) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ _ =>
    Slots.cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (Slots.cliExternsPlaced_mlkemDecaps_sat mmpl W)

theorem cliSpqrExt_libcruxHmac_sat (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    HookSat ext Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0) :=
  cliSpqrExt_hookSat_of_ghost W (by decide) fun mmpl gh _ hHmac =>
    Slots.cliExternsPlaced_libcruxHmac_sat mmpl gh W hHmac

theorem cliSpqrExt_panic_handle_error (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    Slots.cliGhostExterns_panic_handle_error mmpl gh W

theorem cliSpqrExt_panic_handle_alloc_error (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtCs69KKACWg7bl_5alloc5alloc18handle_alloc_error" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    Slots.cliGhostExterns_panic_handle_alloc_error mmpl gh W

theorem cliSpqrExt_panic_assert_jj (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedjjEB4_" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_assert_jj mmpl W)

theorem cliSpqrExt_panic_assert_yy (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RINvNtCskxtBwYRO61I_4core9panicking13assert_failedyyEB4_" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_assert_yy mmpl W)

theorem cliSpqrExt_panic_slice_index_fail (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtNtCskxtBwYRO61I_4core5slice5index16slice_index_fail" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_slice_index_fail mmpl W)

theorem cliSpqrExt_panic_result_unwrap_failed (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtCskxtBwYRO61I_4core6result13unwrap_failed" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_result_unwrap_failed mmpl W)

theorem cliSpqrExt_panic_bounds_check (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtCskxtBwYRO61I_4core9panicking18panic_bounds_check" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_bounds_check mmpl W)

theorem cliSpqrExt_panic_add_overflow (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtNtCskxtBwYRO61I_4core9panicking11panic_const24panic_const_add_overflow" =
      some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_add_overflow mmpl W)

theorem cliSpqrExt_panic_panic (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    ext "_RNvNtCskxtBwYRO61I_4core9panicking5panic" = some Rust.panicked :=
  cliSpqrExt_eq_of_ghost W (by decide) fun mmpl gh =>
    cliGhostExterns_eq_of_base mmpl gh W (Slots.cliExternsPlaced_panic_panic mmpl W)

theorem cliDealloc_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_dealloc_sat W (ext := H))
    (by decide) hi hunmut

theorem cliDeallocWithStack_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocExternSpecWithStack E2E.HooksE.A0 extHookStack) :=
  rustDeallocExternWithStack_of_rustDealloc (cliDealloc_at_block W hi hunmut)

private theorem instHkdfPlacedHooks_cliExt (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    HkdfPlacedHooks W.C.F H where
  memset := by
    obtain ⟨mmpl, gh, _, hMs, hMc, _, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := H)
    exact (heq _ (by decide)).trans (instHkdfPlacedHooks_cli mmpl gh W hMs hMc).memset
  memcpy := by
    obtain ⟨mmpl, gh, _, hMs, hMc, _, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := H)
    exact (heq _ (by decide)).trans (instHkdfPlacedHooks_cli mmpl gh W hMs hMc).memcpy
  compress256 := by
    obtain ⟨mmpl, gh, _, hMs, hMc, _, heq⟩ := CliSpqrExt.exists_ghost (W := W) (ext := H)
    exact (heq _ (by decide)).trans (instHkdfPlacedHooks_cli mmpl gh W hMs hMc).compress256

theorem cliRecvCt2PlacedAllocExt [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CryptoVerification.SpqrV1.States.RecvCt2Chunk.RecvCt2PlacedAlloc E2E.HooksE.A0 ext where
  handleError := cliSpqrExt_panic_handle_error W (ext := Rust.withPanics ext)
  assertFailedU64 := cliSpqrExt_panic_assert_yy W (ext := Rust.withPanics ext)
  sliceIndexFail := cliSpqrExt_panic_slice_index_fail W (ext := Rust.withPanics ext)
  unwrapFailed := cliSpqrExt_panic_result_unwrap_failed W (ext := Rust.withPanics ext)
  panicBoundsCheck := cliSpqrExt_panic_bounds_check W (ext := Rust.withPanics ext)
  panicConstAddOverflow := cliSpqrExt_panic_add_overflow W (ext := Rust.withPanics ext)
  shim := cliSpqrExt_noAllocShim_sat W (ext := Rust.withPanics ext)
  alloc := cliSpqrExt_alloc_sat W (ext := Rust.withPanics ext)
  allocZeroed := cliSpqrExt_allocZeroed_sat W (ext := Rust.withPanics ext)
  dealloc := cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext)
  realloc := cliSpqrExt_realloc_sat W (ext := Rust.withPanics ext)
  memcpy := cliSpqrExt_framelessMemcpy_sat W (ext := Rust.withPanics ext)
  memcpyRO := cliSpqrExt_memcpyRegionRO_sat W (ext := Rust.withPanics ext)

theorem cliStatesPlacedSeamsExt [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CryptoVerification.SpqrV1.StatesPlacedSeams E2E.HooksE.A0 W.C.F W.Q.K ext :=
  letI := instHkdfPlacedHooks_cliExt W (H := Rust.withPanics ext)
  LibsignalBinary.Proofs.Placed.SubsetA4c.statesPlacedSeams_of_hooks
    (cliRecvCt2PlacedAllocExt W)
    (cliSpqrExt_sessionMemmove_sat W 0 (ext := Rust.withPanics ext))
    (cliSpqrExt_sessionMemsetRegion_sat W (ext := Rust.withPanics ext))
    (cliSpqrExt_mlkemValidatePk_sat W (ext := Rust.withPanics ext))
    (cliSpqrExt_mlkemEncaps2_sat W (ext := Rust.withPanics ext))
    (cliSpqrExt_mlkemDecaps_sat W (ext := Rust.withPanics ext))
    (cliSpqrExt_libcruxHmac_sat W (ext := Rust.withPanics ext))

theorem cliSpqrSendAllocContractsPlacedExt (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    AllocContractsPlaced E2E.HooksE.A0 ext where
  handle_error := cliSpqrExt_panic_handle_error W (ext := Rust.withPanics ext)
  shim := cliSpqrExt_shim_sat W (ext := Rust.withPanics ext)
  alloc := cliSpqrExt_alloc_sat W (ext := Rust.withPanics ext)
  dealloc := cliSpqrExt_dealloc_sat W (ext := Rust.withPanics ext)
  realloc := cliSpqrExt_realloc_sat W (ext := Rust.withPanics ext)
  session_memcpy stk := cliSpqrExt_sessionMemcpy_sat W stk (ext := Rust.withPanics ext)
  session_memset_region := cliSpqrExt_sessionMemsetRegion_sat W (ext := Rust.withPanics ext)

/-!
### Block-Level Hook Helpers & `Alloc` / `Chain` Leaves (`Blocks 320, 328, 353, 356, 362..368`)
-/

theorem cliNoAllocShim_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      noAllocShimSpec :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_noAllocShim_sat W (ext := H))
    (by decide) hi hunmut

theorem cliShimWithStack_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H] (stk : Nat := 0)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      (withStack sessionShimSpec stk) :=
  withStack_sessionShim_of_noAllocShim stk (cliNoAllocShim_at_block W hi hunmut)

theorem cliAlloc_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_alloc_sat W (ext := H))
    (by decide) hi hunmut

theorem cliAllocWithStack_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpecWithStack E2E.HooksE.A0 extHookStack) :=
  rustAllocWithStack_of_rustAlloc (cliAlloc_at_block W hi hunmut)

theorem cliAllocZeroed_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_allocZeroed_sat W (ext := H))
    (by decide) hi hunmut

theorem cliAllocZeroedWithStack_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc19___rust_alloc_zeroed")
      (rustAllocZeroedSpecWithStack E2E.HooksE.A0 extHookStack) :=
  rustAllocZeroedWithStack_of_rustAllocZeroed (cliAllocZeroed_at_block W hi hunmut)

theorem cliFormatInner_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ CryptoVerification.SpqrV1.Top.MessageDeserialize.spqrFormatInnerSym)
      (formatInnerSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_formatInner_sat W (ext := H))
    (by decide) hi hunmut

theorem cliRealloc_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_realloc")
      (rustReallocSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_realloc_sat W (ext := H))
    (by decide) hi hunmut

theorem cliSessionMemcpy_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H] (stk : Nat := 0)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "memcpy")
      (sessionMemcpySpec stk) :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_sessionMemcpy_sat W stk (ext := H))
    (by decide) hi hunmut

theorem cliFramelessMemcpy_at_block [LibsignalPlacement] (W : CliHooks)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    [CliSpqrExt W H] [IsLsBlockProg prog i H]
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog
      (lsρ "memcpy")
      framelessMemcpySpec :=
  CryptoVerification.SpqrV1.Alloc.spqr_hook_ok_of_mem
    (cliSpqrExt_framelessMemcpy_sat W (ext := H))
    (by decide) hi hunmut

theorem cliDoReserve7_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl
        (doReserveSpec E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.Alloc.do_reserve_7_placed_ok
    (cliSpqrExt_panic_handle_error W (ext := H))
    (cliSpqrExt_noAllocShim_sat W (ext := H))
    (cliSpqrExt_alloc_sat W (ext := H))
    (cliSpqrExt_realloc_sat W (ext := H))

theorem cliDoReserve7_placed_ok_x [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_320).rebase (blkPl_320).base H)
      (blkPl_320).base
      (withLsCodeLoaded lsmpl
        (doReserveSpecX E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.Alloc.do_reserve_7_placed_ok_x
    (cliSpqrExt_panic_handle_error W (ext := H))
    (cliSpqrExt_noAllocShim_sat W (ext := H))
    (cliSpqrExt_alloc_sat W (ext := H))
    (cliSpqrExt_realloc_sat W (ext := H))

theorem cliGrowOneChainEpochFull_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_356).rebase (blkPl_356).base H)
      (blkPl_356).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.SpqrV1.Alloc.growOneChainEpochFullSpec E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.Alloc.grow_one_chain_epoch_full_placed_ok
    (cliSpqrExt_panic_handle_error W (ext := H))
    (cliSpqrExt_noAllocShim_sat W (ext := H))
    (cliSpqrExt_alloc_sat W (ext := H))
    (cliSpqrExt_realloc_sat W (ext := H))

theorem cliVecDequeGrow_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_353).rebase (blkPl_353).base H)
      (blkPl_353).base
      (withLsCodeLoaded lsmpl
        (CryptoVerification.SpqrV1.ChainProofs.vecDequeGrowSpec E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.Alloc.vec_deque_grow_spec_placed_ok
    (cliSpqrExt_panic_handle_error W (ext := H))
    (cliSpqrExt_noAllocShim_sat W (ext := H))
    (cliSpqrExt_alloc_sat W (ext := H))
    (cliSpqrExt_realloc_sat W (ext := H))
    (cliSpqrExt_framelessMemcpy_sat W (ext := H))
    (cliSpqrExt_sessionMemmove_sat W CryptoVerification.SpqrV1.Alloc.growOneStack (ext := H))

theorem cliNextKeyInternal_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (blkPl_362).base
      (withLsCallInv lsmpl
        (nextKeyInternalSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have := instHkdfPlacedHooks_cliExt W (H := H)
  have hconcat_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec E2E.HooksE.A0)) :=
    NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 362) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (CryptoVerification.SpqrV1.Alloc.slice_concat_2_placed_ok
            (cliSpqrExt_panic_handle_error W (ext := H))
            (cliSpqrExt_noAllocShim_sat W (ext := H))
            (cliSpqrExt_alloc_sat W (ext := H))
            (cliSpqrExt_framelessMemcpy_sat W (ext := H))
            (cliSpqrExt_memcpyRegionRO_sat W (ext := H)))))
  have hhkdf_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F))) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok_of_other_block W.C)
  exact nextKeyInternal_placed_ok hconcat_362 hhkdf_362 (cliDeallocWithStack_at_block W)

theorem cliNextKeyInternal_panic_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    NextKeyInternalPanicPlacedOkX H :=
  nextKeyInternal_panic_placed_ok
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_add_overflow W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_assert_jj W (ext := H)))

theorem cliChainNew_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_363).rebase (blkPl_363).base H)
      (blkPl_363).base
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have := instHkdfPlacedHooks_cliExt W (H := H)
  have hhkdf_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F))) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok_of_other_block W.C)
  have hgrow_363 : subroutine_ok
      ((blkPC_363).rebase (blkPl_363).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (CryptoVerification.SpqrV1.ChainProofs.vecDequeGrowSpec E2E.HooksE.A0)) :=
    NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 363) (j := 353) (cliVecDequeGrow_placed_ok W))
  exact chainNew_placed_ok
    hhkdf_363 hgrow_363
    (cliShimWithStack_at_block W extHookStack)
    (cliAllocWithStack_at_block W)
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W (ext := H)))

theorem cliChainFromVn_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 328 (Rust.withPanics ext))
      (lsmpl.base 328)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (chainFromVersionNegotiationSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have hnew_328 : subroutine_ok
      ((CryptoVerification.SpqrV1.Top.Placed.blkPC_328).rebase
        (CryptoVerification.SpqrV1.Top.Placed.blkPl_328).base (Rust.withPanics ext))
      (lsmpl.base 363)
      (withLsCallInv lsmpl (chainNewSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) :=
    NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 328) (j := 363)
      (cliChainNew_placed_ok W)
  have hraw :=
    CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation.chainFromVersionNegotiation_placed_ok_of_contracts_x
      (hkdf := spqrHkdfWith W.C.F) (A := E2E.HooksE.A0) (H := Rust.withPanics ext)
      hnew_328
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (CryptoVerification.SpqrV1.Top.Placed.blkPC_328).rebase
      (CryptoVerification.SpqrV1.Top.Placed.blkPl_328).base (Rust.withPanics ext))]
  exact CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hraw

theorem cliChainRecvKey_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (blkPl_366).base
      (withLsCallInv lsmpl (chainRecvKeySpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have hnext_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) :=
    NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_placed_ok W)
  have hpanic_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_panic_placed_ok W)
  have hdoRes_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (doReserveSpec E2E.HooksE.A0)) :=
    NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 366) (j := 320) (cliDoReserve7_placed_ok W))
  exact chainRecvKey_placed_ok_of_contracts
    hnext_366 hpanic_366
    (cliShimWithStack_at_block W extHookStack)
    (cliAllocWithStack_at_block W)
    hdoRes_366
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_assert_jj W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_add_overflow W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_slice_index_fail W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_panic W (ext := H)))

theorem cliChainSendKey_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (blkPl_367).base
      (withLsCallInv lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have hnext_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) :=
    NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_placed_ok W)
  have hpanic_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_panic_placed_ok W)
  exact chainSendKey_placed_ok_of_contracts
    hnext_367 hpanic_367
    (cliShimWithStack_at_block W extHookStack)
    (cliAllocWithStack_at_block W)
    (cliDeallocWithStack_at_block W)
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W (ext := H)))

theorem cliChainAddEpoch_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) E2E.HooksE.A0)) := by
  have := instHkdfPlacedHooks_cliExt W (H := H)
  have hhkdf_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F))) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok_of_other_block W.C)
  have hgrow_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (CryptoVerification.SpqrV1.ChainProofs.vecDequeGrowSpec E2E.HooksE.A0)) :=
    NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 368) (j := 353) (cliVecDequeGrow_placed_ok W))
  exact chainAddEpoch_placed_ok_of_contracts_x
    hhkdf_368 hgrow_368
    (NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_plain (cliShimWithStack_at_block W extHookStack))
    (NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_plain (cliAllocWithStack_at_block W))
    (NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_plain (cliDeallocWithStack_at_block W))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_add_overflow W (ext := H)))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_panic W (ext := H)))

/-!
### Single-Block `Drop` Leaves, `MessageSerialize`, `MessageDeserialize`, `AuthNew`, and `EncodeToVec`
-/

theorem cliDrop_287 [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((CryptoVerification.SpqrV1.Drop.Blk337_338.blkPC_287).rebase
        (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base H)
      (CryptoVerification.SpqrV1.Drop.Blk337_338.blkPl_287).base
      (CryptoVerification.SpqrV1.Drop.dropChainEpochSliceSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.Drop.drop_chain_epoch_slice_local2_placed_ok_ext (cliDealloc_at_block W)

theorem cliDrop_288 [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok
      ((CryptoVerification.blkPC_288).rebase
        (CryptoVerification.blkPl_288).base H)
      (CryptoVerification.blkPl_288).base
      (CryptoVerification.SpqrV1.Drop.dropProtoEpochSliceSpec E2E.HooksE.A0) :=
  CryptoVerification.SpqrV1.ChainProofs.drop_proto_epoch_slice_placed_ok (cliDealloc_at_block W)

theorem cliEncodeVarintExt_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    SpqrEncodeVarintPlacedOkExt E2E.HooksE.A0 ext :=
  let hA := cliRecvCt2PlacedAllocExt W (ext := ext)
  spqrEncodeVarint_placed_ok_ext E2E.HooksE.A0 ext
    (growOneU8_placed_ok_ext E2E.HooksE.A0 ext hA.handleError hA.shim hA.alloc hA.realloc)

theorem cliMessageSerialize_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
      (lsmpl.base 352)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (messageSerializeSpecX spqrPolyApi E2E.HooksE.A0)) := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  have hraw :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.messageSerialize_placed_ok_x
      spqrPolyApi E2E.HooksE.A0 ext
      hA.handle_error hA.shim hA.alloc
      (cliDoReserve7_placed_ok W)
      (cliEncodeVarintExt_placed_ok W)
  exact LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hraw

theorem cliMessageDeserialize_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CryptoVerification.SpqrV1.Top.MessageDeserialize.MessageDeserializePlacedOkX
      spqrPolyApi E2E.HooksE.A0 ext := by
  have := CryptoVerification.SpqrV1.Top.Placed.instIsLsBlockProg_351 (Rust.withPanics ext)
  exact CryptoVerification.SpqrV1.Top.MessageDeserialize.messageDeserialize_spqrPolyApi_placed_ok_x
    E2E.HooksE.A0 ext
    (cliFormatInner_at_block W (i := 351))
    (cliDealloc_at_block W (i := 351))

theorem cliAuthUpdate_at_340 [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341)
      (withLsCallInv lsmpl (authUpdateSpec W.C.F E2E.HooksE.A0)) := by
  have := instHkdfPlacedHooks_cliExt W (H := H)
  have hconcat_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec E2E.HooksE.A0)) :=
    NextKeyInternalFacts.subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 341) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (CryptoVerification.SpqrV1.Alloc.slice_concat_2_placed_ok
            (cliSpqrExt_panic_handle_error W (ext := H))
            (cliSpqrExt_noAllocShim_sat W (ext := H))
            (cliSpqrExt_alloc_sat W (ext := H))
            (cliSpqrExt_framelessMemcpy_sat W (ext := H))
            (cliSpqrExt_memcpyRegionRO_sat W (ext := H)))))
  have hhkdf_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F))) :=
    CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hkdf_to_slice_spqr_placed_ok_of_other_block W.C)
  have hupd_341 :=
    CryptoVerification.SpqrV1.Auth.authUpdate_placed_ok hconcat_341 hhkdf_341
      (cliShimWithStack_at_block W extHookStack)
      (cliAllocWithStack_at_block W)
      (cliAllocZeroedWithStack_at_block W)
      (cliDeallocWithStack_at_block W)
      ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
        (cliSpqrExt_panic_handle_error W (ext := H)))
  exact NextKeyInternalFacts.ls_subroutine_ok_callInv_of_block (i := 340) (j := 341) hupd_341

theorem cliAuthNew_placed_ok [LibsignalPlacement] (W : CliHooks)
    {H : String → Option (State → State)} [CliSpqrExt W H] :
    subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (blkPl_340).base
      (withLsCallInv lsmpl (authNewSpec W.C.F E2E.HooksE.A0)) :=
  CryptoVerification.SpqrV1.Auth.authNew_placed_ok
    (cliAuthUpdate_at_340 W)
    (cliShimWithStack_at_block W extHookStack)
    (cliAllocZeroedWithStack_at_block W)
    (cliDeallocWithStack_at_block W)
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      (cliSpqrExt_panic_handle_error W (ext := H)))

theorem cliEncodeToVec_placed_ok [LibsignalPlacement] (W : CliHooks)
    {ext : String → Option (State → State)} [CliSpqrExt W ext] :
    CryptoVerification.SpqrV1.Prost.EncodeToVec.PqRatchetStateEncodeToVecPlacedOkExt
      E2E.HooksE.A0 ext := by
  have hA := cliSpqrSendAllocContractsPlacedExt W (ext := ext)
  exact CryptoVerification.SpqrV1.Prost.EncodeToVec.pqRatchetStateEncodeToVec_placed_ok
    hA.handle_error hA.shim hA.alloc hA.realloc
    (cliSpqrExt_sessionMemcpyRegion_sat W (ext := Rust.withPanics ext))

/-! ### Top-Level SPQR-V1 Placed Entry Seams (`Blocks 427, 327`) -/

private theorem cliGhostExterns_isPanic (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks)
    (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (RunGlue.withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- Block `427` (`spqr::send::<Coins>`) with all unconditionally provable peer contracts discharged. -/
theorem cliSpqrSendCoins_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hChainFromPb : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 364)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainFromPbSpecX E2E.HooksE.A0)))
    (hChainIntoPb : subroutine_ok
      (spqrSendPlacedProg (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 365)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (chainIntoPbSpecX E2E.HooksE.A0)))
    (hDecodeState : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 325
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 325)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.SpqrV1.Top.DecodeState.decodeStatePlacedSpecX
          canonicalV1InnerHeap E2E.HooksE.A0)))
    (hStatesIntoPb : subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 334
        (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (statesIntoPbPlacedSpecX E2E.HooksE.A0 W.C.F))) :
    subroutine_ok
      ((CryptoVerification.CliRatchet.SendPlaced.blkPC_427).rebase
        (CryptoVerification.CliRatchet.SendPlaced.blkPl_427).base
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpecT E2E.HooksE.A0 0#64 (E2E.pqxdhSpqrModel ⟨W.C, W.Q⟩))) := by
  have : CliSpqrExt W (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  exact spqrSendCoins_placed_seam_of_peer_contracts mmpl gh W hG hMs hMc hHmac
    hChainFromPb
    (keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
        (cliChainAddEpoch_placed_ok W)))
    (keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
      (CryptoVerification.SpqrV1.States.Leaves.subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
        (cliChainSendKey_placed_ok W)))
    hChainIntoPb
    (cliAuthMacHdr_placed_ok mmpl gh W hG hHmac)
    (cliAuthUpdate_placed_ok mmpl gh W hG hMs hMc)
    (cliHkdfToVec_placed_ok mmpl gh W hG hMs hMc)
    hDecodeState
    (cliEncodeVarint_placed_ok mmpl gh W hG)
    (cliChainFromVn_placed_ok W)
    hStatesIntoPb
    (cliMessageSerialize_placed_ok W)
    (cliAuthMacHdrPinnedPlacedOkX mmpl gh W hG hHmac)

/-- Block `327` (`spqr::initial_state`) on `RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)`. -/
theorem cliSpqrInitialState_placed_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : RunGlue.CliGhostHooks) (W : CliHooks)
    (hG : Slots.CliGhostA0Hooks E2E.HooksE.A0 gh)
    (hMs : gh.memset = some memsetHook)
    (hMc : gh.memcpy = some memcpyHook)
    (hHmac : HookSat (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))
      Slots.lsLibcruxHmacSymCli (libcruxHmacSpec W.C.F E2E.HooksE.A0))
    (hInitInner :
      CryptoVerification.SpqrV1.Top.InitInner.InitInnerPlacedOkX
        E2E.HooksE.A0 W.C.F (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hDropPqRatchetState :
      subroutine_ok
        ((blkPC_270).rebase (blkPl_270).base
          (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
        (blkPl_270).base
        (withLsCodeLoaded lsmpl
          (CryptoVerification.SpqrV1.Drop.dropProtoPqRatchetStatePlacedSpec E2E.HooksE.A0))) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327
        (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (CryptoVerification.Cli.E2E.V1.spqrInitialStatePlacedInnerSpec E2E.HooksE.A0 W.C.F)) := by
  have : CliSpqrExt W (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    cliSpqrExt_self mmpl gh W hG hMs hMc hHmac
  have := CryptoVerification.SpqrV1.Top.Placed.instIsLsBlockProg_327
    (Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W)))
  exact CryptoVerification.SpqrV1.Top.InitialState.initial_state_placed_ok_blockProgram_ext
    (cliGhostExterns_isPanic mmpl gh W)
    (cliSpqrExt_panic_handle_error W
      (ext := Rust.withPanics (RunGlue.cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (cliNoAllocShim_at_block W (i := 327))
    (cliAlloc_at_block W (i := 327))
    (cliFramelessMemcpy_at_block W (i := 327))
    hInitInner (cliEncodeToVec_placed_ok W) hDropPqRatchetState

end CryptoVerification.SignalSession.Cli
