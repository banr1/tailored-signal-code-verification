/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrowBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat

/-!
# `HookSat` Sibling of `SignalSession.Cli.SpqrSendCoinsPlacedInstBudget` (`SpqrSendCoinsPlacedInstBudgetSat`)

Replaces `memset_row_placed` / `hookMemset_eq_memsetHook` across all `memset`-consuming SPQR Send &
peer leaf bridges in `SpqrSendCoinsPlacedInstBudget` with
`(hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
  (withAllocVmPreserved sessionMemsetRegionSpec))`.
All `memset`-free theorems from `SpqrSendCoinsPlacedInstBudget` are re-exported via `public import`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudgetSat

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalPlacement
   blkPC_341 blkPC_362 blkPC_366 blkPC_367 blkPC_368
   blkPl_341 blkPl_362 blkPl_366 blkPl_367 blkPl_368
   instIsLsBlockProg_417 libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_of_mem ls_subroutine_ok_of_block lsmpl lsρ
   subroutine_ok_withLsCodeLoaded_of_plain)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter cliTapeAt)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (ls_subroutine_ok_of_blockProgram_cro spqrCoinsAfterPlaced spqrCoinsAtPlaced)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (instIsLsBlockProg_427)
open CryptoVerification.CliRatchet.SendPlaced (blkPC_427 blkPl_427)
open CryptoVerification.E2E (pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (spqrHkdfWith spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (SendCall extHookStack keys_ls_subroutine_ok_of_block_cro
   lsCompress256Sym lsMemcpySym lsMemsetSym
   sessionMemcpyRegionSpec sessionMemcpySpec sessionMemsetRegionSpec
   subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded withLsCodeRoLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced lsReadFileSym lsReadStdinSym lsRustAllocSymCli
   lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli
   lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other hookSat_of_eq
   withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliExternsPlaced_panic_add_overflow cliExternsPlaced_panic_assert_jj
   cliExternsPlaced_panic_panic cliExternsPlaced_panic_result_unwrap_failed
   cliExternsPlaced_panic_slice_index_fail cliExternsPlaced_panic_sub_overflow
   cliGhostExterns_panic_handle_error cliGhostExterns_sat_of_cliExternsPlaced
   compress256_row_placed)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec nextKeyInternalPanicSpecX)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (ls_subroutine_ok_callInv_of_block subroutine_ok_withLsCallInv_of_withLsCodeLoaded withLsCallInv)
open CryptoVerification.SpqrV1.States.Leaves
  (subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
   subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv)
open CryptoVerification.SpqrV1.Top.DecodeState (V1InnerHeapPred canonicalV1InnerHeap)
open CryptoVerification.SpqrV1.Top.MessageSerialize
  (MessageSerializeGhost messageAt messageSerializeStackX)
open CryptoVerification.SpqrV1.Unchunked (spqrLibcruxHmacSym)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
   rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
  (ls_subroutine_ok_cro_of_plain ls_subroutine_ok_of_blockProgram_plain
   spqrSendPlacedContractsTight_of_okX spqrSendPlacedContracts_of_okX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX EncodeBytesPlacedOkX PolyNextChunkPlacedOkX
   SpqrSendPlacedContracts SpqrSendPlacedContractsTight spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (CliSpqrSendPeerSeams MessageSerializeEnv messageSerializeSpecX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (doReserve2_placed_ok_ext_x)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.TopPlacedBudget
  (SpqrSendCoinsExactEnv SpqrSendExtraContractsPlaced
   spqrSendCoins_placed_ok_at_prog_ext_of_contracts
   spqrSend_dropChainEpochSlice_raw_ok_of_dealloc spqrSend_dropChunkedStates_ok_of_dealloc)
open LibsignalBinary.Proofs.Placed.SubsetA4cBudgetSat (statesPlacedSeams_of_hooks_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_alloc_budget_sat
   cliExternsPlaced_dealloc_budget_sat cliExternsPlaced_exactMemcpy_sat
   cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudget
  (cliSpqrSend_chainFromPb_ok cliSpqrSend_chainIntoPb_ok cliVecDequeGrow_placed_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrChainPlacedInstBudgetSat
  (HkdfPlacedHooksAllocVmSat HkdfPlacedHooksAllocVmSat.toExactSat cliSpqrSend_chainFromVn_ok_sat
   hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat
   hookSat_sessionMemsetRegionBudget_of_allocVm)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliAllocWithStack_at_block cliAllocZeroedWithStack_at_block
   cliDeallocWithStack_at_block cliExternsPlaced_allocZeroed_budget_sat
   cliExternsPlaced_framelessMemcpyAcp_sat cliExternsPlaced_noAllocShimBudget_sat
   cliExternsPlaced_rustAllocShimVm_sat cliExternsPlaced_sessionMemcpyRegionRO_sat
   cliShimBudgetWithStack_at_block)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudget
  (cliAuthMacHdrPinnedPlacedOkX cliAuthMacHdr_placed_ok cliDoReserve7_acp_placed_ok
   cliExternsPlaced_mlkemDecaps_budget_sat cliExternsPlaced_mlkemEncaps1_budget_sat
   cliExternsPlaced_mlkemEncaps2_budget_sat cliExternsPlaced_mlkemFromSeed_budget_sat
   cliExternsPlaced_mlkemPk1_budget_sat cliExternsPlaced_mlkemPk2_budget_sat
   cliExternsPlaced_mlkemValidatePk_budget_sat cliExternsPlaced_sessionMemmove_allocVm_sat
   cliNextKeyInternal_panic_placed_ok cliRecvCt2PlacedAlloc cliRecvCt2PlacedAllocExt
   cliSpqrSend_coinsFill_ok_cli)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudget (sliceConcat2Spec slice_concat_2_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget (authUpdateSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux (authUpdate_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochBudget (chainAddEpoch_placed_ok_of_contracts_x)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget (chainAddEpochSpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (nextKeyInternalSpecX vecDequeGrowSpec)
open LibsignalBinary.Proofs.SpqrV1.Chain.NextKeyInternalBudget
  (nextKeyInternal_placed_ok withAllocVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyAddBudget (withAllocCallPreserved)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyBudget (chainRecvKey_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Chain.RecvKeyHelpersBudget (chainRecvKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyBudget (chainSendKey_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Chain.SendKeyHelpersBudget (chainSendKeySpecX)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
  (hkdf_to_slice_spqr_placed_ok_of_other_block_sat hkdf_to_vec_spqr_placed_ok_of_other_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (hkdfToVecSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (encodeBytesSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.ProofBudget (encode_bytes_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.TopPlacedBudget (poly_next_chunk_block_ok_x_ext)
open LibsignalBinary.Proofs.SpqrV1.States.FromPb.DefsBudget (StatesFromPbEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.TopPlacedBudget (StatesRecvExactEnv)
open LibsignalBinary.Proofs.SpqrV1.StatesPlacedSeamsBudget
  (Ct1ReceivedSendEkChunkEnv Ct1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
   EkReceivedCt1SampledSendCt1ChunkEnv HeaderSentSendEkChunkEnv StatesPlacedSeamsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsBudget (spqrEncodeVarintSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.DefsPlacedBudget (SpqrEncodeVarintPlacedOkX)
open LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.ProofPlacedBudget
  (spqrEncodeVarint_placed_ok_of_hookSat_x)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (SpqrBoundedEvs statesIntoPbPlacedSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget (messageSerializeEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializePlacedBudget
  (messageSerialize_placed_ok_of_hooks)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat (HkdfPlacedHooksExactSat)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
  (subroutine_ok_withStack_of_subroutine_ok withStack)

/-! ## 1. Internal `cliGhostExterns` & `HkdfPlacedHooks*Sat` Bridges -/

private theorem r1sc_cliGhostExterns_eq_of_base
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {sym : String} {v : Option (State → State)}
    (h : cliExternsPlaced mmpl W sym = v)
    (h1 : sym ≠ lsRustAllocSymCli := by decide)
    (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide)
    (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide)
    (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide)
    (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ lsMemsetSym := by decide)
    (h10 : sym ≠ lsMemcpySym := by decide) :
    cliGhostExterns gh (cliExternsPlaced mmpl W) sym = v :=
  (cliGhostExterns_other gh (cliExternsPlaced mmpl W) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans h

private theorem r1sc_hExt_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  fun _ _ => rfl

private theorem r1sc_hExt_withPanics
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem r1sc_hExt_withPanics_id
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) sym :=
  r1sc_hExt_withPanics mmpl gh W (r1sc_hExt_id mmpl gh W)

private theorem r1sc_hkdfPlacedHooksAllocVmSat_cliExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksAllocVmSat W.C.F H where
  memset := hookSat_of_eq (hExt _ (by decide)) hMemset
  memcpy := by
    rcases cliExternsPlaced_exactMemcpy_sat mmpl gh W hA with ⟨f, hf, hex⟩
    exact ⟨f, (hExt _ (by decide)).trans hf, hex⟩
  compress256 := by
    rw [hExt _ (by decide), cliGhostExterns_other gh (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)

private theorem r1sc_hookSat_sessionMemcpyBudget_of_region_any
    {H : String → Option (State → State)} {sym : String} (hookStack : Nat)
    (h : HookSat H sym sessionMemcpyRegionBudgetSpec) :
    HookSat H sym (sessionMemcpyBudgetSpec hookStack) := by
  refine ProofLib.HookSat.mono h fun ⟨dst, src, bs⟩ R s0 hpre =>
    ⟨(dst, src, bs), stackAt s0.sp hookStack ∗ R, ?_, fun sf hpost => ?_⟩
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, libcMemcpySpec, sessionMemcpyRegionSpec, memcpyRegionSpec] at hpre ⊢
    ac_nf at hpre ⊢
  · dsimp only [sessionMemcpyBudgetSpec, sessionMemcpyRegionBudgetSpec,
      sessionMemcpySpec, sessionMemcpyRegionSpec] at hpost ⊢
    ac_nf at hpost ⊢

private theorem r1sc_cliRustAllocShimVmWithStack_at_block [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hShim : gh.shim = hookNoop := by rfl)
    {prog : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg prog i H]
    (stk : Nat)
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustNoAllocShimSymCli) (withStack rustAllocShimVmSpec stk) :=
  subroutine_ok_withStack_of_subroutine_ok
    (spqr_hook_ok_of_mem
      (hookSat_of_eq (hExt _ (by decide)) (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hShim))
      (by decide) hi hunmut)
    stk

/-! ## 2. `StatesPlacedSeamsOfEnv` and `AllocContractsPlaced` under `HookSat ... "memset"` -/

theorem cliStatesPlacedSeamsExt_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      StatesFromPbEnv (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      ext := by
  have hExtWP := r1sc_hExt_withPanics mmpl gh W hExt
  have hAllocVm :=
    r1sc_hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA.toCliGhostAllocHooks hMemset hExtWP
  let _ : HkdfPlacedHooksExactBudgetSat W.C.F (Rust.withPanics ext) :=
    @HkdfPlacedHooksExactBudgetSat.of_exactSat W.C.F (Rust.withPanics ext)
      (hookSat_sessionMemsetRegionBudget_of_allocVm hAllocVm.memset)
      hAllocVm.toExactSat
  exact statesPlacedSeams_of_hooks_sat
    (cliRecvCt2PlacedAllocExt mmpl gh W hA hExt)
    (hookSat_of_eq (hExtWP _ (by decide))
      (cliExternsPlaced_sessionMemmove_allocVm_sat mmpl gh W))
    (hookSat_sessionMemsetRegionBudget_of_allocVm hAllocVm.memset)
    (hookSat_of_eq (hExtWP _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemValidatePk_budget_sat mmpl W)))
    (hookSat_of_eq (hExtWP _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemEncaps2_budget_sat mmpl W)))
    (hookSat_of_eq (hExtWP _ (by decide))
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
        (cliExternsPlaced_mlkemDecaps_budget_sat mmpl W)))
    (hookSat_of_eq (hExtWP _ (by decide)) hHmac)

theorem cliStatesPlacedSeams_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    StatesPlacedSeamsOfEnv M A lim W.C.F W.Q.K
      StatesFromPbEnv (StatesRecvExactEnv W.Q.K)
      HeaderSentSendEkChunkEnv Ct1ReceivedSendEkChunkEnv
      Ct1SampledSendCt1ChunkEnv EkReceivedCt1SampledSendCt1ChunkEnv Ct2SampledSendCt2ChunkEnv
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliStatesPlacedSeamsExt_sat mmpl gh W hA hMemset hHmac (r1sc_hExt_id mmpl gh W)

theorem cliSpqrSendAllocContractsPlaced_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    AllocContractsPlaced M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  handle_error := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_panic_handle_error mmpl gh W
  shim := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq
  alloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_alloc_budget_sat mmpl gh W hA
  dealloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_dealloc_budget_sat mmpl gh W hA
  realloc := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_realloc_budget_sat mmpl gh W hA
  session_memcpy stk := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_hookSat_sessionMemcpyBudget_of_region_any stk
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA)
  session_memset_region := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact hookSat_sessionMemsetRegionBudget_of_allocVm hMemset

theorem cliSpqrSendAllocContractsPlacedExt_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    AllocContractsPlaced M A lim ext where
  handle_error := (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide)).trans
    (cliGhostExterns_panic_handle_error mmpl gh W)
  shim := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq)
  alloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_alloc_budget_sat mmpl gh W hA)
  dealloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA)
  realloc := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (cliExternsPlaced_realloc_budget_sat mmpl gh W hA)
  session_memcpy stk := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (r1sc_hookSat_sessionMemcpyBudget_of_region_any stk
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
  session_memset_region := hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
    (hookSat_sessionMemsetRegionBudget_of_allocVm hMemset)

/-! ## 3. Closed Budget Leaves (`Blocks 326, 341, 352, 362, 366, 367, 368, 378, 417, 424`) -/

theorem cliNextKeyInternal_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_362).rebase (blkPl_362).base H)
      (blkPl_362).base
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have : HkdfPlacedHooksAllocVmSat W.C.F H :=
    r1sc_hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA hMemset hExt
  have hconcat_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 362) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_2_placed_ok
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA))
            (hookSat_of_eq (hExt _ (by decide))
              (cliExternsPlaced_sessionMemcpyRegionRO_sat mmpl gh W hA)))))
  have hhkdf_362 : subroutine_ok
      ((blkPC_362).rebase (blkPl_362).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat W.C)
  exact nextKeyInternal_placed_ok hconcat_362 hhkdf_362 (cliDeallocWithStack_at_block mmpl gh W hA hExt)

theorem cliChainRecvKey_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_366).rebase (blkPl_366).base H)
      (blkPl_366).base
      (withLsCallInv lsmpl (chainRecvKeySpecX M A lim (spqrHkdfWith W.C.F))) := by
  have hnext_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_placed_ok_sat mmpl gh W hA.toCliGhostAllocHooks hMemset hExt)
  have hpanic_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    ls_subroutine_ok_callInv_of_block (i := 366) (j := 362)
      (cliNextKeyInternal_panic_placed_ok mmpl gh W hExt)
  have hdoRes_366 : subroutine_ok
      ((blkPC_366).rebase (blkPl_366).base H)
      (lsmpl.base 320)
      (withLsCallInv lsmpl (withAllocCallPreserved (doReserveSpec M A lim))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 366) (j := 320)
        (cliDoReserve7_acp_placed_ok mmpl gh W hA hExt))
  exact chainRecvKey_placed_ok_of_contracts
    hnext_366 hpanic_366
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks hExt)
    hdoRes_366
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_assert_jj mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W
          (cliExternsPlaced_panic_slice_index_fail mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W))))

theorem cliChainSendKey_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_367).rebase (blkPl_367).base H)
      (blkPl_367).base
      (withLsCallInv lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have hnext_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl (nextKeyInternalSpecX (spqrHkdfWith W.C.F) M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_placed_ok_sat mmpl gh W hA hMemset hExt)
  have hpanic_367 : subroutine_ok
      ((blkPC_367).rebase (blkPl_367).base H)
      (lsmpl.base 362)
      (withLsCallInv lsmpl nextKeyInternalPanicSpecX) :=
    ls_subroutine_ok_callInv_of_block (i := 367) (j := 362)
      (cliNextKeyInternal_panic_placed_ok mmpl gh W hExt)
  exact chainSendKey_placed_ok_of_contracts
    hnext_367 hpanic_367
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA hExt)
    (cliDeallocWithStack_at_block mmpl gh W hA hExt)

theorem cliChainAddEpoch_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_368).rebase (blkPl_368).base H)
      (blkPl_368).base
      (withLsCallInv lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) := by
  have : HkdfPlacedHooksAllocVmSat W.C.F H :=
    r1sc_hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA hMemset hExt
  have hhkdf_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withAllocVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_allocVm_placed_ok_of_other_block_sat W.C)
  have hgrow_368 : subroutine_ok
      ((blkPC_368).rebase (blkPl_368).base H)
      (lsmpl.base 353)
      (withLsCallInv lsmpl (vecDequeGrowSpec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 368) (j := 353)
        (cliVecDequeGrow_placed_ok mmpl gh W hA hExt))
  exact chainAddEpoch_placed_ok_of_contracts_x
    hhkdf_368 hgrow_368
    (r1sc_cliRustAllocShimVmWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack)
    (cliAllocWithStack_at_block mmpl gh W hA hExt)
    (cliDeallocWithStack_at_block mmpl gh W hA hExt)
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_add_overflow mmpl W))))
    ((ls_externAt?_of_mem (by decide) (by decide) (by decide)).trans
      ((hExt _ (by decide)).trans
        (r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W))))

theorem cliEncodeVarintPlacedOkX_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    SpqrEncodeVarintPlacedOkX A lim ext := by
  have hc := cliSpqrSendAllocContractsPlacedExt_sat mmpl gh W hA.toCliGhostAllocHooks hMemset hExt
  exact spqrEncodeVarint_placed_ok_of_hookSat_x A lim ext
    hc.handle_error
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc

theorem cliEncodeVarint_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 326 (Rust.withPanics ext))
      (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (cliEncodeVarintPlacedOkX_sat mmpl gh W hA hMemset hExt)

private theorem messageSerializeEvents_spqrBoundedEvs_sat
    {P_api : CryptoVerification.LibsignalSpqrV1.PolyApi} (x : MessageSerializeGhost P_api) :
    SpqrBoundedEvs 8 256 (messageSerializeEvents P_api x) := by
  have halloc : SpqrBoundedEvs 8 256 (rustAllocEvents 40 1) := by
    have hr : rustAllocEvents 40 1 = [.alloc 40] := rfl
    rw [hr]
    refine ⟨by decide, fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨by decide, by decide, fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
  have hboth : SpqrBoundedEvs 8 256 (rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1) := by
    have hr : rustAllocEvents 40 1 ++ rustReallocEvents 40 80 1 = [.alloc 40, .realloc 1 40 80] :=
      rfl
    rw [hr]
    refine ⟨by decide, fun ev hev => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · exact ⟨by decide, by decide, fun _ _ h => (by cases h), fun _ _ _ h => (by cases h)⟩
    · refine ⟨by decide, by decide, fun _ _ h => (by cases h), fun al _ _ h => ?_⟩
      cases h; decide
  unfold messageSerializeEvents
  cases x.msg.payload <;> dsimp only <;> first | exact halloc | (split <;> [exact halloc; exact hboth])

theorem cliMessageSerialize_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 352 (Rust.withPanics ext))
      (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)) := by
  have hc := cliSpqrSendAllocContractsPlacedExt_sat mmpl gh W hA.toCliGhostAllocHooks hMemset hExt
  have hraw := messageSerialize_placed_ok_of_hooks spqrPolyApi A lim ext
    hc.handle_error
    (hookSat_of_eq (r1sc_hExt_withPanics mmpl gh W hExt _ (by decide))
      (cliExternsPlaced_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    hc.alloc hc.realloc (cliEncodeVarintPlacedOkX_sat mmpl gh W hA hMemset hExt)
  have hcro := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hraw
  exact subroutine_ok_mono hcro
    (fun (x, stB) _ _ hpre => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecX,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpre ⊢
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left (sepConj_mono_left (sepConj_mono_left ?_))
      exact Entails.pure_mono fun ⟨h1, h2, h3, hfit⟩ =>
        ⟨h1, h2, h3, hfit.mono fun evs hevs => by
          rw [hevs]; exact messageSerializeEvents_spqrBoundedEvs_sat x⟩)
    (fun (x, stB) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, messageSerializeSpecX,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.messageSerializeSpecXOfEnv,
        LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.messageSerializeSpecX] at hpost ⊢
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost ⊢
      rcases hpost with ⟨evs, hpost⟩
      refine ⟨evs, ?_⟩
      have hpost' : sf.mem ⊨ ⌜sf.trace = s0.trace⌝ ∗
          (⌜LibsignalBinary.Proofs.SpqrV1.Top.MessageSerializeBudget.MessageSerializeEnv spqrPolyApi x evs⌝ ∗
            ((messageAt spqrPolyApi x.msgA x.msg ∗
                vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
                A.pool lim (M.stepEvents evs stB) sf ∗
                stackAt s0.sp messageSerializeStackX) ∗ R)) := by
        ac_nf at hpost ⊢
      rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost'
      rcases hpost' with ⟨htr, hevs, hrest⟩
      have hgoal : sf.mem ⊨ ⌜sf.trace = s0.trace ∧ MessageSerializeEnv x evs⌝ ∗
          ((messageAt spqrPolyApi x.msgA x.msg ∗
              vecU8 A.repAlloc x.ret (x.msg.serialize x.index) ∗
              A.pool lim (M.stepEvents evs stB) sf ∗
              stackAt s0.sp messageSerializeStackX) ∗ R) := by
        rw [satisfies_pure_sepConj]
        exact ⟨⟨htr, by rw [hevs]; exact messageSerializeEvents_spqrBoundedEvs_sat x⟩, hrest⟩
      ac_nf at hgoal ⊢)
    (fun _ _ _ _ hp => hp)

theorem cliPolyNextChunkPlacedOkX_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    PolyNextChunkPlacedOkX M A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (poly_next_chunk_block_ok_x_ext (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA hMemset))

theorem cliEncodeBytesPlacedOkX_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    EncodeBytesPlacedOkX A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hc := cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA hMemset
  have hraw := encode_bytes_placed_ok_x hc.shim hc.alloc (hc.session_memcpy allocHookStack)
  exact @ls_subroutine_ok_cro_of_plain _ _
    (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) _ 427 417
    (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (instIsLsBlockProg_427 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (instIsLsBlockProg_417 (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
    (lsmpl.base 417) (encodeBytesSpecX A lim)
    hraw (by decide) (by decide) (by decide)

theorem cliHkdfToVec_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 378)
      (withLsCodeRoLoaded lsmpl (hkdfToVecSpec M A lim (spqrHkdfWith W.C.F))) := by
  have : HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    (r1sc_hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA.toCliGhostAllocHooks hMemset
      (r1sc_hExt_withPanics_id mmpl gh W)).toExactSat
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  exact hkdf_to_vec_spqr_placed_ok_of_other_block_sat
    (i := 427) W.C M A lim
    (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
      (hookSat_sessionMemsetRegionBudget_of_allocVm hMemset))
    (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
      (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    hc.allocZeroed

theorem cliAuthUpdate_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 341)
      (withLsCodeRoLoaded lsmpl (authUpdateSpec W.C.F M A lim)) := by
  have : HkdfPlacedHooksExactSat W.C.F
      (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))) :=
    (r1sc_hkdfPlacedHooksAllocVmSat_cliExt mmpl gh W hA.toCliGhostAllocHooks hMemset
      (r1sc_hExt_withPanics_id mmpl gh W)).toExactSat
  have hc := cliRecvCt2PlacedAlloc mmpl gh W hA
  have hconcat_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 386)
      (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 341) (j := 386)
        (subroutine_ok_withLsCodeLoaded_of_plain
          (slice_concat_2_placed_ok hc.shim hc.alloc hc.memcpy hc.memcpyRO)))
  have hhkdf_341 : subroutine_ok
      ((blkPC_341).rebase (blkPl_341).base
        (Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded
      (hkdf_to_slice_spqr_placed_ok_of_other_block_sat W.C
        (hookSat_of_eq (r1sc_hExt_withPanics_id mmpl gh W _ (by decide))
          (hookSat_sessionMemsetRegionBudget_of_allocVm hMemset)))
  have hupd_341 :=
    authUpdate_placed_ok hconcat_341 hhkdf_341
      (cliShimBudgetWithStack_at_block mmpl gh W hA.shim_eq (r1sc_hExt_withPanics_id mmpl gh W)
        extHookStack (i := 341))
      (cliAllocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
      (cliAllocZeroedWithStack_at_block mmpl gh W hA
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
      (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks
        (r1sc_hExt_withPanics_id mmpl gh W) (i := 341))
  exact keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 341)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv hupd_341)

/-! ## 4. Top-Level `Block 427` (`spqr::send::<Coins>`) Budget Seams under `HookSat ... "memset"` -/

theorem spqrSendExtraContractsPlaced_of_cli_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim)) :
    SpqrSendExtraContractsPlaced M A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) where
  panic_hook := r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_panic mmpl W)
  panicSubOverflow_hook :=
    r1sc_cliGhostExterns_eq_of_base mmpl gh W (cliExternsPlaced_panic_sub_overflow mmpl W)
  unwrapFailed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact r1sc_cliGhostExterns_eq_of_base mmpl gh W
      (cliExternsPlaced_panic_result_unwrap_failed mmpl W)
  allocZeroed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliExternsPlaced_allocZeroed_budget_sat mmpl gh W hA
  mlkemFromSeed_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemFromSeed_budget_sat mmpl W)
  mlkemPk1_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemPk1_budget_sat mmpl W)
  mlkemPk2_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemPk2_budget_sat mmpl W)
  mlkemEncaps1_hook := by
    rw [withPanics_cliGhostExterns mmpl gh W]
    exact cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_mlkemEncaps1_budget_sat mmpl W)
  fromSeed_pk1_slice := W.Q.K.fromSeed_pk1
  fromSeed_pk2_slice := W.Q.K.fromSeed_pk2
  macHdrPinned_ok := cliAuthMacHdrPinnedPlacedOkX mmpl gh W hA hHmac
  doReserve2_ok :=
    doReserve2_placed_ok_ext_x
      (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
  dropChainEpochSlice_raw_ok :=
    spqrSend_dropChainEpochSlice_raw_ok_of_dealloc
      (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
  dropChunkedStates_ok :=
    spqrSend_dropChunkedStates_ok_of_dealloc
      (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)

private theorem r1sc_cliGhostExterns_isPanic
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

theorem spqrSendCoins_placed_seam_of_contracts_ofEnv_sat [LibsignalPlacement]
    {M : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    {SendEnv : SendCall → List AllocEvent → Prop}
    (hSub : ∀ sc evs, SpqrSendCoinsExactEnv W.C.F W.Q.K sc evs → SendEnv sc evs)
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hC : SpqrSendPlacedContracts M H_inner A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv
          M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) SendEnv)) := by
  have hok := spqrSendCoins_placed_ok_at_prog_ext_of_contracts
    (callerProg := (blkPC_427).rebase (blkPl_427).base
      (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (i := 427) (by decide)
    (r1sc_cliGhostExterns_isPanic mmpl gh W)
    (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    hC
    (spqrSendExtraContractsPlaced_of_cli_sat mmpl gh W hA hMemset hHmac)
  have heq_cro (m : Memory) :
      LibsignalCodeRoLoaded lsmpl m =
        CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl m :=
    propext ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  have hmod : pqxdhSpqrModel ⟨W.C, W.Q⟩ = spqrV1 W.C.F W.Q.K := rfl
  rw [hmod]
  have hcoinsAt : spqrCoinsAtPlaced = cliTapeAt := rfl
  have hcoinsAfter : spqrCoinsAfterPlaced = cliTapeAfter := rfl
  exact subroutine_ok_mono hok
    (fun (sc, stB) _ s hpre => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecOfEnv]
        at hpre ⊢
      rw [heq_cro s.mem] at hpre
      rw [hcoinsAt]
      refine Satisfies.mono ?_ hpre
      refine sepConj_mono_left ?_
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_right ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨h1, h2, hfit⟩ => ⟨h1, h2, hfit.mono (hSub sc)⟩)
    (fun (sc, stB) _ s0 sf hpost => by
      dsimp only [CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded,
        LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget.spqrSendCoinsPlacedSpec,
        withLsCodeRoLoaded,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecTOfEnv,
        LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget.spqrSendCoinsPlacedSpecOfEnv]
        at hpost ⊢
      rw [hcoinsAfter] at hpost
      refine Satisfies.mono ?_ hpost
      refine sepConj_mono_left ?_
      refine sepConj_mono_right ?_
      refine Entails.sepExists_mono fun evs => ?_
      refine sepConj_mono_left ?_
      exact Entails.pure_mono fun ⟨hd, htr, hnp, hevs⟩ => ⟨hSub sc evs hevs, hd, htr, hnp⟩)
    (fun _ _ _ _ hpanic => hpanic)

private theorem r1sc_cliSpqrSend_chainAddEpoch_on_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 368)
      (withLsCodeRoLoaded lsmpl (chainAddEpochSpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 368)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainAddEpoch_placed_ok_sat mmpl gh W hA hMemset (r1sc_hExt_withPanics_id mmpl gh W)))

private theorem r1sc_cliSpqrSend_chainSendKey_on_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 367)
      (withLsCodeRoLoaded lsmpl (chainSendKeySpecX (spqrHkdfWith W.C.F) M A lim)) :=
  keys_ls_subroutine_ok_of_block_cro (i := 427) (j := 367)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCallInv
      (cliChainSendKey_placed_ok_sat mmpl gh W hA hMemset (r1sc_hExt_withPanics_id mmpl gh W)))

private theorem r1sc_cliSpqrSend_coinsFill_on [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    CoinsFillPlacedOkX (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  ls_subroutine_ok_of_blockProgram_plain (cliSpqrSend_coinsFill_ok_cli mmpl gh W hA)

private theorem r1sc_cliSpqrSend_messageSerialize_on_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 352)
      (withLsCodeRoLoaded lsmpl (messageSerializeSpecX spqrPolyApi M A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliMessageSerialize_placed_ok_sat mmpl gh W hA hMemset (r1sc_hExt_id mmpl gh W))

private theorem r1sc_cliSpqrSend_encodeVarint_on_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec)) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 326)
      (withLsCodeRoLoaded lsmpl (spqrEncodeVarintSpecX A lim)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliEncodeVarint_placed_ok_sat mmpl gh W hA hMemset (r1sc_hExt_id mmpl gh W))

theorem cliSpqrSendCoins_placed_ok_of_peerSeams_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hPeers : CliSpqrSendPeerSeams M A lim W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok
      ((blkPC_427).rebase (blkPl_427).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 427)
      (CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SignalSession.Cli.SpqrV1PlacedSeamsBudget.spqrSendCoinsPlacedSpecTOfEnv
          M A lim 0#64 (pqxdhSpqrModel ⟨W.C, W.Q⟩) (SpqrSendCoinsExactEnv W.C.F W.Q.K))) :=
  spqrSendCoins_placed_seam_of_contracts_ofEnv_sat (fun _ _ h => h) hA hMemset hHmac
    (spqrSendPlacedContracts_of_okX
      (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
      (cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks)
      (r1sc_cliSpqrSend_chainAddEpoch_on_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
      (r1sc_cliSpqrSend_chainSendKey_on_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
      (cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks)
      (cliAuthMacHdr_placed_ok mmpl gh W hA hHmac)
      (cliAuthUpdate_placed_ok_sat mmpl gh W hA hMemset)
      (cliHkdfToVec_placed_ok_sat mmpl gh W hA hMemset)
      (cliEncodeBytesPlacedOkX_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
      (cliPolyNextChunkPlacedOkX_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
      hPeers)

set_option maxHeartbeats 1600000 in
theorem spqrSendPlacedContractsTight_of_cli_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      (withAllocVmPreserved sessionMemsetRegionSpec))
    (hHmac : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) spqrLibcruxHmacSym
      (libcruxHmacBudgetSpec W.C.F M A lim))
    (hStatesIntoPb : subroutine_ok
      (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))) (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecX M A lim W.C.F))) :
    SpqrSendPlacedContractsTight M canonicalV1InnerHeap A lim 0#64 W.C W.Q.K
      (cliGhostExterns gh (cliExternsPlaced mmpl W)) := by
  have hS := cliStatesPlacedSeams_sat mmpl gh W hA hMemset hHmac
  exact spqrSendPlacedContractsTight_of_okX
    (cliSpqrSendAllocContractsPlaced_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (r1sc_cliSpqrSend_coinsFill_on mmpl gh W hA.toCliGhostAllocHooks)
    (LibsignalBinary.Proofs.SignalSession.Cli.SpqrChunkedMergePlacedInstBudget.cliSpqrSend_decodeState_closed_ok
      mmpl gh W hA.toCliGhostAllocHooks (r1sc_hExt_id mmpl gh W))
    (hS.statesFromPb_on)
    hStatesIntoPb
    (cliSpqrSend_chainFromPb_ok mmpl gh W hA.toCliGhostAllocHooks)
    (cliSpqrSend_chainFromVn_ok_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (r1sc_cliSpqrSend_chainAddEpoch_on_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (r1sc_cliSpqrSend_chainSendKey_on_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (cliSpqrSend_chainIntoPb_ok mmpl gh W hA.toCliGhostAllocHooks)
    (r1sc_cliSpqrSend_messageSerialize_on_sat mmpl gh W hA hMemset)
    (r1sc_cliSpqrSend_encodeVarint_on_sat mmpl gh W hA hMemset)
    (cliAuthMacHdr_placed_ok mmpl gh W hA hHmac)
    (cliAuthUpdate_placed_ok_sat mmpl gh W hA hMemset)
    (cliHkdfToVec_placed_ok_sat mmpl gh W hA hMemset)
    (cliEncodeBytesPlacedOkX_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (cliPolyNextChunkPlacedOkX_sat mmpl gh W hA.toCliGhostAllocHooks hMemset)
    (hS.headerSentSendEkChunk_on)
    (hS.ct1ReceivedSendEkChunk_on)
    (hS.ct1SampledSendCt1Chunk_on)
    (hS.ekReceivedCt1SampledSendCt1Chunk_on)
    (hS.ct2SampledSendCt2Chunk_on)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsPlacedInstBudgetSat
