/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part1PlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Part4aPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Defs

/-!
# `HookSat` Sibling of `SpqrInitialStatePlacedInstBudget` (`SpqrInitialStatePlacedInstBudgetSat`)

Replaces the `memset_row_placed` / `hookMemset_eq_memsetHook` hook-table equality inside
`SpqrInitialStatePlacedInstBudget` (`:622-626`) with
`(hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionBudgetSpec)`
across all 10 `memset`-consuming public theorems (`cliAuthUpdate_placed_ok_sat`,
`cliAuthNew_placed_ok_sat`, `cliInitInner_callInv_placed_ok_sat`,
`cliSpqrInitialState_placed_ok_ext_sat`, `cliSpqrInitialState_placed_ok_blockProgram_ext_sat`,
`cliSpqrInitialState_placed_ok_closed_sat`, `cliSpqrInitialState_at_block_sat`,
`cliSpqrInitialState_lsProg75_sat`, `cliSpqrInitialState_frozen_lsProg75_sat`, and
`cliSpqrInitialState_initProg_sat`). All `memset`-free Group B drop, `Concat`, `into_pb`, and
`encode_to_vec` theorems are re-exported unchanged from `SpqrInitialStatePlacedInstBudget`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudgetSat

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalFrozen LibsignalHooks LibsignalPlacement
   blkPC_270 blkPC_340 blkPC_341 blkPC_386
   blkPl_270 blkPl_340 blkPl_341 blkPl_386
   libsignalSessionLib lsLogFilterAddr lsMemcpySym lsProg_75
   ls_blockPlacement_base ls_externAt?_blockProgram_eq_of_externs_eq
   ls_subroutine_ok_of_block lsmpl lsρ subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1 (Params PqRatchetState Version spqrHkdfWith)
open CryptoVerification.LibsignalTripleRatchet (extHookStack lsMemsetSym)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8At vecU8Buf)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other
   hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate (initProgPlaced)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.ChainProofs (hkdfToSliceSpqrSpec)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts
  (LsCallInv subroutine_ok_withLsCallInv_of_withLsCodeLoaded withLsCallInv)
open CryptoVerification.SpqrV1.Drop
  (dropStack96 optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize protoPqRatchetStateAt)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (encodeToVecStackX pqRatchetStatePBAt)
open CryptoVerification.SpqrV1.Top.InitInner
  (InitInnerGhost initInnerResultAt initInnerStack initInnerStackX
   lsro_statesIntoPbJumpTablePlacedAt statesIntoPbJumpTablePlacedAt)
open CryptoVerification.SpqrV1.Top.InitialState
  (InitialStateGhost h61s_initialStateSavedCells h61s_stackAt_initialState_split
   initialStatePB initialStatePB_encodeRaw_length_lt initialStatePlacedEntry
   initialStatePlacedProg initialStateResultAt initialStateStack initialStateValue
   initialState_pbAt_of_cells memRegion_pqState_split memRegion_ret_32_split paramsAt
   readReg32_of_eq stackAt_initInner_split_allocHook stackAt_initInner_split_dropStack96
   stackAt_initInner_split_encodeToVec)
open CryptoVerification.SpqrV1.Top.Placed (blkPC_324 blkPl_324 instIsLsBlockProg_327)
open CryptoVerification.SpqrV1.Top.Recv
  (lsro_optProtoInnerStateJumpTablePlacedAt protoPqRatchetStateAt_eq_pqRatchetStatePBAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
   rustCliAllocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1PlacedBudget
  (InitialStateMemInvPlacedOk initialStateFrozenPlacedOk_of_codeRoLoaded
   spqrInitialStatePlacedInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.StepSpqrPlacedBudget
  (spqrInitialStateInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks CliGhostSpqrAllocHooks cliExternsPlaced_exactMemcpy_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliAllocBudget_at_block cliAllocWithStack_at_block cliAllocZeroedWithStack_at_block
   cliDeallocWithStack_at_block cliDrop_270_cl_rebase cliEncodeToVec_placed_ok
   cliFramelessMemcpyBudget_at_block cliNoAllocShimBudget_at_block cliShimBudgetWithStack_at_block
   cliSliceConcat2_placed_ok cliStatesIntoPb_initV1State_cl)
open LibsignalBinary.Proofs.SpqrV1.Auth.NewBudgetAux
  (AuthNewPlacedOk authNew_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux
  (AuthUpdatePlacedOk authUpdateSpec authUpdate_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Spec)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOkBudgetSat
  (hkdf_to_slice_spqr_placed_ok_of_other_block_sat)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget
  (PqRatchetStateEncodeToVecPlacedOkExt)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv initInnerPlacedSpecX initInnerPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudget
  (authNew_324_of_placedOk ls_subroutine_ok_callInv_of_block
   withLsCallInv_authNewBudgetSpec_of_authNewSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.ProofPlacedBudgetAux
  (InitInnerBudgetPanic cloneEvs initInner_seq_sepWP_lsInv init_inner_placed_ok_x_of_arms
   sepWPp_call_total_keepLsInv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
  (InitialStateEnv InitialStatePlacedOkBlockProgram InitialStatePlacedOkX
   initialStatePlacedSpec initialStatePlacedSpecOfEnv initialStatePlacedSpecX)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.ProofPlacedBudget
  (initialStateVPlacedSpecX initialState_placed_ok_of_versions initialState_v0_placed_ok
   withPanics_eq_of_isPanicSymbol)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.StepsPlacedBudget
  (InitialStateV1PlacedPost call_dropPqRatchetState_placed call_encodeToVec_placed_x
   fitsEnv_encodeToVec_of_initialStateEnv fitsEnv_initInner_of_initialStateEnv
   initialStateEnv_v1_of_stages initial_state_epilogue_placed initial_state_pre_drop_placed
   initial_state_pre_encode_to_vec_placed initial_state_pre_init_inner_placed
   initial_state_prologue_v1_placed initial_state_to_vec_placed sepWPp_of_initialState_v1_placed_wpp)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat hookSat_sessionMemsetRegion_of_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)

/-! ## 1. `HkdfPlacedHooksExactSat` Bridge & Coercion from `CliGhostAllocHooks` -/

private theorem hExt_withPanics_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  intro sym hne
  refine (?_ : Rust.withPanics ext sym =
    Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym).trans
    (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)
  unfold Rust.withPanics
  rw [hExt sym hne]

/-- Ghost-`memset` discharge of `hMemset` from `CliGhostAllocHooks`. -/
theorem cliGhostExterns_sessionMemsetRegion_budget_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset" sessionMemsetRegionBudgetSpec :=
  cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA

private theorem hkdfPlacedHooksBudgetSat_of_hExt [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    HkdfPlacedHooksExactSat W.C.F H where
  memset := hookSat_of_eq (hExt _ (by decide))
    (hookSat_sessionMemsetRegion_of_budget
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl gh W hA))
  memcpy := by
    rcases cliExternsPlaced_exactMemcpy_sat mmpl gh W hA with ⟨f, hf, hex⟩
    exact ⟨f, (hExt _ (by decide)).trans hf, hex⟩
  compress256 := by
    rw [hExt _ (by decide), cliGhostExterns_other gh (cliExternsPlaced mmpl W)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact cliExternsPlaced_row mmpl W (compress256_row_placed mmpl W)

private theorem subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded_sat [LibsignalPlacement]
    {α : Type} {P : Program} {addr : BitVec 64} {spec : Spec α}
    (h : subroutine_ok P addr (withLsCodeRoLoaded lsmpl spec)) :
    subroutine_ok P addr (withLsCallInv lsmpl spec) := by
  refine subroutine_ok_mono h (fun _ _ _ hm => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withLsCallInv, withLsCodeRoLoaded] at hm ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨⟨hm.1.2, hm.1.1⟩, hm.2⟩

/-! ## 2. Blocks `341, 340, 324` (`Auth::{update,new}`, `init_inner`) under `HookSat` -/

theorem cliAuthUpdate_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    AuthUpdatePlacedOk W.C.F M A lim H := by
  let _ : HkdfPlacedHooksExactSat W.C.F H :=
    hkdfPlacedHooksBudgetSat_of_hExt mmpl gh W hA.toCliGhostAllocHooks hExt
  have h_concat_386 : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsmpl.base 386) (withLsCodeLoaded lsmpl (sliceConcat2Spec M A lim)) := by
    rw [← ls_blockPlacement_base (i := 386)]
    exact subroutine_ok_withLsCodeLoaded_of_plain
      (cliSliceConcat2_placed_ok mmpl gh W hA.toCliGhostAllocHooks hExt)
  have h_concat : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 386) (withLsCallInv lsmpl (sliceConcat2Spec M A lim)) :=
    subroutine_ok_withLsCallInv_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (i := 341) (j := 386) h_concat_386)
  have h_hkdf : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 379)
      (withLsCallInv lsmpl (withVmPreserved (hkdfToSliceSpqrSpec (spqrHkdfWith W.C.F)))) :=
    subroutine_ok_withLsCallInv_of_withLsCodeRoLoaded_sat
      (hkdf_to_slice_spqr_placed_ok_of_other_block_sat W.C
        (hookSat_of_eq (hExt lsMemsetSym (by decide)) hMemset) (i := 341))
  exact authUpdate_placed_ok
    h_concat
    h_hkdf
    (cliShimBudgetWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack (i := 341))
    (cliAllocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks hExt (i := 341))
    (cliAllocZeroedWithStack_at_block mmpl gh W hA hExt (i := 341))
    (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks hExt (i := 341))

theorem cliAuthNew_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    AuthNewPlacedOk W.C.F M A lim H := by
  have h_upd_341 : subroutine_ok ((blkPC_341).rebase (blkPl_341).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec W.C.F M A lim)) := by
    rw [← ls_blockPlacement_base (i := 341)]
    exact cliAuthUpdate_placed_ok_sat mmpl gh W hA hMemset hExt
  have h_upd : subroutine_ok ((blkPC_340).rebase (blkPl_340).base H)
      (lsmpl.base 341) (withLsCallInv lsmpl (authUpdateSpec W.C.F M A lim)) :=
    ls_subroutine_ok_callInv_of_block (i := 340) (j := 341) h_upd_341
  exact authNew_placed_ok
    h_upd
    (cliShimBudgetWithStack_at_block mmpl gh W hA.shim_eq hExt extHookStack (i := 340))
    (cliAllocZeroedWithStack_at_block mmpl gh W hA hExt (i := 340))
    (cliDeallocWithStack_at_block mmpl gh W hA.toCliGhostAllocHooks hExt (i := 340))

theorem cliInitInner_callInv_placed_ok_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim W.C.F)) :=
  init_inner_placed_ok_x_of_arms
    (cliNoAllocShimBudget_at_block mmpl gh W hA.shim_eq (hExt_withPanics_sat mmpl gh W hExt) (i := 324))
    (cliAllocBudget_at_block mmpl gh W hA.toCliGhostAllocHooks
      (hExt_withPanics_sat mmpl gh W hExt) (i := 324))
    (cliFramelessMemcpyBudget_at_block mmpl gh W hA.toCliGhostAllocHooks
      (hExt_withPanics_sat mmpl gh W hExt) (i := 324))
    (withLsCallInv_authNewBudgetSpec_of_authNewSpec
      (authNew_324_of_placedOk
        (cliAuthNew_placed_ok_sat mmpl gh W hA hMemset (hExt_withPanics_sat mmpl gh W hExt))))
    (cliStatesIntoPb_initV1State_cl mmpl gh W hA.toCliGhostAllocHooks hExt .a2b)
    (cliStatesIntoPb_initV1State_cl mmpl gh W hA.toCliGhostAllocHooks hExt .b2a)

/-! ## 3. Block `327` (`spqr::initial_state`) Closed Seam & Cross-Block Corollaries -/

private theorem call_initInner_callInv_placed_x_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)))
    {Q : State → SepProp → Prop}
    (s0 s : State) (x : InitialStateGhost) (st_in : M.σ) (Frame R : SepProp)
    (hinv : LsCallInv lsmpl s.mem) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hak_ne : x.akPtr ≠ 0#64) (hlt : 32 + x.p.authKey.length < 2 ^ 63)
    (hfit_in : FitsEnv M lim st_in
      (InitInnerEnv F ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩))
    (hpc : s.pc = lsmpl.base 324)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 496#64)
    (hlr : s.readReg64 .x30 = initialStatePlacedEntry + 344#64)
    (hx0 : s.readReg64 .x0 = (s0.sp - 456#64) + 0x80#64)
    (hw1 : s.readReg32 .x1 = Version.v1.toI32) (hw2 : s.readReg32 .x2 = x.p.direction.toI32)
    (hx3 : s.readReg64 .x3 = x.akPtr) (hx4 : s.readReg64 .x4 = BitVec.ofNat 64 x.p.authKey.length)
    (htrace : s.trace = s0.trace)
    (hnext : ∀ (sf : State) (evs₂ : List AllocEvent),
      sf.pc = initialStatePlacedEntry + 344#64 →
      sf.status = .Running → LsCallInv lsmpl sf.mem → sf.sp = s0.sp - 496#64 →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      InitInnerEnv F ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩ evs₂ →
      SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) sf
        ((initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
          (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
          A.pool lim (M.stepEvents evs₂ st_in) sf ∗
          stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
        Q (InitInnerBudgetPanic R)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s
      ((memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool lim st_in s ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗ Frame)
      Q (InitInnerBudgetPanic R) := by
  let _ := instIsLsBlockProg_327 (Rust.withPanics ext)
  have hfsp_align : ((s0.sp - 496#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 496#64 hsp0_align (by decide)
  have hinit_base : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (lsmpl.base 324) (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) := by
    rwa [← ls_blockPlacement_base (i := 324)]
  have hcall : subroutine_ok (initialStatePlacedProg ext) (lsmpl.base 324)
      (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)) :=
    ls_subroutine_ok_callInv_of_block (callerProg := initialStatePlacedProg ext)
      (i := 327) (j := 324) hinit_base
  let gx : InitInnerGhost :=
    ⟨(s0.sp - 456#64) + 0x80#64, .v1, x.p.direction, x.akPtr, x.p.authKey⟩
  refine sepWPp_call_total_keepLsInv (gx, st_in) (Frame := Frame)
    hcall hpc hrun (by rw [State.spAligned, hsp]; exact hfsp_align) hlr
    (fun R' hm => by
      dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpecXOfEnv, initInnerStackX, gx]
      rw [hsp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
      exact ⟨hinv, ⟨hx0, hw1, hw2, hx3, hx4, hak_ne, hlt, hfit_in⟩, hm⟩)
    (hnext := fun sf hpc_sf hrun_sf _ hinv_sf hsp_sf hcs_sf => ?_)
  dsimp only [withLsCallInv, initInnerPlacedSpecX, initInnerPlacedSpecXOfEnv, initInnerStackX, gx]
  rw [hsp, sepExists_sepConj_left]
  refine SepWPp.exists_elim fun evs₂ => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_left fun ⟨htr, hevs₂⟩ => ?_
  have hnext' := hnext sf evs₂ hpc_sf hrun_sf (hinv_sf hinv) (by rw [hsp_sf, hsp]) hcs_sf
    (by rw [htr, htrace]) hevs₂
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl)) hnext'

private theorem initial_state_v1_body_callInv_placed_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim)))
    (s0 : State) (x : InitialStateGhost) (st0 : M.σ) (R : SepProp)
    (hinv0 : LsCallInv lsmpl s0.mem)
    (hpc : s0.pc = initialStatePlacedEntry)
    (hrun : s0.status = .Running) (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hv : x.p.version = .v1) (hx0 : s0.readReg64 .x0 = x.pA) (hx8 : s0.readReg64 .x8 = x.ret)
    (hak_ne : x.akPtr ≠ 0#64) (hlen : x.p.authKey.length < 2 ^ 32)
    (hfit : FitsEnv M lim st0 (InitialStateEnv F x))
    (hlen_pb : (PqRatchetState.encodeRaw (initialStatePB F x.p)).length < 2 ^ 63)
    (hproto_eq : protoPqRatchetStateAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) =
      pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p))
    (hpbAt : ∀ ptr : BitVec 64,
      (vecU8At A.repAlloc (s0.sp - 456#64) (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
        (((s0.sp - 456#64) + 0x18#64) ↦₃₂ 1#32) ∗
        (((s0.sp - 456#64) + 0x1c#64) ↦₃₂ x.p.chainParams.intoPb.maxJump) ∗
        (((s0.sp - 456#64) + 0x20#64) ↦₃₂ x.p.chainParams.intoPb.maxOooKeys) ∗
        (((s0.sp - 456#64) + 0x24#64) ↦₃₂ x.p.direction.toI32) ∗
        (((s0.sp - 456#64) + 0x28#64) ↦₃₂ x.p.minVersion.toI32) ∗
        memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
        (((s0.sp - 456#64) + 0x30#64) ↦₆₄ noneCap) ∗
        memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
        initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64)
          .v1 x.p.direction x.p.authKey) ⊢
      pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p)) :
    SepWPp (initialStatePlacedProg ext) (s0.readReg64 .x30) s0
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack)
      (InitialStateV1PlacedPost M A lim F s0 x st0)
      (InitInnerBudgetPanic R) := by
  have hlt63 : x.p.authKey.length < 2 ^ 63 := by omega
  have hlt32_63 : 32 + x.p.authKey.length < 2 ^ 63 := by omega
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 96#64) 12 ∗ paramsAt x.pA x.akPtr x.p ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      ((x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s0 ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [h61s_stackAt_initialState_split s0.sp]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_prologue_v1_placed s0 x _ hsp0_align hpc hrun hx0 hx8 hv hlen) ?_
  intro s1 hpc1 hrun1 _ hinv1
    ⟨hvm1, hsp1, hx29_1, hx19_1, hx20_1, hx21_1, hx22_1, hw25_1, htr1, hvregs1⟩
  refine SepWPp.weaken_pre (P' :=
      (x.akPtr ↦ₛ x.p.authKey) ∗ A.pool lim st0 s1 ∗ stackAt (s0.sp - 496#64) allocHookStack ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13584 ∗ paramsAt x.pA x.akPtr x.p ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [stackAt_initInner_split_allocHook (s0.sp - 496#64), ← A.pool_of_vmPreserved hvm1]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initial_state_to_vec_placed hshim halloc hmemcpy s0 s1 x st0 _ R
    hsp0_align hlt63 hv hfit
    hpc1 hrun1 hsp1 hx29_1 hx19_1 hx20_1 hx21_1 hx22_1 hw25_1 htr1 hvregs1 ?_
  intro s2 ptr hpc2 hrun2 hinv2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2
  let st1 := M.stepEvents (cloneEvs x.p.authKey) st0
  refine SepWPp.weaken_pre (P' :=
      paramsAt x.pA x.akPtr x.p ∗
      (memRegion (s0.sp - 456#64) 352 ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       statesIntoPbJumpTablePlacedAt ∗ A.pool lim st1 s2 ∗
       stackAt (s0.sp - 496#64) initInnerStack ∗
       vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       h61s_initialStateSavedCells s0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 496#64) 40 ∗ memRegion (s0.sp - 104#64) 8 ∗
       memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_allocHook (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_init_inner_placed s0 s2 x ptr _ hsp0_align
      hpc2 hrun2 hsp2 hx29_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hw25_2 htr2 hvregs2) ?_
  intro s3 hpc3 hrun3 _ hinv3
    ⟨hvm3, hsp3, hlr3, hx0_3, hw1_3, hw2_3, hx3_3, hx4_3, hx29_3, hx19_3, hw20_3, hx21_3, hx23_3,
     hw24_3, hw25_3, hw26_3, hw27_3, htr3, hvregs3⟩
  refine SepWPp.weaken_pre (P' :=
      (memRegion ((s0.sp - 456#64) + 0x80#64) optProtoInnerStateSize ∗
        (x.akPtr ↦ₛ x.p.authKey) ∗ statesIntoPbJumpTablePlacedAt ∗
        A.pool lim st1 s3 ∗ stackAt (s0.sp - 496#64) initInnerStack) ∗
      (cells (s0.sp - 456#64) 3 ∗
       (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
       (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
       (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
       (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
       (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
       memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
       (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
       memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
       vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
       paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ memRegion x.ret 32 ∗ optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_pqState_split (s0.sp - 456#64), ← A.pool_of_vmPreserved hvm3]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hinv_s3 : LsCallInv lsmpl s3.mem := hinv3 (hinv2 (hinv1 hinv0))
  have hfit_init := fitsEnv_initInner_of_initialStateEnv ((s0.sp - 456#64) + 0x80#64) hv hfit
  refine call_initInner_callInv_placed_x_sat hinit s0 s3 x st1 _ R hinv_s3 hsp0_align hak_ne hlt32_63 hfit_init
    hpc3 hrun3 hsp3 hlr3 hx0_3 hw1_3 hw2_3 hx3_3 hx4_3 htr3 ?_
  intro s4 evs₂ hpc4 hrun4 hinv4 hsp4 hcs4 htr4 hevs₂
  let st2 := M.stepEvents evs₂ st1
  obtain ⟨hx19_4, hx20_4, hx21_4, _, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, _, hx29_4⟩ := hcs4
  refine SepWPp.weaken_pre (P' :=
      cells (s0.sp - 456#64) 3 ∗
      (∃∗ v0 : BitVec 32, ((s0.sp - 456#64) + 0x18#64) ↦₃₂ v0) ∗
      (∃∗ v1 : BitVec 32, ((s0.sp - 456#64) + 0x1c#64) ↦₃₂ v1) ∗
      (∃∗ v2 : BitVec 32, ((s0.sp - 456#64) + 0x20#64) ↦₃₂ v2) ∗
      (∃∗ v3 : BitVec 32, ((s0.sp - 456#64) + 0x24#64) ↦₃₂ v3) ∗
      (∃∗ v4 : BitVec 32, ((s0.sp - 456#64) + 0x28#64) ↦₃₂ v4) ∗
      memRegion ((s0.sp - 456#64) + 0x2c#64) 4 ∗
      (∃∗ w6 : BitVec 64, ((s0.sp - 456#64) + 0x30#64) ↦₆₄ w6) ∗
      memRegion ((s0.sp - 456#64) + 0x38#64) 72 ∗
      initInnerResultAt A.repAlloc (F := F) ((s0.sp - 456#64) + 0x80#64) .v1 x.p.direction x.p.authKey ∗
      vecU8Buf A.repAlloc (BitVec.ofNat 64 x.p.authKey.length) ptr x.p.authKey ∗
      (memRegion x.ret 32 ∗ A.pool lim st2 s4 ∗ stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
       optProtoInnerStateJumpTablePlacedAt))
    (Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_encode_to_vec_placed s0 s4 x ptr _ (hpbAt ptr) hsp0_align
      hpc4 hrun4 hsp4
      (hx29_4.1.trans hx29_3) (hx19_4.trans hx19_3)
      ((readReg32_of_eq hx20_4).trans hw20_3)
      (hx21_4.trans hx21_3) (hx23_4.trans hx23_3)
      ((readReg32_of_eq hx24_4).trans hw24_3)
      ((readReg32_of_eq hx25_4).trans hw25_3)
      ((readReg32_of_eq hx26_4).trans hw26_3)
      ((readReg32_of_eq hx27_4).trans hw27_3) htr4 (hx29_4.2.trans hvregs3)) ?_
  intro s5 hpc5 hrun5 _ hinv5 ⟨hvm5, hsp5, hlr5, hx0_5, hx1_5, hx29_5, hx19_5, htr5, hvregs5⟩
  refine SepWPp.weaken_pre (P' :=
      ∃∗ r0 : BitVec 64,
        (memRegion (x.ret + 8#64) 24 ∗
         pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
         A.pool lim st2 s5 ∗ stackAt (s0.sp - 496#64) encodeToVecStackX) ∗
        ((x.ret ↦₆₄ r0) ∗
         memRegion ((s0.sp - 496#64) - 17680#64) (initInnerStack - encodeToVecStackX) ∗
         (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
         memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt ∗
         optProtoInnerStateJumpTablePlacedAt))
    (by
      rw [memRegion_ret_32_split x.ret, stackAt_initInner_split_encodeToVec (s0.sp - 496#64),
          ← A.pool_of_vmPreserved hvm5]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply Entails.sepExists_elim; intro r0
      exact Entails.sepExists_right r0 (Entails.of_eq (by sep_ac_rfl))) ?_
  refine SepWPp.exists_elim fun r0 => ?_
  have hinv_s5 : LsCallInv lsmpl s5.mem := hinv5 hinv4
  have hfit_enc := fitsEnv_encodeToVec_of_initialStateEnv hv hfit hevs₂
  refine call_encodeToVec_placed_x henc s0 s5 x st2 _ R hinv_s5 hsp0_align hlen_pb hfit_enc
    hpc5 hrun5 hsp5 hlr5 hx0_5 hx1_5 htr5 ?_
  intro s6 evs₃ hpc6 hrun6 hinv6 hsp6 hcs6 htr6 hevs₃
  let st3 := M.stepEvents evs₃ st2
  obtain ⟨hx19_6, _, _, _, _, _, _, _, _, _, hx29_6⟩ := hcs6
  refine SepWPp.weaken_pre (P' :=
      (x.ret ↦₆₄ r0) ∗ vecU8 A.repAlloc (x.ret + 8#64) (PqRatchetState.encodeRaw (initialStatePB F x.p)) ∗
      (pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st3 s6 ∗
       stackAt (s0.sp - 496#64) initInnerStack ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by rw [stackAt_initInner_split_encodeToVec (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_pre_drop_placed s0 s6 x r0 _ hv hsp0_align
      hpc6 hrun6 hsp6 (hx29_6.1.trans hx29_5) (hx19_6.trans hx19_5) htr6 (hx29_6.2.trans hvregs5)) ?_
  intro s7 hpc7 hrun7 _ hinv7 ⟨hvm7, hsp7, hlr7, hx0_7, hx29_7, htr7, hvregs7⟩
  refine SepWPp.weaken_pre (P' :=
      (pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p) ∗
       optProtoInnerStateJumpTablePlacedAt ∗ A.pool lim st3 s7 ∗
       stackAt (s0.sp - 496#64) dropStack96) ∗
      (memRegion ((s0.sp - 496#64) - 17680#64) 13488 ∗
       initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (x.akPtr ↦ₛ x.p.authKey) ∗ paramsAt x.pA x.akPtr x.p ∗ h61s_initialStateSavedCells s0 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ memRegion (s0.sp - 496#64) 40 ∗
       memRegion (s0.sp - 104#64) 8 ∗ statesIntoPbJumpTablePlacedAt))
    (by
      rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64), ← A.pool_of_vmPreserved hvm7]
      exact Entails.of_eq (by sep_ac_rfl)) ?_
  have hinv_s7 : LsCallInv lsmpl s7.mem := hinv7 hinv6
  refine call_dropPqRatchetState_placed hdrop s0 s7 x st3 _ R hinv_s7 hproto_eq hsp0_align
    hpc7 hrun7 hsp7 hlr7 hx0_7 htr7 ?_
  intro s8 evs₄ hpc8 hrun8 hsp8 hcs8 htr8 hevs₄
  let st4 := M.stepEvents evs₄ st3
  refine SepWPp.weaken_pre (P' :=
      stackAt (s0.sp - 496#64) initInnerStack ∗ memRegion (s0.sp - 496#64) 40 ∗
      memRegion (s0.sp - 456#64) 352 ∗ memRegion (s0.sp - 104#64) 8 ∗
      h61s_initialStateSavedCells s0 ∗
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗
       initialStateResultAt A.repAlloc x.ret (initialStateValue F x.p) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st4 s8))
    (by rw [stackAt_initInner_split_dropStack96 (s0.sp - 496#64)]; exact Entails.of_eq (by sep_ac_rfl)) ?_
  refine initInner_seq_sepWP_lsInv
    (initial_state_epilogue_placed s0 s8 _ hsp0_align hpc8 hrun8 hsp8 htr8
      (hcs8.2.2.2.2.2.2.2.2.2.2.2.trans hvregs7)) ?_
  intro sf hpcf hrunf _ _ ⟨hvmf, hspf, hcsf, htrf⟩
  let evs := ((cloneEvs x.p.authKey ++ evs₂) ++ evs₃) ++ evs₄
  have hevs : InitialStateEnv F x evs :=
    initialStateEnv_v1_of_stages hv hfit hevs₂ hevs₃ hevs₄
  have hst_eq : st4 = M.stepEvents evs st0 := by
    dsimp only [st4, st3, st2, st1, evs]
    simp only [M.stepEvents_append]
  refine SepWPp.done hpcf hrunf ⟨⟨evs, hevs, ?_⟩, hspf, hcsf, htrf⟩
  rw [hst_eq, A.pool_of_vmPreserved hvmf]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem initialState_v1_callInv_placed_ok_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustNoAllocShimSym)
      noAllocShimBudgetSpec)
    (halloc : subroutine_ok (initialStatePlacedProg ext) (lsρ spqrRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (initialStatePlacedProg ext) (lsρ lsMemcpySym)
      framelessMemcpyBudgetSpec)
    (hinit : subroutine_ok ((blkPC_324).rebase (blkPl_324).base (Rust.withPanics ext))
      (blkPl_324).base (withLsCallInv lsmpl (initInnerPlacedSpecX M A lim F)))
    (henc : PqRatchetStateEncodeToVecPlacedOkExt A lim ext)
    (hdrop : subroutine_ok ((blkPC_270).rebase (blkPl_270).base (Rust.withPanics ext))
      (blkPl_270).base (withLsCodeLoaded lsmpl (dropProtoPqRatchetStatePlacedSpec M A lim))) :
    subroutine_ok (initialStatePlacedProg ext) initialStatePlacedEntry
      (initialStateVPlacedSpecX M A lim F .v1) := by
  refine subroutine_ok_of_sepWPp fun (x, st0) R s0 hpc hrun hpre hsp => ?_
  have hsp_align : (s0.sp &&& 15#64 == 0#64) = true := hsp
  dsimp only [initialStateVPlacedSpecX, initialStatePlacedSpecX,
    withLsCodeRoLoaded, initialStatePlacedSpec, initialStatePlacedSpecOfEnv] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hv, hpre⟩ := hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hcl0, hro0⟩, hpre⟩ := hpre
  have hinv0 : LsCallInv lsmpl s0.mem := ⟨hro0, hcl0⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx8, hak_ne, hlen, hfit⟩, hmem⟩ := hpre
  have hmem1 := lsro_optProtoInnerStateJumpTablePlacedAt hro0 hmem
  have hmem2 := lsro_statesIntoPbJumpTablePlacedAt hro0 hmem1
  have hmem3 : s0.mem ⊨
      (statesIntoPbJumpTablePlacedAt ∗ optProtoInnerStateJumpTablePlacedAt ∗
       paramsAt x.pA x.akPtr x.p ∗ (x.akPtr ↦ₛ x.p.authKey) ∗ memRegion x.ret 32 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st0 s0 ∗ stackAt s0.sp initialStateStack) ∗ R :=
    Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem2
  have hwpp := initial_state_v1_body_callInv_placed_sat hshim halloc hmemcpy
    hinit henc hdrop s0 x st0 R hinv0 hpc hrun hsp_align hv hx0 hx8 hak_ne hlen hfit
    (initialStatePB_encodeRaw_length_lt F x.p hlen)
    (protoPqRatchetStateAt_eq_pqRatchetStatePBAt A.repAlloc (s0.sp - 456#64) (initialStatePB F x.p))
    (fun ptr => initialState_pbAt_of_cells A.repAlloc F x.p hv (s0.sp - 456#64)
      (BitVec.ofNat 64 x.p.authKey.length) ptr)
  exact ⟨_, R, hmem3, sepWPp_of_initialState_v1_placed_wpp s0 x st0 _ R hwpp⟩

private theorem cliGhostExterns_isPanic'_sat (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks)
    (W : CliHooks) :
    ∀ sym, Rust.isPanicSymbol sym = true →
      cliGhostExterns gh (cliExternsPlaced mmpl W) sym = some Rust.panicked := by
  intro sym hsym
  have h := congrFun (withPanics_cliGhostExterns mmpl gh W) sym
  simp only [Rust.withPanics, hsym, ↓reduceIte] at h
  exact h.symm

/-- `HookSat` sibling of `cliSpqrInitialState_placed_ok_ext`. -/
theorem cliSpqrInitialState_placed_ok_ext_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    InitialStatePlacedOkX M A lim W.C.F ext := by
  let _ := instIsLsBlockProg_327 (Rust.withPanics ext)
  exact initialState_placed_ok_of_versions
    initialState_v0_placed_ok
    (initialState_v1_callInv_placed_ok_sat
      (cliNoAllocShimBudget_at_block mmpl gh W hA.shim_eq (hExt_withPanics_sat mmpl gh W hExt) (i := 327))
      (cliAllocBudget_at_block mmpl gh W hA.toCliGhostAllocHooks
        (hExt_withPanics_sat mmpl gh W hExt) (i := 327))
      (cliFramelessMemcpyBudget_at_block mmpl gh W hA.toCliGhostAllocHooks
        (hExt_withPanics_sat mmpl gh W hExt) (i := 327))
      (cliInitInner_callInv_placed_ok_sat mmpl gh W hA hMemset hExt)
      (cliEncodeToVec_placed_ok mmpl gh W hA.toCliGhostAllocHooks hExt)
      (cliDrop_270_cl_rebase mmpl gh W hA.toCliGhostAllocHooks hExt))

/-- `HookSat` sibling of `cliSpqrInitialState_placed_ok_blockProgram_ext`. -/
theorem cliSpqrInitialState_placed_ok_blockProgram_ext_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    InitialStatePlacedOkBlockProgram M A lim W.C.F ext := by
  let _ := instIsLsBlockProg_327 (Rust.withPanics ext)
  have hok := cliSpqrInitialState_placed_ok_ext_sat mmpl gh W hA hMemset hExt
  dsimp only [InitialStatePlacedOkBlockProgram, InitialStatePlacedOkX] at hok ⊢
  rw [IsLsBlockProg.eq_blockProgram (prog := initialStatePlacedProg ext),
    initialStatePlacedEntry, ls_blockPlacement_base (i := 327)] at hok
  exact hok

/-- `HookSat` sibling of `cliSpqrInitialState_placed_ok_closed`. -/
theorem cliSpqrInitialState_placed_ok_closed_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 327 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStatePlacedInnerSpec M A lim W.C.F)) := by
  have hok := cliSpqrInitialState_placed_ok_blockProgram_ext_sat mmpl gh W hA hMemset
    (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)) (fun _ _ => rfl)
  dsimp only [InitialStatePlacedOkBlockProgram] at hok
  rwa [withPanics_eq_of_isPanicSymbol (cliGhostExterns_isPanic'_sat mmpl gh W)] at hok

/-- `HookSat` sibling of `cliSpqrInitialState_at_block`. -/
theorem cliSpqrInitialState_at_block_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec)
    {callerProg : Program} {i : Nat}
    [hcaller : IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (_hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl (spqrInitialStatePlacedInnerSpec M A lim W.C.F)) := by
  have hcallee := cliSpqrInitialState_placed_ok_closed_sat mmpl gh W hA hMemset
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hcrl : LibsignalCodeRoLoaded lsmpl s0.mem := by
    dsimp only [withLsCodeRoLoaded] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    exact hpre.1
  have hQL :
      (libsignalSessionLib.blockProgram lsmpl 327
        (cliGhostExterns gh (cliExternsPlaced mmpl W))).CodeLoaded s0.mem :=
    hcrl.1 327 (by decide) (by decide) (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc,
      (libsignalSessionLib.blockProgram lsmpl 327
        (cliGhostExterns gh (cliExternsPlaced mmpl W))).externAt? pc =
        callerProg.externAt? pc := fun pc => by
    rw [hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl
        (cliGhostExterns gh (cliExternsPlaced mmpl W)) Syscall.standard
        ((instIsLsBlockProg_327
          (cliGhostExterns gh (cliExternsPlaced mmpl W))).externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc :
      (libsignalSessionLib.blockProgram lsmpl 327
        (cliGhostExterns gh (cliExternsPlaced mmpl W))).svc = callerProg.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- `HookSat` sibling of `cliSpqrInitialState_lsProg75`. -/
theorem cliSpqrInitialState_lsProg75_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec) :
    InitialStateMemInvPlacedOk M (CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl)
      A lim W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  cliSpqrInitialState_at_block_sat mmpl gh W hA hMemset
    (callerProg := lsProg_75 (cliGhostExterns gh (cliExternsPlaced mmpl W))) (i := 75)

/-- `HookSat` sibling of `cliSpqrInitialState_frozen_lsProg75`. -/
theorem cliSpqrInitialState_frozen_lsProg75_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec) :
    InitialStateMemInvPlacedOk M (LibsignalFrozen lsmpl)
      A lim W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
  initialStateFrozenPlacedOk_of_codeRoLoaded
    (cliSpqrInitialState_lsProg75_sat mmpl gh W hA hMemset)

/-- `HookSat` sibling of `cliSpqrInitialState_initProg`. -/
theorem cliSpqrInitialState_initProg_sat [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostSpqrAllocHooks M A lim gh)
    (hMemset : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) "memset"
      sessionMemsetRegionBudgetSpec) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
      (withLsCodeRoLoaded lsmpl
        (spqrInitialStateInnerSpec A lim
          (fun (p : Params) => InitialStateEnv W.C.F ⟨0#64, 0#64, 0#64, p⟩) W.C.F)) :=
  cliSpqrInitialState_at_block_sat mmpl gh W hA hMemset
    (callerProg := initProgPlaced mmpl gh W) (i := 521)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudgetSat
