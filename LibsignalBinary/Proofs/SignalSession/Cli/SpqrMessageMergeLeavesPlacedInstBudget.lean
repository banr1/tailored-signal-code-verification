/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ExactPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
import LibsignalBinary.Proofs.RecordCodecs.RecordCodecsCodeSymB
import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.BytesMergeCodeSym
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced
import LibsignalBinary.Proofs.SpqrV1.Unchunked.UnchunkedCodeSym
import LibsignalBinary.Proofs.SpqrV1.Varint.VarintCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Prost.ProstCodeSym

/-!
# Budget-Threaded Placed `MessageMerge` Leaf Instantiations

Proves code-and-rodata-loaded placed budget contracts for `bytes::merge` (Block 290),
`RawVec::<Vec<u8>>::grow_one` (Block 621), `PolynomialDecoder::merge` (Block 296),
`PolynomialEncoder::merge` (Block 297), `Authenticator::merge` (Block 295), and
`Unchunked.{EkSentCt1Received,Ct1Sent}::merge` (Blocks 311, 312).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement LsBlockBound
   blkPC_295 blkPl_295 instIsLsBlockProg_295
   libsignalSessionLib lsProg_261 lsProg_263 lsProg_290 lsProg_291 lsProg_311 lsProg_312
   ls_blockPlacement_base lsmpl withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet (withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed (lsProg_257)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced lsRustNoAllocShimSymCli)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns cliGhostExterns_shim withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (blkPC_296 blkPC_297 blkPl_296 blkPl_297 instIsLsBlockProg_296 instIsLsBlockProg_297)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (growOneVecU8BudgetSpec)
open LibsignalBinary.Heap.SpecBudget (decodeErrorFromBudgetSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_framelessMemcpy_budget_sat cliExternsPlaced_noAllocShim_budget_sat
   cliExternsPlaced_realloc_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
  (cliAuthMerge_blockProgram_cro)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (cliBytes_290_cl cliChainParams_294_cl cliEpochDir_299_cl cliFrom_261_cl
   cliPushMerge_257_cl cliSkip_263_cl cliVarint_291_cl)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrUnchunkedMergePlacedInstBudget
  (cliUnchunkedCt1SentMerge_312_of_auth cliUnchunkedCt1SentMerge_caller_of_auth
   cliUnchunkedEkSentCt1ReceivedMerge_311_of_auth
   cliUnchunkedEkSentCt1ReceivedMerge_caller_of_auth)
open LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOneRustAllocPlacedBudget (growOneVecU8_caller_cro_ok)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseClPlacedBudget
  (auth_merge_base_cl_placed_ok_of_cro_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ExactPlacedBudget (bytes_merge_3_exact_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.ChunkedDefsBudget
  (decodeErrorPushMergeBudgetSpec unchunkedCt1SentMergeSpec unchunkedEkSentCt1ReceivedMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommonBudget
  (bytesMerge3RawBudgetSpec polyDecoderMergeSpec polyEncoderMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyDecoderClPlacedBudget
  (polyDecoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyEncoderClPlacedBudget
  (polyEncoderMerge_cro_placed_ok_of_contracts)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget (decodeVarint2Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)

export LibsignalBinary.Proofs.SignalSession.Cli.SpqrDecodeStatePlacedInstBudgetAux
  (cliChainParams_294_cl cliEpochDir_299_cl)

private theorem hExt_withPanics (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} (hne : sym ≠ "libsignal_session_rng_fill" := by decide) :
    Rust.withPanics ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym := by
  have h1 : Rust.withPanics ext sym =
      Rust.withPanics (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym := by
    simp only [Rust.withPanics, hExt sym hne]
  exact h1.trans (congrFun (withPanics_cliGhostExterns mmpl gh W) sym)

private theorem hookSat_withPanics_hExt {α : Type}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} {spec : Spec α}
    (h : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec)
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide) :
    HookSat (Rust.withPanics ext) sym spec := by
  rcases h with ⟨f, hf, hok⟩
  exact ⟨f, (hExt_withPanics mmpl gh W hExt hne).trans hf, hok⟩

private theorem cliGhost_noAllocShimBudget_sat
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hShim : gh.shim = hookNoop := by rfl) :
    HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsRustNoAllocShimSymCli
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShimSpec :=
  ⟨hookNoop, (cliGhostExterns_shim gh _).trans (congrArg some hShim),
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.noAllocShim_hookOk⟩

private theorem rebase_to_blockProgram [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {H : LibsignalHooks}
    [hcallee : IsLsBlockProg calleeProg j H] {spec : Spec α}
    (h : subroutine_ok calleeProg (libsignalSessionLib.blockPlacement lsmpl j).base spec) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H) (lsmpl.base j) spec := by
  have h' : subroutine_ok (libsignalSessionLib.blockProgram lsmpl j H)
      (libsignalSessionLib.blockPlacement lsmpl j).base spec :=
    hcallee.eq_blockProgram ▸ h
  rwa [ls_blockPlacement_base (i := j)] at h'

private theorem lift_261_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      261 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_261 (Rust.withPanics ext))
      261 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl (cliFrom_261_cl mmpl gh W hA (ext := ext) hExt) hi (by decide) (by decide)

private theorem lift_257_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushMergeBudgetSpec M A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      257 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_257 (Rust.withPanics ext))
      257 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl (cliPushMerge_257_cl mmpl gh W hA (ext := ext) hExt) hi (by decide) (by decide)

private theorem lift_291_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      291 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_291 (Rust.withPanics ext))
      291 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl (cliVarint_291_cl mmpl gh W hA (ext := ext) hExt) hi (by decide) (by decide)

private theorem lift_263_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      263 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_263 (Rust.withPanics ext))
      263 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cl (cliSkip_263_cl mmpl gh W hA (ext := ext) hExt) hi (by decide) (by decide)

private theorem lift_290_cro [LibsignalPlacement] {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      290 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_290 (Rust.withPanics ext))
      290 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro (cliBytes_290_cl mmpl gh W hA (ext := ext) hExt) hi (by decide) (by decide)

/-- Exact-capacity own-block `blockProgram` contract for Block `290` (`bytes::merge [local#3]`)
against `SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim` (`hBytes290` of `SpqrDecodeStatePlacedInstBudget`). -/
theorem cliBytesExact_290_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.bytesMerge3RawBudgetSpec M A lim)) := by
  have h := bytes_merge_3_exact_placed_ok (M := M) (A := A) (lim := lim) (H := Rust.withPanics ext)
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_framelessMemcpy_budget_sat mmpl gh W hA))
    ((hExt_withPanics mmpl gh W hExt).trans (cliGhostExterns_panic_handle_error mmpl gh W))
  rw [IsLsBlockProg.eq_blockProgram (prog := lsProg_290 (Rust.withPanics ext)),
      ls_blockPlacement_base (i := 290)] at h
  exact h

/-- B2 in-image Block `621` (`RawVec::<Vec<u8>>::grow_one`) lifted to any caller block `i < bi`. -/
theorem cliGrowOneVecU8_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    {bi : Nat} [LsBlockBound bi] (hi : i < bi := by decide) :
    subroutine_ok callerProg (lsmpl.base 621)
      (withLsCodeRoLoaded lsmpl (growOneVecU8BudgetSpec M A lim)) :=
  growOneVecU8_caller_cro_ok
    ((hExt_withPanics mmpl gh W hExt).trans (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliGhost_noAllocShimBudget_sat mmpl gh W hA.shim_eq))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_withPanics_hExt mmpl gh W hExt (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    hi

/-- Block `296` (`PolynomialDecoder::merge`) on `(blkPC_296).rebase` with `withLsCodeRoLoaded`. -/
theorem cliPolyDecoderMerge_296_rebase_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_296).rebase (blkPl_296).base (Rust.withPanics ext))
      (blkPl_296).base
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  polyDecoderMerge_cro_placed_ok_of_contracts
    (lift_261_cro (i := 296) mmpl gh W hA hExt)
    (lift_257_cro (i := 296) mmpl gh W hA hExt)
    (lift_291_cro (i := 296) mmpl gh W hA hExt)
    (lift_263_cro (i := 296) mmpl gh W hA hExt)
    (lift_290_cro (i := 296) mmpl gh W hA hExt)
    (cliGrowOneVecU8_at_block (i := 296) (bi := 623) mmpl gh W hA hExt)

/-- Own-block `blockProgram` contract for Block `296` (`PolynomialDecoder::merge`) with `withLsCodeRoLoaded`. -/
theorem cliPolyDecoderMerge_296_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) :=
  rebase_to_blockProgram (j := 296) (cliPolyDecoderMerge_296_rebase_cro mmpl gh W hA (ext := ext) hExt)

/-- Caller-lifted `withLsCodeRoLoaded` contract for Block `296` (`PolynomialDecoder::merge`). -/
theorem cliPolyDecoderMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 296)
      (withLsCodeRoLoaded lsmpl (polyDecoderMergeSpec A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 296 (Rust.withPanics ext))
      296 (Rust.withPanics ext) :=
    ⟨rfl, (instIsLsBlockProg_296 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro (cliPolyDecoderMerge_296_cro mmpl gh W hA (ext := ext) hExt)
    hi (by decide) (by decide)

/-- Block `297` (`PolynomialEncoder::merge`) on `(blkPC_297).rebase` with `withLsCodeRoLoaded`. -/
theorem cliPolyEncoderMerge_297_rebase_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_297).rebase (blkPl_297).base (Rust.withPanics ext))
      (blkPl_297).base
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)) :=
  polyEncoderMerge_cro_placed_ok_of_contracts
    (lift_261_cro (i := 297) mmpl gh W hA hExt)
    (lift_257_cro (i := 297) mmpl gh W hA hExt)
    (lift_291_cro (i := 297) mmpl gh W hA hExt)
    (lift_263_cro (i := 297) mmpl gh W hA hExt)
    (lift_290_cro (i := 297) mmpl gh W hA hExt)
    (cliGrowOneVecU8_at_block (i := 297) (bi := 623) mmpl gh W hA hExt)

/-- Own-block `blockProgram` contract for Block `297` (`PolynomialEncoder::merge`) with `withLsCodeRoLoaded`. -/
theorem cliPolyEncoderMerge_297_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)) :=
  rebase_to_blockProgram (j := 297) (cliPolyEncoderMerge_297_rebase_cro mmpl gh W hA (ext := ext) hExt)

/-- Caller-lifted `withLsCodeRoLoaded` contract for Block `297` (`PolynomialEncoder::merge`). -/
theorem cliPolyEncoderMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 297)
      (withLsCodeRoLoaded lsmpl (polyEncoderMergeSpec A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 297 (Rust.withPanics ext))
      297 (Rust.withPanics ext) :=
    ⟨rfl, (instIsLsBlockProg_297 (Rust.withPanics ext)).externs_eq⟩
  exact ls_subroutine_ok_cro_of_cro (cliPolyEncoderMerge_297_cro mmpl gh W hA (ext := ext) hExt)
    hi (by decide) (by decide)

/-- Closed own-block `blockProgram` contract for Block `295` (`Authenticator::merge`) against
`MergeBaseBudget.authMergeSpec A lim` (using `decodeErrorPushMergeBudgetSpec` on Block `257`). -/
theorem cliAuthMergeBase_blockProgram_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) := by
  let _ := instIsLsBlockProg_295 (Rust.withPanics ext)
  exact rebase_to_blockProgram (j := 295)
    (auth_merge_base_cl_placed_ok_of_cro_contracts (H := Rust.withPanics ext)
      (lift_261_cro (i := 295) mmpl gh W hA (ext := ext) hExt)
      (lift_257_cro (i := 295) mmpl gh W hA (ext := ext) hExt)
      (lift_291_cro (i := 295) mmpl gh W hA (ext := ext) hExt)
      (lift_263_cro (i := 295) mmpl gh W hA (ext := ext) hExt)
      (lift_290_cro (i := 295) mmpl gh W hA (ext := ext) hExt))

/-- Closed own-block `blockProgram` contract for Block `311` (`unchunked::EkSentCt1Received::merge`). -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_311_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 311 (Rust.withPanics ext))
      (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  cliUnchunkedEkSentCt1ReceivedMerge_311_of_auth mmpl gh W hA hExt
    (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt)

/-- Closed caller-lifted contract for Block `311` (`unchunked::EkSentCt1Received::merge`). -/
theorem cliUnchunkedEkSentCt1ReceivedMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 311)
      (withLsCodeRoLoaded lsmpl (unchunkedEkSentCt1ReceivedMergeSpec A lim)) :=
  cliUnchunkedEkSentCt1ReceivedMerge_caller_of_auth mmpl gh W hA hExt
    (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt) hi

/-- Closed own-block `blockProgram` contract for Block `312` (`unchunked::Ct1Sent::merge`). -/
theorem cliUnchunkedCt1SentMerge_312_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 312 (Rust.withPanics ext))
      (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  cliUnchunkedCt1SentMerge_312_of_auth mmpl gh W hA hExt
    (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt)

/-- Closed caller-lifted contract for Block `312` (`unchunked::Ct1Sent::merge`). -/
theorem cliUnchunkedCt1SentMerge_at_block_cro [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 312)
      (withLsCodeRoLoaded lsmpl (unchunkedCt1SentMergeSpec A lim)) :=
  cliUnchunkedCt1SentMerge_caller_of_auth mmpl gh W hA hExt
    (cliAuthMergeBase_blockProgram_cro mmpl gh W hA hExt) hi

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrMessageMergeLeavesPlacedInstBudget
