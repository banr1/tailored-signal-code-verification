/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInst
public import LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlaced

/-!
# Budget-Threaded Code-Loaded Placed `Authenticator::merge` (Block `295`) CLI Instantiations

Instantiates `MergeClPlacedBudget.auth_merge_cl_placed_ok_of_contracts` (and `_env`) for Block `295`
(`prost::encoding::message::merge::<spqr::proto::pq_ratchet::Authenticator, &mut &[u8]> [local#2]`)
and its five cross-block callees (Blocks `257, 261, 263, 290, 291`) under `[LibsignalPlacement]`
and `CliGhostAllocHooks M A lim gh`, providing hook-polymorphic, own-block, `blockProgram`, and
caller-block-polymorphic corollaries.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkPC_261 blkPC_263 blkPC_290 blkPC_291 blkPC_295
   blkPl_261 blkPl_263 blkPl_290 blkPl_291 blkPl_295
   instIsLsBlockProg_261 instIsLsBlockProg_263 instIsLsBlockProg_290
   instIsLsBlockProg_291 instIsLsBlockProg_295
   libsignalSessionLib
   lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym
   lsRustNoAllocShimSym lsRustReallocSym
   ls_blockPlacement_base ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.LibsignalTripleRatchet
  (noAllocShimSpec withLsCodeRoLoaded)
open CryptoVerification.RecordCodecs.Placed
  (blkPC_257 blkPl_257 instIsLsBlockProg_257)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error)
open CryptoVerification.SpqrV1.Auth (AuthMergeGhost)
open CryptoVerification.SpqrV1.ChainProofs.NextKeyInternalFacts (withLsCallInv)
open CryptoVerification.SpqrV1.Top.Recv
  (ls_subroutine_ok_cro_of_cl ls_subroutine_ok_cro_of_cro)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec)
open LibsignalBinary.Heap.SpecBudget
  (decodeErrorFromBudgetSpec decodeErrorPushBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.RecordCodecs.AssemblyBudget
  (decode_error_push_spec_placed_ok hookSat_sessionShimBudget_of_withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks
   cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_realloc_budget_sat
   cliExternsPlaced_sessionMemcpyRegion_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrVarintPlacedInst
  (subroutine_ok_callInv_of_cro)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeBaseBudget (authMergeSpecOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergeClPlacedBudget
  (auth_merge_cl_placed_ok_of_contracts auth_merge_cl_placed_ok_of_contracts_env)
open LibsignalBinary.Proofs.SpqrV1.Auth.MergePlacedBudgetAux
  (AuthPlacedMergeEnv AuthPlacedMergePostEnv authMergeSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofBudget
  (bytesMerge3ProtoRawSpec bytesMerge3RawBudgetSpec bytesMerge3RawSpec)
open LibsignalBinary.Proofs.SpqrV1.Prost.BytesMerge.ProofClPlacedBudget
  (bytes_merge_3_cl_placed_ok bytes_merge_3_proto_cl_placed_ok)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2Budget
  (decodeVarint2Spec decodeVarint2SpecX)
open LibsignalBinary.Proofs.SpqrV1.Varint.DecodeVarint2ClPlacedBudget
  (decodeVarint2_cl_placed_ok decodeVarint2_cl_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3Budget (skipField3Spec)
open LibsignalBinary.Proofs.SpqrV1.Varint.SkipField3ClPlacedBudget (skipField3_cl_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSliceBudget
  (decode_error_from_placed_ok)

/-! ## Budget-threaded hook-only contracts -/

/-- Envelope-parameterized verification of Block `295` (`Authenticator::merge`), discharging all five
cross-block callees (Blocks `257, 261, 263, 290, 291`) for arbitrary `A : RustCliAllocBudget M`. -/
theorem auth_merge_cl_placed_ok_env [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  have hshim_sess := hookSat_sessionShimBudget_of_withVmPreserved hshim
  have hFrom261 : subroutine_ok ((blkPC_261).rebase (blkPl_261).base H) (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
    rw [← ls_blockPlacement_base (i := 261)]
    exact subroutine_ok_withLsCodeLoaded_of_plain
      (decode_error_from_placed_ok hshim_sess halloc)
  have hPush257 : subroutine_ok ((blkPC_257).rebase (blkPl_257).base H) (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) := by
    rw [← ls_blockPlacement_base (i := 257)]
    exact decode_error_push_spec_placed_ok hpanic_raw hshim halloc hrealloc
  have hVarint291 : subroutine_ok ((blkPC_291).rebase (blkPl_291).base H) (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
    rw [← ls_blockPlacement_base (i := 291)]
    exact decodeVarint2_cl_placed_ok hshim_sess halloc
  have hSkip263 : subroutine_ok ((blkPC_263).rebase (blkPl_263).base H) (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
    rw [← ls_blockPlacement_base (i := 263)]
    exact skipField3_cl_placed_ok hshim_sess halloc
  have hBytes290 : subroutine_ok ((blkPC_290).rebase (blkPl_290).base H) (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawBudgetSpec A lim)) := by
    rw [← ls_blockPlacement_base (i := 290)]
    exact bytes_merge_3_cl_placed_ok hshim_sess halloc hrealloc hdealloc hmc hpanic_raw
  exact auth_merge_cl_placed_ok_of_contracts_env hPre hPost
    (ls_subroutine_ok_of_block (i := 295) (j := 261) hFrom261)
    (ls_subroutine_ok_of_block (i := 295) (j := 257) hPush257)
    (ls_subroutine_ok_of_block (i := 295) (j := 291) hVarint291)
    (ls_subroutine_ok_of_block (i := 295) (j := 263) hSkip263)
    (ls_subroutine_ok_cro_of_cro (i := 295) (j := 290) hBytes290)

/-- Verifies Block `295` (`Authenticator::merge`) against `authMergeSpec A lim` for arbitrary
`A : RustCliAllocBudget M`. -/
theorem auth_merge_cl_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (withVmPreserved noAllocShimSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmc : HookSat H lsMemcpySym sessionMemcpyRegionBudgetSpec)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_295).rebase (blkPl_295).base H)
      (blkPl_295).base
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  auth_merge_cl_placed_ok_env (fun _ _ h => h) (fun _ _ h => h)
    hshim halloc hrealloc hdealloc hmc hpanic_raw

private theorem hookSat_of_hExt {α : Type} {mmpl : Obj.MultiPlacement} {gh : CliGhostHooks}
    {W : CliHooks} {H : String → Option (State → State)} {sym : String} {spec : Spec α}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    (hne : sym ≠ "libsignal_session_rng_fill" := by decide)
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat H sym spec :=
  hookSat_of_eq (hExt sym hne) hsat

private theorem hExt_withPanics (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
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

/-! ## Own-block rebased leaf contracts under `CliGhostAllocHooks` -/

theorem cliDecodeErrorFrom_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_261).rebase (blkPl_261).base H)
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 261)]
  exact subroutine_ok_withLsCodeLoaded_of_plain
    (decode_error_from_placed_ok
      (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA)))

theorem cliDecodeErrorPush_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_257).rebase (blkPl_257).base H)
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) := by
  rw [← ls_blockPlacement_base (i := 257)]
  exact decode_error_push_spec_placed_ok
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_noAllocShim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))

theorem cliDecodeVarint2_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
  rw [← ls_blockPlacement_base (i := 291)]
  exact decodeVarint2_cl_placed_ok
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))

theorem cliDecodeVarint2X_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_291).rebase (blkPl_291).base H)
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2SpecX A lim)) := by
  rw [← ls_blockPlacement_base (i := 291)]
  exact decodeVarint2_cl_placed_ok_x
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))

theorem cliSkipField3_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_263).rebase (blkPl_263).base H)
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
  rw [← ls_blockPlacement_base (i := 263)]
  exact skipField3_cl_placed_ok
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))

theorem cliBytesMerge3_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) := by
  rw [← ls_blockPlacement_base (i := 290)]
  exact bytes_merge_3_cl_placed_ok
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide)
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))

theorem cliBytesMerge3_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A lim)) :=
  subroutine_ok_callInv_of_cro (cliBytesMerge3_cro mmpl gh W hA hExt)

theorem cliBytesMerge3Proto_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_290).rebase (blkPl_290).base H)
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3ProtoRawSpec A lim)) := by
  rw [← ls_blockPlacement_base (i := 290)]
  exact bytes_merge_3_proto_cl_placed_ok
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_shim_budget_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_realloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide) (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (hookSat_of_hExt hExt (by decide)
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
    ((hExt _ (by decide)).trans (cliGhostExterns_panic_handle_error mmpl gh W))

/-! ## Caller-block-polymorphic leaf contracts (Blocks `257, 261, 263, 290, 291`) -/

theorem cliDecodeErrorFrom_at_block_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := i) (j := 261) (cliDecodeErrorFrom_cl mmpl gh W hA hExt) hi

theorem cliDecodeErrorFrom_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 261)
      (withLsCodeRoLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := i) (j := 261) (cliDecodeErrorFrom_cl mmpl gh W hA hExt) hi

theorem cliDecodeErrorPush_at_block_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) :=
  ls_subroutine_ok_of_block (i := i) (j := 257) (cliDecodeErrorPush_cl mmpl gh W hA hExt) hi

theorem cliDecodeErrorPush_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 257)
      (withLsCodeRoLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := i) (j := 257) (cliDecodeErrorPush_cl mmpl gh W hA hExt) hi

theorem cliDecodeVarint2_at_block_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) :=
  ls_subroutine_ok_of_block (i := i) (j := 291) (cliDecodeVarint2_cl mmpl gh W hA hExt) hi

theorem cliDecodeVarint2_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 291)
      (withLsCodeRoLoaded lsmpl (decodeVarint2Spec A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := i) (j := 291) (cliDecodeVarint2_cl mmpl gh W hA hExt) hi

theorem cliSkipField3_at_block_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) :=
  ls_subroutine_ok_of_block (i := i) (j := 263) (cliSkipField3_cl mmpl gh W hA hExt) hi

theorem cliSkipField3_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 263)
      (withLsCodeRoLoaded lsmpl (skipField3Spec A lim)) :=
  ls_subroutine_ok_cro_of_cl (i := i) (j := 263) (cliSkipField3_cl mmpl gh W hA hExt) hi

theorem cliBytesMerge3_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) :=
  ls_subroutine_ok_cro_of_cro (i := i) (j := 290) (cliBytesMerge3_cro mmpl gh W hA hExt) hi

theorem cliBytesMerge3_at_block_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A lim)) :=
  subroutine_ok_callInv_of_cro (cliBytesMerge3_at_block_cro mmpl gh W hA hExt hi)

/-! ## Own-block rebased Block `295` (`Authenticator::merge`) contracts -/

theorem cliAuthMerge_cro_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_295).rebase (blkPl_295).base H)
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  rw [← ls_blockPlacement_base (i := 295)]
  exact auth_merge_cl_placed_ok_of_contracts_env hPre hPost
    (cliDecodeErrorFrom_at_block_cl mmpl gh W hA hExt)
    (cliDecodeErrorPush_at_block_cl mmpl gh W hA hExt)
    (cliDecodeVarint2_at_block_cl mmpl gh W hA hExt)
    (cliSkipField3_at_block_cl mmpl gh W hA hExt)
    (cliBytesMerge3_at_block_cro mmpl gh W hA hExt)

theorem cliAuthMerge_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_295).rebase (blkPl_295).base H)
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) := by
  rw [← ls_blockPlacement_base (i := 295)]
  exact auth_merge_cl_placed_ok_of_contracts
    (cliDecodeErrorFrom_at_block_cl mmpl gh W hA hExt)
    (cliDecodeErrorPush_at_block_cl mmpl gh W hA hExt)
    (cliDecodeVarint2_at_block_cl mmpl gh W hA hExt)
    (cliSkipField3_at_block_cl mmpl gh W hA hExt)
    (cliBytesMerge3_at_block_cro mmpl gh W hA hExt)

theorem cliAuthMerge_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      ((blkPC_295).rebase (blkPl_295).base H)
      (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A lim)) :=
  subroutine_ok_callInv_of_cro (cliAuthMerge_cro mmpl gh W hA hExt)

/-! ## Own-block `blockProgram` contracts -/

theorem cliDecodeErrorFrom_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 261 (Rust.withPanics ext))
      (lsmpl.base 261)
      (withLsCodeLoaded lsmpl (decodeErrorFromBudgetSpec M A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_261).rebase (blkPl_261).base (Rust.withPanics ext))]
  exact cliDecodeErrorFrom_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliDecodeErrorPush_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 257 (Rust.withPanics ext))
      (lsmpl.base 257)
      (withLsCodeLoaded lsmpl (decodeErrorPushBudgetSpec M A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_257).rebase (blkPl_257).base (Rust.withPanics ext))]
  exact cliDecodeErrorPush_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliDecodeVarint2_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 291 (Rust.withPanics ext))
      (lsmpl.base 291)
      (withLsCodeLoaded lsmpl (decodeVarint2Spec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_291).rebase (blkPl_291).base (Rust.withPanics ext))]
  exact cliDecodeVarint2_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliSkipField3_blockProgram_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 263 (Rust.withPanics ext))
      (lsmpl.base 263)
      (withLsCodeLoaded lsmpl (skipField3Spec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_263).rebase (blkPl_263).base (Rust.withPanics ext))]
  exact cliSkipField3_cl mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliBytesMerge3_blockProgram_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCodeRoLoaded lsmpl (bytesMerge3RawSpec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext))]
  exact cliBytesMerge3_cro mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliBytesMerge3_blockProgram_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 290 (Rust.withPanics ext))
      (lsmpl.base 290)
      (withLsCallInv lsmpl (bytesMerge3RawSpec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_290).rebase (blkPl_290).base (Rust.withPanics ext))]
  exact cliBytesMerge3_callInv mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliAuthMerge_blockProgram_cro_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_295).rebase (blkPl_295).base (Rust.withPanics ext))]
  exact cliAuthMerge_cro_env mmpl gh W hA hPre hPost (hExt_withPanics mmpl gh W hExt)

theorem cliAuthMerge_blockProgram_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_295).rebase (blkPl_295).base (Rust.withPanics ext))]
  exact cliAuthMerge_cro mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

theorem cliAuthMerge_blockProgram_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok
      (libsignalSessionLib.blockProgram lsmpl 295 (Rust.withPanics ext))
      (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A lim)) := by
  rw [← IsLsBlockProg.eq_blockProgram
    (prog := (blkPC_295).rebase (blkPl_295).base (Rust.withPanics ext))]
  exact cliAuthMerge_callInv mmpl gh W hA (hExt_withPanics mmpl gh W hExt)

/-! ## Caller-block-polymorphic Block `295` contracts -/

/-- Envelope-parameterized transfer of Block `295` (`Authenticator::merge`, `withLsCodeRoLoaded`) to any caller block `i`. -/
theorem cliAuthMerge_at_block_cro_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {PreEnv PostEnv : AuthMergeGhost → List AllocEvent → Prop}
    (hPre : ∀ x evs, AuthPlacedMergeEnv x evs → PreEnv x evs)
    (hPost : ∀ x evs, AuthPlacedMergePostEnv x evs → PostEnv x evs)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpecOfEnv A lim PreEnv PostEnv)) :=
  ls_subroutine_ok_cro_of_cro (i := i) (j := 295) (cliAuthMerge_cro_env mmpl gh W hA hPre hPost hExt) hi

/-- Transfers Block `295` (`Authenticator::merge`, `withLsCodeRoLoaded`) to any caller block `i`. -/
theorem cliAuthMerge_at_block_cro [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 295)
      (withLsCodeRoLoaded lsmpl (authMergeSpec A lim)) :=
  ls_subroutine_ok_cro_of_cro (i := i) (j := 295) (cliAuthMerge_cro mmpl gh W hA hExt) hi

/-- Transfers Block `295` (`Authenticator::merge`, `withLsCallInv`) to any caller block `i`. -/
theorem cliAuthMerge_at_block_callInv [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {callerProg : Program} {i : Nat} {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [hcaller : IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 295)
      (withLsCallInv lsmpl (authMergeSpec A lim)) :=
  subroutine_ok_callInv_of_cro (cliAuthMerge_at_block_cro mmpl gh W hA hExt hi)

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrAuthMergePlacedInstBudget
