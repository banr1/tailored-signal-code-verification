/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.IntoPbClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.ContractsPlacedBudget
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget

/-!
# Budget-Threaded Placed `PolyEncoder::into_pb`, `PolyDecoder::into_pb`, and `States::into_pb`

Code-loaded placed budget contracts under `CliGhostAllocHooks M A lim gh` for
`PolyEncoder::into_pb` (Block 375), `PolyDecoder::into_pb` (Block 377), and `States::into_pb`
(Block 334, exact `StatesIntoPbExactEnv` and envelope-parametric forms), lifted to
`spqrSendPlacedProg` (Block 427) and `spqrRecvPlacedProg` (Block 329).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkPC_375 blkPC_377 blkPl_375 blkPl_377
   libsignalSessionLib lsProg_265 ls_blockPlacement_base ls_subroutine_ok_cl_of_block
   lsmpl lsρ withLsCl withLsCodeLoaded)
open CryptoVerification.Cli.SpqrV1.Top.Send (ls_subroutine_ok_of_blockProgram_cro)
open CryptoVerification.LibsignalPublicApi.StoreKit (withLsCodeRoLoaded)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliGhostExterns hookSat_of_eq withPanics_cliGhostExterns)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_panic_handle_error lsRngFillSym trTrapExternsPlaced)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.IntoPb.Placed (blkPC_334 blkPl_334)
open CryptoVerification.SpqrV1.Top.Recv (ls_subroutine_ok_cro_of_cro spqrRecvPlacedProg)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget allocMemcpyVmSpec)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget (spqrSendPlacedProg)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_sessionMemcpyRegion_budget_sat)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrInitialStatePlacedInstBudget
  (cliDecoderIntoPb_cl_placed_ok cliDrop_265_cl cliExternsPlaced_framelessMemcpyAcp_sat
   cliExternsPlaced_rustAllocShimVm_sat)
open LibsignalBinary.Proofs.SpqrV1.Alloc.ConcatBudgetAux (framelessMemcpyAcpSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget (decoderIntoPbSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget (encoderIntoPbSpec encoderIntoPbSpecX)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.IntoPbClPlacedBudget
  (encoder_into_pb_cl_placed_ok_ext encoder_into_pb_cl_placed_ok_x)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.DefsPlacedBudget
  (StatesIntoPbAllocPlacedBudget statesIntoPbPlacedRoSpecX statesIntoPbPlacedRoSpecXOfEnv
   statesIntoPbPlacedSpecOfEnv statesIntoPbPlacedSpecXOfEnv)
open LibsignalBinary.Proofs.SpqrV1.States.IntoPb.TopClPlacedBudget
  (StatesIntoPbExactEnv StatesIntoPbPlacedOkExtOfEnv StatesIntoPbPlacedOkXOfEnv
   StatesIntoPbPlacedRoFreeOkXOfEnv statesIntoPbExactPlacedRoSpecX statesIntoPbExactPlacedSpec
   states_into_pb_cl_placed_blockProgram_ok_x_of_env
   states_into_pb_cl_placed_blockProgram_ro_cro_ok_x_of_env
   states_into_pb_cl_placed_ok_ext states_into_pb_cl_placed_ok_ext_of_env
   states_into_pb_cl_placed_ok_x states_into_pb_cl_placed_ok_x_of_env
   states_into_pb_cl_placed_ro_cro_ok_x states_into_pb_cl_placed_ro_cro_ok_x_of_env
   states_into_pb_cl_placed_ro_ok_x states_into_pb_cl_placed_ro_ok_x_of_env)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget
  (statesIntoPbPlacedOkXOfEnv_of_blockProgram)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

/-! ### Private Helpers -/

private theorem hookSat_of_hExt {α : Type}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {H : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      H sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {sym : String} (hne : sym ≠ "libsignal_session_rng_fill") {spec : Spec α}
    (hsat : HookSat (cliGhostExterns gh (cliExternsPlaced mmpl W)) sym spec) :
    HookSat H sym spec :=
  hookSat_of_eq (hExt sym hne) hsat

private theorem hExt_withPanics
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

private theorem hookSat_allocMemcpyVm_of_framelessAcp {hooks : String → Option (State → State)}
    {name : String}
    (h : HookSat hooks name framelessMemcpyAcpSpec) :
    HookSat hooks name allocMemcpyVmSpec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [allocMemcpyVmSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2_bv, hlt⟩, hm⟩
  have hx2 : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2_bv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hpre' : s0.mem ⊨ framelessMemcpyAcpSpec.pre (dst, src, bs) s0 ∗ R := by
    dsimp only [framelessMemcpyAcpSpec]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  rcases hsat (dst, src, bs) R s0 hrun hpre' hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [allocMemcpyVmSpec, framelessMemcpyAcpSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr hrest

private theorem lift_265_cl [LibsignalPlacement]
    {callerProg : Program} {i : Nat}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 265)
      (withLsCodeLoaded lsmpl (dropGluePoly16Spec M A lim)) := by
  let _ : IsLsBlockProg
      (libsignalSessionLib.blockProgram lsmpl 265 (Rust.withPanics ext))
      265 (Rust.withPanics ext) :=
    ⟨rfl, (inferInstance : IsLsBlockProg (lsProg_265 (Rust.withPanics ext))
      265 (Rust.withPanics ext)).externs_eq⟩
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (cliDrop_265_cl mmpl gh W hA hExt) hi (by decide) (by decide))

/-! ### 1. Block `375` (`PolyEncoder::into_pb`) and Block `377` (`PolyDecoder::into_pb`) -/

/-- Block `375` (`<PolyEncoder>::into_pb`) on `(blkPC_375).rebase` with `withLsCodeLoaded`. -/
theorem cliEncoderIntoPb_375_rebase_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_375).rebase (blkPl_375).base (Rust.withPanics ext))
      (blkPl_375).base (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)) :=
  encoder_into_pb_cl_placed_ok_ext
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (lift_265_cl (i := 375) mmpl gh W hA hExt)

/-- Own-block code-loaded Block `375` (`<PolyEncoder>::into_pb`). -/
theorem cliEncoderIntoPb_375_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 375 (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)) :=
  rebase_to_blockProgram (j := 375) (cliEncoderIntoPb_375_rebase_cl mmpl gh W hA hExt)

/-- Extended-stack variant (`encoderIntoPbSpecX`) of own-block code-loaded Block `375`. -/
theorem cliEncoderIntoPb_375_cl_x [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 375 (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpecX M A lim)) :=
  rebase_to_blockProgram (j := 375)
    (encoder_into_pb_cl_placed_ok_x
      (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
        (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
      (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
        (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
      (lift_265_cl (i := 375) mmpl gh W hA hExt))

/-- Block `377` (`<PolyDecoder>::into_pb`) on `(blkPC_377).rebase` with `withLsCodeLoaded`. -/
theorem cliDecoderIntoPb_377_rebase_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_377).rebase (blkPl_377).base (Rust.withPanics ext))
      (blkPl_377).base (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)) :=
  cliDecoderIntoPb_cl_placed_ok mmpl gh W hA hExt

/-- Own-block code-loaded Block `377` (`<PolyDecoder>::into_pb`). -/
theorem cliDecoderIntoPb_377_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 377 (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)) :=
  rebase_to_blockProgram (j := 377) (cliDecoderIntoPb_377_rebase_cl mmpl gh W hA hExt)

private theorem lift_375_to_334 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 375) (withLsCodeLoaded lsmpl (encoderIntoPbSpec M A lim)) := by
  have h := cliEncoderIntoPb_375_rebase_cl mmpl gh W hA hExt
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 375)]
  exact withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (i := 334) (j := 375) h)

private theorem lift_377_to_334 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsmpl.base 377) (withLsCodeLoaded lsmpl (decoderIntoPbSpec M A lim)) :=
  withLsCodeLoaded_of_withLsCl
    (ls_subroutine_ok_cl_of_block (i := 334) (j := 377)
      (cliDecoderIntoPb_cl_placed_ok mmpl gh W hA hExt))

/-! ### 2. Block `334` (`States::into_pb`, All 11 Arms) -/

/-- `StatesIntoPbAllocPlacedBudget M A lim ext` discharged from `hExt` + `CliGhostAllocHooks`. -/
theorem cliStatesIntoPbAllocPlaced [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesIntoPbAllocPlacedBudget M A lim ext where
  shim_ok := spqr_hook_ok_of_mem
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_rustAllocShimVm_sat mmpl gh W hA.shim_eq))
    (by decide) (by decide) (by decide)
  alloc_ok := spqr_hook_ok_of_mem
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_alloc_budget_sat mmpl gh W hA))
    (by decide) (by decide) (by decide)
  dealloc_ok := spqr_hook_ok_of_mem
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_dealloc_budget_sat mmpl gh W hA))
    (by decide) (by decide) (by decide)
  memcpy_ok := spqr_hook_ok_of_mem
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (hookSat_allocMemcpyVm_of_framelessAcp
        (cliExternsPlaced_framelessMemcpyAcp_sat mmpl gh W hA)))
    (by decide) (by decide) (by decide)
  panic_ok :=
    (hExt_withPanics mmpl gh W hExt _ (by decide)).trans
      (cliGhostExterns_panic_handle_error mmpl gh W)

/-- `sessionMemcpyRegionBudgetSpec` on `memcpy` inside Block `334`. -/
theorem cliSessionMemcpyRegion_at_334 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok ((blkPC_334).rebase (blkPl_334).base (Rust.withPanics ext))
      (lsρ "memcpy") sessionMemcpyRegionBudgetSpec :=
  spqr_hook_ok_of_mem
    (hookSat_of_hExt mmpl gh W (hExt_withPanics mmpl gh W hExt) (by decide)
      (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl gh W hA))
    (by decide) (by decide) (by decide)

/-- Envelope-parametric `StatesIntoPbPlacedOkExtOfEnv` on `(blkPC_334).rebase`. -/
theorem cliStatesIntoPb_334_placed_ok_ext_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedOkExtOfEnv M A lim W.C.F Env ext :=
  states_into_pb_cl_placed_ok_ext_of_env
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)
    hEnv

/-- Exact-envelope `StatesIntoPbPlacedOkExtOfEnv` (`StatesIntoPbExactEnv`) on `(blkPC_334).rebase`. -/
theorem cliStatesIntoPb_334_placed_ok_ext [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesIntoPbPlacedOkExtOfEnv M A lim W.C.F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ok_ext
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)

/-- Own-block code-loaded Block `334` (`statesIntoPbExactPlacedSpec`). -/
theorem cliStatesIntoPb_334_cl [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeLoaded lsmpl (statesIntoPbExactPlacedSpec M A lim W.C.F)) :=
  rebase_to_blockProgram (j := 334) (cliStatesIntoPb_334_placed_ok_ext mmpl gh W hA hExt)

/-- Envelope-parametric `withLsCodeLoaded` extended-stack contract on `blockProgram lsmpl 334`. -/
theorem cliStatesIntoPb_334_ro_cl_x_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedOkXOfEnv M A lim W.C.F Env ext :=
  states_into_pb_cl_placed_blockProgram_ok_x_of_env
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)
    hEnv

/-- Exact-envelope `withLsCodeLoaded` extended-stack contract on `blockProgram lsmpl 334`. -/
theorem cliStatesIntoPb_334_ro_cl_x [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesIntoPbPlacedOkXOfEnv M A lim W.C.F StatesIntoPbExactEnv ext :=
  cliStatesIntoPb_334_ro_cl_x_of_env mmpl gh W hA hExt (fun _ _ h => h)

/-! ### 3. Cross-Block Lifts for `spqr::send::<Coins>` (`427`) and `spqr::recv` (`329`) -/

/-- `.rodata`-free extended-stack contract (`StatesIntoPbPlacedRoFreeOkXOfEnv`) on `(blkPC_334).rebase`. -/
theorem cliStatesIntoPb_334_placed_ok_x_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim W.C.F Env ext :=
  states_into_pb_cl_placed_ok_x_of_env
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)
    hEnv

/-- Tight `StatesIntoPbExactEnv` `.rodata`-free extended-stack contract on `(blkPC_334).rebase`. -/
theorem cliStatesIntoPb_334_placed_ok_x [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    StatesIntoPbPlacedRoFreeOkXOfEnv M A lim W.C.F StatesIntoPbExactEnv ext :=
  states_into_pb_cl_placed_ok_x
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)

/-- Envelope-parametric `withLsCodeRoLoaded` contract on `blockProgram lsmpl 334`. -/
theorem cliStatesIntoPb_334_ro_cro_ok_x_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim W.C.F Env)) :=
  states_into_pb_cl_placed_blockProgram_ro_cro_ok_x_of_env
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)
    hEnv

/-- Tight `StatesIntoPbExactEnv` `withLsCodeRoLoaded` contract on `blockProgram lsmpl 334`. -/
theorem cliStatesIntoPb_334_ro_cro_ok_x [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (libsignalSessionLib.blockProgram lsmpl 334 (Rust.withPanics ext))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (statesIntoPbPlacedSpecXOfEnv M A lim W.C.F StatesIntoPbExactEnv)) :=
  cliStatesIntoPb_334_ro_cro_ok_x_of_env mmpl gh W hA hExt (fun _ _ h => h)

/-- Envelope-parametric `statesIntoPb_ok` contract on `spqrSendPlacedProg ext` (`Block 427`). -/
theorem cliStatesIntoPb_sendCoins_ok_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    subroutine_ok (spqrSendPlacedProg ext)
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl (statesIntoPbPlacedSpecXOfEnv M A lim W.C.F Env)) :=
  ls_subroutine_ok_of_blockProgram_cro
    (cliStatesIntoPb_334_ro_cro_ok_x_of_env mmpl gh W hA hExt hEnv)

/-- Tight `StatesIntoPbExactEnv` `statesIntoPb_ok` contract on
    `spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W))`
    matching `SpqrSendPlacedContractsOfEnv.statesIntoPb_ok`. -/
theorem cliStatesIntoPb_sendCoins_exact_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok (spqrSendPlacedProg (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (statesIntoPbPlacedSpecXOfEnv M A lim W.C.F StatesIntoPbExactEnv)) :=
  cliStatesIntoPb_sendCoins_ok_of_env mmpl gh W hA
    (ext := cliGhostExterns gh (cliExternsPlaced mmpl W)) (fun _ _ => rfl) (fun _ _ h => h)

/-- Envelope-parametric `SpqrV1.Top.Recv.ContractsPlacedBudget.StatesIntoPbPlacedOkXOfEnv` for Block `329`. -/
theorem cliStatesIntoPb_recv_okX_of_env [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym)
    {Env : StatesIntoPbGhost W.C.F → List AllocEvent → Prop}
    (hEnv : ∀ x evs, StatesIntoPbExactEnv x evs → Env x evs) :
    LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget.StatesIntoPbPlacedOkXOfEnv
      M A lim W.C.F Env ext :=
  statesIntoPbPlacedOkXOfEnv_of_blockProgram
    (cliStatesIntoPb_334_ro_cl_x_of_env mmpl gh W hA hExt hEnv)

/-- Tight `StatesIntoPbExactEnv` `StatesIntoPbPlacedOkXOfEnv` for `spqr::recv` (`Block 329`),
    generic in `hExt`. -/
theorem cliStatesIntoPb_recv_exact_okX [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    LibsignalBinary.Proofs.SpqrV1.Top.Recv.ContractsPlacedBudget.StatesIntoPbPlacedOkXOfEnv
      M A lim W.C.F StatesIntoPbExactEnv ext :=
  cliStatesIntoPb_recv_okX_of_env mmpl gh W hA hExt (fun _ _ h => h)

/-- Tight `StatesIntoPbExactEnv` `statesIntoPb_ok` contract on `spqrRecvPlacedProg ext` (`Block 329`). -/
theorem cliStatesIntoPb_recv_exact_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh)
    {ext : String → Option (State → State)}
    (hExt : ∀ sym : String, sym ≠ "libsignal_session_rng_fill" →
      ext sym = cliGhostExterns gh (cliExternsPlaced mmpl W) sym) :
    subroutine_ok (spqrRecvPlacedProg ext)
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv
          M A lim W.C.F StatesIntoPbExactEnv)) := by
  have h := states_into_pb_cl_placed_ro_cro_ok_x (F := W.C.F)
    (cliStatesIntoPbAllocPlaced mmpl gh W hA hExt)
    (lift_375_to_334 mmpl gh W hA hExt)
    (lift_377_to_334 mmpl gh W hA hExt)
    (cliSessionMemcpyRegion_at_334 mmpl gh W hA hExt)
  conv at h => arg 2; rw [ls_blockPlacement_base (i := 334)]
  exact ls_subroutine_ok_cro_of_cro (i := 329) (j := 334) h

/-- Tight `StatesIntoPbExactEnv` `statesIntoPb_ok` contract on
    `spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))`. -/
theorem cliStatesIntoPb_recv_trTrap_exact_ok [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hA : CliGhostAllocHooks M A lim gh) :
    subroutine_ok
      (spqrRecvPlacedProg (trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W))))
      (lsmpl.base 334)
      (withLsCodeRoLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget.statesIntoPbPlacedSpecXOfEnv
          M A lim W.C.F StatesIntoPbExactEnv)) :=
  cliStatesIntoPb_recv_exact_ok mmpl gh W hA
    (ext := trTrapExternsPlaced (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (fun sym hne => by
      have hbeq : (sym == lsRngFillSym) = false := beq_false_of_ne hne
      simp [trTrapExternsPlaced, ProofLib.Variant.trapAt, hbeq])

end LibsignalBinary.Proofs.SignalSession.Cli.SpqrStatesIntoPbPlacedInstBudget
