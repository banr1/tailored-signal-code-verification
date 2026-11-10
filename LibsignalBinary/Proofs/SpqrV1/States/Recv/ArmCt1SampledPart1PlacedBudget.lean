/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 1 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` shared direct epilogue (`+19324 -> s0.x30`), prologue,
jump-table dispatch, epoch comparison at `+1528`, and `FreeOnlyEvs` Path 1 (`Error::EpochOutOfRange`).
-/

@[expose] public section

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget

open Std
open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 lsProg_332 lsmpl lsρ
  sepWP_seq_lscl withMemEq
)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (
  NUM_POLYS PolyDecoder PolyEncoder spqrAuthApi spqrPolyApi
)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled)
open CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt (Ct1Sent)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (
  chunkedCt1SampledAt chunkedStatesAt chunkedStatesSize chunked_400_join dropGluePoly16Stack
  fiveVec400HeadersAt fiveVec400HeadersAt_entails_memRegion_128 polyDecoderAt_entails_vecs_tail
  polyEncoderAt_entails_tag_vecs_tail unchunkedCt1SentAt vecCapPtrDealloc vecPtListOf
)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes polyDecoderAt polyEncoderAt)
open CryptoVerification.SpqrV1.States.Recv (
  StatesRecvGhost TraceCalleeSaved ValidStatesTag ct1Sampled_join_928 epoch_cmp_b_eq_of_eq
  epoch_cmp_b_eq_of_gt epoch_cmp_b_eq_of_lt epoch_cmp_b_ne_of_gt epoch_cmp_b_ne_of_lt
  err_epochOutOfRange_entails_resultV1RecvAt memRegion_out_960_split_err resultV1RecvAt
  sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_3272 sp_sub_4240_add_3856
  sp_sub_4240_add_4096 sp_sub_4240_add_4144 sp_sub_4240_add_48 sp_sub_96_add_16
  sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_4096
  spqrDeallocSym stackAt_statesRecvCallee_eq_allocHook' stackAt_statesRecvCallee_eq_dropGluePoly16'
  stackAt_statesRecvCallee_from_allocHook stackAt_statesRecvCallee_from_dropGluePoly16
  statesRecvCalleeStackX statesRecvRoPlacedAt statesRecvSavedCells statesRecvStackX
  unchunkedCt1Sent400_entails_dealloc v1RecvSize
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
  VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Drop.PolyBudget (dropGluePoly16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_cont
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget (StatesRecvEnv)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget (drop_glue_poly16_mem_on)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux (
  align_pre_st align_pre_vm deallocFreeOnlySpec sepWP_evs_dealloc sepWP_evs_nil sepWP_vm_evs_nil
  seq_evs_step seq_evs_step_lscl subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

local elab "by_vm_steps_nest " tac:Lean.Parser.Tactic.tacticSeq : tactic => do
  Lean.Elab.Tactic.evalTactic
    (← `(tactic| apply LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved))
  let g ← Lean.Elab.Tactic.getMainGoal
  g.withContext do
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
    let e2 := ty.getArg! 0
    let e1 := e2.getArg! 0
    let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
    let g1 ← Lean.Meta.mkFreshExprMVar ty1
    let savedGoals ← Lean.Elab.Tactic.getGoals
    Lean.Elab.Tactic.setGoals [g1.mvarId!]
    Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
    let rem ← Lean.Elab.Tactic.getGoals
    unless rem.isEmpty do
      Lean.Meta.throwTacticEx `by_vm_steps_nest g m!"inner tactic left {rem.length} unsolved goal(s)"
    Lean.Elab.Tactic.setGoals savedGoals.tail!
    let prf1 ← Lean.instantiateMVars g1
    let prf2 := prf1.replace fun sub =>
      if sub.isAppOfArity ``Arm64.Program.withSvc 2 then some sub
      else if sub.eqv e1 then some e2
      else none
    g.assign prf2

private theorem acpOfVm {s sm : State} (_ : VmPreserved s sm) (h : AllocCallPreserved s sm) :
    AllocCallPreserved s sm := h

/-! ## Envelope Lift for `FreeOnlyEvs` -/

theorem FreeOnlyEvs_to_statesRecvEnv [LibsignalPlacement] {F : ShaCompress}
    (x : StatesRecvGhost F) {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    StatesRecvEnv x evs :=
  SpqrBoundedEvs.mono (Nat.zero_le _) (Nat.zero_le _) (SpqrBoundedEvs.of_freeOnly h)

/-! ## 1. Shared Direct Epilogue (`+19324 -> s0.x30`), Prologue, & Dispatch -/

theorem ct1Sampled_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

theorem ct1Sampled_seq_vm_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  sepWP_seq_lscl hcl (SepWP.mono h1 fun sm _Pm hpc hrun ⟨hvm, hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hvm hQ))

theorem ct1Sampled_epilogue_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  DispatchPlacedBudget.states_recv_epilogue_19324_placed s0 s1 Rest hsp0_align
    (by rwa [lsmpl_base_332_eq]) hrun1 hsp1 htr1

theorem ct1Sampled_epilogue_19324_acp_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s1 sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  DispatchPlacedBudget.states_recv_epilogue_19324_acp_placed s0 s1 Rest hsp0_align
    (by rwa [lsmpl_base_332_eq]) hrun1 hsp1 htr1

theorem ct1Sampled_epilogue_19324_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = (blkPl_332).base + 19324#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (htr1 : TraceCalleeSaved s1 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s1 sf ∧
        (Pf ⊢ A.pool lim st_cost sf ∗ Rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s1 sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  DispatchPlacedBudget.states_recv_epilogue_19324_pool_placed st_cost s0 s1 Rest hsp0_align
    (by rwa [lsmpl_base_332_eq]) hrun1 hsp1 htr1

theorem ct1Sampled_prologue_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = lsmpl.base 332)
    (hrun0 : s0.status = .Running) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) :=
  DispatchPlacedBudget.states_recv_prologue_placed s0 Rest hsp0_align hpc0 hrun0

theorem ct1Sampled_prologue_acp_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = lsmpl.base 332)
    (hrun0 : s0.status = .Running) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          Rest) ∧
        AllocCallPreserved s0 s1 ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) :=
  DispatchPlacedBudget.states_recv_prologue_acp_placed s0 Rest hsp0_align hpc0 hrun0

theorem ct1Sampled_prologue_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s0 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc0 : s0.pc = lsmpl.base 332)
    (hrun0 : s0.status = .Running) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 36#64)
      s0
      (stackAt s0.sp statesRecvStackX ∗ A.pool lim st_cost s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 ∗
          A.pool lim st_cost s1 ∗
          Rest) ∧
        AllocCallPreserved s0 s1 ∧
        s1.sp = s0.sp - 4240#64 ∧
        s1.readReg64 .x0 = s0.readReg64 .x0 ∧
        s1.readReg64 .x1 = s0.readReg64 .x1 ∧
        s1.readReg64 .x2 = s0.readReg64 .x2 ∧
        s1.readReg64 .x3 = s0.readReg64 .x3 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        TraceCalleeSaved s1 s0) :=
  DispatchPlacedBudget.states_recv_prologue_pool_placed st_cost s0 Rest hsp0_align hpc0 hrun0

theorem ct1Sampled_dispatch_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 1528#64)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest)
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) := by
  rcases htag with rfl | rfl
  · exact DispatchPlacedBudget.states_recv_dispatch_placed s1 fsp st_ptr 0#64 Rest
      (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  · exact DispatchPlacedBudget.states_recv_dispatch_placed s1 fsp st_ptr 1#64 Rest
      (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1

theorem ct1Sampled_dispatch_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : tag = 0#64 ∨ tag = 1#64)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 1528#64)
      s1
      ((st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s1 ∗ Rest)
      (fun s2 P2 =>
        VmPreserved s1 s2 ∧
        (P2 ⊢ (st_ptr ↦₆₄ tag) ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗ Rest) ∧
        s2.sp = fsp ∧
        s2.readReg64 .x0 = s1.readReg64 .x0 ∧
        s2.readReg64 .x1 = st_ptr ∧
        s2.readReg64 .x2 = s1.readReg64 .x2 ∧
        s2.readReg64 .x3 = s1.readReg64 .x3 ∧
        s2.readReg64 .x8 = 7#64 ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) :=
  SepWP.mono
    (ct1Sampled_dispatch_placed s1 fsp st_ptr tag (A.pool lim st_cost s1 ∗ Rest)
      htag hpc1 hrun1 hsp1 hx1_1)
    fun s2 _ _ _ ⟨hvm, hP2, hq⟩ =>
      ⟨hvm, Entails.trans hP2 (Entails.of_eq (by rw [A.pool_of_vmPreserved hvm]; try sep_ac_rfl)), hq⟩

/-! ## 2. Epoch Comparison at `+1528` (`0x55a4c..0x55a70`) -/

theorem ct1Sampled_epoch_cmp_gt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hgt : msg_ep.toNat > st_ep.toNat)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 1564#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_gt hgt
  have hcond2 := epoch_cmp_b_ne_of_gt hgt
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_epoch_cmp_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA st_ep msg_ep : BitVec 64) (Rest : SepProp)
    (hlt : msg_ep.toNat < st_ep.toNat)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 10500#64)
      s2
      (((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest)
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ st_ep) ∗ (msgA ↦₆₄ msg_ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = msg_ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_lt hlt
  have hcond2 := epoch_cmp_b_ne_of_lt hlt
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  by_vm_steps (wp_steps; wp_done)

theorem ct1Sampled_epoch_cmp_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s2 : State) (selfA msgA ep : BitVec 64) (Rest : SepProp)
    (hpc2 : s2.pc = (blkPl_332).base + 1528#64)
    (hrun2 : s2.status = .Running)
    (hx1 : s2.readReg64 .x1 = selfA)
    (hx24 : s2.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 7052#64)
      s2
      (((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest)
      (fun s3 P3 =>
        VmPreserved s2 s3 ∧
        (P3 ⊢ ((selfA + 520#64) ↦₆₄ ep) ∗ (msgA ↦₆₄ ep) ∗ Rest) ∧
        s3.sp = s2.sp ∧
        s3.readReg64 .x0 = s2.readReg64 .x0 ∧
        s3.readReg64 .x1 = selfA ∧
        s3.readReg64 .x2 = s2.readReg64 .x2 ∧
        s3.readReg64 .x3 = s2.readReg64 .x3 ∧
        s3.readReg64 .x12 = s2.readReg64 .x12 ∧
        s3.readReg64 .x19 = s2.readReg64 .x19 ∧
        s3.readReg64 .x20 = ep ∧
        s3.readReg64 .x21 = s2.readReg64 .x21 ∧
        s3.readReg64 .x24 = msgA ∧
        s3.readReg64 .x28 = s2.readReg64 .x28 ∧
        s3.readReg64 .x29 = s2.readReg64 .x29 ∧
        TraceCalleeSaved s3 s2) := by
  subst hx1 hx24
  have hcond1 := epoch_cmp_b_eq_of_eq ep
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc2 ⊢
  by_vm_steps (wp_steps; wp_done)

/-! ## 3. Path 1: `msg.epoch > st.uc.epoch` (`Error::EpochOutOfRange`, `+1564 -> s0.x30`) -/

set_option maxHeartbeats 800000 in
theorem ct1Sampled_write_err_and_dealloc5_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s3 : State) (fsp outA selfA msg_ep : BitVec 64)
    (uc : Ct1Sent (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (blkPl_332).base + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 1744#64)
      s3
      (memRegion outA v1RecvSize ∗
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) uc ∗
        A.pool lim st_cost s3 ∗
        stackAt fsp allocHookStack ∗
        Rest)
      (fun s8 P8 =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P8 ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion (selfA + 400#64) 128 ∗
            A.pool lim (M.stepEvents evs st_cost) s8 ∗
            stackAt fsp allocHookStack ∗
            Rest) ∧
          s8.sp = fsp ∧
          AllocCallPreserved s3 s8 ∧
          s8.readReg64 .x1 = selfA ∧
          TraceCalleeSaved s8 s3) := by
  have hdealloc_fo : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc)
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, BitVec.ofNat_eq_ofNat] at hpc3 hdealloc_fo ⊢
  refine SepWP.mono
    (post := fun s8 P8 =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (P8 ⊢
          (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion (selfA + 400#64) 128) ∗
          A.pool lim (M.stepEvents evs st_cost) s8 ∗
          (stackAt fsp allocHookStack ∗ Rest)) ∧
        (s8.sp = fsp ∧ AllocCallPreserved s3 s8 ∧
          s8.readReg64 .x1 = selfA ∧ TraceCalleeSaved s8 s3))
    ?_
    (fun _ _ _ _ ⟨evs, hevs, hP8, hq⟩ =>
      ⟨evs, hevs, Entails.trans hP8 (Entails.of_eq (by sep_ac_rfl)), hq⟩)
  wp_conv_pre =>
    rw [memRegion_out_960_split_err outA]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro v16_out
  apply ProofLib.SepWP.exists_left; intro b8_out
  apply ProofLib.SepWP.exists_left; intro v0_out
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        unchunkedCt1SentAt A.repAlloc (selfA + 400#64) uc ∗
        ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
         memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
         A.pool lim st_cost s3 ∗ stackAt fsp allocHookStack ∗ Rest) by sep_ac_rfl))
      (sepConj_mono_left (unchunkedCt1Sent400_entails_dealloc A.repAlloc selfA uc))) ?_
  rw [sepExists_sepConj_left]
  apply ProofLib.SepWP.exists_left; intro g
  refine seq_evs_step (mid := (blkPl_332).base + 1616#64)
    (P_mid := fun st1 sm =>
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
        (fiveVec400HeadersAt selfA g ∗
         vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
         vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
      A.pool lim st1 sm ∗ (stackAt fsp allocHookStack ∗ Rest))
    (Q_mid := fun sm =>
      sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧
      sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
    ?_ ?_
  · have hstep1 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
        ((blkPl_332).base + 1616#64) s3
        ((fiveVec400HeadersAt selfA g ∗
          vecCapPtrDealloc A.repAlloc g.v1.cap g.v1.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
          vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr) ∗
         ((outA ↦₆₄ v0_out) ∗ ((outA + 8#64) ↦₈ b8_out) ∗ ((outA + 16#64) ↦₆₄ v16_out) ∗
          memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗
          A.pool lim st_cost s3 ∗ stackAt fsp allocHookStack ∗ Rest))
        (fun sm Pm =>
          ∃ evs1, FreeOnlyEvs evs1 ∧
            (Pm ⊢ (((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_ep) ∗
              memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936) ∗
              (fiveVec400HeadersAt selfA g ∗
               vecCapPtrDealloc A.repAlloc g.v2.cap g.v2.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
              A.pool lim (M.stepEvents evs1 st_cost) sm ∗ (stackAt fsp allocHookStack ∗ Rest)) ∧
            (sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧
              sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)) := by
      dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live, noneCap]
      by_cases hc1 : (g.v1.cap == 0#64) = true <;>
        simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · refine sepWP_vm_evs_nil (fun sm hvm => by
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, A.pool_of_vmPreserved hvm]) ?_
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by
            simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil, wp_norm, arm64_norm]
            try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, TraceCalleeSaved, hsp3, hx1, hx19, hx20, wp_norm, arm64_norm]
          wp_done)
      · apply sepWP_evs_dealloc g.v1.cap.toNat 1
        refine seq_vm_cont (mid := lsmpl.ρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") ?_
        by_vm_steps_nest (
          wp_steps
          refine SepWP.done rfl (by assumption) ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
          wp_conv_pre => rw [← A.pool_of_vmPreserved hvm1]
          wp_apply
          have hacp_1 : AllocCallPreserved s3 sf := by assumption
          rcases hacp_1 with ⟨_, _, _, _, _, _, _⟩
          wp_steps
          refine align_pre_st (by rw [hsp3]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done)
    exact SepWP.mono hstep1 fun _ _ _ _ ⟨evs1, hevs1, hPm, hq⟩ =>
      ⟨evs1, hevs1, Entails.trans hPm
        (sepConj_mono_left (sepConj_mono_left
          (err_epochOutOfRange_entails_resultV1RecvAt A.repAlloc (F := F) outA msg_ep))), hq⟩
  · intro st1 s4 hpc4 hrun4 ⟨hsp4, hacp4, hx1_4, htr4⟩
    have ⟨_, _, _, _, _, _, _⟩ := hacp4
    refine seq_evs_step (mid := (blkPl_332).base + 1648#64)
      (P_mid := fun st2 sm =>
        (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
          (fiveVec400HeadersAt selfA g ∗
           vecCapPtrDealloc A.repAlloc g.v3.cap g.v3.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
           vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
        A.pool lim st2 sm ∗ (stackAt fsp allocHookStack ∗ Rest))
      (Q_mid := fun sm =>
        sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧
        sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
      ?_ ?_
    · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc,
        LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
      by_cases hc2 : (g.v2.cap == 0#64) = true <;>
        simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
      · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
        wp_steps
        refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done
      · apply sepWP_evs_dealloc g.v2.cap.toNat 1
        wp_steps; wp_apply
        have hacp' : AllocCallPreserved s3 sf := hacp4.trans (by assumption)
        rcases hacp' with ⟨_, _, _, _, _, _, _⟩
        wp_steps
        refine align_pre_st (by rw [hsp4]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
        wp_done
    · intro st2 s5 hpc5 hrun5 ⟨hsp5, hacp5, hx1_5, htr5⟩
      have ⟨_, _, _, _, _, _, _⟩ := hacp5
      refine seq_evs_step (mid := (blkPl_332).base + 1680#64)
        (P_mid := fun st3 sm =>
          (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            (fiveVec400HeadersAt selfA g ∗
             vecCapPtrDealloc A.repAlloc g.v4.cap g.v4.ptr ∗
             vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
          A.pool lim st3 sm ∗ (stackAt fsp allocHookStack ∗ Rest))
        (Q_mid := fun sm =>
          sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧
          sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
        ?_ ?_
      · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc,
          LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
        by_cases hc3 : (g.v3.cap == 0#64) = true <;>
          simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
        · apply sepWP_evs_dealloc g.v3.cap.toNat 1
          wp_steps; wp_apply
          have hacp' : AllocCallPreserved s3 sf := hacp5.trans (by assumption)
          rcases hacp' with ⟨_, _, _, _, _, _, _⟩
          wp_steps
          refine align_pre_st (by rw [hsp5]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          wp_done
      · intro st3 s6 hpc6 hrun6 ⟨hsp6, hacp6, hx1_6, htr6⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacp6
        refine seq_evs_step (mid := (blkPl_332).base + 1712#64)
          (P_mid := fun st4 sm =>
            (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
              (fiveVec400HeadersAt selfA g ∗
               vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
            A.pool lim st4 sm ∗ (stackAt fsp allocHookStack ∗ Rest))
          (Q_mid := fun sm =>
            sm.sp = fsp ∧ AllocCallPreserved s3 sm ∧
            sm.readReg64 .x1 = selfA ∧ TraceCalleeSaved sm s3)
          ?_ ?_
        · dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc,
            LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          by_cases hc4 : (g.v4.cap == 0#64) = true <;>
            simp only [hc4, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
          · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
            wp_steps
            refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
          · apply sepWP_evs_dealloc g.v4.cap.toNat 1
            wp_steps; wp_apply
            have hacp' : AllocCallPreserved s3 sf := hacp6.trans (by assumption)
            rcases hacp' with ⟨_, _, _, _, _, _, _⟩
            wp_steps
            refine align_pre_st (by rw [hsp6]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
            wp_done
        · intro st4 s7 hpc7 hrun7 ⟨hsp7, hacp7, hx1_7, htr7⟩
          have ⟨_, _, _, _, _, _, _⟩ := hacp7
          have hstep5 : SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
              ((blkPl_332).base + 1744#64) s7
              ((resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                (fiveVec400HeadersAt selfA g ∗
                 vecCapPtrDealloc A.repAlloc g.v5.cap g.v5.ptr)) ∗
                A.pool lim st4 s7 ∗ (stackAt fsp allocHookStack ∗ Rest))
              (fun s8 P8 =>
                ∃ evs5, FreeOnlyEvs evs5 ∧
                  (P8 ⊢ (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
                    fiveVec400HeadersAt selfA g) ∗
                    A.pool lim (M.stepEvents evs5 st4) s8 ∗ (stackAt fsp allocHookStack ∗ Rest)) ∧
                  (s8.sp = fsp ∧ AllocCallPreserved s3 s8 ∧
                    s8.readReg64 .x1 = selfA ∧ TraceCalleeSaved s8 s3)) := by
            dsimp only [fiveVec400HeadersAt, vecCapPtrDealloc,
              LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
            by_cases hc5 : (g.v5.cap == 0#64) = true <;>
              simp only [hc5, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
            · apply sepWP_evs_nil; simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
              wp_steps
              refine align_pre_st (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
            · apply sepWP_evs_dealloc g.v5.cap.toNat 1
              wp_steps; wp_apply
              have hacp' : AllocCallPreserved s3 sf := hacp7.trans (by assumption)
              rcases hacp' with ⟨_, _, _, _, _, _, _⟩
              wp_steps
              refine align_pre_st (by rw [hsp7]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
              wp_done
          exact SepWP.mono hstep5 fun _ _ _ _ ⟨evs5, hevs5, hP8, hq⟩ =>
            ⟨evs5, hevs5, Entails.trans hP8
              (sepConj_mono_left (sepConj_mono_right
                (fiveVec400HeadersAt_entails_memRegion_128 selfA g))), hq⟩

theorem ct1Sampled_drop_encoders_epilogue_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s8 : State) (selfA : BitVec 64)
    (enc : PolyEncoder) (dec : PolyDecoder)
    (Rest : SepProp)
    (hcl8 : LibsignalCodeLoaded lsmpl s8.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc8 : s8.pc = (blkPl_332).base + 1744#64)
    (hrun8 : s8.status = .Running)
    (hsp8 : s8.sp = s0.sp - 4240#64)
    (hx1_8 : s8.readReg64 .x1 = selfA)
    (htr8 : TraceCalleeSaved s8 s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s8
      (polyEncoderAt A.repAlloc selfA enc ∗
        memRegion (selfA + 400#64) 128 ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) dec ∗
        A.pool lim st_cost s8 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s8 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  refine SepWP.mono
    (post := fun sf Pf =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (Pf ⊢
          memRegion selfA chunkedStatesSize ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          (stackAt s0.sp statesRecvStackX ∗ Rest)) ∧
        (sf.sp = s0.sp ∧ AllocCallPreserved s8 sf ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
    ?_
    (fun _ _ _ _ ⟨evs, hevs, hPf, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hq⟩)
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        polyEncoderAt A.repAlloc selfA enc ∗
        polyDecoderAt A.repAlloc (selfA + 528#64) dec ∗
        (memRegion (selfA + 400#64) 128 ∗
         A.pool lim st_cost s8 ∗
         stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         Rest) by sep_ac_rfl))
      (sepConj_mono (polyEncoderAt_entails_tag_vecs_tail A.repAlloc selfA enc)
        (sepConj_mono_left (polyDecoderAt_entails_vecs_tail A.repAlloc (selfA + 528#64) dec)))) ?_
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_dropGluePoly16' (s0.sp - 4240#64)]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro dec_vecs
  apply ProofLib.SepWP.exists_left; intro enc_tag
  apply ProofLib.SepWP.exists_left; intro enc_vecs
  wp_focus_pure; intro henc_len
  wp_focus_pure; intro hdec_len
  subst hx1_8
  have h912 : (s8.readReg64 .x1 + 528#64) + 384#64 = s8.readReg64 .x1 + 912#64 := by bv_omega
  refine seq_evs_step_lscl hcl8 (mid := (blkPl_332).base + 1760#64)
    (P_mid := fun st1 s9 =>
      memRegion (s8.readReg64 .x1 + 8#64) polyArrayBytes ∗
      A.pool lim st1 s9 ∗
      stackAt (s0.sp - 4240#64) dropGluePoly16Stack ∗
      ((s8.readReg64 .x1 ↦₆₄ enc_tag) ∗ memRegion (s8.readReg64 .x1 + 392#64) 8 ∗
       vecPtListOf A.repAlloc (s8.readReg64 .x1 + 528#64) dec_vecs ∗
       memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗
       memRegion (s8.readReg64 .x1 + 400#64) 128 ∗ memRegion (s0.sp - 23792#64) 15424 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗ Rest))
    (Q_mid := fun s9 =>
      s9.sp = s8.sp ∧ AllocCallPreserved s8 s9 ∧
      s9.readReg64 .x0 = s8.readReg64 .x1 + 528#64 ∧ TraceCalleeSaved s9 s8)
    ?_ ?_
  · have hpoly16_raw := drop_glue_poly16_mem_on
      (callerProg := lsProg_332 (Rust.withPanics ext)) hdealloc hcl8
    dsimp only [lsProg_332, withMemEq, dropGluePoly16Spec, BitVec.ofNat_eq_ofNat]
      at hpc8 hpoly16_raw ⊢
    wp_steps
    wp_call hpoly16_raw (⟨s8.readReg64 .x1 + 8#64, enc_vecs⟩, st_cost)
    have hacp8 : AllocCallPreserved s8 sf := by assumption
    have hevs1 : FreeOnlyEvs w := by assumption
    rcases hacp8 with ⟨_, _, _, _, _, _, _⟩
    wp_steps
    refine SepWP.mono
      (post := fun s9 P9 =>
        (P9 ⊢ memRegion (s8.readReg64 .x1 + 8#64) polyArrayBytes ∗
          A.pool lim (M.stepEvents w st_cost) s9 ∗
          stackAt (s0.sp - 4240#64) dropGluePoly16Stack ∗
          ((s8.readReg64 .x1 ↦₆₄ enc_tag) ∗ memRegion (s8.readReg64 .x1 + 392#64) 8 ∗
           vecPtListOf A.repAlloc (s8.readReg64 .x1 + 528#64) dec_vecs ∗
           memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗
           memRegion (s8.readReg64 .x1 + 400#64) 128 ∗ memRegion (s0.sp - 23792#64) 15424 ∗
           memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗ Rest)) ∧
        (s9.sp = s8.sp ∧ AllocCallPreserved s8 s9 ∧
          s9.readReg64 .x0 = s8.readReg64 .x1 + 528#64 ∧ TraceCalleeSaved s9 s8))
      ?_
      (fun _ _ _ _ ⟨hP9, hq⟩ => ⟨w, hevs1, hP9, hq⟩)
    refine align_pre_st (by rw [hsp8, h912]; simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
    wp_done
  · intro st1 s9 hpc9 hrun9 hcl9 ⟨hsp9, hacp89, hx0_9, htr9⟩
    rw [hsp8] at hsp9
    have hstack_fold :
        memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack ⊢
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX := by
      have h := stackAt_statesRecvCallee_from_dropGluePoly16 (s0.sp - 4240#64)
      have heq : s0.sp - 4240#64 - 19552#64 = s0.sp - 23792#64 := by bv_omega
      rwa [heq] at h
    refine SepWP.weaken_pre
      (Entails.trans
        (Entails.of_eq (show _ =
          ((s8.readReg64 .x1 ↦₆₄ enc_tag) ∗ memRegion (s8.readReg64 .x1 + 8#64) polyArrayBytes ∗
           memRegion (s8.readReg64 .x1 + 392#64) 8 ∗ memRegion (s8.readReg64 .x1 + 400#64) 128) ∗
          (memRegion (s0.sp - 23792#64) 15424 ∗ stackAt (s0.sp - 4240#64) dropGluePoly16Stack) ∗
          (memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0 ∗
           vecPtListOf A.repAlloc (s8.readReg64 .x1 + 528#64) dec_vecs ∗ A.pool lim st1 s9 ∗
           (memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest)) by sep_ac_rfl))
        (sepConj_mono (chunked_400_join (s8.readReg64 .x1) enc_tag 128 528 rfl (by decide))
          (sepConj_mono_left hstack_fold))) ?_
    refine SepWP.weaken_pre
      (Entails.of_eq (show _ =
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A.repAlloc (s8.readReg64 .x1 + 528#64) dec_vecs ∗
        A.pool lim st1 s9 ∗
        (memRegion (s8.readReg64 .x1) 528 ∗
          memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest) by sep_ac_rfl)) ?_
    have htail := DispatchPlacedBudget.states_recv_tail_drop_sortedSetPt16_1760_dealloc_placed
      hdealloc st1 s0 s9 (s8.readReg64 .x1 + 528#64) dec_vecs hdec_len
      (memRegion (s8.readReg64 .x1) 528 ∗
        memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16 ∗ Rest)
      hsp0_align (by rwa [lsmpl_base_332_eq]) hrun9 hsp9 hx0_9 (htr9.trans htr8) hcl9
    refine SepWP.mono htail ?_
    intro sf Pf _ _ ⟨evs2, hevs2, hPf, hsp_f, hacp9f, hcs_f, htr_f⟩
    refine ⟨evs2, hevs2, ?_, hsp_f, hacp89.trans hacp9f, hcs_f, htr_f⟩
    exact Entails.trans hPf (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s8.readReg64 .x1) 528 ∗
          memRegion (s8.readReg64 .x1 + 528#64) polyArrayBytes ∗
          memRegion ((s8.readReg64 .x1 + 528#64) + 384#64) 16) ∗
        (A.pool lim (M.stepEvents evs2 st1) sf ∗
          (stackAt s0.sp statesRecvStackX ∗ Rest)) by sep_ac_rfl))
      (sepConj_mono_left (ct1Sampled_join_928 (s8.readReg64 .x1))))

theorem ct1Sampled_drop_epochOutOfRange_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ)
    (s0 s3 : State) (outA selfA msg_ep : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hcl3 : LibsignalCodeLoaded lsmpl s3.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc3 : s3.pc = (blkPl_332).base + 1564#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s0.sp - 4240#64)
    (hx1 : s3.readReg64 .x1 = selfA)
    (hx19 : s3.readReg64 .x19 = outA)
    (hx20 : s3.readReg64 .x20 = msg_ep)
    (htr3 : TraceCalleeSaved s3 s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (memRegion outA v1RecvSize ∗
        chunkedStatesAt A.repAlloc selfA (.ct1Sampled st) ∗
        A.pool lim st_cost s3 ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s3 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  refine SepWP.mono
    (post := fun sf Pf =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        (Pf ⊢
          (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
            memRegion selfA chunkedStatesSize) ∗
          A.pool lim (M.stepEvents evs st_cost) sf ∗
          (stackAt s0.sp statesRecvStackX ∗ Rest)) ∧
        (sf.sp = s0.sp ∧ AllocCallPreserved s3 sf ∧
          CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace))
    ?_
    (fun _ _ _ _ ⟨evs, hevs, hPf, hq⟩ =>
      ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hq⟩)
  dsimp only [chunkedStatesAt, chunkedCt1SampledAt]
  wp_conv_pre =>
    rw [stackAt_statesRecvCallee_eq_allocHook' (s0.sp - 4240#64)]
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      memRegion outA v1RecvSize ∗
      unchunkedCt1SentAt A.repAlloc (selfA + 400#64) st.uc ∗
      A.pool lim st_cost s3 ∗
      stackAt (s0.sp - 4240#64) allocHookStack ∗
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
       polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest) by sep_ac_rfl)) ?_
  refine seq_evs_step_lscl hcl3
    (P_mid := fun st1 s8 =>
      resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗
      memRegion (selfA + 400#64) 128 ∗
      A.pool lim st1 s8 ∗
      stackAt (s0.sp - 4240#64) allocHookStack ∗
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
       polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest))
    (Q_mid := fun s8 =>
      s8.sp = s0.sp - 4240#64 ∧ AllocCallPreserved s3 s8 ∧
      s8.readReg64 .x1 = selfA ∧ TraceCalleeSaved s8 s3)
    (ct1Sampled_write_err_and_dealloc5_placed hdealloc st_cost s3 (s0.sp - 4240#64)
      outA selfA msg_ep st.uc
      (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
       polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
       memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗
       memRegion (s0.sp - 4240#64) 4144 ∗
       statesRecvSavedCells s0 ∗
       Rest)
      hfsp_align hpc3 hrun3 hsp3 hx1 hx19 hx20) ?_
  intro st1 s8 hpc8 hrun8 hcl8 ⟨hsp8, hacp38, hx1_8, htr8⟩
  refine SepWP.weaken_pre
    (Entails.trans
      (Entails.of_eq (show _ =
        (memRegion (s0.sp - 4240#64 - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) allocHookStack) ∗
        (polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
         memRegion (selfA + 400#64) 128 ∗
         polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
         A.pool lim st1 s8 ∗
         memRegion (s0.sp - 4240#64) 4144 ∗
         statesRecvSavedCells s0 ∗
         (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest))
        by sep_ac_rfl))
      (sepConj_mono_left (stackAt_statesRecvCallee_from_allocHook (s0.sp - 4240#64)))) ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (show _ =
      polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
      memRegion (selfA + 400#64) 128 ∗
      polyDecoderAt A.repAlloc (selfA + 528#64) st.receiving_ek ∗
      A.pool lim st1 s8 ∗
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
      memRegion (s0.sp - 4240#64) 4144 ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)
      by sep_ac_rfl)) ?_
  refine SepWP.mono
    (ct1Sampled_drop_encoders_epilogue_placed hdealloc st1 s0 s8 selfA st.sending_ct1 st.receiving_ek
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err (.epochOutOfRange msg_ep))) ∗ Rest)
      hcl8 hsp0_align hpc8 hrun8 hsp8 hx1_8 (htr8.trans htr3) (hlr_ls := hlr_ls)) ?_
  intro sf Pf _ _ ⟨evs2, hevs2, hPf, hspf, hacp8f, hcsf, htrf⟩
  refine ⟨evs2, hevs2, ?_, hspf, hacp38.trans hacp8f, hcsf, htrf⟩
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
