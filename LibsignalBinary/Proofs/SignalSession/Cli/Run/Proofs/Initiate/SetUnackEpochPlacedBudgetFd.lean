/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesAuxBudgetFd
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import ProofLib.SepLogic.WP.Apply

/-!
# `State.fs`- and `FdsGe3Closed`-Threaded `set_unacknowledged_pre_key_message` at `UNIX_EPOCH`

Proves `.keepsFs` and `withFdsGe3Closed` contracts on block `33`
(`<SessionState>::set_unacknowledged_pre_key_message`) at `now = UNIX_EPOCH`, using the fact that
`durationSinceExactHook` preserves `State.fs`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SetUnackEpochPlacedBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_plain lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalPublicApi.StoreKit (
  ls_subroutine_ok_rocl_of_block subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  withLsCodeRoLoaded withLsRoCl
)
open CryptoVerification.E2E.Pqxdh.Initiator (
  blkPC_33 blkPl_33 bv_sub_add_lit' bytesToBv8 encodeEC instIsLsBlockProg_33
  readReg_setMem_setPC_pre readReg_setPC_pre
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top vecU8
)
open CryptoVerification.SignalSession (
  CliHooks cliExternsPlaced durationSinceExactHook lsDurationSinceSym
)
open CryptoVerification.SignalSession.Cli.RunGlue (
  CliGhostHooks cliExternsPlaced_row cliGhostExterns
)
open CryptoVerification.SignalSession.Cli.Slots (
  cliGhostExterns_sat_of_cliExternsPlaced
  durationSinceEpochAllocSpec durationSinceEpochAtSpec durationSince_row_placed
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvent FitsEvents RustCliAllocBudget
  VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesAuxBudgetFd (
  dealloc_bytes_keepsFs_placed_ok ecPubKeySerializeRaw_keepsFs_placed_ok_of_session
  hookSat_sessionMemcpyRegionBudget_keepsFs_of_allocMemcpyVm
  hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget (
  ecPubKeySerializeAllocEvents ecPubKeySerializeRawPlacedSpec
  rustDeallocBytesSpec setUnackPreKeyMsgEvents
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.FdThreadKit (
  hookSat_keepsFs_of_fs_eq subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (
  withFdsGe3Closed
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlacedBudget (
  RunHooksPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SetUnackEpochPlacedBudget (
  cliExternsPlaced_durationSinceEpochAlloc_budget_sat durationSinceEpochAllocBudgetSpec
  setUnackPreKeyMsgEpochEvents setUnackPreKeyMsgEpochInnerSpec
  setUnackPreKeyMsgExactStackEpochSpecPlaced
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

/-! ## `durationSinceExactHook` preserves `State.fs` -/

private theorem durationSinceExactHook_fs_local (s : State) :
    (durationSinceExactHook s).fs = s.fs := by
  unfold durationSinceExactHook; try dsimp only
  split
  · rfl
  · try dsimp only
    split
    · rfl
    · rfl

theorem cliExternsPlaced_durationSinceEpochAlloc_budget_keepsFs_sat (mmpl : Obj.MultiPlacement)
    (W : CliHooks) :
    HookSat (cliExternsPlaced mmpl W) lsDurationSinceSym
      (keepsFs durationSinceEpochAllocBudgetSpec) := by
  rcases cliExternsPlaced_durationSinceEpochAlloc_budget_sat mmpl W with ⟨g, hg, hok⟩
  have hfeq : cliExternsPlaced mmpl W lsDurationSinceSym = some durationSinceExactHook :=
    cliExternsPlaced_row mmpl W (durationSince_row_placed mmpl W)
  rw [hfeq] at hg
  injection hg with hfg
  subst hfg
  exact hookSat_keepsFs_of_fs_eq hfeq durationSinceExactHook_fs_local hok

/-! ## Block `33` `.keepsFs` and `withFdsGe3Closed` proofs -/

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.read8_write64_264_271
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.read8_write64_408_415
  Memory.read8_write64_base_off_disjoint
  Memory.read64_write8_base_off_disjoint

local macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_epoch_placed_fd :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_ite_zero64_epoch_placed_fd (b : Bool) :
    (if b = true then 0#64 else 0#64) = 0#64 := by
  cases b <;> rfl

private theorem memRegion_16_split_64_epoch_placed_fd (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64, (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) := by
  rw [ProofLib.memRegion_split a 8 8 (by decide), ProofLib.memRegion_eight a,
    ProofLib.memRegion_eight (a + 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

private theorem memRegion_24_split_64_epoch_placed_fd (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2)) := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 8#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right]

private theorem pointsTo64_triple_entails_memRegion24_epoch_placed_fd
    (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_split_64_epoch_placed_fd a]
  exact Entails.sepExists_right w2 (Entails.sepExists_right w1
    (Entails.sepExists_right w0 (Entails.refl _)))

private theorem memRegion_40_unack_split_epoch_placed_fd (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (statePtr + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗
      (∃∗ w114 : BitVec 32, (statePtr + 0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (statePtr + 0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [ProofLib.memRegion_split (statePtr + 0x100#64) 8 32 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    ProofLib.memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4
      (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four,
    ProofLib.memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackAt_setUnack_call_epoch_placed_fd (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := ProofLib.stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1

private theorem stackAt_setUnack_hooks_epoch_placed_fd (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call_epoch_placed_fd sp]
  have h1 := stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]

set_option maxHeartbeats 4000000 in
theorem setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_cl_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym (keepsFs sessionMemcpyRegionBudgetSpec))
    (hTime : HookSat H lsDurationSinceSym (keepsFs durationSinceEpochAllocBudgetSpec)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (keepsFs (setUnackPreKeyMsgEpochInnerSpec A lim))) := by
  unfold withLsCodeLoaded keepsFs setUnackPreKeyMsgEpochInnerSpec
    setUnackPreKeyMsgEpochEvents setUnackPreKeyMsgEvents
  have hser : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (lsmpl.base 205)
      (withLsCl lsmpl (keepsFs (ecPubKeySerializeRawPlacedSpec M A lim))) :=
    ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
      (ecPubKeySerializeRaw_keepsFs_placed_ok_of_session hshim halloc)
  dsimp only [withLsCl, keepsFs, ecPubKeySerializeRawPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) (keepsFs sessionShimBudgetSpec) := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_keepsFs_placed_ok
    (prog := (blkPC_33).rebase (blkPl_33).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) (keepsFs sessionMemcpyRegionBudgetSpec) := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsDurationSinceSym) (keepsFs durationSinceEpochAllocBudgetSpec) :=
    ls_hook_ok_of_mem hTime
  dsimp only [keepsFs, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [keepsFs, rustDeallocBytesSpec] at hdealloc'
  dsimp only [keepsFs, sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  dsimp only [keepsFs, durationSinceEpochAllocBudgetSpec, withVmPreserved,
    durationSinceEpochAllocSpec, durationSinceEpochAtSpec] at htime'
  wp_init x s0
  rcases x with ⟨⟨statePtr, optOpkTag, optOpkVal, spkId, baseKeyPtr, baseKeyBytes⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx5 : s0.readReg64 (.gpr 5#5) = 0#64 := ‹_›
  have hx6 : (s0.readReg64 (.gpr 6#5)).setWidth 32 = 0#32 := ‹_›
  have hx6_ext : (s0.readReg64 (.gpr 6#5)).extractLsb' 0 32 = 0#32 := by
    ext i hi
    have := congrArg (fun v => v[i]) hx6
    simpa using this
  have hlen_base : baseKeyBytes.length = 32 := ‹_›
  subst statePtr optOpkTag optOpkVal spkId baseKeyPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  have henc33 : (encodeEC baseKeyBytes).length = 33 := by
    change (0x05 :: baseKeyBytes).length = 33; simp [hlen_base]
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  rw [memRegion_40_unack_split_epoch_placed_fd (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun c0 => SepWP.exists_elim fun c1 => SepWP.exists_elim fun c2 => ?_
  repeat (refine SepWP.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call_epoch_placed_fd s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKeyBytes), st)
  apply SepWP.replace_pre (by sep_focus) (Entails.of_eq (stackAt_setUnack_hooks_epoch_placed_fd s0.sp))
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_1› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st1)
  have htr_2 : sf_2.trace = sf_1.trace := (‹AllocCallPreserved _ sf_2›).2.1
  have hfs_2 : sf_2.fs = sf_1.fs := (‹AllocCallPreserved _ sf_2›).1
  have hne : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_enc]
  wp_call hmemcpy' (sf_2.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC baseKeyBytes))
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  simp only [hlen_enc]
  wp_steps_sync_pool (lsρ lsDurationSinceSym)
  simp only [State.setMem_setMem]
  have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
  have h136_12 : s0.sp - 136#64 + 12#64 = s0.sp - 124#64 := by bv_arith
  have h120_8 : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
  have h120_16 : s0.sp - 120#64 + 16#64 = s0.sp - 104#64 := by bv_arith
  have h124_ent : ∀ v, ((s0.sp - 124#64) ↦₃₂ v) ⊢ memRegion (s0.sp - 136#64 + 12#64) 4 := by
    intro v; rw [h136_12]; exact pointsTo32_entails_memRegion (s0.sp - 124#64) v
  rw [← h136_eq]
  apply SepWP.replace_pre (by sep_focus) (h124_ent _)
  apply SepWP.replace_pre (by sep_focus)
    (h120_8 ▸ h120_16 ▸ pointsTo64_triple_entails_memRegion24_epoch_placed_fd (s0.sp - 120#64) _ _ _)
  have hsp3 : sf_3.sp = s0.sp - 144#64 := by simp only [*, arm64_norm]
  wp_call htime' (s0.sp - 136#64, s0.sp - 120#64)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_4› (hnext := ?_)
  rw [memRegion_16_split_64_epoch_placed_fd (s0.sp - 136#64), h136_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  rw [show sf_3.sp = sf_4.sp by simp only [*, arm64_norm]]
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC baseKeyBytes), 33, 1), st2)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  simp only [*] at *
  apply SepWP.replace_pre (by sep_focus)
    (Entails.of_eq ((stackAt_setUnack_call_epoch_placed_fd s0.sp).trans
      (stackAt_setUnack_hooks_epoch_placed_fd s0.sp)).symm)
  dsimp only [st2, st1]
  simp only [vecU8, A.repAlloc_live, AllocCostModel.stepEvents_append]
  cells_unfold
  wp_done

theorem setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym (keepsFs sessionMemcpyRegionBudgetSpec))
    (hTime : HookSat H lsDurationSinceSym (keepsFs durationSinceEpochAllocBudgetSpec)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim).keepsFs :=
  subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_cl_ok hshim halloc hdealloc hmemcpy hTime)

theorem setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_at_block [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H]
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym (keepsFs sessionMemcpyRegionBudgetSpec))
    (hTime : HookSat H lsDurationSinceSym (keepsFs durationSinceEpochAllocBudgetSpec))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (setUnackPreKeyMsgExactStackEpochSpecPlaced A lim).keepsFs := by
  have h33 : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim).keepsFs) :=
    setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_ok hshim halloc hdealloc hmemcpy hTime
  have hrocl := @ls_subroutine_ok_rocl_of_block _ _ callerProg
    ((blkPC_33).rebase (blkPl_33).base H) i 33 H
    hcaller (instIsLsBlockProg_33 H) (blkPl_33).base _
    h33
    _ _ _ _ hi (by decide) (by decide)
  refine subroutine_ok_mono hrocl (fun _ _ _ h => h) ?_
  intro x R s0 sf hpost
  dsimp only [withLsRoCl] at hpost
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
  exact hpost.2

theorem setUnackPreKeyMsg_cli_keepsFs_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A lim)).keepsFs :=
  setUnackPreKeyMsg_exact_stack_epoch_keepsFs_placed_at_block
    (hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm hh.shimVm)
    hh.rawAlloc
    hh.rawDealloc
    (hookSat_sessionMemcpyRegionBudget_keepsFs_of_allocMemcpyVm hh.allocMemcpyVm)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_durationSinceEpochAlloc_budget_keepsFs_sat mmpl W))
    hi

theorem setUnackPreKeyMsg_cli_fds_placed_ok [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    [IsLsBlockProg callerProg i (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    (hh : RunHooksPlaced W A lim (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (blkPl_33).base
      (withLsCodeRoLoaded lsmpl (withFdsGe3Closed (setUnackPreKeyMsgEpochInnerSpec A lim))) :=
  subroutine_ok_withLsCodeRoLoaded_withFdsGe3Closed_of_keepsFs
    (setUnackPreKeyMsg_cli_keepsFs_placed_ok mmpl gh W hh hi)

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SetUnackEpochPlacedBudgetFd
