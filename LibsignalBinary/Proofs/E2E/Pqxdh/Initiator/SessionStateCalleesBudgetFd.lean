/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesAuxBudgetFd
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.GenLsBlock
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPFrozen

/-!
# `fs`-Preserving Budget Contracts for `SessionState` Builders (Blocks `37`, `27`, `30`)

Proves `sf.fs = s0.fs`-preserving `[LibsignalPlacement]` contracts under `RustCliAllocBudget M` for
`<SessionState>::new` (Block `37`), `<SessionState>::with_sender_chain` (Block `27`), and
`<SessionState>::with_receiver_chain` (Block `30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetFd

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  lsMemcpySym lsRustAllocSym lsRustDeallocSym lsRustNoAllocShimSym
  ls_hook_ok_of_mem ls_subroutine_ok_cl_of_block ls_subroutine_ok_cl_of_plain
  lsmpl lsρ sepWP_seq_lscl withLsCl withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.E2E.Pqxdh.Initiator (
  Bytes blkPC_27 blkPl_27 blkPC_30 blkPl_30 blkPC_37 blkPl_37
  bv_sub_add_lit' bytesToBv8 encodeEC
  readReg32_setMem_setPC_pre readReg32_setPC_pre
  readReg64_setMem_setPC_pre readReg64_setPC_pre
  readReg_setMem_setPC_pre readReg_setPC_pre
  receiverChainElemAt receiverChainVecBytes24 receiverChainVecFieldsAt
  senderChainBytes100
  sp_setMem_setPC_pre sp_setPC_pre stackAt_split_top
  withReceiverChain_pack344 withReceiverChain_pack344_unfolded
  withSenderChain_pack344 withSenderChain_pack344_unfolded
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvent FitsEvents RustCliAllocBudget
  VmPreserved rustAllocEvents rustCliAllocBudgetSpec
  rustCliDeallocBudgetSpec rustDeallocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomSpecWithStack subroutine_ok_rustCliAllocNoOom_withStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  allocMemcpyVmSpec rustAllocShimVmSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesAuxBudgetFd (
  dealloc_bytes_keepsFs_placed_ok ecPubKeySerialize_alloc_keepsFs_placed_ok_of_session
  growOneChain_zero_region_keepsFs_placed_ok_of_session
  hookSat_sessionMemcpyRegionBudget_keepsFs_of_allocMemcpyVm
  hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm
  privKeySerialize_keepsFs_placed_ok_of_session
)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudget (
  ecPubKeySerializeAllocEvents ecPubKeySerializeAllocPlacedSpec
  growOneChainZeroEvents growOneChainZeroRegionPlacedSpec
  privKeySerializePlacedEvents privKeySerializePlacedSpec
  rustDeallocBytesSpec sessionStateNewEvents sessionStateNewPlacedSpec
  withReceiverChainEmptyEvents withReceiverChainEmptyPlacedSpec
  withSenderChainNoneEvents withSenderChainNonePlacedSpec
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff FitsEvent
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local simp, local wp_norm, local arm64_norm]
private theorem bytesToBv8_length_fd (bs : Bytes) : (bytesToBv8 bs).length = bs.length :=
  List.length_map _

/-! ## 1. `<SessionState>::new` (Block `37`) -/

private theorem stackAt_sessionStateNew_entry_fd (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 96#64 - 4128#64) 32 ∗ stackAt (sp - 96#64) allocHookStack) ∗
      cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 128 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 12 (by decide)
  have h3 := stackAt_split_top (sp - 96#64) 32 allocHookStack (by decide)
  have h4 : (128 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 12 := by decide
  have h5 : BitVec.ofNat 64 (128 + allocHookStack) = 4224#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1
  rw [h6] at h2
  rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_344_sessionStateNew_split_fd (outPtr : BitVec 64) :
    memRegion outPtr 344 =
      cells outPtr 19 ∗ memRegion (outPtr + 0x98#64) 96 ∗
      (∃∗ u_f8 : BitVec 64, (outPtr + 0xf8#64) ↦₆₄ u_f8) ∗
      memRegion (outPtr + 0x100#64) 40 ∗
      (∃∗ u_128 : BitVec 64, (outPtr + 0x128#64) ↦₆₄ u_128) ∗
      memRegion (outPtr + 0x130#64) 24 ∗
      (∃∗ u_148 : BitVec 32, (outPtr + 0x148#64) ↦₃₂ u_148) ∗
      (∃∗ u_14c : BitVec 64, (outPtr + 0x14c#64) ↦₆₄ u_14c) ∗
      (∃∗ u_154 : BitVec 32, (outPtr + 0x154#64) ↦₃₂ u_154) := by
  rw [memRegion_split outPtr 152 192 (by decide), memRegion_cells outPtr 19 (by decide),
    memRegion_split (outPtr + 152#64) 96 96 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64) 8 88 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64) 40 48 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 4 12 (by decide),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64) 8 4 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

set_option maxHeartbeats 4000000 in
theorem sessionStateNew_keepsFs_placed_ok_of_session [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (keepsFs (sessionStateNewPlacedSpec M A lim))) := by
  unfold withLsCodeLoaded keepsFs sessionStateNewPlacedSpec sessionStateNewEvents
  simp only [stackAt_sessionStateNew_entry_fd, memRegion_344_sessionStateNew_split_fd]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_37).rebase (blkPl_37).base H)
    (ecPubKeySerialize_alloc_keepsFs_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (keepsFs (ecPubKeySerializeAllocPlacedSpec M A lim))) at hser
  simp only [withLsCl, keepsFs, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hshim' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustNoAllocShimSym) (keepsFs sessionShimBudgetSpec) := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  dsimp only [keepsFs, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init x s0
  rcases x with ⟨⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr version localIkPtr remoteIkPtr rootKeyPtr baseKeyPtr spqrVecPtr
  have hfe_all : FitsEvents M lim st [.alloc 33, .alloc 33, .alloc 32, .alloc 33] := by
    simpa [rustAllocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 33 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by
    simp [bytesToBv8, ‹rootKey32.length = 32›]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), localIk32), st)
  have hfs_0 : sf.fs = s0.fs := by assumption
  have hcl2 : LibsignalCodeLoaded lsmpl sf.mem := by assumption
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hser ((s0.readReg64 (.gpr 2#5), remoteIk32), st1)
  have hfs_1 : sf_1.fs = s0.fs := (‹sf_1.fs = _›).trans hfs_0
  have hcl4 : LibsignalCodeLoaded lsmpl sf_1.mem := by assumption
  apply sepWP_seq_lscl hcl4 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_2 : sf_2.fs = s0.fs := (‹sf_2.fs = _›).trans hfs_1
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st2)
  have htr_3 : sf_3.trace = sf_2.trace := (‹AllocCallPreserved _ sf_3›).2.1
  have hfs_3 : sf_3.fs = s0.fs := (‹AllocCallPreserved _ sf_3›).1.trans hfs_2
  have hne_rk : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq_rk : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne_rk
  have hm32 : memRegion (sf_3.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_3.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl5
  wp_call hser ((s0.readReg64 (.gpr 4#5), baseKey32), st3)
  have hfs_4 : sf_4.fs = s0.fs := (‹sf_4.fs = _›).trans hfs_3
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, hrk_cells, sepConj_assoc]
  wp_done

theorem sessionStateNew_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (keepsFs (sessionStateNewPlacedSpec M A lim))) :=
  sessionStateNew_keepsFs_placed_ok_of_session
    (hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm hshim) halloc

/-! ## 2. `<SessionState>::with_sender_chain` None Branch (Block `27`) -/

private theorem stackAt_withSenderChain_entry_fd (sp : BitVec 64) :
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack) ∗
        cells (sp - 128#64) 16 := by
  have h1 := stackAt_split_top sp 160 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 16 (by decide)
  have h3 := stackAt_split_top (sp - 128#64) 32 allocHookStack (by decide)
  have h4 : (160 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 16 := by decide
  have h5 : BitVec.ofNat 64 (160 + allocHookStack) = 4256#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 16) = 128#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1; rw [h6] at h2; rw [h7] at h3
  rw [← h1, h4, h2, ← h3]

private theorem memRegion_92_senderChain_split_fd (ptr : BitVec 64) :
    memRegion (ptr + 0x98#64) 92 =
      cells (ptr + 0x98#64) 11 ∗ (∃∗ v : BitVec 32, (ptr + 0xf0#64) ↦₃₂ v) := by
  have hsplit := memRegion_split (ptr + 0x98#64) 88 4 (by decide)
  have haddr : ptr + 0x98#64 + BitVec.ofNat 64 88 = ptr + 0xf0#64 := by bv_omega
  rw [hsplit, memRegion_cells (ptr + 0x98#64) 11 (by decide), haddr, ProofLib.memRegion_four]

private theorem sepWP_focus_fd {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hf : P = T ∗ F) (h : SepWP prog ret s (T ∗ F) Q) : SepWP prog ret s P Q :=
  hf ▸ h

private theorem cells_three_entails_fd (sp v0 v1 v2 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v0 ∗ (sp - 112#64) ↦₆₄ v1 ∗ (sp - 104#64) ↦₆₄ v2) ⊢
      cells (sp - 120#64) 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.refl _)))

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_adds_neg1_1_fd :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

set_option maxHeartbeats 4000000 in
theorem withSenderChain_none_keepsFs_placed_ok_of_session [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym (keepsFs sessionMemcpyRegionBudgetSpec)) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (keepsFs (withSenderChainNonePlacedSpec M A lim))) := by
  unfold withLsCodeLoaded keepsFs withSenderChainNonePlacedSpec withSenderChainNoneEvents
  simp only [stackAt_withSenderChain_entry_fd, memRegion_92_senderChain_split_fd]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (ecPubKeySerialize_alloc_keepsFs_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (keepsFs (ecPubKeySerializeAllocPlacedSpec M A lim))) at hser
  dsimp only [withLsCl, keepsFs, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hpser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (privKeySerialize_keepsFs_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 208)
    (withLsCl lsmpl (keepsFs (privKeySerializePlacedSpec M A lim))) at hpser
  dsimp only [withLsCl, keepsFs, privKeySerializePlacedSpec, privKeySerializePlacedEvents] at hpser
  have hshim' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustNoAllocShimSym) (keepsFs sessionShimBudgetSpec) := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_keepsFs_placed_ok
    (prog := (blkPC_27).rebase (blkPl_27).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsMemcpySym) (keepsFs sessionMemcpyRegionBudgetSpec) := ls_hook_ok_of_mem hmemcpy
  dsimp only [keepsFs, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [keepsFs, rustDeallocBytesSpec] at hdealloc'
  dsimp only [keepsFs, sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  wp_init x s0
  rcases x with ⟨⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderKeyPairPtr senderChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .alloc 32, .alloc 32, .free 1 32, .free 1 33] := by
    simpa [rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 32 1 ++ rustAllocEvents 32 1 ++
        rustDeallocEvents 32 1 ++ rustDeallocEvents 33 1)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, hfe4, hfe5, -, -, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustAllocEvents 32 1) st3
  let st5 := M.stepEvents (rustAllocEvents 32 1) st4
  let st6 := M.stepEvents (rustDeallocEvents 32 1) st5
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by
    simp [bytesToBv8, ‹senderChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_0 : sf.fs = s0.fs := by assumption
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have htr_1 : sf_1.trace = sf.trace := (‹AllocCallPreserved _ sf_1›).2.1
  have hfs_1 : sf_1.fs = s0.fs := (‹AllocCallPreserved _ sf_1›).1.trans hfs_0
  have hne1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne1
  have hm32_1 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32_1, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hck_cells (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem, hck_cells, sepConj_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), senderRatchetPub32), st1)
  have hfs_2 : sf_2.fs = s0.fs := (‹sf_2.fs = _›).trans hfs_1
  have hcl2 : LibsignalCodeLoaded lsmpl sf_2.mem := by assumption
  have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
    change (0x05 :: senderRatchetPub32).length = 33; simp [‹senderRatchetPub32.length = 32›]
  have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
    simp [bytesToBv8, henc33]
  have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by
    simp [bytesToBv8, ‹senderRatchetPriv32.length = 32›]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 208)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_3 : sf_3.fs = s0.fs := (‹sf_3.fs = _›).trans hfs_2
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st2)
  have htr_4 : sf_4.trace = sf_3.trace := (‹AllocCallPreserved _ sf_4›).2.1
  have hfs_4 : sf_4.fs = s0.fs := (‹AllocCallPreserved _ sf_4›).1.trans hfs_3
  have hne2 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_4.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne2
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_pub33]
  wp_call hmemcpy' (sf_4.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC senderRatchetPub32))
  have hfs_5 : sf_5.fs = s0.fs := (‹sf_5.fs = _›).trans hfs_4
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  simp only [hlen_pub33, henc33]
  wp_steps_sync_pool (lsmpl.base 208)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  apply SepWP.replace_pre (by sep_focus) (cells_three_entails_fd s0.sp _ _ _)
  wp_call hpser ((s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp - 120#64), st3)
  have hfs_6 : sf_6.fs = s0.fs := (‹sf_6.fs = _›).trans hfs_5
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_7 : sf_7.fs = s0.fs := (‹sf_7.fs = _›).trans hfs_6
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_7› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st4)
  have htr_8 : sf_8.trace = sf_7.trace := (‹AllocCallPreserved _ sf_8›).2.1
  have hfs_8 : sf_8.fs = s0.fs := (‹AllocCallPreserved _ sf_8›).1.trans hfs_7
  have hne3 : sf_8.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_8.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne3
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_priv32]
  wp_call hmemcpy' (sf_8.readReg64 (Reg.gpr 0#5), _, bytesToBv8 senderRatchetPriv32)
  have hfs_9 : sf_9.fs = s0.fs := (‹sf_9.fs = _›).trans hfs_8
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_9› (hnext := ?_)
  simp only [hlen_priv32, ‹senderRatchetPriv32.length = 32›]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 senderRatchetPriv32, 32, 1), st5)
  have hfs_10 : sf_10.fs = s0.fs := (‹sf_10.fs = _›).trans hfs_9
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st6)
  have hfs_11 : sf_11.fs = s0.fs := (‹sf_11.fs = _›).trans hfs_10
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    (sf_4.readReg64 (.gpr 0#5)) (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
    senderChainIdx pre144 post100 ‹pre144.length = 144›
  have hlen_full : (pre144 ++ (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
      post100)).length = 344 := by
    simp [‹pre144.length = 144›, ‹post100.length = 100›]
  refine sepWP_focus_fd (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_4.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb0#64) ↦₆₄ sf_8.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd0#64) ↦₆₄ 0#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf0#64) ↦₃₂ senderChainIdx) ∗
    ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_focus) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
    (senderChainBytes100 (sf_4.readReg64 (.gpr 0#5))
      (sf_8.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
  have hfs_12 : sf_12.fs = s0.fs := (‹sf_12.fs = _›).trans hfs_11
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_12› (hnext := ?_)
  simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ ‹pre144.length = 144›, sepConj_assoc]
  wp_done

theorem withSenderChain_none_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (keepsFs (withSenderChainNonePlacedSpec M A lim))) :=
  withSenderChain_none_keepsFs_placed_ok_of_session
    (hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_keepsFs_of_allocMemcpyVm hmemcpy)

/-! ## 3. `<SessionState>::with_receiver_chain` Empty Branch (Block `30`) -/

private theorem stackAt_withReceiverChain_entry_fd (sp : BitVec 64) :
    memRegion (sp - 4576#64) 480 ∗ stackAt sp allocHookStack =
      memRegion (sp - 368#64 - 4208#64) 80 ∗
        (memRegion (sp - 368#64 - 4128#64) 32 ∗ stackAt (sp - 368#64) allocHookStack) ∗
        memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 480 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (112 + allocHookStack) 46 (by decide)
  have h3 := stackAt_split_top (sp - 368#64) 112 allocHookStack (by decide)
  have h4 := memRegion_split (sp - 368#64 - 4208#64) 80 32 (by decide)
  have h5 : (480 + allocHookStack : Nat) = (112 + allocHookStack) + 8 * 46 := by decide
  have h6 : BitVec.ofNat 64 (480 + allocHookStack) = 4576#64 := rfl
  have h7 : BitVec.ofNat 64 (8 * 46) = 368#64 := rfl
  have h8 : BitVec.ofNat 64 (112 + allocHookStack) = 4208#64 := rfl
  have h9 : sp - 368#64 - 4208#64 + BitVec.ofNat 64 80 = sp - 368#64 - 4128#64 := by bv_omega
  have hcells46 : cells (sp - 368#64) 46 = memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
    rw [← memRegion_cells (sp - 368#64) 46 (by decide),
      memRegion_split (sp - 368#64) 272 96 (by decide),
      show sp - 368#64 + BitVec.ofNat 64 272 = sp - 96#64 by bv_omega,
      memRegion_cells (sp - 96#64) 12 (by decide)]
  rw [h6] at h1; rw [h7] at h2; rw [h8] at h3; rw [h9] at h4
  rw [← h1, h5, h2, h3, h4, hcells46]
  simp only [sepConj_assoc]

private theorem memRegion_416_receiverChain_split_fd (ptr : BitVec 64) :
    memRegion ptr 416 =
      cells ptr 12 ∗ (∃∗ v : BitVec 32, (ptr + 0x60#64) ↦₃₂ v) ∗ memRegion (ptr + 0x64#64) 316 := by
  have h1 := memRegion_split ptr 96 320 (by decide)
  have h2 := memRegion_split (ptr + BitVec.ofNat 64 96) 4 316 (by decide)
  have h3 : ptr + BitVec.ofNat 64 96 = ptr + 0x60#64 := by bv_omega
  have h4 : ptr + 0x60#64 + BitVec.ofNat 64 4 = ptr + 0x64#64 := by bv_omega
  rw [h1, memRegion_cells ptr 12 (by decide), h3]
  rw [h3, h4] at h2
  rw [h2, ProofLib.memRegion_four (ptr + 0x60#64)]

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs_0_0_fd :
    ConditionHolds CondCode.EQ (subsPState64 0#64 0#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_0_5_fd :
    ConditionHolds CondCode.LT (subsPState64 0#64 5#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem madd_zero_104_fd (ptr : BitVec 64) : ptr + 0#64 * 104#64 = ptr := by simp

set_option maxHeartbeats 4000000 in
theorem withReceiverChain_empty_keepsFs_placed_ok_of_session [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym (keepsFs sessionShimBudgetSpec))
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym (keepsFs sessionMemcpyRegionBudgetSpec)) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (keepsFs (withReceiverChainEmptyPlacedSpec M A lim))) := by
  unfold withLsCodeLoaded keepsFs withReceiverChainEmptyPlacedSpec withReceiverChainEmptyEvents
  simp only [stackAt_withReceiverChain_entry_fd]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (ecPubKeySerialize_alloc_keepsFs_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 205)
    (withLsCl lsmpl (keepsFs (ecPubKeySerializeAllocPlacedSpec M A lim))) at hser
  dsimp only [withLsCl, keepsFs, ecPubKeySerializeAllocPlacedSpec, ecPubKeySerializeAllocEvents] at hser
  have hgrow := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (growOneChain_zero_region_keepsFs_placed_ok_of_session hshim halloc)
  change subroutine_ok _ (lsmpl.base 43)
    (withLsCl lsmpl (keepsFs (growOneChainZeroRegionPlacedSpec M A lim))) at hgrow
  dsimp only [withLsCl, keepsFs, growOneChainZeroRegionPlacedSpec, growOneChainZeroEvents] at hgrow
  have hshim' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustNoAllocShimSym) (keepsFs sessionShimBudgetSpec) := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_withStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hdealloc' := dealloc_bytes_keepsFs_placed_ok
    (prog := (blkPC_30).rebase (blkPl_30).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsMemcpySym) (keepsFs sessionMemcpyRegionBudgetSpec) := ls_hook_ok_of_mem hmemcpy
  dsimp only [keepsFs, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  dsimp only [keepsFs, rustDeallocBytesSpec] at hdealloc'
  dsimp only [keepsFs, sessionMemcpyRegionBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionMemcpyRegionSpec, memcpyRegionSpec] at hmemcpy'
  wp_init x s0
  rcases x with ⟨⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩, st⟩
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderRatchetPubPtr receiverChainKeyPtr
  have hfe_all : FitsEvents M lim st
      [.alloc 32, .alloc 33, .alloc 33, .free 1 33, .alloc 416] := by
    simpa [growOneChainZeroEvents, rustAllocEvents, rustDeallocEvents] using
      ‹FitsEvents M lim st (rustAllocEvents 32 1 ++ rustAllocEvents 33 1 ++
        rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++ growOneChainZeroEvents)›
  rcases hfe_all with ⟨hfe1, hfe2, hfe3, -, hfe4, -⟩
  let st1 := M.stepEvents (rustAllocEvents 32 1) st
  let st2 := M.stepEvents (rustAllocEvents 33 1) st1
  let st3 := M.stepEvents (rustAllocEvents 33 1) st2
  let st4 := M.stepEvents (rustDeallocEvents 33 1) st3
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by
    simp [bytesToBv8, ‹receiverChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos32 : 0 < (32 : Nat) := by decide
  have hpos33 : 0 < (33 : Nat) := by decide
  have hal1 : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum32 : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  have hsum33 : (33 : Nat) + 1 ≤ 2 ^ 63 := by decide
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_0 : sf.fs = s0.fs := by assumption
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have htr_1 : sf_1.trace = sf.trace := (‹AllocCallPreserved _ sf_1›).2.1
  have hfs_1 : sf_1.fs = s0.fs := (‹AllocCallPreserved _ sf_1›).1.trans hfs_0
  have hne1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne1
  have hm32_1 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
      cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
    memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
  simp only [hm32_1, cells, sepConj_emp, sepExists_sepConj_left,
    sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  rw [hck_cells (s0.readReg64 (.gpr 2#5))]
  wp_steps_sync_pool (lsmpl.base 205)
  simp only [State.setMem_setMem, hck_cells, sepConj_assoc]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  wp_call hser ((s0.readReg64 (.gpr 1#5), senderRatchetPub32), st1)
  have hfs_2 : sf_2.fs = s0.fs := (‹sf_2.fs = _›).trans hfs_1
  have hcl2 : LibsignalCodeLoaded lsmpl sf_2.mem := by assumption
  have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
    change (0x05 :: senderRatchetPub32).length = 33; simp [‹senderRatchetPub32.length = 32›]
  have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
    simp [bytesToBv8, henc33]
  apply sepWP_seq_lscl hcl2 (mid := lsmpl.base 43)
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have hfs_3 : sf_3.fs = s0.fs := (‹sf_3.fs = _›).trans hfs_2
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_3› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (33, 1, st2)
  have htr_4 : sf_4.trace = sf_3.trace := (‹AllocCallPreserved _ sf_4›).2.1
  have hfs_4 : sf_4.fs = s0.fs := (‹AllocCallPreserved _ sf_4›).1.trans hfs_3
  have hne2 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_4.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne2
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  rw [← hlen_pub33]
  wp_call hmemcpy' (sf_4.readReg64 (Reg.gpr 0#5), _, bytesToBv8 (encodeEC senderRatchetPub32))
  have hfs_5 : sf_5.fs = s0.fs := (‹sf_5.fs = _›).trans hfs_4
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_5› (hnext := ?_)
  simp only [hlen_pub33, henc33]
  wp_steps_sync_pool (lsρ lsRustDeallocSym)
  simp only [State.setMem_setMem]
  wp_call hdealloc' ((_, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1), st3)
  have hfs_6 : sf_6.fs = s0.fs := (‹sf_6.fs = _›).trans hfs_5
  wp_steps_sync_pool (lsmpl.base 43)
  simp only [State.setMem_setMem]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  wp_call hgrow ((s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr), st4)
  have hfs_7 : sf_7.fs = s0.fs := (‹sf_7.fs = _›).trans hfs_6
  simp only [memRegion_416_receiverChain_split_fd w_1, cells, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
    w_1 pre72 post248 ‹pre72.length = 72›
  have hlen_full : (pre72 ++ (receiverChainVecBytes24 w_1 ++ post248)).length = 344 := by
    simp [‹pre72.length = 72›, ‹post248.length = 248›]
  refine sepWP_focus_fd (T :=
    (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ w_1) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x58#64) ↦₆₄ 1#64) ∗
    ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_focus) ?_
  rw [hpack_in, ← hlen_full]
  wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5),
    pre72 ++ (receiverChainVecBytes24 w_1 ++ post248))
  have hfs_8 : sf_8.fs = s0.fs := (‹sf_8.fs = _›).trans hfs_7
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_8› (hnext := ?_)
  simp only [← withReceiverChain_pack344 _ _ _ _ ‹pre72.length = 72›]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  unfold receiverChainElemAt receiverChainVecFieldsAt
  simp only [State.setMem_setMem, sepConj_assoc]
  wp_done

theorem withReceiverChain_empty_keepsFs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (keepsFs (withReceiverChainEmptyPlacedSpec M A lim))) :=
  withReceiverChain_empty_keepsFs_placed_ok_of_session
    (hookSat_sessionShimBudget_keepsFs_of_rustAllocShimVm hshim) halloc hdealloc
    (hookSat_sessionMemcpyRegionBudget_keepsFs_of_allocMemcpyVm hmemcpy)

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesBudgetFd
