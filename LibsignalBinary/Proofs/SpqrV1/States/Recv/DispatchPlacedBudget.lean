/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Budget-Threaded Prologue, Dispatch, and Epilogues

Relocatable `[LibsignalPlacement]` `RustCliAllocBudget` proofs of the prologue, jump-table dispatch,
tail-call drop/dealloc epilogues (`FreeOnlyEvs`), and `Ok(V1Recv)` writeback epilogue with `VmPreserved`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_332 blkPl_332 lsProg_332 lsmpl lsρ
   withLsCodeLoaded withMemEq)
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS Pt spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct2Sampled)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk (EkSentCt1Received HeaderSent)
open CryptoVerification.LibsignalTripleRatchet
  (memcpyName sessionMemcpyRegionSpec sessionMemcpySpec withStack)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop
  (chunkedCt2SampledAt chunkedCt2SampledSize chunkedEkSentCt1ReceivedAt
   chunkedEkSentCt1ReceivedSize chunkedHeaderSentAt chunkedHeaderSentSize dropGluePoly16Stack
   dropStack32 dropStackPoly64 vecPtListOf)
open CryptoVerification.SpqrV1.Poly (polyArrayBytes)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable)
open CryptoVerification.SpqrV1.States.Recv
  (SendEkSpills TraceCalleeSaved ValidStatesTag bv376_toNat cell48_4088_entails_memRegion_4144
   epilogueRecvOutPartA epilogueRecvOutPartB epilogueRecvStackPartA epilogueRecvStackPartB
   memRegion_4144_split_cell48 out_488_add_8 out_888_add_16 out_888_add_8 out_904_add_8
   sendEkSpillsAt sendEkUnusedAt sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_4096
   sp_sub_4240_add_4144 sp_sub_4240_add_48 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
   sp_sub_96_add_64 sp_sub_96_add_80 sp_sub_96_sub_4096 spqrDeallocSym spqrRustDeallocSym
   stackAt_statesRecvStackX_eq_allocHook stackAt_statesRecvStackX_eq_dropGluePoly16
   stackAt_statesRecvStackX_eq_dropStack32 stackAt_statesRecvStackX_eq_dropStackPoly64
   stackAt_statesRecv_split_96 stackAt_statesRecv_split_fsp stack_restore_statesRecv
   statesRecvArmOffset statesRecvCalleeStackX statesRecvJumpIdx statesRecvJumpTablePlacedAt
   statesRecvJumpTablePlacedExpanded statesRecvRoPlacedAt statesRecvSavedCells statesRecvStackX
   v1RecvSize words63At writebackWords63)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChunkedBudget
  (dropChunkedCt2SampledSpec dropChunkedEkSentCt1ReceivedSpec dropChunkedHeaderSentSpec)
open LibsignalBinary.Proofs.SpqrV1.Drop.SortedSetPtBudget (dropGlueSortedSetPt16Spec)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
  (seq_vm_clean)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
  (drop_chunked_ct2_sampled_cl_on drop_chunked_ek_sent_ct1_received_cl_on
   drop_chunked_header_sent_cl_on drop_glue_sorted_set_pt16_cl_on)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudgetAux
  (align_pre_vm deallocFreeOnlySpec subroutine_ok_deallocFreeOnly)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local arm64_norm, local wp_norm]
  sp_sub_4240_add_4144
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
  out_488_add_8 out_888_add_8 out_888_add_16 out_904_add_8 bv376_toNat
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg

private theorem seq_vm_lscl {prog : Program} {pl : MultiPlacement} {mid tgt : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded pl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ hclm =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hclm hvm hQ))

theorem lsmpl_base_332_eq [LibsignalPlacement] : lsmpl.base 332 = (blkPl_332).base := rfl

/-! ## Prologue (`+0 -> +36`) -/

/-- Relocatable prologue of `States::recv` (Block `332`, `+0 -> +36`) with `VmPreserved s0 s1`
    and `AllocCallPreserved s0 s1`. -/
theorem states_recv_prologue_acp_placed [LibsignalPlacement]
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
        TraceCalleeSaved s1 s0) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc0 ⊢
  dsimp only [lsProg_332]
  rw [stackAt_statesRecv_split_96 s0.sp, stackAt_statesRecv_split_fsp s0.sp]
  nth_rw 1 [memRegion_4144_split_cell48 (s0.sp - 4240#64)]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sp_sub_4240_add_48]
  apply ProofLib.SepWP.exists_left; intro v48
  apply ProofLib.SepWP.exists_left; intro v_fp
  apply ProofLib.SepWP.exists_left; intro v_lr
  apply ProofLib.SepWP.exists_left; intro v_x28
  apply ProofLib.SepWP.exists_left; intro v_x27
  apply ProofLib.SepWP.exists_left; intro v_x26
  apply ProofLib.SepWP.exists_left; intro v_x25
  apply ProofLib.SepWP.exists_left; intro v_x24
  apply ProofLib.SepWP.exists_left; intro v_x23
  apply ProofLib.SepWP.exists_left; intro v_x22
  apply ProofLib.SepWP.exists_left; intro v_x21
  apply ProofLib.SepWP.exists_left; intro v_x20
  apply ProofLib.SepWP.exists_left; intro v_x19
  have hjoin4144 := cell48_4088_entails_memRegion_4144 (s0.sp - 4240#64) 0#64
  rw [sp_sub_4240_add_48] at hjoin4144
  have h4184 : (s0.sp - 4240#64) + 56#64 = s0.sp - 4184#64 := by bv_omega
  rw [h4184] at hjoin4144 ⊢
  refine SepWP.mono (post := fun s1 P1 =>
      VmPreserved s0 s1 ∧
      (P1 ⊢
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        (memRegion (s0.sp - 4240#64) 48 ∗ ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 4184#64) 4088) ∗
        statesRecvSavedCells s0 ∗
        Rest) ∧
      AllocCallPreserved s0 s1 ∧
      s1.sp = s0.sp - 4240#64 ∧
      s1.readReg64 .x0 = s0.readReg64 .x0 ∧
      s1.readReg64 .x1 = s0.readReg64 .x1 ∧
      s1.readReg64 .x2 = s0.readReg64 .x2 ∧
      s1.readReg64 .x3 = s0.readReg64 .x3 ∧
      s1.readReg64 .x29 = s0.sp - 96#64 ∧
      TraceCalleeSaved s1 s0)
    (by
      by_vm_steps (
        wp_steps
        refine align_pre_vm ?_ ?_
        · dsimp only [statesRecvSavedCells, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
            Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.x30]
          simp only [wp_norm, arm64_norm]
          try sep_ac_rfl
        · simp only [AllocCallPreserved, TraceCalleeSaved, Reg.x29, wp_norm, arm64_norm]
          try wp_done
      ))
    (fun _ _ _ _ ⟨hvm, hP1, hq⟩ =>
      ⟨hvm, Entails.trans hP1 (sepConj_mono_right (sepConj_mono_left hjoin4144)), hq⟩)

/-- Relocatable prologue of `States::recv` (Block `332`, `+0 -> +36`) with `VmPreserved s0 s1`. -/
theorem states_recv_prologue_placed [LibsignalPlacement]
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
  SepWP.mono (states_recv_prologue_acp_placed s0 Rest hsp0_align hpc0 hrun0)
    fun _ _ _ _ ⟨hvm, hP1, _, hq⟩ => ⟨hvm, hP1, hq⟩

theorem states_recv_prologue_pool_placed [LibsignalPlacement]
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
  SepWP.mono
    (states_recv_prologue_acp_placed s0 (A.pool lim st_cost s0 ∗ Rest) hsp0_align hpc0 hrun0)
    fun s1 _ _ _ ⟨hvm, hP1, hq⟩ =>
      ⟨hvm, Entails.trans hP1 (Entails.of_eq (by
        rw [A.pool_of_vmPreserved hvm]; try sep_ac_rfl)), hq⟩

/-! ## Shared Direct Epilogue (`+19324 -> s0.x30`) and Tail-Call Epilogues -/

/-- Relocatable shared direct epilogue at `+19324` (Block `332`) with `VmPreserved s1 sf`. -/
theorem states_recv_epilogue_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 19324#64)
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
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_epilogue_19324_placed
    s0 s1 Rest hsp0_align hpc1 hrun1 hsp1 htr1

/-- Relocatable shared direct epilogue at `+19324` (Block `332`) with both `VmPreserved s1 sf`
    and `AllocCallPreserved s1 sf`. -/
theorem states_recv_epilogue_19324_acp_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 19324#64)
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
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_epilogue_19324_acp_placed
    s0 s1 Rest hsp0_align hpc1 hrun1 hsp1 htr1

theorem states_recv_epilogue_19324_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s0 s1 : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 19324#64)
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
  SepWP.mono
    (states_recv_epilogue_19324_acp_placed s0 s1 (A.pool lim st_cost s1 ∗ Rest)
      hsp0_align hpc1 hrun1 hsp1 htr1)
    fun sf _ _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by
        rw [A.pool_of_vmPreserved hvm]; try sep_ac_rfl)), hq⟩

/-- Exact-event budget-threaded relocatable tail-call epilogue at `+192` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `__rust_dealloc(ptr, cap, 1)`,
    and returns to `s0.readReg64 .x30` advancing `st_cost` by `rustDeallocEvents cap.toNat 1`. -/
theorem states_recv_tail_dealloc_192_exact_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          A.pool lim (M.stepEvents (rustDeallocEvents cap.toNat 1) st_cost) sf ∗
          Rest ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s1 sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  have hdealloc_ok : subroutine_ok ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      (lsρ spqrRustDeallocSym) (deallocFreeOnlySpec M A lim) :=
    subroutine_ok_deallocFreeOnly (spqr_hook_ok_of_mem hdealloc)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest ⊢
  refine seq_vm_clean (mid := lsρ spqrRustDeallocSym)
    (P_mid :=
      A.pool lim st_cost s1 ∗
      A.live ptr cap.toNat 1 ∗
      memRegion ptr cap.toNat ∗
      stackAt s0.sp statesRecvStackX ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = ptr ∧
      sc.readReg64 .x1 = cap ∧
      sc.readReg64 .x2 = 1#64 ∧
      sc.readReg64 .x30 = s0.readReg64 .x30 ∧
      AllocCallPreserved s1 sc ∧
      CalleeSavedPreserved s0 sc)
    ?_ ?_
  · refine SepWP.mono (post := fun sc Pc =>
        VmPreserved s1 sc ∧
        (Pc ⊢
          (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
             ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
             ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
          (A.pool lim st_cost s1 ∗
            A.live ptr cap.toNat 1 ∗
            memRegion ptr cap.toNat ∗
            Rest)) ∧
        (sc.sp = s0.sp ∧
         sc.trace = s0.trace ∧
         sc.readReg64 .x0 = ptr ∧
         sc.readReg64 .x1 = cap ∧
         sc.readReg64 .x2 = 1#64 ∧
         sc.readReg64 .x30 = s0.readReg64 .x30 ∧
         AllocCallPreserved s1 sc ∧
         CalleeSavedPreserved s0 sc))
      (by
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, hx0_1, hx1_1, hx2_1, htr1.1, htr1.2, wp_norm, arm64_norm]
          try wp_done
        ))
      (fun _ _ _ _ ⟨hvm, hPc, hq⟩ =>
        ⟨hvm,
         Entails.trans hPc (Entails.trans (sepConj_mono_left hrest) (Entails.of_eq (by sep_ac_rfl))),
         hq⟩)
  · intro sc hpcc hrunc hvmc ⟨hsp_c, htr_c, hx0_c, hx1_c, hx2_c, hlr_c, hacp_c, hcs_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hsp0_align
    have hx1_nat : (sc.readReg64 .x1).toNat = cap.toNat := by rw [hx1_c]
    have hx2_nat : (sc.readReg64 .x2).toNat = 1 := by rw [hx2_c]; rfl
    have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
      dsimp only [Reg.lr, Reg.x30] at hlr_c hlr_ls ⊢
      exact hlr_c ▸ hlr_ls
    rw [stackAt_statesRecvStackX_eq_allocHook s0.sp]
    refine SepWP.call_subroutine_frame hdealloc_ok
      (x := (ptr, cap.toNat, 1, st_cost))
      (F := memRegion (s0.sp - 23792#64) 19696 ∗ Rest)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro Frame hm
      rw [← A.pool_of_vmPreserved hvmc] at hm
      dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec]
      rw [hsp_c]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_c, hx1_nat, hx2_nat, hlr_sc⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold deallocFreeOnlySpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold deallocFreeOnlySpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [deallocFreeOnlySpec]
      rw [hsp_c]
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨htr_sf, hacp_sf⟩ => ?_
      refine SepWP.done hpc_sf hrun_sf ?_
      refine ⟨?_, hsp_sf.trans hsp_c, hacp_c.trans hacp_sf, hcs_c.trans hcs_sf, htr_sf.trans htr_c⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro _ _ _ ho
      unfold deallocFreeOnlySpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

/-- `FreeOnlyEvs`-packaged budget-threaded relocatable tail-call epilogue at `+192` (Block `332`). -/
theorem states_recv_tail_dealloc_192_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (ptr cap : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 192#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = ptr)
    (hx1_1 : s1.readReg64 .x1 = cap)
    (hx2_1 : s1.readReg64 .x2 = 1#64)
    (htr1 : TraceCalleeSaved s1 s0)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        A.live ptr cap.toNat 1 ∗
        memRegion ptr cap.toNat ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  SepWP.mono
    (states_recv_tail_dealloc_192_exact_placed hdealloc st_cost s0 s1 ptr cap Rest
      hsp0_align hpc1 hrun1 hsp1 hx0_1 hx1_1 hx2_1 htr1 hlr_ls)
    fun _ _ _ _ ⟨hPf, hq⟩ =>
      ⟨rustDeallocEvents cap.toNat 1, FreeOnlyEvs.singleton 1 cap.toNat, hPf, hq⟩

theorem subroutine_ok_withMemEq_of_withLsCodeLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α} {m : Memory}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hcl : LibsignalCodeLoaded pl m) :
    subroutine_ok prog entry (withMemEq m spec) :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.subroutine_ok_withMemEq_of_withLsCodeLoaded h hcl

/-- Relocatable budget-threaded tail-call epilogue at `+552` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<EkSentCt1Received>` (Block `278`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ekSentCt1Received_552_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 278)
      (withLsCodeLoaded lsmpl (dropChunkedEkSentCt1ReceivedSpec M A lim F)))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedEkSentCt1ReceivedAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedEkSentCt1ReceivedSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332] at hdrop ⊢
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest ⊢
  refine seq_vm_lscl hcode (mid := lsmpl.base 278)
    (P_mid :=
      chunkedEkSentCt1ReceivedAt A.repAlloc a st ∗
      A.pool lim st_cost s1 ∗
      stackAt s0.sp statesRecvStackX ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = a ∧
      sc.readReg64 .x30 = s0.readReg64 .x30 ∧
      AllocCallPreserved s1 sc ∧
      CalleeSavedPreserved s0 sc)
    ?_ ?_
  · refine SepWP.mono (post := fun sc Pc =>
        VmPreserved s1 sc ∧
        (Pc ⊢
          (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
             ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
             ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
          (chunkedEkSentCt1ReceivedAt A.repAlloc a st ∗
            A.pool lim st_cost s1 ∗
            Rest)) ∧
        (sc.sp = s0.sp ∧
         sc.trace = s0.trace ∧
         sc.readReg64 .x0 = a ∧
         sc.readReg64 .x30 = s0.readReg64 .x30 ∧
         AllocCallPreserved s1 sc ∧
         CalleeSavedPreserved s0 sc))
      (by
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, hx0_1, htr1.1, htr1.2, wp_norm, arm64_norm]
          try wp_done
        ))
      (fun _ _ _ _ ⟨hvm, hPc, hq⟩ =>
        ⟨hvm,
         Entails.trans hPc (Entails.trans (sepConj_mono_left hrest) (Entails.of_eq (by sep_ac_rfl))),
         hq⟩)
  · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hsp0_align
    rw [stackAt_statesRecvStackX_eq_dropStack32 s0.sp]
    refine SepWP.call_subroutine_frame hdrop
      (x := (⟨a, st⟩, st_cost))
      (F := memRegion (s0.sp - 23792#64) 19664 ∗ Rest)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro Frame hm
      rw [← A.pool_of_vmPreserved hvmc] at hm
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hclc, ?_⟩
      dsimp only [dropChunkedEkSentCt1ReceivedSpec]
      rw [hsp_c]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
        dsimp only [Reg.lr, Reg.x30] at hlr_c hlr_ls ⊢
        exact hlr_c ▸ hlr_ls
      exact ⟨⟨hx0_c, hlr_sc⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withLsCodeLoaded dropChunkedEkSentCt1ReceivedSpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withLsCodeLoaded dropChunkedEkSentCt1ReceivedSpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [withLsCodeLoaded, dropChunkedEkSentCt1ReceivedSpec]
      rw [hsp_c, sepExists_sepConj_left]
      apply SepWP.exists_left; intro evs
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨htr_sf, hacp_sf, hevs⟩ => ?_
      refine SepWP.done hpc_sf hrun_sf ?_
      refine ⟨evs, hevs, ?_, hsp_sf.trans hsp_c, hacp_c.trans hacp_sf, hcs_c.trans hcs_sf,
        htr_sf.trans htr_c⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro _ _ _ ho
      unfold withLsCodeLoaded dropChunkedEkSentCt1ReceivedSpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

theorem states_recv_tail_drop_ekSentCt1Received_552_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : EkSentCt1Received spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 552#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedEkSentCt1ReceivedAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedEkSentCt1ReceivedSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  states_recv_tail_drop_ekSentCt1Received_552_placed
    (drop_chunked_ek_sent_ct1_received_cl_on
      (callerProg := lsProg_332 (Rust.withPanics ext)) (idx := 332) hdealloc)
    st_cost s0 s1 a st Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 htr1 hcode hlr_ls

/-- Relocatable budget-threaded tail-call epilogue at `+1168` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<HeaderSent>` (Block `276`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_headerSent_1168_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 276)
      (withLsCodeLoaded lsmpl (dropChunkedHeaderSentSpec M A lim F)))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : HeaderSent spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1168#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedHeaderSentAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedHeaderSentSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332] at hdrop ⊢
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest ⊢
  refine seq_vm_lscl hcode (mid := lsmpl.base 276)
    (P_mid :=
      chunkedHeaderSentAt A.repAlloc a st ∗
      A.pool lim st_cost s1 ∗
      stackAt s0.sp statesRecvStackX ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = a ∧
      sc.readReg64 .x30 = s0.readReg64 .x30 ∧
      AllocCallPreserved s1 sc ∧
      CalleeSavedPreserved s0 sc)
    ?_ ?_
  · refine SepWP.mono (post := fun sc Pc =>
        VmPreserved s1 sc ∧
        (Pc ⊢
          (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
             ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
             ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
          (chunkedHeaderSentAt A.repAlloc a st ∗
            A.pool lim st_cost s1 ∗
            Rest)) ∧
        (sc.sp = s0.sp ∧
         sc.trace = s0.trace ∧
         sc.readReg64 .x0 = a ∧
         sc.readReg64 .x30 = s0.readReg64 .x30 ∧
         AllocCallPreserved s1 sc ∧
         CalleeSavedPreserved s0 sc))
      (by
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, hx0_1, htr1.1, htr1.2, wp_norm, arm64_norm]
          try wp_done
        ))
      (fun _ _ _ _ ⟨hvm, hPc, hq⟩ =>
        ⟨hvm,
         Entails.trans hPc (Entails.trans (sepConj_mono_left hrest) (Entails.of_eq (by sep_ac_rfl))),
         hq⟩)
  · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hsp0_align
    rw [stackAt_statesRecvStackX_eq_dropStackPoly64 s0.sp]
    refine SepWP.call_subroutine_frame hdrop
      (x := (⟨a, st⟩, st_cost))
      (F := memRegion (s0.sp - 23792#64) 19632 ∗ Rest)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro Frame hm
      rw [← A.pool_of_vmPreserved hvmc] at hm
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hclc, ?_⟩
      dsimp only [dropChunkedHeaderSentSpec]
      rw [hsp_c]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
        dsimp only [Reg.lr, Reg.x30] at hlr_c hlr_ls ⊢
        exact hlr_c ▸ hlr_ls
      exact ⟨⟨hx0_c, hlr_sc⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withLsCodeLoaded dropChunkedHeaderSentSpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withLsCodeLoaded dropChunkedHeaderSentSpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [withLsCodeLoaded, dropChunkedHeaderSentSpec]
      rw [hsp_c, sepExists_sepConj_left]
      apply SepWP.exists_left; intro evs
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨htr_sf, hacp_sf, hevs⟩ => ?_
      refine SepWP.done hpc_sf hrun_sf ?_
      refine ⟨evs, hevs, ?_, hsp_sf.trans hsp_c, hacp_c.trans hacp_sf, hcs_c.trans hcs_sf,
        htr_sf.trans htr_c⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro _ _ _ ho
      unfold withLsCodeLoaded dropChunkedHeaderSentSpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

theorem states_recv_tail_drop_headerSent_1168_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : HeaderSent spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1168#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedHeaderSentAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedHeaderSentSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  states_recv_tail_drop_headerSent_1168_placed
    (drop_chunked_header_sent_cl_on (callerProg := lsProg_332 (Rust.withPanics ext)) (idx := 332)
      hdealloc)
    st_cost s0 s1 a st Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 htr1 hcode hlr_ls

/-- Relocatable budget-threaded tail-call epilogue at `+1760` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<[SortedSet<Pt>; 16]>` (Block `264`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_sortedSetPt16_1760_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec M A lim)))
    (st_cost : M.σ) (s0 s1 : State) (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs : vecs.length = NUM_POLYS)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = arrA)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A.repAlloc arrA vecs ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion arrA polyArrayBytes ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332] at hdrop ⊢
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest ⊢
  refine seq_vm_lscl hcode (mid := lsmpl.base 264)
    (P_mid :=
      vecPtListOf A.repAlloc arrA vecs ∗
      A.pool lim st_cost s1 ∗
      stackAt s0.sp statesRecvStackX ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = arrA ∧
      sc.readReg64 .x30 = s0.readReg64 .x30 ∧
      AllocCallPreserved s1 sc ∧
      CalleeSavedPreserved s0 sc)
    ?_ ?_
  · refine SepWP.mono (post := fun sc Pc =>
        VmPreserved s1 sc ∧
        (Pc ⊢
          (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
             ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
             ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
          (vecPtListOf A.repAlloc arrA vecs ∗
            A.pool lim st_cost s1 ∗
            Rest)) ∧
        (sc.sp = s0.sp ∧
         sc.trace = s0.trace ∧
         sc.readReg64 .x0 = arrA ∧
         sc.readReg64 .x30 = s0.readReg64 .x30 ∧
         AllocCallPreserved s1 sc ∧
         CalleeSavedPreserved s0 sc))
      (by
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, hx0_1, htr1.1, htr1.2, wp_norm, arm64_norm]
          try wp_done
        ))
      (fun _ _ _ _ ⟨hvm, hPc, hq⟩ =>
        ⟨hvm,
         Entails.trans hPc (Entails.trans (sepConj_mono_left hrest) (Entails.of_eq (by sep_ac_rfl))),
         hq⟩)
  · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hsp0_align
    rw [stackAt_statesRecvStackX_eq_dropGluePoly16 s0.sp]
    refine SepWP.call_subroutine_frame hdrop
      (x := (⟨arrA, vecs⟩, st_cost))
      (F := memRegion (s0.sp - 23792#64) 19664 ∗ Rest)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro Frame hm
      rw [← A.pool_of_vmPreserved hvmc] at hm
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hclc, ?_⟩
      dsimp only [dropGlueSortedSetPt16Spec]
      rw [hsp_c]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
        dsimp only [Reg.lr, Reg.x30] at hlr_c hlr_ls ⊢
        exact hlr_c ▸ hlr_ls
      exact ⟨⟨hx0_c, hvecs, hlr_sc⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withLsCodeLoaded dropGlueSortedSetPt16Spec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withLsCodeLoaded dropGlueSortedSetPt16Spec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [withLsCodeLoaded, dropGlueSortedSetPt16Spec]
      rw [hsp_c, sepExists_sepConj_left]
      apply SepWP.exists_left; intro evs
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨htr_sf, hacp_sf, hevs⟩ => ?_
      refine SepWP.done hpc_sf hrun_sf ?_
      refine ⟨evs, hevs, ?_, hsp_sf.trans hsp_c, hacp_c.trans hacp_sf, hcs_c.trans hcs_sf,
        htr_sf.trans htr_c⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro _ _ _ ho
      unfold withLsCodeLoaded dropGlueSortedSetPt16Spec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

theorem states_recv_tail_drop_sortedSetPt16_1760_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (arrA : BitVec 64) (vecs : List (List Pt))
    (hvecs : vecs.length = NUM_POLYS)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 1760#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = arrA)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        vecPtListOf A.repAlloc arrA vecs ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion arrA polyArrayBytes ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  states_recv_tail_drop_sortedSetPt16_1760_placed
    (drop_glue_sorted_set_pt16_cl_on (callerProg := lsProg_332 (Rust.withPanics ext)) (idx := 332)
      hdealloc)
    st_cost s0 s1 arrA vecs hvecs Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 htr1 hcode hlr_ls

/-- Relocatable budget-threaded tail-call epilogue at `+10952` (Block `332`):
    restores `sp = s0.sp` and `x19..x30`, tail-calls `drop_glue::<Ct2Sampled>` (Block `274`),
    and returns to `s0.readReg64 .x30`. -/
theorem states_recv_tail_drop_ct2Sampled_10952_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 274)
      (withLsCodeLoaded lsmpl (dropChunkedCt2SampledSpec M A lim F)))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 10952#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedCt2SampledAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedCt2SampledSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332] at hdrop ⊢
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest ⊢
  refine seq_vm_lscl hcode (mid := lsmpl.base 274)
    (P_mid :=
      chunkedCt2SampledAt A.repAlloc a st ∗
      A.pool lim st_cost s1 ∗
      stackAt s0.sp statesRecvStackX ∗
      Rest)
    (Q := fun sc =>
      sc.sp = s0.sp ∧
      sc.trace = s0.trace ∧
      sc.readReg64 .x0 = a ∧
      sc.readReg64 .x30 = s0.readReg64 .x30 ∧
      AllocCallPreserved s1 sc ∧
      CalleeSavedPreserved s0 sc)
    ?_ ?_
  · refine SepWP.mono (post := fun sc Pc =>
        VmPreserved s1 sc ∧
        (Pc ⊢
          (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
            memRegion (s0.sp - 4240#64) 4144 ∗
            (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
             ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
             ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
             ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
             ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
             ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
             ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
             ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗
          (chunkedCt2SampledAt A.repAlloc a st ∗
            A.pool lim st_cost s1 ∗
            Rest)) ∧
        (sc.sp = s0.sp ∧
         sc.trace = s0.trace ∧
         sc.readReg64 .x0 = a ∧
         sc.readReg64 .x30 = s0.readReg64 .x30 ∧
         AllocCallPreserved s1 sc ∧
         CalleeSavedPreserved s0 sc))
      (by
        by_vm_steps (
          wp_steps
          refine align_pre_vm (by simp only [wp_norm, arm64_norm]; try sep_ac_rfl) ?_
          simp only [AllocCallPreserved, hx0_1, htr1.1, htr1.2, wp_norm, arm64_norm]
          try wp_done
        ))
      (fun _ _ _ _ ⟨hvm, hPc, hq⟩ =>
        ⟨hvm,
         Entails.trans hPc (Entails.trans (sepConj_mono_left hrest) (Entails.of_eq (by sep_ac_rfl))),
         hq⟩)
  · intro sc hpcc hrunc hclc hvmc ⟨hsp_c, htr_c, hx0_c, hlr_c, hacp_c, hcs_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hsp0_align
    rw [stackAt_statesRecvStackX_eq_dropStack32 s0.sp]
    refine SepWP.call_subroutine_frame hdrop
      (x := (⟨a, st⟩, st_cost))
      (F := memRegion (s0.sp - 23792#64) 19664 ∗ Rest)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro Frame hm
      rw [← A.pool_of_vmPreserved hvmc] at hm
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hclc, ?_⟩
      dsimp only [dropChunkedCt2SampledSpec]
      rw [hsp_c]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      have hlr_sc : LsRetAddr624 (sc.readReg64 .lr) := by
        dsimp only [Reg.lr, Reg.x30] at hlr_c hlr_ls ⊢
        exact hlr_c ▸ hlr_ls
      exact ⟨⟨hx0_c, hlr_sc⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withLsCodeLoaded dropChunkedCt2SampledSpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withLsCodeLoaded dropChunkedCt2SampledSpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf hpc_sf hrun_sf hsp_sf hcs_sf
      dsimp only [withLsCodeLoaded, dropChunkedCt2SampledSpec]
      rw [hsp_c, sepExists_sepConj_left]
      apply SepWP.exists_left; intro evs
      simp only [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨htr_sf, hacp_sf, hevs⟩ => ?_
      refine SepWP.done hpc_sf hrun_sf ?_
      refine ⟨evs, hevs, ?_, hsp_sf.trans hsp_c, hacp_c.trans hacp_sf, hcs_c.trans hcs_sf,
        htr_sf.trans htr_c⟩
      exact Entails.of_eq (by sep_ac_rfl)
    · intro _ _ _ ho
      unfold withLsCodeLoaded dropChunkedCt2SampledSpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

theorem states_recv_tail_drop_ct2Sampled_10952_dealloc_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (st_cost : M.σ) (s0 s1 : State) (a : BitVec 64)
    (st : Ct2Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc1 : s1.pc = lsmpl.base 332 + 10952#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = s0.sp - 4240#64)
    (hx0_1 : s1.readReg64 .x0 = a)
    (htr1 : TraceCalleeSaved s1 s0)
    (hcode : LibsignalCodeLoaded lsmpl s1.mem)
    (hlr_ls : LsRetAddr624 (s0.readReg64 .x30) := by
      first
      | assumption
      | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s1
      (stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        chunkedCt2SampledAt A.repAlloc a st ∗
        A.pool lim st_cost s1 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            memRegion a chunkedCt2SampledSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            Rest ∗
            stackAt s0.sp statesRecvStackX) ∧
          sf.sp = s0.sp ∧
          AllocCallPreserved s1 sf ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  states_recv_tail_drop_ct2Sampled_10952_placed
    (drop_chunked_ct2_sampled_cl_on (callerProg := lsProg_332 (Rust.withPanics ext)) (idx := 332)
      hdealloc)
    st_cost s0 s1 a st Rest hsp0_align hpc1 hrun1 hsp1 hx0_1 htr1 hcode hlr_ls

/-! ## Relocatable Jump-Table Dispatch (`+36 -> +statesRecvArmOffset tag`) -/

theorem statesRecvJumpTablePlacedAt_eq [LibsignalPlacement] :
    statesRecvJumpTablePlacedAt = statesRecvJumpTablePlacedExpanded :=
  LibsignalBinary.Proofs.SpqrV1.States.Recv.statesRecvJumpTablePlacedAt_eq

/-- Relocatable jump-table dispatch (`+36 -> +statesRecvArmOffset tag` in Block `332`)
    with `VmPreserved s1 s2`. -/
theorem states_recv_dispatch_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : ValidStatesTag tag)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + statesRecvArmOffset tag)
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
        s2.readReg64 .x8 = statesRecvJumpIdx tag ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) :=
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_dispatch_placed
    s1 fsp st_ptr tag Rest htag hpc1 hrun1 hsp1 hx1_1

theorem states_recv_dispatch_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ) (s1 : State) (fsp st_ptr tag : BitVec 64) (Rest : SepProp)
    (htag : ValidStatesTag tag)
    (hpc1 : s1.pc = lsmpl.base 332 + 36#64)
    (hrun1 : s1.status = .Running)
    (hsp1 : s1.sp = fsp)
    (hx1_1 : s1.readReg64 .x1 = st_ptr) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + statesRecvArmOffset tag)
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
        s2.readReg64 .x8 = statesRecvJumpIdx tag ∧
        s2.readReg64 .x12 = tag ∧
        s2.readReg64 .x19 = s1.readReg64 .x0 ∧
        s2.readReg64 .x21 = fsp + 3856#64 ∧
        s2.readReg64 .x24 = s1.readReg64 .x2 ∧
        s2.readReg64 .x28 = fsp + 3272#64 ∧
        s2.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved s2 s1) :=
  SepWP.mono
    (states_recv_dispatch_placed s1 fsp st_ptr tag (A.pool lim st_cost s1 ∗ Rest)
      htag hpc1 hrun1 hsp1 hx1_1)
    fun s2 _ _ _ ⟨hvm, hP2, hq⟩ =>
      ⟨hvm, Entails.trans hP2 (Entails.of_eq (by
        rw [A.pool_of_vmPreserved hvm]; try sep_ac_rfl)), hq⟩

/-! ## Relocatable Shared `Ok(V1Recv)` Store Epilogue (`+18940 / +18996 -> +19324`) -/

theorem epilogue_step_18940_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp : BitVec 64)
    (w8 w56 w64 w96 w128 w136 w152 w160 w168 w176 w184 w192 w216 u368 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 18940#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 18996#64)
      s
      (((fsp + 8#64) ↦₆₄ w8) ∗
       ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
       ((fsp + 96#64) ↦₆₄ w96) ∗
       ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
       ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
       ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
       ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
       ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ u368) ∗
       Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          ((fsp + 8#64) ↦₆₄ w8) ∗
          ((fsp + 56#64) ↦₆₄ w56) ∗ ((fsp + 64#64) ↦₆₄ w64) ∗
          ((fsp + 96#64) ↦₆₄ w96) ∗
          ((fsp + 128#64) ↦₆₄ w128) ∗ ((fsp + 136#64) ↦₆₄ w136) ∗
          ((fsp + 152#64) ↦₆₄ w152) ∗ ((fsp + 160#64) ↦₆₄ w160) ∗
          ((fsp + 168#64) ↦₆₄ w168) ∗ ((fsp + 176#64) ↦₆₄ w176) ∗
          ((fsp + 184#64) ↦₆₄ w184) ∗ ((fsp + 192#64) ↦₆₄ w192) ∗
          ((fsp + 216#64) ↦₆₄ w216) ∗ ((fsp + 368#64) ↦₆₄ s.readReg64 .x0) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = s.readReg64 .x11 ∧
        sm.readReg64 .x1 = w136 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x4 = w184 ∧
        sm.readReg64 .x5 = w216 ∧
        sm.readReg64 .x6 = w56 ∧
        sm.readReg64 .x7 = w64 ∧
        sm.readReg64 .x8 = s.readReg64 .x14 ∧
        sm.readReg64 .x9 = w192 ∧
        sm.readReg64 .x10 = s.readReg64 .x10 ∧
        sm.readReg64 .x11 = s.readReg64 .x20 ∧
        sm.readReg64 .x12 = s.readReg64 .x12 ∧
        sm.readReg64 .x13 = w8 ∧
        sm.readReg64 .x14 = s.readReg64 .x17 ∧
        sm.readReg64 .x15 = s.readReg64 .x15 ∧
        sm.readReg64 .x16 = w96 ∧
        sm.readReg64 .x17 = s.readReg64 .x27 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x22 = w176 ∧
        sm.readReg64 .x23 = w152 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = w168 ∧
        sm.readReg64 .x27 = w160 ∧
        sm.readReg64 .x28 = w128 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 .x30 = s.readReg64 .x30 ∧
        TraceCalleeSaved sm s) := by
  subst hsp
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  by_vm_steps (
    wp_steps
    wp_done
  )

set_option maxHeartbeats 1200000 in
theorem epilogue_step_18996_19128_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : BitVec 64)
    (u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 : BitVec 64)
    (w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 : BitVec 64)
    (q960 : BitVec 128)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19128#64)
      s
      (epilogueRecvOutPartA out u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112
         u264 u272 u280 u288 u296 u304 u312 u320 u328 u336 u344 u352 u392 u400 u424 u432 ∗
       epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
       Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          epilogueRecvOutPartA out
            w224 (s.readReg64 .x1) (s.readReg64 .x8) w496
            w456 w376 w368 w504
            w288 w432 w408 w352
            w384 w336 w296
            (s.readReg64 .x25) (s.readReg64 .x12) (s.readReg64 .x11) (s.readReg64 .x10)
            (s.readReg64 .x15) (s.readReg64 .x28) (s.readReg64 .x7) (s.readReg64 .x0)
            (s.readReg64 .x6) (s.readReg64 .x30) (s.readReg64 .x21) (s.readReg64 .x9)
            (s.readReg64 .x5) (s.readReg64 .x4) (s.readReg64 .x13) (s.readReg64 .x14) ∗
          epilogueRecvStackPartA fsp w224 w288 w296 w336 w352 w368 w376 w384 w408 w432 w456 w496 w504 q960 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = s.readReg64 .x2 ∧
        sm.readReg64 .x3 = s.readReg64 .x3 ∧
        sm.readReg64 .x16 = s.readReg64 .x16 ∧
        sm.readReg64 .x17 = s.readReg64 .x17 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readVReg128 0#5 = q960 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  by_vm_steps (
    wp_simp_pre [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
    wp_steps
    simp only [epilogueRecvOutPartA, epilogueRecvStackPartA, pointsTo128, sepConj_assoc]
    wp_done
  )

set_option maxHeartbeats 1600000 in
theorem epilogue_step_19128_19280_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp out : BitVec 64)
    (u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256 : BitVec 64)
    (u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 : BitVec 64)
    (uq488 : BitVec 128) (u504 : BitVec 64)
    (w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 19128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19280#64)
      s
      (epilogueRecvOutPartB out u120 u128 u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u232 u240 u248 u256
         u360 u368 u376 u384 u408 u416 u440 u448 u456 u464 u472 u480 uq488 u504 ∗
       epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
       Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          epilogueRecvOutPartB out
            w424 (s.readReg64 .x23) (s.readReg64 .x27) w440
            w264 w344 w392 w272
            w360 w400 w464 w304
            w328 w280 w320 (s.readReg64 .x3)
            w312 (s.readReg64 .x24)
            w416 (s.readReg64 .x17) w472 (s.readReg64 .x26)
            w448 (s.readReg64 .x22)
            w480 (s.readReg64 .x16) w488 (s.readReg64 .x2)
            w248 (s.readReg64 .x20)
            (s.readVReg128 0#5) w256 ∗
          epilogueRecvStackPartB fsp w248 w256 w264 w272 w280 w304 w312 w320 w328 w344 w360 w392 w400 w416 w424 w440 w448 w464 w472 w480 w488 ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = out + 512#64 ∧
        sm.readReg64 .x1 = fsp + 576#64 ∧
        sm.readReg64 .x2 = 376#64 ∧
        sm.readReg64 .x19 = out ∧
        sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        TraceCalleeSaved sm s) := by
  subst hsp hx19
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  by_vm_steps (
    wp_simp_pre [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
    wp_steps
    simp only [epilogueRecvOutPartB, epilogueRecvStackPartB, pointsTo128, sepConj_assoc]
    wp_done
  )

theorem epilogue_step_19280_19324_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s : State) (fsp out : BitVec 64)
    (bs576 : List (BitVec 8)) (hbs576 : bs576.length = 376)
    (uq888 uq904 uq944 q512 q528 q544 : BitVec 128)
    (u920 u928 u936 w232 w560 : BitVec 64)
    (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = lsmpl.base 332 + 19280#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = out + 512#64)
    (hx1 : s.readReg64 .x1 = fsp + 576#64)
    (hx2 : s.readReg64 .x2 = 376#64)
    (hx19 : s.readReg64 .x19 = out) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332 + 19324#64)
      s
      (stackAt fsp allocHookStack ∗
       memRegion (out + 512#64) 376 ∗
       ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
       ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
       ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
       ((fsp + 232#64) ↦₆₄ w232) ∗
       ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
       ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
       ((fsp + 576#64) ↦ₛ bs576) ∗
       Frame)
      (fun sm Pm =>
        VmPreserved s sm ∧
        (Pm ⊢
          stackAt fsp allocHookStack ∗
          ((out + 512#64) ↦ₛ bs576) ∗
          ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
          ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
          ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
          ((fsp + 232#64) ↦₆₄ w232) ∗
          ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
          ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
          ((fsp + 576#64) ↦ₛ bs576) ∗
          Frame) ∧
        sm.sp = fsp ∧
        TraceCalleeSaved sm s) := by
  have hmemcpy : subroutine_ok ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      (lsρ "memcpy") (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem hmemcpy_sat
  rw [lsmpl_base_332_eq] at hpc ⊢
  dsimp only [lsProg_332]
  refine seq_vm_clean (mid := lsρ "memcpy")
    (P_mid :=
      stackAt fsp allocHookStack ∗
      memRegion (out + 512#64) 376 ∗
      ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
      ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
      ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
      ((fsp + 232#64) ↦₆₄ w232) ∗
      ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
      ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
      ((fsp + 576#64) ↦ₛ bs576) ∗
      Frame)
    (Q := fun sc =>
      sc.sp = fsp ∧
      sc.readReg64 .lr = (blkPl_332).base + 19284#64 ∧
      sc.readReg64 .x0 = out + 512#64 ∧
      sc.readReg64 .x1 = fsp + 576#64 ∧
      (sc.readReg64 .x2).toNat = 376 ∧
      sc.readReg64 .x19 = out ∧
      sc.readReg64 .x20 = s.readReg64 .x20 ∧
      TraceCalleeSaved sc s)
    ?_ ?_
  · by_vm_steps (
      wp_steps
      simp only [TraceCalleeSaved, Reg.x29, hsp, hx0, hx1, hx2, hx19, bv376_toNat, wp_norm, arm64_norm]
      wp_done
    )
  · intro sc hpcc hrunc hvm_sc ⟨hsp_c, hlr_c, hx0_c, hx1_c, hx2_c, hx19_c, hx20_c, htr_c⟩
    have hsp_align_c : sc.spAligned = true := by
      rw [State.spAligned, hsp_c]; exact hfsp_align
    refine SepWP.call_subroutine_frame hmemcpy
      (x := (out + 512#64, fsp + 576#64, bs576))
      (F :=
        ((out + 888#64) ↦₁₂₈ uq888) ∗ ((out + 904#64) ↦₁₂₈ uq904) ∗
        ((out + 920#64) ↦₆₄ u920) ∗ ((out + 928#64) ↦₆₄ u928) ∗
        ((out + 936#64) ↦₆₄ u936) ∗ ((out + 944#64) ↦₁₂₈ uq944) ∗
        ((fsp + 232#64) ↦₆₄ w232) ∗
        ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
        ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
        Frame)
      hpcc hrunc hsp_align_c hlr_c ?_ ?_ ?_ ?_ ?_
    · intro R hm
      dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack,
        allocHookStack] at hm ⊢
      rw [hbs576, hsp_c, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_c, hx1_c, hx2_c⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
    · intro _ _ _ hp
      unfold withVmPreserved sessionMemcpySpec at hp; dsimp only at hp
      exact ((satisfies_pure_sepConj _ _ _).mp hp).1
    · intro _ _ _ _ he
      unfold withVmPreserved sessionMemcpySpec at he; dsimp only at he
      exact ((satisfies_pure_sepConj _ _ _).mp he).1
    · intro sf1 hpc1 hrun1 hsp1 hcs1
      dsimp only [withVmPreserved, sessionMemcpySpec, allocHookStack]
      rw [hsp_c, sepConj_assoc, sepConj_assoc]
      refine SepWP.pure_elim fun hvm1 => ?_
      refine SepWP.pure_elim fun ⟨_, htr1⟩ => ?_
      have hsp_1 : sf1.sp = fsp := hsp1.trans hsp_c
      have hx19_1 : sf1.readReg64 .x19 = out := hcs1.1.trans hx19_c
      have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1.trans hx20_c
      have htr_s1 : TraceCalleeSaved sf1 s :=
        ⟨htr1.trans htr_c.1, hcs1.2.2.2.2.2.2.2.2.2.2.2.trans htr_c.2⟩
      have hvm_s1 : VmPreserved s sf1 := hvm_sc.trans hvm1
      refine SepWP.mono (post := fun sm Pm =>
          VmPreserved sf1 sm ∧
          (Pm ⊢
            stackAt fsp allocHookStack ∗
            ((out + 512#64) ↦ₛ bs576) ∗
            ((out + 888#64) ↦₁₂₈ q528) ∗ ((out + 904#64) ↦₁₂₈ q544) ∗
            ((out + 920#64) ↦₆₄ w560) ∗ ((out + 928#64) ↦₆₄ w232) ∗
            ((out + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((out + 944#64) ↦₁₂₈ q512) ∗
            ((fsp + 232#64) ↦₆₄ w232) ∗
            ((fsp + 512#64) ↦₁₂₈ q512) ∗ ((fsp + 528#64) ↦₁₂₈ q528) ∗
            ((fsp + 544#64) ↦₁₂₈ q544) ∗ ((fsp + 560#64) ↦₆₄ w560) ∗
            ((fsp + 576#64) ↦ₛ bs576) ∗
            Frame) ∧
          (sm.sp = fsp ∧ TraceCalleeSaved sm s))
        (by
          by_vm_steps (
            wp_simp_pre [pointsTo128, sepConj_assoc, allocHookStack]
            wp_steps
            refine align_pre_vm ?_ ?_
            · simp only [pointsTo128, sepConj_assoc, allocHookStack, hx19_1, hx20_1, hsp_1,
                wp_norm, arm64_norm]
              try sep_ac_rfl
            · simp only [TraceCalleeSaved, Reg.x29, hsp_1, htr_s1.1, htr_s1.2, wp_norm, arm64_norm]
              try wp_done
          ))
        (fun _ _ _ _ ⟨hvm2, hPm, hsp_m, htr_m⟩ => ⟨hvm_s1.trans hvm2, hPm, hsp_m, htr_m⟩)
    · intro _ _ _ ho
      unfold withVmPreserved sessionMemcpySpec at ho; dsimp only at ho
      exact False.elim ((satisfies_pure_sepConj _ _ _).mp ho).1

/-- `HookSat`-parameterized shared `Ok(V1Recv)` writeback + epilogue (`+18996 -> s0.x30`, Block `332`). -/
theorem states_recv_writeback_59e88_sat_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy_sat : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          (outA ↦₆₄ sp.b2.w7) ∗
          words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗
          memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_sat_placed
    hmemcpy_sat hrel s0 s outA sp P_rest hpc hrun hsp hsp_align hx19 htr

/-- `subroutine_ok`-parameterized shared `Ok(V1Recv)` writeback + epilogue (`+18996 -> s0.x30`, Block `332`). -/
theorem states_recv_writeback_59e88_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved sessionMemcpyRegionSpec))
    {F_tail : BitVec 64 → SepProp} (hrel : Relocatable 376 F_tail)
    (s0 s : State) (outA : BitVec 64) (sp : SendEkSpills) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = outA)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        memRegion outA v1RecvSize ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        sendEkSpillsAt (s0.sp - 4240#64) sp ∗
        F_tail ((s0.sp - 4240#64) + 576#64) ∗
        memRegion ((s0.sp - 4240#64) + 976#64) 880 ∗
        memRegion ((s0.sp - 4240#64) + 1856#64) 880 ∗
        sendEkUnusedAt (s0.sp - 4240#64) ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢
          P_rest ∗
          (outA ↦₆₄ sp.b2.w7) ∗
          words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗
          memRegion (outA + 888#64) 40 ∗
          ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
          ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
          stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) :=
  ArmNoHeaderReceivedStepsPlacedBudgetAux.states_recv_writeback_59e88_placed
    hmemcpy hrel s0 s outA sp P_rest hpc hrun hsp hsp_align hx19 htr

end LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget
