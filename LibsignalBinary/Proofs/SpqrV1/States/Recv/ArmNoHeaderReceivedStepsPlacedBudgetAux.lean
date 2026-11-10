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
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DropChunkedClPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommon
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.SendEkCommonPlaced
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.GettersCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# `<States>::recv` (Block `332`) — Shared `VmPreserved` Dispatch, Epilogue & Writeback Helpers

Shared Block `332` `VmPreserved` jump-table dispatch (`+36`), direct epilogues (`+19324`),
relocatable `memcpy` call wrappers, and `Ok(V1Recv)` writeback (`+18996 -> s0.x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoVerification (LibsignalPlacement blkPC_332 blkPC_332_pairStep_0x48 blkPl_332 libsignalSessionCode lsProg_332 lsmpl lsρ)
open CryptoVerification.LibsignalTripleRatchet (memcpyName sessionMemcpyRegionSpec sessionMemcpySpec withStack)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.States.Leaves (Relocatable relocate_post_entails relocate_pre_entails relocatedHeap)
open CryptoVerification.SpqrV1.States.Recv (SendEkSpills TraceCalleeSaved ValidStatesTag Words63 bv376_toNat bv_add_lit_add_lit_recv bv_sub_sub_recv memRegion_960_entails_writebackOut out_488_add_8 out_888_add_16 out_888_add_8 out_904_add_8 pointsTo128_eq_pair64_recv q2_w1_entails_memRegion_40 sendEkFrame_entails_memRegion_4144 sendEkSpillsAt sendEkUnusedAt sp_sub_144_add_48 sp_sub_16_add_8_recv sp_sub_32_add_8_recv sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_4240_add_4144 sp_sub_4240_add_48 sp_sub_48_add_8_recv sp_sub_64_add_8_recv sp_sub_80_add_8_recv sp_sub_96_add_8_recv sp_sub_96_add_96_recv sp_sub_96_sub_4096 stackAt_statesRecvCallee_eq_allocHook stack_restore_statesRecv statesRecvArmOffset statesRecvCalleeStackX statesRecvJumpIdx statesRecvJumpTablePlacedExpanded statesRecvJumpTableSym statesRecvRoPlacedAt statesRecvSavedCells statesRecvStackX v1RecvSize words10At words63At writebackWords63)

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap (AllocCallPreserved VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_sub_recv bv_add_lit_add_lit_recv
  BitVec.sub_add_cancel BitVec.toNat_zero
  CryptoVerification.SpqrV1.States.Leaves.extractLsb'_0_64_append CryptoVerification.SpqrV1.States.Leaves.extractLsb'_64_64_append
  sp_sub_4240_add_4144
  CryptoVerification.SpqrV1.States.Recv.sp_sub_96_add_16 CryptoVerification.SpqrV1.States.Recv.sp_sub_96_add_32 CryptoVerification.SpqrV1.States.Recv.sp_sub_96_add_48
  CryptoVerification.SpqrV1.States.Recv.sp_sub_96_add_64 CryptoVerification.SpqrV1.States.Recv.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_4096 sp_sub_144_add_48 sp_sub_4240_add_48
  sp_sub_96_add_8_recv sp_sub_80_add_8_recv sp_sub_64_add_8_recv
  sp_sub_48_add_8_recv sp_sub_32_add_8_recv sp_sub_16_add_8_recv sp_sub_96_add_96_recv
  out_488_add_8 out_888_add_8 out_888_add_16 out_904_add_8 bv376_toNat

/-! ## 1. `VmPreserved` Sequencing & `ADRP` Helpers -/

/-- Sequence a `VmPreserved` segment before an arbitrary continuation on `prog`. -/
theorem seq_vm_clean {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running → VmPreserved s sm → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ _ _ => trivial) trivial
    (SepWP.mono h1 fun sm _ hpc hrun ⟨hvm, hPm, hQ⟩ _ =>
      SepWP.weaken_pre hPm (h2 sm hpc hrun hvm hQ))

/-- Continuation-passing `VmPreserved` cut combinator (avoids spelling out intermediate `P_mid` / `Q`). -/
theorem seq_vm_cont {prog : Program} {mid tgt : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (h : SepWP prog mid s Pre
      (fun sm Pm => VmPreserved s sm ∧ (VmPreserved s sm → SepWP prog tgt sm Pm post))) :
    SepWP prog tgt s Pre post :=
  SepWP.seq (SepWP.mono h fun _ _ _ _ ⟨hvm, hk⟩ => hk hvm) fun _ _ _ _ hwp => hwp

/-- Step across a `blkPC_332_pairStep_*` (`ADRP`) transition while preserving `VmPreserved`. -/
theorem step_adrp_vm {P : Program} {s0 s : State} {rd : BitVec 5} {v next_pc tgt : BitVec 64}
    {Pre : SepProp} {post : State → SepProp → Prop}
    (hvm0 : VmPreserved s0 s)
    (hpair : SepWP P tgt ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) Pre
      (fun sm Pm => VmPreserved ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) sm ∧ post sm Pm) →
      SepWP P tgt s Pre
      (fun sm Pm => VmPreserved ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) sm ∧ post sm Pm))
    (hnext : SepWP P tgt ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) Pre
      (fun sm Pm => VmPreserved ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) sm ∧ post sm Pm)) :
    SepWP P tgt s Pre (fun sm Pm => VmPreserved s0 sm ∧ post sm Pm) :=
  SepWP.mono (hpair hnext) fun _ _ _ _ ⟨hvm1, hp⟩ =>
    ⟨hvm0.trans ((show VmPreserved s ((s.writeReg64 (Reg.gpr rd) v).setPC next_pc) by
      simp [LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_setPC,
        LibsignalBinary.Proofs.Placed.BudgetVmSteps.vmPreserved_writeReg64]).trans hvm1), hp⟩

/-! ## 2. Jump-Table Dispatch & Direct Epilogues (`+36`, `+19324`) -/

set_option maxHeartbeats 1200000 in
/-- Relocatable jump-table dispatch (`+36 -> +statesRecvArmOffset tag` in Block `332`) with `VmPreserved`. -/
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
        TraceCalleeSaved s2 s1) := by
  subst hsp1 hx1_1
  rw [lsmpl_base_332_eq] at hpc1 ⊢
  dsimp only [lsProg_332]
  rcases htag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · dsimp [statesRecvArmOffset, statesRecvJumpIdx]
    refine seq_vm_clean (mid := (blkPl_332).base + 72#64)
      (P_mid := (s1.readReg64 .x1 ↦₆₄ _) ∗ statesRecvRoPlacedAt ∗ Rest)
      (Q := fun sm =>
        sm.sp = s1.sp ∧
        sm.readReg64 .x0 = s1.readReg64 .x0 ∧
        sm.readReg64 .x1 = s1.readReg64 .x1 ∧
        sm.readReg64 .x2 = s1.readReg64 .x2 ∧
        sm.readReg64 .x3 = s1.readReg64 .x3 ∧
        sm.readReg64 .x8 = _ ∧
        sm.readReg64 .x12 = _ ∧
        sm.readReg64 .x19 = s1.readReg64 .x0 ∧
        sm.readReg64 .x21 = s1.sp + 3856#64 ∧
        sm.readReg64 .x24 = s1.readReg64 .x2 ∧
        sm.readReg64 .x28 = s1.sp + 3272#64 ∧
        sm.readReg64 .x29 = s1.readReg64 .x29 ∧
        TraceCalleeSaved sm s1)
      (by wp_steps_vm) ?_
    intro sm hpcm hrunm hvmm ⟨hsp_m, hx0_m, hx1_m, hx2_m, hx3_m, hx8_m, hx12_m, hx19_m, hx21_m, hx24_m, hx28_m, hx29_m, htr_m1, htr_m2⟩
    refine step_adrp_vm hvmm (blkPC_332_pairStep_0x48 (blkPl_332).base (Rust.withPanics ext) rfl hpcm hrunm) ?_
    dsimp only [statesRecvRoPlacedAt]
    rw [statesRecvJumpTablePlacedAt_eq]
    dsimp only [statesRecvJumpTablePlacedExpanded, statesRecvJumpTableSym, BitVec.ofNat_eq_ofNat]
    by_vm_steps (
      wp_steps
      simp only [TraceCalleeSaved, Reg.x29, hx0_m, hx1_m, hx2_m, hx3_m, hx8_m, hx12_m, hx19_m, hx21_m, hx24_m, hx28_m, hx29_m, hsp_m, htr_m1, htr_m2, wp_norm, arm64_norm]
      wp_done
    )

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
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.mono (post := fun sf Pf =>
      VmPreserved s1 sf ∧
      (Pf ⊢ Rest ∗
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
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
      sf.sp = s0.sp ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace)
    (by
      by_vm_steps (
        wp_steps
        refine DropChunkedClPlacedBudgetAux.align_pre_vm (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      ))
    (fun _ _ _ _ ⟨hvm, hPf, hq⟩ => ⟨hvm, Entails.trans hPf (sepConj_mono_right hrest), hq⟩)

/-- Relocatable shared epilogue `+19324 -> +19356` (Block `332`) with `P_rest` first and `VmPreserved s sf`. -/
theorem states_recv_epilogue_59fd0_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 19324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ P_rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [show P_rest ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 =
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        P_rest by sep_ac_rfl]
  exact states_recv_epilogue_19324_placed s0 s P_rest hsp_align hpc hrun hsp htr

abbrev epilogue_19324_ret_placed := @states_recv_epilogue_59fd0_placed

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
        sf.trace = s0.trace) := by
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  rw [lsmpl_base_332_eq] at hpc1
  dsimp only [lsProg_332]
  unfold statesRecvSavedCells
  have hrest := stack_restore_statesRecv s0
  unfold statesRecvSavedCells at hrest
  refine SepWP.mono (post := fun sf Pf =>
      VmPreserved s1 sf ∧
      (Pf ⊢ Rest ∗
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
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))) ∧
      sf.sp = s0.sp ∧
      AllocCallPreserved s1 sf ∧
      CalleeSavedPreserved s0 sf ∧
      sf.trace = s0.trace)
    (by
      by_vm_steps (
        wp_steps
        refine DropChunkedClPlacedBudgetAux.align_pre_vm (by simp only [wp_norm, arm64_norm]; sep_ac_rfl) ?_
        wp_done
      ))
    (fun _ _ _ _ ⟨hvm, hPf, hq⟩ => ⟨hvm, Entails.trans hPf (sepConj_mono_right hrest), hq⟩)

/-- Relocatable shared epilogue `+19324 -> +19356` (Block `332`) with `P_rest` first,
    `VmPreserved s sf`, and `AllocCallPreserved s sf`. -/
theorem states_recv_epilogue_59fd0_acp_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s0 s : State) (P_rest : SepProp)
    (hpc : s.pc = lsmpl.base 332 + 19324#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4240#64)
    (hsp_align : s0.spAligned = true)
    (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (P_rest ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0)
      (fun sf Pf =>
        VmPreserved s sf ∧
        (Pf ⊢ P_rest ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧
        AllocCallPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  rw [show P_rest ∗
        stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 =
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
        memRegion (s0.sp - 4240#64) 4144 ∗
        statesRecvSavedCells s0 ∗
        P_rest by sep_ac_rfl]
  exact states_recv_epilogue_19324_acp_placed s0 s P_rest hsp_align hpc hrun hsp htr

/-! ## 3. Relocatable `memcpy` Call Helpers (`withVmPreserved`) -/

/-- Region-only `memcpy` relocation call rule (`withVmPreserved sessionMemcpyRegionSpec`) forwarding `VmPreserved s sf`. -/
theorem call_memcpy_relocate_cs {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → VmPreserved s sf → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.fold (relocate_pre_entails hrel dst src Frame) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · dsimp only [withVmPreserved, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ relocatedHeap F bs ∗ Frame by sep_ac_rfl)) ?_
    refine SepWP.fold (relocate_post_entails dst src hlen Frame) (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hvm_sf hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Framed `memcpy` relocation call rule (`withVmPreserved (sessionMemcpySpec 4096)`) forwarding `VmPreserved s sf`. -/
theorem call_memcpy_relocate_cs_stack {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved (sessionMemcpySpec 4096)))
    {n : Nat} {F : BitVec 64 → SepProp} (hrel : Relocatable n F)
    (dst src : BitVec 64)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : TraceCalleeSaved s s0)
    (hx0 : s.readReg64 Reg.x0 = dst)
    (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src ∗ stackAt sp_call 4096) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → VmPreserved s sf → CalleeSavedPreserved s sf → TraceCalleeSaved sf s0 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n ∗ stackAt sp_call 4096) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit, show (memRegion dst n ∗ F src ∗ stackAt sp_call 4096) ∗ Frame =
    (memRegion dst n ∗ F src) ∗ (stackAt sp_call 4096 ∗ Frame) by sep_ac_rfl]
  refine SepWP.fold (relocate_pre_entails hrel dst src (stackAt sp_call 4096 ∗ Frame)) (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  wp_pull_exists
  rename_i bs
  refine SepWP.pure_elim fun hlen => ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := relocatedHeap F bs ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack]
    rw [hlen, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
  · dsimp only [withVmPreserved, sessionMemcpySpec]
    rw [hsp, sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm_sf => ?_
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ relocatedHeap F bs ∗ (stackAt sp_call 4096 ∗ Frame) by sep_ac_rfl)) ?_
    refine SepWP.fold (relocate_post_entails dst src hlen (stackAt sp_call 4096 ∗ Frame)) (sepConj_emp _).symm ?_
    rw [sepConj_emp, show (F dst ∗ memRegion src n) ∗ (stackAt sp_call 4096 ∗ Frame) =
      (F dst ∗ memRegion src n ∗ stackAt sp_call 4096) ∗ Frame by sep_ac_rfl]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) hvm_sf hcs_sf
      ⟨htr.trans htrace.1, hcs_sf.2.2.2.2.2.2.2.2.2.2.2.trans htrace.2⟩

/-- Frame `stackAt s0.sp 4096` onto `withVmPreserved sessionMemcpyRegionSpec` to obtain
    `withVmPreserved (sessionMemcpySpec 4096)`. -/
theorem withVmPreserved_sessionMemcpySpec_of_region {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (withVmPreserved sessionMemcpyRegionSpec)) :
    subroutine_ok prog entry (withVmPreserved (sessionMemcpySpec 4096)) := by
  refine subroutine_ok_of_sepWP fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  refine ⟨(withVmPreserved (sessionMemcpySpec 4096)).pre (dst, src, bs) s0, R, hpre, ?_⟩
  dsimp only [withVmPreserved, sessionMemcpySpec, libcMemcpySpec, memcpyRegionSpec, withStack]
  refine SepWP.pure_elim fun ⟨hx0, hx1, hx2⟩ => ?_
  refine SepWP.call_subroutine_frame h (x := (dst, src, bs)) (F := stackAt s0.sp 4096)
    hpc hrun hsp rfl ?_
    (fun _ _ _ hp => ((satisfies_pure_sepConj _ _ _).mp hp).1)
    (fun _ _ _ _ hp => ((satisfies_pure_sepConj _ _ _).mp hp).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro Frame hm
    dsimp only [withVmPreserved, sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm⟩
  · dsimp only [withVmPreserved, sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hx0_f, htr_f⟩ => ?_
    refine SepWP.done hpc_sf hrun_sf ?_
    refine ⟨fun hm => ?_, hsp_sf, hcs_sf⟩
    have hm' : sf.mem ⊨ ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp 4096) ∗ R :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0_f, htr_f⟩, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm'⟩

/-! ## 4. Shared `Ok(V1Recv)` Writeback + Epilogue (`+18996 -> s0.x30`) -/

set_option maxHeartbeats 1600000 in
/-- Pure store segment `+18996 -> +19280` (71 instructions) before `BL memcpy` in Block `332`. -/
theorem writeback_59e88_pre_memcpy_vm [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s : State) (fsp outA v0 : BitVec 64) (w_init : Words63) (sp : SendEkSpills) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 18996#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) :
    SepWP ((blkPC_332).rebase (blkPl_332).base (Rust.withPanics ext))
      ((blkPl_332).base + 19280#64) s
      ((outA ↦₆₄ v0) ∗ words63At (outA + 8#64) w_init ∗ sendEkSpillsAt fsp sp ∗ Frame)
      (fun sc Pm =>
        VmPreserved s sc ∧
        (Pm ⊢ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          sendEkSpillsAt fsp sp ∗ Frame) ∧
        sc.sp = fsp ∧
        sc.readReg64 .x0 = outA + 512#64 ∧
        sc.readReg64 .x1 = fsp + 576#64 ∧
        (sc.readReg64 .x2).toNat = 376 ∧
        sc.readReg64 .x19 = outA ∧
        sc.readReg64 .x20 = s.readReg64 .x20 ∧
        TraceCalleeSaved sc s) := by
  subst hsp hx19
  by_vm_steps (
    wp_conv_pre =>
      dsimp only [sendEkSpillsAt, words63At, words10At]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
    wp_steps
    refine DropChunkedClPlacedBudgetAux.align_pre_vm ?_ ?_
    · dsimp only [words63At, writebackWords63, sendEkSpillsAt, words10At,
        Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6, Reg.x7, Reg.x8, Reg.x9,
        Reg.x10, Reg.x11, Reg.x12, Reg.x13, Reg.x14, Reg.x15, Reg.x16, Reg.x17,
        Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x30]
      simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, wp_norm, arm64_norm]
    · dsimp only [Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x20]
      wp_done
  )

set_option maxHeartbeats 800000 in
/-- Core shared `Ok(V1Recv)` writeback + epilogue (`+18996 -> s0.x30`, Block `332`) with `VmPreserved s sf`. -/
theorem states_recv_writeback_59e88_core_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ memcpyName) (withVmPreserved (sessionMemcpySpec 4096)))
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
        sf.trace = s0.trace) := by
  have hepilogue := @states_recv_epilogue_59fd0_placed _ ext s0
  have hsp_align' : (s0.sp &&& 15#64 == 0#64) = true := hsp_align
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 4240#64 hsp_align (by decide)
  rw [lsmpl_base_332_eq] at hpc hepilogue
  dsimp only [lsProg_332, lsρ, memcpyName] at hmemcpy hepilogue ⊢
  refine SepWP.fold (memRegion_960_entails_writebackOut outA) (by sep_focus) ?_
  wp_pull_exists; rename_i v0 w_init q888 q904 w920 w928 w936 q944
  generalize hsp0 : s0.sp = sp0 at hsp hsp_align' hfsp_align ⊢
  rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64)]
  dsimp only [allocHookStack]
  have h576_eq : (sp0 - 4240#64) + 576#64 = sp0 - 3664#64 := by bv_omega
  refine seq_vm_clean (mid := (blkPl_332).base + 19280#64)
    (P_mid :=
      (memRegion (outA + 512#64) 376 ∗ F_tail (sp0 - 3664#64) ∗ stackAt (sp0 - 4240#64) 4096) ∗
      (P_rest ∗
       (outA ↦₆₄ sp.b2.w7) ∗
       words63At (outA + 8#64) (writebackWords63 s sp) ∗
       ((outA + 888#64) ↦₁₂₈ q888) ∗ ((outA + 904#64) ↦₁₂₈ q904) ∗
       ((outA + 920#64) ↦₆₄ w920) ∗ ((outA + 928#64) ↦₆₄ w928) ∗
       ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       memRegion ((sp0 - 4240#64) - 19552#64) 15456 ∗
       sendEkSpillsAt (sp0 - 4240#64) sp ∗
       memRegion ((sp0 - 4240#64) + 976#64) 880 ∗
       memRegion ((sp0 - 4240#64) + 1856#64) 880 ∗
       sendEkUnusedAt (sp0 - 4240#64) ∗
       statesRecvSavedCells s0))
    (Q := fun sc =>
      sc.sp = sp0 - 4240#64 ∧
      sc.readReg64 .x0 = outA + 512#64 ∧
      sc.readReg64 .x1 = sp0 - 3664#64 ∧
      (sc.readReg64 .x2).toNat = 376 ∧
      sc.readReg64 .x19 = outA ∧
      sc.readReg64 .x20 = s.readReg64 .x20 ∧
      TraceCalleeSaved sc s0)
    ?_ ?_
  · rw [h576_eq]
    refine SepWP.weaken_pre (Entails.of_eq (show _ =
      (outA ↦₆₄ v0) ∗ words63At (outA + 8#64) w_init ∗ sendEkSpillsAt (sp0 - 4240#64) sp ∗
      (P_rest ∗ memRegion (outA + 512#64) 376 ∗
       ((outA + 888#64) ↦₁₂₈ q888) ∗ ((outA + 904#64) ↦₁₂₈ q904) ∗
       ((outA + 920#64) ↦₆₄ w920) ∗ ((outA + 928#64) ↦₆₄ w928) ∗
       ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
       memRegion ((sp0 - 4240#64) - 19552#64) 15456 ∗ stackAt (sp0 - 4240#64) 4096 ∗
       F_tail (sp0 - 3664#64) ∗ memRegion ((sp0 - 4240#64) + 976#64) 880 ∗
       memRegion ((sp0 - 4240#64) + 1856#64) 880 ∗ sendEkUnusedAt (sp0 - 4240#64) ∗
       statesRecvSavedCells s0) by sep_ac_rfl)) ?_
    refine SepWP.mono
      (writeback_59e88_pre_memcpy_vm s (sp0 - 4240#64) outA v0 w_init sp _ hfsp_align hpc hrun hsp hx19)
      fun sc Pm _ _ ⟨hvm0, hPm0, hsp0', hx0_0, hx1_0, hx2_0, hx19_0, hx20_0, htr0⟩ =>
        ⟨hvm0, Entails.trans hPm0 (Entails.of_eq (by sep_ac_rfl)),
         hsp0', hx0_0, hx1_0.trans h576_eq, hx2_0, hx19_0, hx20_0, ⟨htr0.1.trans htr.1, htr0.2.trans htr.2⟩⟩
  · intro sc0 hpcc0 hrunc0 hvm_sc0 ⟨hsp_c0, hx0_c0, hx1_c0, hx2_c0, hx19_c0, hx20_c0, htr_c0_1, htr_c0_2⟩
    refine seq_vm_clean (mid := lsmpl.ρ "memcpy")
      (P_mid :=
        (memRegion (outA + 512#64) 376 ∗ F_tail (sp0 - 3664#64) ∗ stackAt (sp0 - 4240#64) 4096) ∗
        (P_rest ∗
         (outA ↦₆₄ sp.b2.w7) ∗
         words63At (outA + 8#64) (writebackWords63 s sp) ∗
         ((outA + 888#64) ↦₁₂₈ q888) ∗ ((outA + 904#64) ↦₁₂₈ q904) ∗
         ((outA + 920#64) ↦₆₄ w920) ∗ ((outA + 928#64) ↦₆₄ w928) ∗
         ((outA + 936#64) ↦₆₄ w936) ∗ ((outA + 944#64) ↦₁₂₈ q944) ∗
         memRegion ((sp0 - 4240#64) - 19552#64) 15456 ∗
         sendEkSpillsAt (sp0 - 4240#64) sp ∗
         memRegion ((sp0 - 4240#64) + 976#64) 880 ∗
         memRegion ((sp0 - 4240#64) + 1856#64) 880 ∗
         sendEkUnusedAt (sp0 - 4240#64) ∗
         statesRecvSavedCells s0))
      (Q := fun sc =>
        sc.sp = sp0 - 4240#64 ∧
        sc.readReg64 .lr = (blkPl_332).base + 19284#64 ∧
        sc.readReg64 .x0 = outA + 512#64 ∧
        sc.readReg64 .x1 = sp0 - 3664#64 ∧
        (sc.readReg64 .x2).toNat = 376 ∧
        sc.readReg64 .x19 = outA ∧
        sc.readReg64 .x20 = s.readReg64 .x20 ∧
        TraceCalleeSaved sc s0)
      (by
        by_vm_steps (
          wp_steps
          refine SepWP.done rfl hrunc0 ?_
          simp only [TraceCalleeSaved, Reg.x29, hsp_c0, hx0_c0, hx1_c0, hx2_c0, hx19_c0, hx20_c0,
            htr_c0_1, htr_c0_2, wp_norm, arm64_norm]
          exact Entails.refl _
        )) ?_
    intro sc hpcc hrunc hvm_sc1 ⟨hsp_c, hlr_c, hx0_c, hx1_c, hx2_c, hx19_c, hx20_c, htr_c⟩
    have hvm_sc : VmPreserved s sc := hvm_sc0.trans hvm_sc1
    refine call_memcpy_relocate_cs_stack (ret_pc := (blkPl_332).base + 19284#64)
      hmemcpy hrel (outA + 512#64) (sp0 - 3664#64)
      hpcc hrunc hsp_c hfsp_align hlr_c htr_c hx0_c hx1_c hx2_c rfl ?_
    intro sf1 hpc1 hrun1 hsp1 hvm1 hcs1 htr1
    have hx19_1 : sf1.readReg64 .x19 = outA := hcs1.1.trans hx19_c
    have hx20_1 : sf1.readReg64 .x20 = s.readReg64 .x20 := hcs1.2.1.trans hx20_c
    have hvm_s1 : VmPreserved s sf1 := hvm_sc.trans hvm1
    have hq40 := q2_w1_entails_memRegion_40 (outA + 888#64) sp.q210 sp.q220 sp.w230
    rw [show (outA + 888#64) + 16#64 = outA + 904#64 by bv_omega,
        show (outA + 888#64) + 32#64 = outA + 920#64 by bv_omega] at hq40
    refine seq_vm_clean (mid := (blkPl_332).base + 19324#64)
      (P_mid :=
        (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
          F_tail (outA + 512#64) ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
          ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
          stackAt (sp0 - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0) ∗
        (memRegion (outA + 888#64) 40 ∗ memRegion (sp0 - 4240#64) 4144))
      (Q := fun sf2 => sf2.sp = sp0 - 4240#64 ∧ TraceCalleeSaved sf2 s0)
      ?_ ?_
    · refine SepWP.mono (post := fun sf2 Pf2 =>
          VmPreserved sf1 sf2 ∧
          (Pf2 ⊢
            (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
              F_tail (outA + 512#64) ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
              ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
              stackAt (sp0 - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0) ∗
            (((outA + 888#64) ↦₁₂₈ sp.q210) ∗ ((outA + 904#64) ↦₁₂₈ sp.q220) ∗
              ((outA + 920#64) ↦₆₄ sp.w230)) ∗
            (sendEkSpillsAt (sp0 - 4240#64) sp ∗ memRegion ((sp0 - 4240#64) + 576#64) 376 ∗
              memRegion ((sp0 - 4240#64) + 976#64) 880 ∗ memRegion ((sp0 - 4240#64) + 1856#64) 880 ∗
              sendEkUnusedAt (sp0 - 4240#64))) ∧
          (sf2.sp = sp0 - 4240#64 ∧ TraceCalleeSaved sf2 s0))
        (by
          by_vm_steps (
            wp_conv_pre =>
              dsimp only [sendEkSpillsAt, words10At]
              simp only [pointsTo128_eq_pair64_recv, BitVec.add_assoc, arm64_norm]
            wp_steps
            refine DropChunkedClPlacedBudgetAux.align_pre_vm ?_ ?_
            · rw [stackAt_statesRecvCallee_eq_allocHook (sp0 - 4240#64), h576_eq]
              dsimp only [allocHookStack, sendEkSpillsAt, words10At]
              simp only [hx19_1, hx20_1, pointsTo128_eq_pair64_recv, BitVec.add_assoc, bv_sub_sub_recv, wp_norm, arm64_norm]
              sep_ac_rfl
            · wp_done
          ))
        (fun _ _ _ _ ⟨hvm2, hPf2, hq2⟩ =>
          ⟨hvm2, Entails.trans hPf2 (sepConj_mono_right
            (sepConj_mono hq40 (sendEkFrame_entails_memRegion_4144 (sp0 - 4240#64) sp))), hq2⟩)
    · intro sf2 hpc2 hrun2 hvm2 ⟨hsp2, htr2⟩
      have hvm_s2 : VmPreserved s sf2 := hvm_s1.trans hvm2
      subst hsp0
      rw [show (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
            F_tail (outA + 512#64) ∗ ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗
            ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗ ((outA + 944#64) ↦₁₂₈ sp.q200) ∗
            stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ statesRecvSavedCells s0) ∗
          (memRegion (outA + 888#64) 40 ∗ memRegion (s0.sp - 4240#64) 4144) =
          (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
            F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp.q200)) ∗
          stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗
          memRegion (s0.sp - 4240#64) 4144 ∗
          statesRecvSavedCells s0 by sep_ac_rfl]
      refine SepWP.mono
        (hepilogue sf2
          (P_rest ∗ (outA ↦₆₄ sp.b2.w7) ∗ words63At (outA + 8#64) (writebackWords63 s sp) ∗
            F_tail (outA + 512#64) ∗ memRegion (outA + 888#64) 40 ∗
            ((outA + 928#64) ↦₆₄ sp.b2.w8) ∗ ((outA + 936#64) ↦₆₄ s.readReg64 .x20) ∗
            ((outA + 944#64) ↦₁₂₈ sp.q200))
          hpc2 hrun2 hsp2 hsp_align htr2)
        (fun sf Pf _ _ ⟨hvm3, hPf, hsp_sf, hcs_sf, htr_sf⟩ =>
          ⟨hvm_s2.trans hvm3, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_sf, hcs_sf, htr_sf⟩)

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
  states_recv_writeback_59e88_core_placed (spqr_hook_ok_of_mem hmemcpy_sat)
    hrel s0 s outA sp P_rest hpc hrun hsp hsp_align hx19 htr

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
  states_recv_writeback_59e88_core_placed (withVmPreserved_sessionMemcpySpec_of_region hmemcpy)
    hrel s0 s outA sp P_rest hpc hrun hsp hsp_align hx19 htr

abbrev epilogue_18996_writeback_ret_placed := @states_recv_writeback_59e88_placed

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
