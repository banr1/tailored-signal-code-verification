/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1Placed
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Phase 1 Prologue & Shared Epilogues (Block `427`)

Threads `RustCliAllocBudget` and `FreeOnlyEvs` through the relocatable prologue (`+0 -> +76`)
and shared cleanup/return epilogues (`+904`, `+4608`, `+4632 -> s0.lr`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoVerification (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded lsmpl lsρ)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded sepWP_seq_lscro spqrSendStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (ChainPB)
open CryptoVerification.SpqrV1.Alloc (spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (DropProtoSpqrChainGhost dropStack48)
open CryptoVerification.SpqrV1.Poly.ComputeAt (spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.EncoderFromPb (align_pre seq_clean)
open CryptoVerification.SpqrV1.ProtoRepr (chainPBAt chainPBSize optChainPBAt)
open CryptoVerification.SpqrV1.Top.Send
  (cap_add_one_beq_zero_false chainPBAt_entails_first_word chainPBRestAt
   first_word_entails_chainPBAt fsp_add_30_add_30 memRegion_7968_split_probes
   memRegion_rejoin_30_8_8_32 memRegion_rejoin_60_80 optChainPBAt_none_entails_memRegion_80'
   probes_entails_memRegion_7968 sp_sub_3968_add_3872 sp_sub_3968_add_608 sp_sub_4192_sub_3872
   sp_sub_8064_add_4096 sp_sub_8064_add_7968 sp_sub_8064_add_7976 sp_sub_8064_add_7984
   sp_sub_8064_add_7992 sp_sub_8064_add_8000 sp_sub_8064_add_8008 sp_sub_8064_add_8016
   sp_sub_8064_add_8024 sp_sub_8064_add_8032 sp_sub_8064_add_8040 sp_sub_8064_add_8048
   sp_sub_8064_add_8056 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
   sp_sub_96_add_80 sp_sub_96_sub_4096 spqrSendCalleeStack spqrSendSavedRegs
   spqrSendSavedRegs_eq_sp0 stackAt_spqrSendCallee_split_allocHook
   stackAt_spqrSendCallee_split_dropStack48 stackAt_spqrSend_eq_callee_and_frame
   stack_restore_spqrSend)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget
   VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoChainBudget (dropProtoSpqrChainSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp] do
    Lean.Attribute.erase nm `arm64_norm
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero
attribute [local simp, local arm64_norm, local wp_norm]
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48
  sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_3872 sp_sub_8064_add_4096 sp_sub_3968_add_3872
  sp_sub_8064_add_7968 sp_sub_8064_add_7976 sp_sub_8064_add_7984 sp_sub_8064_add_7992
  sp_sub_8064_add_8000 sp_sub_8064_add_8008 sp_sub_8064_add_8016 sp_sub_8064_add_8024
  sp_sub_8064_add_8032 sp_sub_8064_add_8040 sp_sub_8064_add_8048 sp_sub_8064_add_8056
  sp_sub_3968_add_608 fsp_add_30_add_30

/-! ## 1. Re-Exports of Allocator-Free Sequencing & `.rodata` Jump Table Lemmas -/

export CryptoVerification.Cli.SpqrV1.Top.Send
  (seq_clean_lscro spqrSendRoSym_bytes_split lsro_spqrSendJumpTablesPlacedAt
   lsro_statesFromPbJumpTablePlacedAt lsro_statesIntoPbJumpTablePlacedAt)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (lsro_v1StateJumpTablesPlacedAt lsro_spqrSendRoPlacedAt)

/-- Sequence a VM-preserving `SepWP` segment to `mid` while preserving
    `LibsignalCodeRoLoaded lsmpl`. -/
theorem seq_vm_lscro {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => VmPreserved s sm ∧ (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → VmPreserved s sm → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post := by
  refine sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hvm, hPm, hQ⟩ hcrl_m
  exact SepWP.weaken_pre hPm (h2 sm hpc hrun hcrl_m hvm hQ)

private def deallocFreeOnlySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

/-! ## 2. VM-Preserving Shared Epilogue (`+4632 -> s0.lr`) -/

/-- Relocatable VM-preserving epilogue (`+4632 -> s0.lr`):
    adds `0x1000 + 0xf20 = 0x1f20` (`7968`) to `sp = s0.sp - 0x1f80`, restores `x19..x30`
    from `s0.sp - 96`, and executes `ret`, preserving `VmPreserved s sf` and
    `AllocCallPreserved s sf`. -/
theorem spqr_send_epilogue_4632_placed {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [spqrSendSavedRegs_eq_sp0 s0]
  by_vm_steps (
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], ?_,
        by wp_norm_goal,
        by unfold CalleeSavedPreserved; refine
          ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
           by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
           by simp only [wp_norm, arm64_norm, *]⟩,
        by wp_norm_goal⟩
    have hrest := stack_restore_spqrSend s0.sp s0
    rw [spqrSendSavedRegs_eq_sp0 s0] at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
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
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by sep_ac_rfl))
      (sepConj_mono_left hrest))

/-- Pool-threading corollary of `spqr_send_epilogue_4632_placed`, transporting
    `A.pool lim st s` to `A.pool lim st sf` across `VmPreserved s sf`. -/
theorem spqr_send_epilogue_4632_placed_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s0 s : State) (st : M.σ) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        VmPreserved s sf ∧
        AllocCallPreserved s sf ∧
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim st sf ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hep := spqr_send_epilogue_4632_placed (ext := ext) s0 s (A.pool lim st s ∗ Rest)
    hsp0_align hpc hrun hsp hvregs
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hep ?_)
  intro sf Pf _ _ ⟨hvm, hacp, hPf, hspf, hccf, htrf⟩
  refine ⟨hvm, hacp, ?_, hspf, hccf, htrf⟩
  rw [A.pool_transport lim st s sf hvm]
  exact Entails.trans hPf (Entails.of_eq (by sep_ac_rfl))

/-! ## 3. VM-Preserving Prologue (`+0 -> +76`) -/

/-- Relocatable VM-preserving prologue (`+0 -> +76`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 0x1f80`,
    `x19 = ret`, `x0 = stV`, `x8 = x21 = x26 = sp + 0x1260`, and probes `[s0.sp - 4192]` and
    `[sp]`, establishing `VmPreserved s0 s1` and `AllocCallPreserved s0 s1`. -/
theorem spqr_send_prologue_placed {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps (
    wp_conv_pre =>
      rw [stackAt_spqrSend_eq_callee_and_frame s0.sp,
          sp_sub_8064_add_7968 s0.sp,
          ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide),
          memRegion_7968_split_probes s0.sp]
    cells_unfold
    wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    apply ProofLib.SepWP.exists_left; intro w0
    apply ProofLib.SepWP.exists_left; intro w1
    apply ProofLib.SepWP.exists_left; intro w2
    apply ProofLib.SepWP.exists_left; intro w3
    apply ProofLib.SepWP.exists_left; intro w4
    apply ProofLib.SepWP.exists_left; intro w5
    apply ProofLib.SepWP.exists_left; intro w6
    apply ProofLib.SepWP.exists_left; intro w7
    apply ProofLib.SepWP.exists_left; intro w8
    apply ProofLib.SepWP.exists_left; intro w9
    apply ProofLib.SepWP.exists_left; intro w10
    apply ProofLib.SepWP.exists_left; intro w11
    apply ProofLib.SepWP.exists_left; intro v_probe
    apply ProofLib.SepWP.exists_left; intro v0
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], ?_,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by simp only [wp_norm, arm64_norm, *]⟩
    rw [spqrSendSavedRegs_eq_sp0 s0]
    have hfsp := probes_entails_memRegion_7968 s0.sp 0#64 0#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 0x1f80#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 8056#64) 3864 ∗
         ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 4184#64) 4088) ∗
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
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
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         Rest) by sep_ac_rfl))
      (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by sep_ac_rfl))))

/-- Pool-threading corollary of `spqr_send_prologue_placed`, transporting `A.pool lim st s0`
    to `A.pool lim st s1` across `VmPreserved s0 s1`. -/
theorem spqr_send_prologue_placed_pool {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (s0 : State) (st : M.σ) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ A.pool lim st s0 ∗ Rest)
      (fun s1 P1 =>
        VmPreserved s0 s1 ∧
        AllocCallPreserved s0 s1 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim st s1 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hpr := spqr_send_prologue_placed (ext := ext) s0 ret stV (A.pool lim st s0 ∗ Rest)
    hsp0_align hpc hrun hx0 hx1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hpr ?_)
  intro s1 P1 _ _ ⟨hvm, hacp, hP1, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, htr, hvregs⟩
  refine ⟨hvm, hacp, ?_, hsp1, hx29, hx19, hx0', hx8, hx21, hx26, htr, hvregs⟩
  rw [A.pool_transport lim st s0 s1 hvm]
  exact Entails.trans hP1 (Entails.of_eq (by sep_ac_rfl))

/-! ## 4. Budget-Threaded Shared Cleanup Epilogues (`+4608` and `+904`) -/

/-- Budget-threaded shared `st.chain` drop + register-restore epilogue (`+4608 -> s0.lr`):
    drops `optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh` (calling Block `439`
    when `some`), rejoins `memRegion (s0.sp - 0x1f80#64) 0x1f20`, and runs
    `spqr_send_epilogue_4632_placed_pool`, emitting `FreeOnlyEvs evs`. -/
theorem spqr_send_chain_drop_epilogue_4608_placed {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine SepWP.seq
    (mid := spqrSendPlacedEntry + 4632#64)
    (Mid := fun s2 P2 =>
      ∃ evs : List AllocEvent,
        FreeOnlyEvs evs ∧
        AllocCallPreserved s s2 ∧
        s2.sp = s0.sp - 0x1f80#64 ∧
        s2.trace = s.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
        (P2 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim (M.stepEvents evs st) s2 ∗ Rest))
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry,
      withLsCodeRoLoaded, dropProtoSpqrChainSpec, chainPBSize, BitVec.ofNat_eq_ofNat] at hpc hdrop ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    cases optCh with
    | none =>
      have hnone : optChainPBAt A.repAlloc (fsp + 96#64) none =
          (((fsp + 96#64) ↦₆₄ noneCap) ∗
           memRegion ((fsp + 96#64) + 8#64) 72) := rfl
      wp_conv_pre => rw [hnone]
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨[], FreeOnlyEvs.nil, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by simp only [wp_norm, arm64_norm, *], ?_⟩
      simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
        LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg]
      have hch := optChainPBAt_none_entails_memRegion_80' A.repAlloc (fsp + 96#64)
      rw [hnone] at hch
      refine Entails.trans
        (Entails.of_eq (show _ =
          ((fsp + 96#64) ↦₆₄ noneCap ∗
           memRegion ((fsp + 96#64) + 8#64) 72) ∗
          (memRegion fsp 96 ∗
           memRegion (fsp + 176#64) 7792 ∗
           stackAt fsp spqrSendCalleeStack ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool lim st s ∗ Rest) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left hch) ?_
      rw [← memRegion_rejoin_60_80 fsp]
      exact Entails.of_eq (by sep_ac_rfl)
    | some ch =>
      have hsome : optChainPBAt A.repAlloc (fsp + 96#64) (some ch) =
          chainPBAt A.repAlloc (fsp + 96#64) ch := rfl
      wp_conv_pre => rw [hsome]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (chainPBAt_entails_first_word A.repAlloc (fsp + 96#64) ch)))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro cap
      apply ProofLib.SepWP.exists_left; intro ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ cap ∗
             chainPBRestAt A.repAlloc (fsp + 96#64) cap ptr ch) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool lim st s ∗ Rest) by sep_ac_rfl))
          (sepConj_mono_left (first_word_entails_chainPBAt A.repAlloc (fsp + 96#64) cap ptr ch))) ?_
      wp_conv_pre => rw [stackAt_spqrSendCallee_split_dropStack48 fsp]
      have hcl : LibsignalCodeLoaded lsmpl s.mem := hcrl.1
      have hro : LibsignalRoLoaded lsmpl s.mem := hcrl.2
      wp_call hdrop (⟨fsp + 96#64, ch⟩, st)
      have hacp_ch : AllocCallPreserved s sf := by assumption
      have hevs_ch : FreeOnlyEvs w := by assumption
      refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨w, hevs_ch, by simp only [wp_norm, arm64_norm, *],
          by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], ?_⟩
      rw [hsp, stackAt_spqrSendCallee_split_dropStack48 fsp, ← memRegion_rejoin_60_80 fsp]
      exact Entails.of_eq (by sep_ac_rfl)
  · intro s2 P2 hpc2 hrun2 ⟨evs, hevs, hacp2, hsp2, htr2, hvregs2, hP2⟩
    refine SepWP.weaken_pre hP2 ?_
    have hep := spqr_send_epilogue_4632_placed_pool (M := M) (A := A) (lim := lim) (ext := ext)
      s0 s2 (M.stepEvents evs st) Rest hsp0_align hpc2 hrun2 hsp2 hvregs2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨_, hacp_ep, hPf, hsp_f, hcc_f, htr_f⟩
    exact ⟨evs, hevs, hacp2.trans hacp_ep, hPf, hsp_f, hcc_f, htr_f.trans htr2⟩

/-- Budget-threaded shared `st.version_negotiation.auth_key` dealloc + `st.chain` drop +
    register-restore epilogue (`+904 -> s0.lr`), parameterized directly by `hdealloc`. -/
theorem spqr_send_vn_chain_drop_epilogue_904_dealloc_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustDeallocSym)
      (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hw0_pos : 0 < w0.toNat)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hw1_ne : w1 ≠ 0)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, spqrRustDeallocSym] at hdealloc_fo
  let evs₁ := rustDeallocEvents w0.toNat 1
  have h1 : SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 4608#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun s2 P2 =>
        AllocCallPreserved s s2 ∧
        s2.sp = s0.sp - 0x1f80#64 ∧
        s2.trace = s.trace ∧
        calleeSavedVRegs s2 = calleeSavedVRegs s0 ∧
        (P2 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x60 ∗
          optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool lim (M.stepEvents evs₁ st) s2 ∗ Rest)) := by
    dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_fo ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    wp_steps
    wp_conv_pre => rw [stackAt_spqrSendCallee_split_allocHook fsp]
    wp_call hdealloc_fo (w1, w0.toNat, 1, st)
    wp_steps
    refine ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by simp only [wp_norm, arm64_norm, *],
        by wp_norm_goal, by wp_norm_goal, by simp only [wp_norm, arm64_norm, *], ?_⟩
    try simp only [LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32,
      LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg]
    rw [hsp, stackAt_spqrSendCallee_split_allocHook fsp]
    have h60 := memRegion_rejoin_30_8_8_32 fsp w1
    refine Entails.trans
      (Entails.of_eq (show _ =
        (memRegion fsp 48 ∗
         memRegion (fsp + 48#64) 8 ∗
         ((fsp + 56#64) ↦₆₄ w1) ∗
         memRegion (fsp + 64#64) 32) ∗
        (memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
         stackAt fsp allocHookStack ∗
         optChainPBAt A.repAlloc (fsp + 96#64) optCh ∗
         memRegion (fsp + 176#64) 7792 ∗
         spqrSendSavedRegs fsp s0 ∗
         A.pool lim (M.stepEvents evs₁ st) _ ∗ Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left h60) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro s2 P2 hpc2 hrun2 ⟨hacp1, hsp2, htr2, hvregs2, hP2⟩ hcrl2
  refine SepWP.weaken_pre hP2 ?_
  have hep := spqr_send_chain_drop_epilogue_4608_placed hdrop s0 s2 (M.stepEvents evs₁ st)
    optCh Rest hcrl2 hsp0_align hpc2 hrun2 hsp2 hvregs2
  refine SepWP.mono hep ?_
  intro sf Pf _ _ ⟨evs₂, hevs₂, hacp2, hPf, hsp_f, hcc_f, htr_f⟩
  refine ⟨evs₁ ++ evs₂, FreeOnlyEvs.append (FreeOnlyEvs.singleton 1 w0.toNat) hevs₂,
    hacp1.trans hacp2, ?_, hsp_f, hcc_f, htr_f.trans htr2⟩
  rw [M.stepEvents_append]
  exact hPf

/-- `AllocContractsPlaced`-parameterized wrapper for
    `spqr_send_vn_chain_drop_epilogue_904_dealloc_placed` (`+904 -> s0.lr`). -/
theorem spqr_send_vn_chain_drop_epilogue_904_placed {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec M A lim)))
    (s0 s : State) (st : M.σ) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hw0_pos : 0 < w0.toNat)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hw1_ne : w1 ≠ 0)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        optChainPBAt A.repAlloc ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool lim st s ∗ Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          AllocCallPreserved s sf ∧
          (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool lim (M.stepEvents evs st) sf ∗ Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s.trace) :=
  spqr_send_vn_chain_drop_epilogue_904_dealloc_placed (spqr_hook_ok_of_mem hA.dealloc)
    hdrop s0 s st w0 w1 optCh Rest hcrl hsp0_align hpc hrun hsp hx23 hw0_pos hw0_lt hw1_ne hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
