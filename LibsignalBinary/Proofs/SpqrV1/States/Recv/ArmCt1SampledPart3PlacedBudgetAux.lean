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
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch5Placed
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WP.FrameAuto
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 3 Aux (`VmPreserved` Steppers)

`VmPreserved` shared `Ok(V1Recv)` store (`+18996 -> +19324`), state-copy helpers (`+10500`,
`+12144`), message-kind dispatch (`+7052`), and budget-pool-threaded unchanged return paths.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (
  LibsignalPlacement blkPl_332 libsignalSessionCode lsProg_332 lsmpl lsρ
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.LibsignalSpqrV1 (spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt (Ct1Sampled)
open CryptoVerification.SpqrV1.Alloc (spqrMemcpySym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Drop (chunkedStatesAt chunkedStatesSize)
open CryptoVerification.SpqrV1.States.Leaves (relocatedHeap wordsAt wordsAt_16)
open CryptoVerification.SpqrV1.States.Recv (
  CopyScratchStack EpilogueStoreStack Split928 TraceCalleeSaved Words16 Words5
  chunkedCt1SampledAt_reconstruct_split928 chunkedCt1SampledBodyAt copyLtScratch copyOtherScratch
  copyScratchStackAt copyScratch_and_epilogueStack_entails_memRegion_4144 copy_pre_entails
  epilogueRegsEqSplit928 epilogueSplit928 epilogueSplit928_of_eq epilogueStackOfSplit928
  epilogueStoreStackPart1At epilogueStoreStackPart2At memRegion_32_entails_words4
  memRegion_928_entails_split928 optEpochSecretAt_none_of_words4 pointsToBytes_entails_memRegion_376
  polyEncoderTagVal resultV1RecvAt sp_sub_144_add_48 sp_sub_4192_sub_48 sp_sub_4240_add_2752
  sp_sub_4240_add_3272 sp_sub_4240_add_3696 sp_sub_4240_add_3832 sp_sub_4240_add_3840
  sp_sub_4240_add_3848 sp_sub_4240_add_3856 sp_sub_4240_add_4096 sp_sub_4240_add_4144
  sp_sub_4240_add_48 sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64
  sp_sub_96_add_80 sp_sub_96_sub_4096 split928At split928At_entails_memRegion
  stackAt_statesRecvCallee_eq_allocHook' statesRecvCalleeStackX statesRecvSavedCells
  statesRecvStackX v1RecvAt v1RecvSize wordsAt_5
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmNoHeaderReceivedStepsPlacedBudgetAux (
  seq_vm_clean seq_vm_cont
)
open LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlacedBudget (lsmpl_base_332_eq)

set_option maxRecDepth 400000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero
  sp_sub_96_add_16 sp_sub_96_add_32 sp_sub_96_add_48 sp_sub_96_add_64 sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_48 sp_sub_4240_add_48 sp_sub_4240_add_4096 sp_sub_144_add_48
  sp_sub_4240_add_4144 sp_sub_4240_add_3856 sp_sub_4240_add_3272
  sp_sub_4240_add_2752 sp_sub_4240_add_3696 sp_sub_4240_add_3832
  sp_sub_4240_add_3840 sp_sub_4240_add_3848
  lsmpl_base_332_eq
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

/-! ## 1. `VmPreserved` Shared `Ok` Return Store (`+18996 -> +19324`) & State-Copy Helpers -/

set_option maxHeartbeats 800000 in
theorem ct1Sampled_epilogue_store_part1_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (c0_out c1_out c2_out c3_out : Words16)
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19280#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA c0_out.toList ∗
        wordsAt (outA + 128#64) c1_out.toList ∗
        wordsAt (outA + 256#64) c2_out.toList ∗
        wordsAt (outA + 384#64) c3_out.toList ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
          wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
          wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
          wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x0 = outA + 512#64 ∧
        sf.readReg64 .x1 = fsp + 576#64 ∧
        sf.readReg64 .x2 = 376#64 ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx19
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  dsimp only [epilogueStoreStackPart1At, epilogueSplit928, Words16.toList]
  simp only [wordsAt_16, BitVec.add_assoc, BitVec.reduceAdd]
  by_vm_steps_nest (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x0, Reg.x1, Reg.x2, Reg.x19, Reg.x20]
    wp_done
  )

theorem ct1Sampled_epilogue_store_part2_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_mid : State) (fsp outA v20 : BitVec 64)
    (k : EpilogueStoreStack)
    (tail_out : Words5) (v928 v936 v944 v952 : BitVec 64)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_mid.pc = (blkPl_332).base + 19280#64)
    (hrun : s_mid.status = .Running)
    (hsp : s_mid.sp = fsp)
    (hx0 : s_mid.readReg64 .x0 = outA + 512#64)
    (hx1 : s_mid.readReg64 .x1 = fsp + 576#64)
    (hx2 : s_mid.readReg64 .x2 = 376#64)
    (hx19 : s_mid.readReg64 .x19 = outA)
    (hx20 : s_mid.readReg64 .x20 = v20) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_mid
      (epilogueStoreStackPart2At fsp k ∗
        memRegion (outA + 512#64) 376 ∗
        wordsAt (outA + 888#64) tail_out.toList ∗
        ((outA + 928#64) ↦₆₄ v928) ∗
        ((outA + 936#64) ↦₆₄ v936) ∗
        ((outA + 944#64) ↦₆₄ v944) ∗
        ((outA + 952#64) ↦₆₄ v952) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_mid sf ∧
        (Pf ⊢
          epilogueStoreStackPart2At fsp k ∗
          ((outA + 512#64) ↦ₛ k.mid) ∗
          wordsAt (outA + 888#64) [k.w210, k.w218, k.w220, k.w228, k.w230] ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ v20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_mid) := by
  subst hsp hx19 hx20
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_mid.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [epilogueStoreStackPart2At, Words5.toList, withVmPreserved, sessionMemcpySpec, allocHookStack]
    at hmemcpy_raw ⊢
  simp only [wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx0, hx1, hx2]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    wp_call hmemcpy_raw (s_mid.readReg64 .x19 + 512#64, s_mid.sp + 576#64, k.mid)
    have hvm_all : VmPreserved s_mid sf := hvm1.trans (by assumption)
    refine SepWP.mono (post := fun sf2 Pf2 =>
      VmPreserved sf sf2 ∧
      (Pf2 ⊢ _) ∧
      sf2.sp = s_mid.sp ∧
      TraceCalleeSaved sf2 s_mid) ?_
      (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
    by_vm_steps_nest (wp_steps; dsimp only [TraceCalleeSaved]; wp_done)
  )

theorem ct1Sampled_epilogue_store_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp outA : BitVec 64)
    (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : k.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 18996#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 19324#64) s_in
      (epilogueStoreStackPart1At fsp k ∗
        epilogueStoreStackPart2At fsp k ∗
        memRegion outA chunkedStatesSize ∗
        memRegion (outA + 928#64) 32 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          epilogueStoreStackPart1At fsp k ∗
          epilogueStoreStackPart2At fsp k ∗
          split928At outA (epilogueSplit928 s_in k) ∗
          ((outA + 928#64) ↦₆₄ k.we8) ∗
          ((outA + 936#64) ↦₆₄ (s_in.readReg64 .x20)) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗
          ((outA + 952#64) ↦₆₄ k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        sf.sp = fsp ∧
        TraceCalleeSaved sf s_in) := by
  have hpre :
      epilogueStoreStackPart1At fsp k ∗
      epilogueStoreStackPart2At fsp k ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      Rest ⊢
      ∃∗ d_out : Split928, ∃∗ v928 : BitVec 64, ∃∗ v936 : BitVec 64,
      ∃∗ v944 : BitVec 64, ∃∗ v952 : BitVec 64,
        epilogueStoreStackPart1At fsp k ∗
        wordsAt outA d_out.c0.toList ∗
        wordsAt (outA + 128#64) d_out.c1.toList ∗
        wordsAt (outA + 256#64) d_out.c2.toList ∗
        wordsAt (outA + 384#64) d_out.c3.toList ∗
        (epilogueStoreStackPart2At fsp k ∗
          memRegion (outA + 512#64) 376 ∗
          wordsAt (outA + 888#64) d_out.tail.toList ∗
          ((outA + 928#64) ↦₆₄ v928) ∗
          ((outA + 936#64) ↦₆₄ v936) ∗
          ((outA + 944#64) ↦₆₄ v944) ∗
          ((outA + 952#64) ↦₆₄ v952) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_928_entails_split928 outA)
        (sepConj_mono_left (memRegion_32_entails_words4 (outA + 928#64)))))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    apply Entails.sepExists_elim; intro v952
    apply Entails.sepExists_elim; intro v944
    apply Entails.sepExists_elim; intro v936
    apply Entails.sepExists_elim; intro v928
    apply Entails.sepExists_elim; intro d_out
    refine Entails.sepExists_right d_out (Entails.sepExists_right v928
      (Entails.sepExists_right v936 (Entails.sepExists_right v944
        (Entails.sepExists_right v952 ?_))))
    rw [show epilogueStoreStackPart1At fsp k ∗
        (epilogueStoreStackPart2At fsp k ∗
          ((⌜d_out.mid.length = 376⌝ ∗ split928At outA d_out) ∗
            ((((outA + 928#64) ↦₆₄ v928) ∗ ((outA + 936#64) ↦₆₄ v936) ∗
              ((outA + 944#64) ↦₆₄ v944) ∗ ((outA + 952#64) ↦₆₄ v952)) ∗
            (stackAt fsp statesRecvCalleeStackX ∗ Rest)))) =
        ⌜d_out.mid.length = 376⌝ ∗
        ((outA + 512#64) ↦ₛ d_out.mid) ∗
        (epilogueStoreStackPart1At fsp k ∗
          wordsAt outA d_out.c0.toList ∗
          wordsAt (outA + 128#64) d_out.c1.toList ∗
          wordsAt (outA + 256#64) d_out.c2.toList ∗
          wordsAt (outA + 384#64) d_out.c3.toList ∗
          (epilogueStoreStackPart2At fsp k ∗
            wordsAt (outA + 888#64) d_out.tail.toList ∗
            ((outA + 928#64) ↦₆₄ v928) ∗
            ((outA + 936#64) ↦₆₄ v936) ∗
            ((outA + 944#64) ↦₆₄ v944) ∗
            ((outA + 952#64) ↦₆₄ v952) ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest)) by
      dsimp only [split928At]; sep_ac_rfl]
    apply Entails.pure_left; intro hd_mid
    refine Entails.trans (sepConj_mono_left
      (pointsToBytes_entails_memRegion_376 (outA + 512#64) d_out.mid hd_mid)) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre ?_
  apply ProofLib.SepWP.exists_left; intro d_out
  apply ProofLib.SepWP.exists_left; intro v928
  apply ProofLib.SepWP.exists_left; intro v936
  apply ProofLib.SepWP.exists_left; intro v944
  apply ProofLib.SepWP.exists_left; intro v952
  refine SepWP.seq (ct1Sampled_epilogue_store_part1_placed s_in fsp outA k
    d_out.c0 d_out.c1 d_out.c2 d_out.c3 _ hfsp_align hpc hrun hsp hx19) ?_
  intro s_mid P_mid hpc_mid hrun_mid
    ⟨hvm_mid, hP_mid, hsp_mid, hx0_mid, hx1_mid, hx2_mid, hx19_mid, hx20_mid, htr_mid⟩
  have hP_mid' : P_mid ⊢
      epilogueStoreStackPart2At fsp k ∗
      memRegion (outA + 512#64) 376 ∗
      wordsAt (outA + 888#64) d_out.tail.toList ∗
      ((outA + 928#64) ↦₆₄ v928) ∗
      ((outA + 936#64) ↦₆₄ v936) ∗
      ((outA + 944#64) ↦₆₄ v944) ∗
      ((outA + 952#64) ↦₆₄ v952) ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (epilogueStoreStackPart1At fsp k ∗
        wordsAt outA (epilogueSplit928 s_in k).c0.toList ∗
        wordsAt (outA + 128#64) (epilogueSplit928 s_in k).c1.toList ∗
        wordsAt (outA + 256#64) (epilogueSplit928 s_in k).c2.toList ∗
        wordsAt (outA + 384#64) (epilogueSplit928 s_in k).c3.toList ∗
        Rest) :=
    Entails.trans hP_mid (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hP_mid' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_store_part2_placed hmemcpy s_mid fsp outA (s_in.readReg64 .x20) k
      d_out.tail v928 v936 v944 v952 _ hmid hfsp_align hpc_mid hrun_mid
      hsp_mid hx0_mid hx1_mid hx2_mid hx19_mid hx20_mid) ?_
  intro sf Pf _ _ ⟨hvm_f, hPf, hsp_f, htr_f⟩
  refine ⟨hvm_mid.trans hvm_f, ?_, hsp_f, htr_f.trans htr_mid⟩
  refine Entails.trans hPf ?_
  dsimp only [split928At, epilogueSplit928, Words5.toList]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_copy_lt_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 10500#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyLtScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyLtScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList, withVmPreserved, sessionMemcpySpec, allocHookStack]
    at hmemcpy_raw ⊢
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx12]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid)
    have hvm_all : VmPreserved s_in sf := hvm1.trans (by assumption)
    refine SepWP.mono (post := fun sf2 Pf2 =>
      VmPreserved sf sf2 ∧
      (Pf2 ⊢ _) ∧
      epilogueRegsEqSplit928 sf2 d ∧
      sf2.sp = s_in.sp ∧
      sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf2 s_in) ?_
      (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
    by_vm_steps_nest (
      wp_steps
      dsimp only [epilogueRegsEqSplit928, TraceCalleeSaved, Reg.x19, Reg.x29]
      wp_done
    )
  )

set_option maxHeartbeats 1200000 in
theorem ct1Sampled_copy_other_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s_in : State) (fsp stA outA : BitVec 64)
    (d : Split928) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hmid : d.mid.length = 376)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 12144#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx1 : s_in.readReg64 .x1 = stA)
    (hx12 : s_in.readReg64 .x12 = d.c0.w0)
    (hx19 : s_in.readReg64 .x19 = outA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 18996#64) s_in
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          split928At stA d ∗
          copyScratchStackAt fsp (copyOtherScratch sc d) ∗
          epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
          stackAt fsp statesRecvCalleeStackX ∗
          Rest) ∧
        epilogueRegsEqSplit928 sf d ∧
        sf.sp = fsp ∧
        sf.readReg64 .x19 = outA ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hsp hx1 hx19
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) (withVmPreserved sessionMemcpySpec) :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  have hsplit := stackAt_statesRecvCallee_eq_allocHook' s_in.sp
  rw [hsplit, ← hmid]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym, BitVec.ofNat_eq_ofNat] at hpc hmemcpy_raw ⊢
  dsimp only [split928At, copyScratchStackAt, epilogueStoreStackPart1At, epilogueStoreStackPart2At,
    copyOtherScratch, epilogueStackOfSplit928, epilogueRegsEqSplit928, EpilogueStoreStack.tail,
    noneCap, Words16.toList, Words5.toList, withVmPreserved, sessionMemcpySpec, allocHookStack]
    at hmemcpy_raw ⊢
  simp only [wordsAt_16, wordsAt_5, BitVec.add_assoc, BitVec.reduceAdd, hx12]
  refine seq_vm_cont (mid := lsmpl.ρ "memcpy") ?_
  by_vm_steps_nest (
    wp_steps
    refine SepWP.done rfl hrun ⟨by simp only [wp_norm, arm64_norm], fun hvm1 => ?_⟩
    wp_call hmemcpy_raw (s_in.sp + 576#64, s_in.readReg64 .x1 + 512#64, d.mid)
    have hvm_all : VmPreserved s_in sf := hvm1.trans (by assumption)
    refine SepWP.mono (post := fun sf2 Pf2 =>
      VmPreserved sf sf2 ∧
      (Pf2 ⊢ _) ∧
      epilogueRegsEqSplit928 sf2 d ∧
      sf2.sp = s_in.sp ∧
      sf2.readReg64 .x19 = s_in.readReg64 .x19 ∧
      sf2.readReg64 .x29 = s_in.readReg64 .x29 ∧
      TraceCalleeSaved sf2 s_in) ?_
      (fun _ _ _ _ ⟨hvm2, hrest⟩ => ⟨hvm_all.trans hvm2, hrest⟩)
    by_vm_steps_nest (
      wp_steps
      dsimp only [epilogueRegsEqSplit928, TraceCalleeSaved, Reg.x19, Reg.x29]
      wp_done
    )
  )

/-! ## 2. Message Kind Dispatch (`+7052`) & Unchanged Return Paths (`Path 2` & `Path 3`) -/

theorem ct1Sampled_msg_kind_check_other_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (msg_tag : BitVec 8) (Rest : SepProp)
    (hne2 : (BitVec.zeroExtend 32 msg_tag == 2#32) = false)
    (hne3 : (BitVec.zeroExtend 32 msg_tag != 3#32) = true)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 12144#64) s_in
      (((msgA + 8#64) ↦₈ msg_tag) ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ ((msgA + 8#64) ↦₈ msg_tag) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x12 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps_nest (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x1, Reg.x12, Reg.x19, Reg.x29]
    wp_done
  )

theorem ct1Sampled_msg_kind_check_ek_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 2#8) ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ ((msgA + 8#64) ↦₈ 2#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = 0#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps_nest (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x1, Reg.x12, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
      Reg.x24, Reg.x28, Reg.x29]
    wp_done
  )

theorem ct1Sampled_msg_kind_check_ekCt1Ack_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (msgA : BitVec 64) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 7052#64)
    (hrun : s_in.status = .Running)
    (hx24 : s_in.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11404#64) s_in
      (((msgA + 8#64) ↦₈ 3#8) ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ ((msgA + 8#64) ↦₈ 3#8) ∗ Rest) ∧
        sf.sp = s_in.sp ∧
        sf.readReg64 .x1 = s_in.readReg64 .x1 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = 1#64 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x12 ∧
        sf.readReg64 .x24 = msgA ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  subst hx24
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  by_vm_steps_nest (
    wp_steps
    dsimp only [TraceCalleeSaved, Reg.x1, Reg.x12, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
      Reg.x24, Reg.x28, Reg.x29]
    wp_done
  )

set_option maxHeartbeats 800000 in
theorem ct1Sampled_store_and_epilogue_same_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s4 : State) (fsp stA outA w200 w208 : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (d : Split928) (sc' : CopyScratchStack)
    (Rest : SepProp)
    (htag : d.c0.w0 = polyEncoderTagVal st.sending_ct1)
    (hmid : d.mid.length = 376)
    (hregs4 : epilogueRegsEqSplit928 s4 d)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc4 : s4.pc = (blkPl_332).base + 18996#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = fsp)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
      (split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest))
      (fun sf Pf =>
        VmPreserved s4 sf ∧
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  let k' := epilogueStackOfSplit928 d noneCap w200 w208
  have hmid' : k'.mid.length = 376 := hmid
  have hP4' :
      split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp k' ∗
        epilogueStoreStackPart2At fsp k' ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest) ⊢
      epilogueStoreStackPart1At fsp k' ∗
      epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗
      memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (split928At stA d ∗
        relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
        copyScratchStackAt fsp sc' ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗
        statesRecvSavedCells s0 ∗
        Rest) := Entails.of_eq (by dsimp only [k']; sep_ac_rfl)
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq (ct1Sampled_epilogue_store_placed hmemcpy s4 fsp outA k' _
    hmid' hfsp_align hpc4 hrun4 hsp4 hx19_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hvm45, hP5, hsp5, htr5⟩
  have heq_split : epilogueSplit928 s4 k' = d :=
    epilogueSplit928_of_eq s4 d noneCap w200 w208 hregs4
  have hP5' : P5 ⊢
      stackAt fsp statesRecvCalleeStackX ∗
      memRegion fsp 4144 ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
        memRegion stA chunkedStatesSize ∗
        Rest) := by
    refine Entails.trans hP5 ?_
    rw [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp sc' k' hmid'
    have hst_out := chunkedCt1SampledAt_reconstruct_split928 A outA st d htag hmid
    have hst_in := split928At_entails_memRegion stA d hmid
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s4.readReg64 .x20) w200 w208
    dsimp only [resultV1RecvAt, v1RecvAt, chunkedStatesAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗ relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗
          ((outA + 936#64) ↦₆₄ s4.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ w200) ∗
          ((outA + 952#64) ↦₆₄ w208))) ∗
        split928At stA d ∗
        Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono (sepConj_mono hst_out hkey)
        (sepConj_mono_left hst_in))))
  subst hfsp
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.mono
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epilogue_19324_placed s0 s5 _
      hsp0_align hpc5 hrun5 hsp5 (htr5.trans htr4)) ?_
  intro sf Pf _ _ ⟨hvm5f, hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨hvm45.trans hvm5f, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_store_and_epilogue_same_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s4 : State) (fsp stA outA w200 w208 : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (d : Split928) (sc' : CopyScratchStack)
    (Rest : SepProp)
    (htag : d.c0.w0 = polyEncoderTagVal st.sending_ct1)
    (hmid : d.mid.length = 376)
    (hregs4 : epilogueRegsEqSplit928 s4 d)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc4 : s4.pc = (blkPl_332).base + 18996#64)
    (hrun4 : s4.status = .Running)
    (hsp4 : s4.sp = fsp)
    (hx19_4 : s4.readReg64 .x19 = outA)
    (htr4 : TraceCalleeSaved s4 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s4
      (split928At stA d ∗
        copyScratchStackAt fsp sc' ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap w200 w208) ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A.repAlloc b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          A.pool lim st_cost s4 ∗
          Rest))
      (fun sf Pf =>
        VmPreserved s4 sf ∧
        (Pf ⊢
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.mono
    (ct1Sampled_store_and_epilogue_same_placed (A := A.repAlloc) hmemcpy s0 s4 fsp stA outA
      w200 w208 st d sc' (A.pool lim st_cost s4 ∗ Rest)
      htag hmid hregs4 hfsp_align hsp0_align hfsp hpc4 hrun4 hsp4 hx19_4 htr4)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s4 sf hvm]; sep_ac_rfl)), hq⟩

theorem copy_pre_entails_placed {A : RustAlloc} {F : ShaCompress}
    (s0 : State) (fsp stA outA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp) :
    ((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
      memRegion outA v1RecvSize ∗
      memRegion fsp 4144 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      statesRecvSavedCells s0 ∗
      Rest ⊢
    ∃∗ d : Split928, ∃∗ sc : CopyScratchStack, ∃∗ k : EpilogueStoreStack,
      ⌜d.c0.w0 = polyEncoderTagVal st.sending_ct1⌝ ∗
      ⌜d.mid.length = 376⌝ ∗
      (split928At stA d ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ k.we8) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (relocatedHeap (fun b => chunkedCt1SampledBodyAt A b st) d.tailBytes ∗
          memRegion outA chunkedStatesSize ∗
          memRegion (outA + 928#64) 32 ∗
          memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 3168 ∗
          statesRecvSavedCells s0 ∗
          Rest)) := by
  refine Entails.trans (copy_pre_entails s0 fsp stA outA st Rest) ?_
  apply Entails.sepExists_elim; intro d
  apply Entails.sepExists_elim; intro sc
  apply Entails.sepExists_elim; intro k
  refine Entails.sepExists_right d (Entails.sepExists_right sc (Entails.sepExists_right k ?_))
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
theorem ct1Sampled_path_lt_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 10500#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s3 sf ∧
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails_placed s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_lt_placed hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hvm34, hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono
    (ct1Sampled_store_and_epilogue_same_placed hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyLtScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))
    fun _ _ _ _ ⟨hvm4f, hrest⟩ => ⟨hvm34.trans hvm4f, hrest⟩

theorem ct1Sampled_path_lt_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 10500#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
          chunkedCt1SampledBodyAt A.repAlloc (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        A.pool lim st_cost s3 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s3 sf ∧
        (Pf ⊢
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.mono
    (ct1Sampled_path_lt_placed (A := A.repAlloc) hmemcpy s0 s3 fsp stA outA st
      (A.pool lim st_cost s3 ∗ Rest)
      hfsp_align hsp0_align hfsp hpc3 hrun3 hsp3 hx1_3 hx12_3 hx19_3 hx29_3 htr3)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s3 sf hvm]; sep_ac_rfl)), hq⟩

set_option maxHeartbeats 800000 in
theorem ct1Sampled_path_other_from_12144_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 12144#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ chunkedCt1SampledBodyAt A (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s3 sf ∧
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.weaken_pre (copy_pre_entails_placed s0 fsp stA outA st Rest) ?_
  apply ProofLib.SepWP.exists_left; intro d
  apply ProofLib.SepWP.exists_left; intro sc
  apply ProofLib.SepWP.exists_left; intro k
  wp_focus_pure; intro htag
  wp_focus_pure; intro hmid
  refine SepWP.seq (ct1Sampled_copy_other_placed hmemcpy s3 fsp stA outA d sc k _
    hmid hfsp_align hpc3 hrun3 hsp3 hx1_3 (hx12_3.trans htag.symm) hx19_3) ?_
  intro s4 P4 hpc4 hrun4 ⟨hvm34, hP4, hregs4, hsp4, hx19_4, _, htr4⟩
  refine SepWP.weaken_pre hP4 ?_
  refine SepWP.mono
    (ct1Sampled_store_and_epilogue_same_placed hmemcpy s0 s4 fsp stA outA k.w200 k.w208 st d
      (copyOtherScratch sc d) Rest htag hmid hregs4 hfsp_align hsp0_align hfsp
      hpc4 hrun4 hsp4 hx19_4 (htr4.trans htr3))
    fun _ _ _ _ ⟨hvm4f, hrest⟩ => ⟨hvm34.trans hvm4f, hrest⟩

theorem ct1Sampled_path_other_from_12144_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s3 : State) (fsp stA outA : BitVec 64)
    (st : Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (Rest : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc3 : s3.pc = (blkPl_332).base + 12144#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = fsp)
    (hx1_3 : s3.readReg64 .x1 = stA)
    (hx12_3 : s3.readReg64 .x12 = polyEncoderTagVal st.sending_ct1)
    (hx19_3 : s3.readReg64 .x19 = outA)
    (hx29_3 : s3.readReg64 .x29 = s0.sp - 96#64)
    (htr3 : TraceCalleeSaved s3 s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s3
      (((stA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
          chunkedCt1SampledBodyAt A.repAlloc (stA + 8#64) st) ∗
        memRegion outA v1RecvSize ∗
        memRegion fsp 4144 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        A.pool lim st_cost s3 ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s3 sf ∧
        (Pf ⊢
          resultV1RecvAt A.repAlloc (F := F) outA (.ok { key := none, state := .ct1Sampled st }) ∗
          memRegion stA chunkedStatesSize ∗
          A.pool lim st_cost sf ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine SepWP.mono
    (ct1Sampled_path_other_from_12144_placed (A := A.repAlloc) hmemcpy s0 s3 fsp stA outA st
      (A.pool lim st_cost s3 ∗ Rest)
      hfsp_align hsp0_align hfsp hpc3 hrun3 hsp3 hx1_3 hx12_3 hx19_3 hx29_3 htr3)
    fun sf Pf _ _ ⟨hvm, hPf, hq⟩ =>
      ⟨hvm, Entails.trans hPf (Entails.of_eq (by rw [A.pool_transport lim st_cost s3 sf hvm]; sep_ac_rfl)), hq⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
