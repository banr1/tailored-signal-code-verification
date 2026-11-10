/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlaced
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Code-Loaded Epilogue for `<spqr::chain::Chain>::into_pb` (Block `365`)

Budget-threaded, code-loaded `[LibsignalPlacement]` epilogue (`chainIntoPb_epilogue_cl_placed`)
for `<spqr::chain::Chain>::into_pb` (`blkPC_365`) under `RustCliAllocBudget M`, taking
`withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)` on cross-block callee `287`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open CryptoVerification (
  LibsignalCodeLoaded LibsignalPlacement blkPC_365 blkPl_365 lsmpl lsρ withLsCodeLoaded withMemEq
)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainIntoPbCall TraceCalleeSaved calleeSavedFromPbAt cap_mul_112_shift_eq
  chainEpoch chainEpochIntoPb chainEpochSize
  chainHeaderCellsAt chainHeaderCellsAt_entails_memRegion_88 chainIntoPbStack
  chainPBAt_entails_chainPBIntoPinnedAt chainPBAt_pack_out chainPBIntoPinnedAt
  chain_subroutine_ok_withMemEq_of_withLsCodeLoaded
  intoPbScratchAt linksRawAllocAt memRegion_80_split_out restore_stack_chainIntoPb
  stackAt_dropStack32_split_allocHook toChainEpochPBGhost vecU8BufAt
)
open CryptoVerification.SpqrV1.Drop (dropStack32)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainEpochPBAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.SpqrV1.Chain.FromPbJoinClPlacedBudgetAux1 (
  deallocFreeOnlySpec pool_entails_empty_arrayAt_pool_budget
  sepWP_evs_dealloc sepWP_evs_nil seq_clean_evs seq_clean_evs_lscl subroutine_ok_deallocFreeOnly
)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (
  ChainIntoPbAllocEnv ChainIntoPbEnv
)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget (
  chainIntoPbEnv_append_freeOnly intoPbPinnedRetPost
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Code-Loaded Relocatable Epilogue (`+820 .. lr`, Block `365`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` budget-threaded epilogue of `<spqr::chain::Chain>::into_pb`
    at `+820`, using `withLsCodeLoaded lsmpl` for cross-block callee `287`. -/
theorem chainIntoPb_epilogue_cl_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (withLsCodeLoaded lsmpl (dropChainEpochSliceSpec M A lim)))
    (x : ChainIntoPbCall) (st : M.σ) (evs_alloc : List AllocEvent)
    (s0 s : State) (newLinksPtr : BitVec 64)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hevs_alloc : ChainIntoPbAllocEnv x evs_alloc)
    (hacp : AllocCallPreserved s0 s)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hlen : x.gChain.epochs.length = x.chain.links.length)
    (hl_cap_lt : x.gChain.linksCap.toNat * 112 < 2 ^ 63)
    (hl_cap_ne : x.gChain.linksPtr ≠ 0)
    (hl_new_lt : x.chain.links.length * 112 < 2 ^ 63)
    (hl_new_ne : newLinksPtr ≠ 0)
    (hn1 : x.chain.nextRoot.length ≤ x.gChain.nextRoot.cap.toNat)
    (hn2 : x.gChain.nextRoot.cap.toNat < 2 ^ 63)
    (hn3 : x.gChain.nextRoot.ptr ≠ 0)
    (hpc : s.pc = (blkPl_365).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx8 : s.readReg64 .x8 = 0#64)
    (hx9 : s.readReg64 .x9 = 0#64)
    (hx19 : s.readReg64 .x19 = x.chainPtr)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length)
    (hx23 : s.readReg64 .x23 = 0#64)
    (hx24 : s.readReg64 .x24 = newLinksPtr)
    (hx26 : s.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64)
    (hx28 : s.readReg64 .x28 = x.gChain.linksPtr) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H) (s0.readReg64 .lr) s
      (memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents evs_alloc st) s ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (intoPbPinnedRetPost M A lim x st s0) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hdealloc
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  let st0 := M.stepEvents evs_alloc st
  change SepWP _ _ _
    (memRegion x.out 80 ∗
      chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim st0 s ∗
      intoPbScratchAt s0 x.gChain x.chain ∗
      calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32) _
  dsimp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec, BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  refine seq_clean_evs_lscl hcl (mid := (blkPl_365).base + 840#64)
    (P_evs := fun evs sm => memRegion x.out 80 ∗
      chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
      arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
        ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
      linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
      (if (x.gChain.linksCap == 0#64) = true then emp
       else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
         memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
      vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
      A.pool lim (M.stepEvents evs st0) sm ∗
      intoPbScratchAt s0 x.gChain x.chain ∗
      calleeSavedFromPbAt s0 ∗
      stackAt (s0.sp - 288#64) dropStack32)
    (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
      AllocCallPreserved s0 sm ∧
      sm.readReg64 .fp = s0.sp - 96#64 ∧
      sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
      sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
      sm.readReg64 .x23 = 0#64 ∧
      sm.readReg64 .x24 = newLinksPtr ∧
      sm.readReg64 .x25 = x.chain.sendEpoch ∧
      sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
      sm.readReg64 .x27 = x.chain.currentEpoch ∧
      sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
  · have ⟨_, _, _, _, _, _, _⟩ := hacp
    refine SepWP.focus_weaken
      (pool_entails_empty_arrayAt_pool_budget A lim st0 s (chainEpoch A.repAlloc) 112 x.gChain.linksPtr)
      (by sep_focus) ?_
    unfold intoPbScratchAt
    wp_steps_lscl (lsmpl.base 287)
    have hdrop_call :=
      chain_subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
    dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop_call
    wp_call hdrop_call (⟨x.gChain.linksPtr, []⟩, st0)
    rw [hsp, memRegion_zero, emp_sepConj]
    have hevs_1 : FreeOnlyEvs w := by assumption
    have hacp_s0 : AllocCallPreserved s0 sf := by
      refine hacp.trans ?_
      simp only [wp_norm, arm64_norm] at *
      assumption
    rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
    refine SepWP.mono (post := fun sm Pm =>
        (Pm ⊢ memRegion x.out 80 ∗
          chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
          (if (x.gChain.linksCap == 0#64) = true then emp
           else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
             memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents w st0) sm ∗
          intoPbScratchAt s0 x.gChain x.chain ∗
          calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32) ∧
        sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x23 = 0#64 ∧
        sm.readReg64 .x24 = newLinksPtr ∧
        sm.readReg64 .x25 = x.chain.sendEpoch ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.chain.currentEpoch ∧
        sm.readReg64 .x28 = x.gChain.linksPtr)
      ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_1, hp, hq⟩)
    unfold intoPbScratchAt
    wp_done
  · rintro evs1 s1 hevs1 hpc1 hrun1 hcl1 ⟨hsp1, htr1, hacp1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs_lscl hcl1 (mid := (blkPl_365).base + 852#64)
      (P_evs := fun evs sm => memRegion x.out 80 ∗
        chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
        arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
          ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
        linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
        (if (x.gChain.linksCap == 0#64) = true then emp
         else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
           memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
        vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
        A.pool lim (M.stepEvents evs st1) sm ∗
        intoPbScratchAt s0 x.gChain x.chain ∗
        calleeSavedFromPbAt s0 ∗
        stackAt (s0.sp - 288#64) dropStack32)
      (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
        AllocCallPreserved s0 sm ∧
        sm.readReg64 .fp = s0.sp - 96#64 ∧
        sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
        sm.readReg64 .x24 = newLinksPtr ∧
        sm.readReg64 .x25 = x.chain.sendEpoch ∧
        sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
        sm.readReg64 .x27 = x.chain.currentEpoch ∧
        sm.readReg64 .x28 = x.gChain.linksPtr) ?_ ?_
    · have ⟨_, _, _, _, _, _, _⟩ := hacp1
      refine SepWP.focus_weaken
        (pool_entails_empty_arrayAt_pool_budget A lim st1 s1 (chainEpoch A.repAlloc) 112 x.gChain.linksPtr)
        (by sep_focus) ?_
      wp_steps_lscl (lsmpl.base 287)
      have hdrop_call :=
        chain_subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop ‹LibsignalCodeLoaded lsmpl _›
      dsimp only [withMemEq, dropChainEpochSliceSpec, chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop_call
      wp_call hdrop_call (⟨x.gChain.linksPtr, []⟩, st1)
      rw [hsp1, memRegion_zero, emp_sepConj]
      have hevs_2 : FreeOnlyEvs w := by assumption
      have hacp_s0 : AllocCallPreserved s0 sf := by
        refine hacp1.trans ?_
        simp only [wp_norm, arm64_norm] at *
        assumption
      rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
      refine SepWP.mono (post := fun sm Pm =>
          (Pm ⊢ memRegion x.out 80 ∗
            chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
            arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
              ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
            linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
            (if (x.gChain.linksCap == 0#64) = true then emp
             else A.repAlloc.live x.gChain.linksPtr (x.gChain.linksCap.toNat * 112) 8 ∗
               memRegion x.gChain.linksPtr (x.gChain.linksCap.toNat * 112)) ∗
            vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
            A.pool lim (M.stepEvents w st1) sm ∗
            intoPbScratchAt s0 x.gChain x.chain ∗
            calleeSavedFromPbAt s0 ∗
            stackAt (s0.sp - 288#64) dropStack32) ∧
          sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x24 = newLinksPtr ∧
          sm.readReg64 .x25 = x.chain.sendEpoch ∧
          sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          sm.readReg64 .x27 = x.chain.currentEpoch ∧
          sm.readReg64 .x28 = x.gChain.linksPtr)
        ?_ (fun _ _ _ _ ⟨hp, hq⟩ => ⟨w, hevs_2, hp, hq⟩)
      wp_done
    · rintro evs2 s2 hevs2 hpc2 hrun2 _hcl2 ⟨hsp2, htr2, hacp2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2⟩
      let st2 := M.stepEvents evs2 st1
      refine seq_clean_evs (mid := (blkPl_365).base + 880#64)
        (P_evs := fun evs sm => memRegion x.out 80 ∗
          chainHeaderCellsAt x.chainPtr x.gChain x.chain ∗
          arrayAt (chainEpochPBAt A.repAlloc) 112 newLinksPtr
            ((x.gChain.epochs.map toChainEpochPBGhost).zip (x.chain.links.map chainEpochIntoPb)) ∗
          linksRawAllocAt A.repAlloc (BitVec.ofNat 64 x.chain.links.length) newLinksPtr x.chain.links.length ∗
          vecU8BufAt A.repAlloc x.gChain.nextRoot.cap x.gChain.nextRoot.ptr x.chain.nextRoot ∗
          A.pool lim (M.stepEvents evs st2) sm ∗
          intoPbScratchAt s0 x.gChain x.chain ∗
          calleeSavedFromPbAt s0 ∗
          stackAt (s0.sp - 288#64) dropStack32)
        (Q := fun sm => sm.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sm s0 ∧
          AllocCallPreserved s0 sm ∧
          sm.readReg64 .fp = s0.sp - 96#64 ∧
          sm.readReg64 .x19 = x.chainPtr ∧ sm.readReg64 .x20 = x.out ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 x.chain.links.length ∧
          sm.readReg64 .x24 = newLinksPtr ∧
          sm.readReg64 .x25 = x.chain.sendEpoch ∧
          sm.readReg64 .x26 = x.chain.dir.toI32.zeroExtend 64 ∧
          sm.readReg64 .x27 = x.chain.currentEpoch) ?_ ?_
      · have ⟨_, _, _, _, _, _, _⟩ := hacp2
        unfold intoPbScratchAt
        by_cases hcap : x.gChain.linksCap = 0
        · have hcapb : (x.gChain.linksCap == 0#64) = true := beq_iff_eq.mpr hcap
          simp only [hcapb, ↓reduceIte, emp_sepConj, sepConj_emp]
          apply sepWP_evs_nil
          simp only [LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
          wp_steps
          wp_done
        · have hcapb : (x.gChain.linksCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
          have hcap_pos : x.gChain.linksCap.toNat * 112 > 0 := by
            have hpos := BitVec.toNat_pos_of_ne_zero hcap; omega
          have hsz_bv := cap_mul_112_shift_eq x.gChain.linksCap hl_cap_lt
          have hsplit_stack := stackAt_dropStack32_split_allocHook (s0.sp - 288#64)
          simp only [hcapb, Bool.false_eq_true, ↓reduceIte, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
          rw [hsplit_stack]
          apply sepWP_evs_dealloc (x.gChain.linksCap.toNat * 112) 8
          wp_steps
          wp_call hdealloc_fo (x.gChain.linksPtr, x.gChain.linksCap.toNat * 112, 8, st2)
          rw [hsp2]
          have hacp_s0 : AllocCallPreserved s0 sf := by
            refine hacp2.trans ?_
            simp only [wp_norm, arm64_norm] at *
            assumption
          rcases hacp_s0 with ⟨_, _, _, _, _, _, _⟩
          wp_done
      · rintro evs3 sm hevs3 hpcm hrunm ⟨hspm, htrm, hacpm, hfpm, hx19m, hx20m, hx21m, hx22m, hx24m, hx25m, hx26m, hx27m⟩
        have ⟨_, _, _, _, _, _, _⟩ := hacpm
        let evs_free := evs1 ++ evs2 ++ evs3
        have hevs_free : FreeOnlyEvs evs_free := (hevs1.append hevs2).append hevs3
        have hevs_tot : ChainIntoPbEnv x (evs_alloc ++ evs_free) :=
          chainIntoPbEnv_append_freeOnly hevs_alloc hevs_free
        have hst_eq : M.stepEvents evs3 st2 = M.stepEvents (evs_alloc ++ evs_free) st := by
          simp only [st0, st1, st2, evs_free, List.append_assoc,
            LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
        rw [hst_eq]
        rw [memRegion_80_split_out x.out]
        wp_pull_exists
        refine SepWP.mono (post := fun sf Pf =>
            VmPreserved sm sf ∧
            ((Pf ⊢ chainPBIntoPinnedAt A.repAlloc x.gChain x.out x.chain ∗
              memRegion x.chainPtr 88 ∗
              A.pool lim (M.stepEvents (evs_alloc ++ evs_free) st) sm ∗
              stackAt s0.sp chainIntoPbStack) ∧
             sf.sp = s0.sp ∧ sf.trace = s0.trace ∧
             AllocCallPreserved s0 sf ∧ CalleeSavedPreserved s0 sf))
          ?_ ?_
        · by_vm_steps (
            unfold chainHeaderCellsAt calleeSavedFromPbAt
            wp_steps
            refine SepWP.focus_weaken
              (restore_stack_chainIntoPb s0 x.gChain x.chain)
              (by unfold calleeSavedFromPbAt; sep_focus) ?_
            refine SepWP.focus_weaken
              (chainHeaderCellsAt_entails_memRegion_88 x.chainPtr x.gChain x.chain)
              (by unfold chainHeaderCellsAt; sep_focus) ?_
            refine SepWP.focus_weaken
              (Entails.trans
                (chainPBAt_pack_out A.repAlloc x.out newLinksPtr x.gChain x.chain
                  hlen hl_new_lt hl_new_ne hn1 hn2 hn3)
                (chainPBAt_entails_chainPBIntoPinnedAt A.repAlloc x.out newLinksPtr x.gChain x.chain))
              (by sep_focus) ?_
            wp_done)
        · rintro sf Pf _ _ ⟨hvm, hp, hspf, htrf, hacpf, hcsf⟩
          refine ⟨Entails.trans hp ?_, hspf, htrf, hcsf⟩
          rw [← A.pool_of_vmPreserved hvm]
          refine Entails.sepExists_right (evs_alloc ++ evs_free) ?_
          exact Entails.pure_right ⟨hevs_tot, htrf, hacpf⟩ (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopClPlacedBudget
