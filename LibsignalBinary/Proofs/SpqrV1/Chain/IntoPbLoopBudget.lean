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
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoop
public import LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPbLoop
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Epilogue and Loop Proofs for `<spqr::chain::Chain>::into_pb` (Block `365`)

Threads `RustCliAllocBudget M`, `BudgetLimits`, `VmPreserved`, `AllocCallPreserved`, and
`ChainIntoPbEnv` across the `[LibsignalPlacement]` epilogue and conversion loops of
`<spqr::chain::Chain>::into_pb` (`blkPC_365`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 800000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

open CryptoVerification (LibsignalPlacement lsmpl lsρ blkPC_365 blkPl_365)
open CryptoVerification.LibsignalSpqrV1 (Chain ChainEpoch)
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.SpqrV1.ChainProofs (
  ChainEpochGhost ChainGhost ChainIntoPbCall TraceCalleeSaved
  add_curPtr_112 add_curPtr_112_offset calleeSavedFromPbAt cap_mul_112_shift_eq
  chainEpoch chainEpochAt chainEpochAt_unpack_cells chainEpochIntoPb
  chainEpochPBAt_repack_dst chainEpochSize chainEpochSrcCells_entails_memRegion_112
  chainHeaderCellsAt chainHeaderCellsAt_entails_memRegion_88 chainIntoPbStack
  chainPBAt_entails_chainPBIntoPinnedAt chainPBAt_pack_out chainPBIntoPinnedAt
  intoPbLoopScratchAt intoPbScratchAt intoPbScratchAt_pack linksRawAllocAt
  memRegion_112_split_dst memRegion_80_split_out memRegion_append_112
  ofNat_mul_112_beq_false ofNat_succ_mul_112_sub_112 restore_stack_chainIntoPb
  setWidth32_setWidth64 shift52_stack_eq
  stackAt_dropStack32_split_allocHook toChainEpochPBGhost
  vecU8BufAt arrayAt_chainEpochPBAt_snoc
)
open CryptoVerification.SpqrV1.Drop (dropStack32)
open CryptoVerification.SpqrV1.Top.ChainFrom (chainEpochPBAt)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec rustDeallocEvents
)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (
  ChainIntoPbAllocEnv ChainIntoPbEnv
)
open LibsignalBinary.Proofs.SpqrV1.Drop.ChainEpochBudget (dropChainEpochSliceSpec)

namespace LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget

open Arm64 ProofLib ProofLib.ProgramReflection

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.SpqrV1.ChainProofs.truncate32_zeroExtend64 setWidth32_setWidth64
  add_curPtr_112_offset ofNat_succ_mul_112_sub_112

/-! ## Envelope Composition and Sequencing Helpers -/

theorem chainIntoPbEnv_append_freeOnly {x : ChainIntoPbCall} {evs_alloc evs_free : List AllocEvent}
    (ha : ChainIntoPbAllocEnv x evs_alloc) (hf : FreeOnlyEvs evs_free) :
    ChainIntoPbEnv x (evs_alloc ++ evs_free) := by
  unfold ChainIntoPbAllocEnv ChainIntoPbEnv at *
  split at ha <;> simp_all only [↓reduceIte, List.nil_append]
  exact ⟨evs_free, hf, rfl⟩

private def deallocFreeOnlySpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := (rustCliDeallocBudgetSpec M A lim).pre
  post := fun (_, size, align, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (M.stepEvents (rustDeallocEvents size align) st) sf ∗ stackAt s0.sp allocHookStack

private theorem subroutine_ok_deallocFreeOnly [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok prog entry (deallocFreeOnlySpec M A lim) := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustCliDeallocBudgetSpec, deallocFreeOnlySpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1.2.1, hq.1.1⟩, hq.2⟩

private theorem align_pre_st {prog : Program} {pc : BitVec 64} {s : State}
    {P P' : SepProp} {post : State → SepProp → Prop}
    (heq : P = P') (h : SepWP prog pc s P post (fun _ => ⌜False⌝)) :
    SepWP prog pc s P' post (fun _ => ⌜False⌝) := by
  rw [← heq]; exact h

private theorem seq_clean_evs {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    {post : State → SepProp → Prop}
    (h1 : SepWP prog mid s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm))
    (h2 : ∀ (evs : List AllocEvent) (sm : State),
      FreeOnlyEvs evs → sm.pc = mid → sm.status = .Running → Q sm →
      SepWP prog target sm (P_evs evs sm) post) :
    SepWP prog target s P post :=
  SepWP.seq h1 fun sm _Pm hpc hrun ⟨evs, hevs, hent, hQ⟩ =>
    SepWP.weaken_pre hent (h2 evs sm hevs hpc hrun hQ)

private theorem sepWP_evs_nil {prog : Program} {target : BitVec 64}
    {s : State} {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm => (Pm ⊢ P_evs [] sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ => ⟨[], FreeOnlyEvs.nil, hp, hq⟩

private theorem sepWP_evs_dealloc {prog : Program} {target : BitVec 64}
    {s : State} (sz al : Nat)
    {P : SepProp} {P_evs : List AllocEvent → State → SepProp} {Q : State → Prop}
    (h : SepWP prog target s P (fun sm Pm =>
      (Pm ⊢ P_evs (rustDeallocEvents sz al) sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm =>
      ∃ evs, FreeOnlyEvs evs ∧ (Pm ⊢ P_evs evs sm) ∧ Q sm) :=
  SepWP.mono h fun _ _ _ _ ⟨hp, hq⟩ =>
    ⟨rustDeallocEvents sz al, FreeOnlyEvs.singleton al sz, hp, hq⟩

private theorem pool_entails_empty_arrayAt_pool_budget {α : Type} {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (elem : α → BitVec 64 → SepProp) (stride : Nat) (ptr : BitVec 64) :
    A.pool lim st s ⊢ arrayAt elem stride ptr [] ∗ A.pool lim st s :=
  Entails.of_eq (emp_sepConj (A.pool lim st s)).symm

/-! ## Return Postcondition and Relocatable Epilogue (`+820 .. lr`, Block `365`) -/

/-- Return postcondition of budget-threaded `chainIntoPbPinnedSpec`. -/
abbrev intoPbPinnedRetPost (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (x : ChainIntoPbCall) (st : M.σ) (s0 : State) : State → SepProp → Prop :=
  fun sf P' =>
    (P' ⊢ ∃∗ evs : List AllocEvent,
      ⌜ChainIntoPbEnv x evs ∧ sf.trace = s0.trace ∧ AllocCallPreserved s0 sf⌝ ∗
      chainPBIntoPinnedAt A.repAlloc x.gChain x.out x.chain ∗
      memRegion x.chainPtr 88 ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp chainIntoPbStack) ∧
    sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ CalleeSavedPreserved s0 sf

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` epilogue of `<spqr::chain::Chain>::into_pb` at `+820`. -/
theorem chainIntoPb_epilogue_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustCliDeallocBudgetSpec M A lim))
    (hdrop : subroutine_ok ((blkPC_365).rebase (blkPl_365).base H)
      (lsmpl.base 287) (dropChainEpochSliceSpec M A lim))
    (x : ChainIntoPbCall) (st : M.σ) (evs_alloc : List AllocEvent)
    (s0 s : State) (newLinksPtr : BitVec 64)
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
  dsimp only [dropChainEpochSliceSpec, deallocFreeOnlySpec, rustCliDeallocBudgetSpec,
    chainEpochSize, BitVec.ofNat_eq_ofNat] at hdrop hdealloc_fo hpc ⊢
  refine seq_clean_evs (mid := (blkPl_365).base + 840#64)
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
    wp_steps
    wp_call hdrop (⟨x.gChain.linksPtr, []⟩, st0)
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
  · rintro evs1 s1 hevs1 hpc1 hrun1 ⟨hsp1, htr1, hacp1, hfp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1⟩
    let st1 := M.stepEvents evs1 st0
    refine seq_clean_evs (mid := (blkPl_365).base + 852#64)
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
      wp_steps
      wp_call hdrop (⟨x.gChain.linksPtr, []⟩, st1)
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
    · rintro evs2 s2 hevs2 hpc2 hrun2 ⟨hsp2, htr2, hacp2, hfp2, hx19_2, hx20_2, hx21_2, hx22_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2⟩
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

/-! ## Relocatable Loop 1 (`+300 .. +460`, Block `365`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` single iteration of Loop 1 (`+300 .. +456`),
preserving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem intoPb_loop1_step_placed [LibsignalPlacement] {A : CryptoVerification.RustHeap.RustAlloc}
    {H : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (blkPl_365).base + 300#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
    (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
    (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      (if rest.isEmpty then (blkPl_365).base + 460#64
       else (blkPl_365).base + 300#64)
      s
      (memRegion srcBase (conv.length * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        VmPreserved s sf ∧
        ((Pm ⊢ memRegion srcBase ((conv.length + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = s.readReg64 .x9 ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x13 = s0.sp - 160#64 ∧
        sf.readReg64 .x14 = s0.sp - 208#64 ∧
        sf.readReg64 .x15 = s0.sp - 260#64 ∧
        sf.readReg64 .x16 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x17 = srcBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 56#64 ∧
        AllocCallPreserved s sf ∧ CalleeSavedPreserved s sf)) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  by_vm_steps (
    refine SepWP.focus_rw
      (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
      (by sep_focus) ?_
    wp_pull_exists
    refine SepWP.focus_rw
      (by rfl : intoPbScratchAt s0 gChain cChain =
        ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
        ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
        ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
        intoPbLoopScratchAt s0)
      (by sep_focus) ?_
    unfold intoPbLoopScratchAt
    wp_pull_exists
    refine SepWP.focus_weaken
      (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 (conv.length * 112)))
      (by sep_focus) ?_
    wp_focus_pure
    rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)))
      (by sep_focus) ?_
    cases rest with
    | nil =>
      simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
      wp_steps
      refine SepWP.focus_weaken
        (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
          ep.send.ctr ep.recv.ctr)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
          g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
        (by sep_focus) ?_
      wp_done
    | cons ep2 rest2 =>
      have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
        have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
            BitVec.ofNat 64 (1 * 112)) = false :=
          ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
        simpa [bne] using hbeq
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.focus_weaken
        (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
          ep.send.ctr ep.recv.ctr)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (memRegion_append_112 srcBase conv.length (by omega)))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
          g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
        (by sep_focus) ?_
      wp_done)

/-- Relocatable `[LibsignalPlacement]` inductive Loop 1 theorem (`+300 .. +460`),
preserving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem intoPb_loop1_run_placed [LibsignalPlacement] {A : CryptoVerification.RustHeap.RustAlloc}
    {H : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (blkPl_365).base + 300#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = BitVec.ofNat 64 (rem.length * 112))
      (hx13 : s.readReg64 .x13 = s0.sp - 160#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 208#64)
      (hx15 : s.readReg64 .x15 = s0.sp - 260#64)
      (hx16 : s.readReg64 .x16 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx17 : s.readReg64 .x17 = srcBase + BitVec.ofNat 64 (conv.length * 112) + 56#64),
      SepWP ((blkPC_365).rebase (blkPl_365).base H)
        ((blkPl_365).base + 460#64)
        s
        (memRegion srcBase (conv.length * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          VmPreserved s sf ∧ AllocCallPreserved s sf ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x9 = s.readReg64 .x9 ∧
          sf.readReg64 .x10 = s0.sp - 160#64 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase hsp0_align _ hrem_len hconv_len hbound
      hpc hrun hsp htr hfp hx10 hx12 hx13 hx14 hx15 hx16 hx17
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop1_step_placed (A := A) (H := H)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest hsp0_align
        hconv_len hrest_len (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp hx10 (by rw [hlen_cons] at hx12; exact hx12)
        hx13 hx14 hx15 hx16 hx17
      change SepWP _ _ _
        (memRegion srcBase (conv.length * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 (conv.length * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 (conv.length * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase conv.length, hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hvm1, hPm, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, _, _, _, _, _, _, hacp1, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hvm1, hacp1, hsp1, htr1, hfp1, hx0_1, hx3_1, hx8_1, hx9_1, hx10_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by sep_ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hvmm, hPm, hspm, htrm, hfpm, hx0m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hx17m, hacpm, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase
          hsp0_align (by simp) hrest_len (by simp [hconv_len]) hbound'
          hpcm hrunm hspm htrm hfpm hx10m hx12m hx13m hx14m hx15m
          (by rw [hconv1]; exact hx16m)
          (by rw [hconv1]; exact hx17m)
        simp only [hconv1, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hvm2, hacp2, hsp2, htr2, hfp2, hx0_2, hx3_2, hx8_2, hx9_2, hx10_2, hx11_2, hcs2⟩
        have hlen_add : conv.length + 1 + (ep2 :: rest2).length = conv.length + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hvmm.trans hvm2, hacpm.trans hacp2, hsp2, htr2, hfp2,
          hx0_2.trans hx0m, hx3_2.trans hx3m, hx8_2.trans hx8m,
          hx9_2.trans hx9m, hx10_2, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

/-! ## Relocatable Loop 2 (`+512 .. +672`, Block `365`) -/

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` single iteration of Loop 2 (`+512 .. +668`),
preserving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem intoPb_loop2_step_placed [LibsignalPlacement] {A : CryptoVerification.RustHeap.RustAlloc}
    {H : String → Option (State → State)}
    (s0 s : State) (gChain : ChainGhost) (cChain : Chain)
    (srcBase dstBase : BitVec 64)
    (convG : List ChainEpochGhost) (conv : List ChainEpoch)
    (g : ChainEpochGhost) (ep : ChainEpoch)
    (restG : List ChainEpochGhost) (rest : List ChainEpoch)
    (m₁ : Nat)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hconv_len : convG.length = conv.length)
    (hrest_len : restG.length = rest.length)
    (hm1_le : m₁ ≤ conv.length)
    (hbound : (conv.length + 1 + rest.length) * 112 < 2 ^ 63)
    (hpc : s.pc = (blkPl_365).base + 512#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 288#64)
    (htr : TraceCalleeSaved s s0)
    (hfp : s.readReg64 .fp = s0.sp - 96#64)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 ((1 + rest.length) * 112))
    (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
    (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
    (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
    (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
    (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
    (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64) :
    SepWP ((blkPC_365).rebase (blkPl_365).base H)
      (if rest.isEmpty then (blkPl_365).base + 672#64
       else (blkPl_365).base + 512#64)
      s
      (memRegion srcBase ((conv.length - m₁) * 112) ∗
        chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
        arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
          (restG.zip rest) ∗
        arrayAt (chainEpochPBAt A) 112 dstBase
          ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
        memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
        memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
        intoPbScratchAt s0 gChain cChain)
      (fun sf Pm =>
        VmPreserved s sf ∧
        ((Pm ⊢ memRegion srcBase ((conv.length - m₁ + 1) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112))
            (restG.zip rest) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            (((convG ++ [g]).map toChainEpochPBGhost).zip ((conv ++ [ep]).map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) ∗
          intoPbScratchAt s0 gChain cChain) ∧
        sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
        sf.readReg64 .fp = s0.sp - 96#64 ∧
        sf.readReg64 .x0 = s.readReg64 .x0 ∧
        sf.readReg64 .x2 = s.readReg64 .x2 ∧
        sf.readReg64 .x3 = s.readReg64 .x3 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧
        sf.readReg64 .x9 = BitVec.ofNat 64 (rest.length * 112) ∧
        sf.readReg64 .x10 = s0.sp - 160#64 ∧
        sf.readReg64 .x11 = s.readReg64 .x11 ∧
        sf.readReg64 .x12 = s0.sp - 160#64 ∧
        sf.readReg64 .x13 = s0.sp - 208#64 ∧
        sf.readReg64 .x14 = s0.sp - 260#64 ∧
        sf.readReg64 .x15 = dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112) + 52#64 ∧
        sf.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁ + 1) * 112) + 56#64 ∧
        AllocCallPreserved s sf ∧ CalleeSavedPreserved s sf)) := by
  have hfsp_align : ((s0.sp - 288#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 288#64 hsp0_align (by decide)
  by_vm_steps (
    refine SepWP.focus_rw
      (memRegion_112_split_dst (dstBase + BitVec.ofNat 64 (conv.length * 112)))
      (by sep_focus) ?_
    wp_pull_exists
    refine SepWP.focus_rw
      (by rfl : intoPbScratchAt s0 gChain cChain =
        ((s0.sp - 288#64) ↦₆₄ cChain.currentEpoch) ∗
        ((s0.sp - 280#64) ↦₆₄ cChain.sendEpoch) ∗
        ((s0.sp - 272#64) ↦₆₄ gChain.linksCap) ∗
        intoPbLoopScratchAt s0)
      (by sep_focus) ?_
    unfold intoPbLoopScratchAt
    wp_pull_exists
    refine SepWP.focus_weaken
      (chainEpochAt_unpack_cells A g ep (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)))
      (by sep_focus) ?_
    wp_focus_pure
    rintro ⟨hs1, hs2, hs3, hs4, hs5, hs6, hr1, hr2, hr3, hr4, hr5, hr6⟩
    wp_steps
    refine SepWP.focus_weaken
      (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
        (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
        (BitVec.ofNat 64 ep.recv.prev.data.length)))
      (by sep_focus) ?_
    cases rest with
    | nil =>
      simp only [List.isEmpty_nil, List.length_nil, Nat.mul_zero, ↓reduceIte]
      wp_steps
      refine SepWP.focus_weaken
        (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
          ep.send.ctr ep.recv.ctr)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
          g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
        (by sep_focus) ?_
      wp_done
    | cons ep2 rest2 =>
      have hne : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) != 112#64) = true := by
        have hbeq : (BitVec.ofNat 64 ((1 + (ep2 :: rest2).length) * 112) ==
            BitVec.ofNat 64 (1 * 112)) = false :=
          ofNat_mul_112_beq_false (by simp) (by simp at hbound ⊢; omega) (by decide)
        simpa [bne] using hbeq
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      wp_steps
      refine SepWP.focus_weaken
        (Entails.of_eq (shift52_stack_eq s0.sp _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)).symm)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (intoPbScratchAt_pack s0 gChain cChain _ g.recv.next.cap g.recv.next.ptr
          (BitVec.ofNat 64 ep.recv.next.length) g.recv.prev.cap g.recv.prev.ptr
          (BitVec.ofNat 64 ep.recv.prev.data.length)
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochSrcCells_entails_memRegion_112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
          g.send.next.cap g.send.next.ptr (BitVec.ofNat 64 ep.send.next.length)
          g.send.prev.cap g.send.prev.ptr (BitVec.ofNat 64 ep.send.prev.data.length)
          g.recv.next.cap g.recv.next.ptr (BitVec.ofNat 64 ep.recv.next.length)
          g.recv.prev.cap g.recv.prev.ptr (BitVec.ofNat 64 ep.recv.prev.data.length)
          ep.send.ctr ep.recv.ctr)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (Entails.of_eq (memRegion_append_112 srcBase (conv.length - m₁) (by omega)))
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (chainEpochPBAt_repack_dst A (dstBase + BitVec.ofNat 64 (conv.length * 112))
          g ep _ hs1 hs2 hs3 hs4 hs5 hs6 hr1 hr2 hr3 hr4 hr5 hr6)
        (by sep_focus) ?_
      refine SepWP.focus_weaken
        (arrayAt_chainEpochPBAt_snoc A dstBase convG conv g ep hconv_len)
        (by sep_focus) ?_
      wp_done)

/-- Relocatable `[LibsignalPlacement]` inductive Loop 2 theorem (`+512 .. +672`),
preserving `VmPreserved s sf` and `AllocCallPreserved s sf`. -/
theorem intoPb_loop2_run_placed [LibsignalPlacement] {A : CryptoVerification.RustHeap.RustAlloc}
    {H : String → Option (State → State)}
    (rem : List ChainEpoch) :
    ∀ (remG : List ChainEpochGhost) (convG : List ChainEpochGhost) (conv : List ChainEpoch)
      (s0 s : State) (gChain : ChainGhost) (cChain : Chain) (srcBase dstBase : BitVec 64)
      (m₁ : Nat)
      (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
      (hrem_pos : 1 ≤ rem.length)
      (hrem_len : remG.length = rem.length)
      (hconv_len : convG.length = conv.length)
      (hm1_le : m₁ ≤ conv.length)
      (hbound : (conv.length + rem.length) * 112 < 2 ^ 63)
      (hpc : s.pc = (blkPl_365).base + 512#64)
      (hrun : s.status = .Running)
      (hsp : s.sp = s0.sp - 288#64)
      (htr : TraceCalleeSaved s s0)
      (hfp : s.readReg64 .fp = s0.sp - 96#64)
      (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 (rem.length * 112))
      (hx10 : s.readReg64 .x10 = s0.sp - 160#64)
      (hx12 : s.readReg64 .x12 = s0.sp - 160#64)
      (hx13 : s.readReg64 .x13 = s0.sp - 208#64)
      (hx14 : s.readReg64 .x14 = s0.sp - 260#64)
      (hx15 : s.readReg64 .x15 = dstBase + BitVec.ofNat 64 (conv.length * 112) + 52#64)
      (hx16 : s.readReg64 .x16 = srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 56#64),
      SepWP ((blkPC_365).rebase (blkPl_365).base H)
        ((blkPl_365).base + 672#64)
        s
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112))
            (remG.zip rem) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) (rem.length * 112) ∗
          intoPbScratchAt s0 gChain cChain)
        (fun sf Pm =>
          (Pm ⊢ memRegion srcBase ((conv.length - m₁ + rem.length) * 112) ∗
            arrayAt (chainEpochPBAt A) 112 dstBase
              (((convG ++ remG).map toChainEpochPBGhost).zip ((conv ++ rem).map chainEpochIntoPb)) ∗
            intoPbScratchAt s0 gChain cChain) ∧
          VmPreserved s sf ∧ AllocCallPreserved s sf ∧
          sf.sp = s0.sp - 288#64 ∧ TraceCalleeSaved sf s0 ∧
          sf.readReg64 .fp = s0.sp - 96#64 ∧
          sf.readReg64 .x0 = s.readReg64 .x0 ∧
          sf.readReg64 .x2 = s.readReg64 .x2 ∧
          sf.readReg64 .x3 = s.readReg64 .x3 ∧
          sf.readReg64 .x8 = s.readReg64 .x8 ∧
          sf.readReg64 .x11 = s.readReg64 .x11 ∧
          CalleeSavedPreserved s sf) := by
  induction rem with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ hpos; simp at hpos
  | cons ep rest ih =>
    intro remG convG conv s0 s gChain cChain srcBase dstBase m₁ hsp0_align _ hrem_len hconv_len hm1_le hbound
      hpc hrun hsp htr hfp hx9 hx10 hx12 hx13 hx14 hx15 hx16
    cases remG with
    | nil => simp at hrem_len
    | cons g restG =>
      have hrest_len : restG.length = rest.length := by simpa using hrem_len
      have hlen_cons : (ep :: rest).length = 1 + rest.length := by simp [Nat.add_comm]
      have hsplit_dst :
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) =
            memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) 112 ∗
            memRegion (dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112)) (rest.length * 112) := by
        rw [hlen_cons, Nat.add_mul, Nat.one_mul]
        exact ProofLib.memRegion_split' (b := dstBase + BitVec.ofNat 64 (conv.length * 112))
          (n := 112) (k := rest.length * 112)
          (b' := dstBase + BitVec.ofNat 64 ((conv.length + 1) * 112))
          rfl (by rw [add_curPtr_112]) (by omega)
      have hstep := intoPb_loop2_step_placed (A := A) (H := H)
        s0 s gChain cChain srcBase dstBase convG conv g ep restG rest m₁ hsp0_align
        hconv_len hrest_len hm1_le (by rw [hlen_cons] at hbound; omega)
        hpc hrun hsp htr hfp (by rw [hlen_cons] at hx9; exact hx9)
        hx10 hx12 hx13 hx14 hx15 hx16
      change SepWP _ _ _
        (memRegion srcBase ((conv.length - m₁) * 112) ∗
          (chainEpochAt A (g, ep) (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112)) ∗
            arrayAt (chainEpochAt A) 112 (srcBase + BitVec.ofNat 64 ((conv.length - m₁) * 112) + 112#64)
              (restG.zip rest)) ∗
          arrayAt (chainEpochPBAt A) 112 dstBase
            ((convG.map toChainEpochPBGhost).zip (conv.map chainEpochIntoPb)) ∗
          memRegion (dstBase + BitVec.ofNat 64 (conv.length * 112)) ((ep :: rest).length * 112) ∗
          intoPbScratchAt s0 gChain cChain) _
      rw [add_curPtr_112 srcBase (conv.length - m₁), hsplit_dst]
      cases rest with
      | nil =>
        have hrestG_nil : restG = [] := List.eq_nil_of_length_eq_zero hrest_len
        subst hrestG_nil
        simp only [List.isEmpty_nil, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.mono hstep ?_)
        rintro sf Pm _ _ ⟨hvm1, hPm, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, _, _, hx11_1, _, _, _, _, _, hacp1, hcs1⟩
        refine ⟨Entails.trans hPm ?_, hvm1, hacp1, hsp1, htr1, hfp1, hx0_1, hx2_1, hx3_1, hx8_1, hx11_1, hcs1⟩
        simp only [List.zip_nil_right, arrayAt, List.length_nil, Nat.mul_zero, Nat.zero_mul,
          memRegion_zero, emp_sepConj, sepConj_emp, List.length_singleton, List.append_assoc,
          List.nil_append]
        exact Entails.of_eq (by sep_ac_rfl)
      | cons ep2 rest2 =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at hstep
        refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl)) (SepWP.seq hstep ?_)
        rintro sm Pm hpcm hrunm ⟨hvmm, hPm, hspm, htrm, hfpm, hx0m, hx2m, hx3m, hx8m, hx9m, hx10m, hx11m, hx12m, hx13m, hx14m, hx15m, hx16m, hacpm, hcsm⟩
        have hconv1 : (conv ++ [ep]).length = conv.length + 1 := by
          rw [List.length_append, List.length_singleton]
        have hsub_add : conv.length + 1 - m₁ = conv.length - m₁ + 1 := by omega
        have hbound' : ((conv ++ [ep]).length + (ep2 :: rest2).length) * 112 < 2 ^ 63 := by
          rw [hconv1]; rw [hlen_cons] at hbound; omega
        have hih := ih restG (convG ++ [g]) (conv ++ [ep]) s0 sm gChain cChain srcBase dstBase m₁
          hsp0_align (by simp) hrest_len (by simp [hconv_len])
          (by rw [hconv1]; omega) hbound'
          hpcm hrunm hspm htrm hfpm hx9m hx10m hx12m hx13m hx14m
          (by rw [hconv1]; exact hx15m)
          (by rw [hconv1, hsub_add]; exact hx16m)
        simp only [hconv1, hsub_add, List.append_assoc, List.singleton_append] at hih
        refine SepWP.weaken_pre (Entails.trans hPm (Entails.of_eq (by sep_ac_rfl))) (SepWP.mono hih ?_)
        rintro sf Pf _ _ ⟨hPf, hvm2, hacp2, hsp2, htr2, hfp2, hx0_2, hx2_2, hx3_2, hx8_2, hx11_2, hcs2⟩
        have hlen_add : conv.length - m₁ + 1 + (ep2 :: rest2).length =
            conv.length - m₁ + (ep :: ep2 :: rest2).length := by
          simp [Nat.add_assoc, Nat.add_comm 1]
        rw [hlen_add] at hPf
        exact ⟨hPf, hvmm.trans hvm2, hacpm.trans hacp2, hsp2, htr2, hfp2,
          hx0_2.trans hx0m, hx2_2.trans hx2m, hx3_2.trans hx3m,
          hx8_2.trans hx8m, hx11_2.trans hx11m,
          CalleeSavedPreserved.trans hcsm hcs2⟩

end LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbLoopBudget
