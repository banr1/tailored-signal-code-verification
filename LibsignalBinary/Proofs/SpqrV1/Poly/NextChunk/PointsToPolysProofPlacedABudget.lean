/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProof
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedA
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Sum and Cleanup

Relocatable `[LibsignalPlacement]` verification of `lagrangeSumAndFree_placed_sepWPp`
(`+2608 -> +4004`) and per-iteration slot cleanup (`+4004 -> +976 / +4424`) threading
`RustCliAllocBudget M`, `BudgetLimits`, `LagrangeSumStepEnv`, and `FreeOnlyEvs`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedABudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (Point Poly Pt)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly (gf16SliceAt polyOf ptSliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (lagrangePrepareStack readReg32_setMem_setPC_pre readReg32_setPC_pre
   readReg64_setMem_setPC_pre readReg64_setPC_pre readReg_setMem_setPC_pre readReg_setPC_pre
   sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (add_8_add_8_eq basisVecAt cmn_one_ne_zero completePointsBasisPure
   completePointsBasisPure_length completePointsBasisPure_mem_length newPolyBufAt
   ofNat_pos_ne_zero pointToPolyPure polyOf_empty_unfold polyOf_of_newPolyBufAt
   ptVecBufAt ptVecBufAt_pos_entails ptVecBufAt_zero_drop shl1_oldCap_eq shl2_len_eq)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget (LagrangeSumStepEnv RepeatSeqEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudget
  (lagrangeSumAndFree_gen_placed_sepWPp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by cases s; rfl
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl
private theorem pstate_setMem_pre (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl
private theorem fs_setMem_pre (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
private theorem sigActions_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
private theorem tpidrEl0_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem brkStart_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).brkStart = s.brkStart := by cases s; rfl
private theorem oracle_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).oracle = s.oracle := by cases s; rfl
private theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by cases s; rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_p2p_pl_b :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm] add_8_add_8_eq

/-! ## 1. Specialization of `lagrangeSumAndFree_gen_placed_sepWPp` to `completePointsBasisPure` -/

/-- Budget-threaded combined `Poly::lagrange_sum` + `polys` deallocation (`+2608 -> +4004`)
    specialized to `completePointsBasisPure pts`, stepping `st` along
    `SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs`. -/
theorem lagrangeSumAndFree_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (pts : List Pt) (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u640 u648 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 pts.length)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)))
    (hcont : ∀ (evs : List AllocEvent) s1 u656' u664' u672',
      SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs evs →
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 4004#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 pts.length →
      s1.readReg64 .x20 = cIdx →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         ptSliceAt ptVecPtr pts ∗
         A.live accPtr (2 * pts.length) 2 ∗
         gf16SliceAt accPtr (Poly.lagrangeSum pts (completePointsBasisPure pts)).coefficients ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         memRegion (fsp + 112#64) 120 ∗
         ((fsp + 640#64) ↦₆₄ accPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 656#64) ↦₆₄ u656') ∗
         ((fsp + 664#64) ↦₆₄ u664') ∗
         ((fsp + 672#64) ↦₆₄ u672') ∗
         reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ptSliceAt ptVecPtr pts ∗
       basisVecAt A.repAlloc basisPtr (completePointsBasisPure pts) ∗
       A.live accPtr (2 * pts.length) 2 ∗
       memRegion accPtr (2 * pts.length) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       memRegion (fsp + 112#64) 120 ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       memRegion (fsp + 656#64) 24 ∗
       reduceTablePlacedAt ∗ tokenInitPlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumAndFree_gen_placed_sepWPp hA pts (completePointsBasisPure pts)
      hpts_ne hbound
      (completePointsBasisPure_length pts)
      (completePointsBasisPure_mem_length pts)
      s0 s hcl fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
      u16 u64 u72 u80 u640 u648 Frame _R
      hpc hrun hsp htrace hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 hfit ?_)
  intro evs s1 u656' u664' u672' henv hcl1 hpc1 hrun1 hsp1 htr1 hvregs1
    hx19_1 hx20_1 hx26_1 hx27_1 hx28_1 hx29_1
  exact SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont evs s1 u656' u664' u672' henv hcl1 hpc1 hrun1 hsp1 htr1 hvregs1
      hx19_1 hx20_1 hx26_1 hx27_1 hx28_1 hx29_1)

/-! ## 2. Budget-Threaded Per-Iteration Cleanup (`+4004 -> +976 / +4424`, Block `416`) -/

/-- Budget-threaded sub-block 1 (`+4004 -> +4048`):
    checks `x19 + 1 != 0`, computes `slot = (fsp + 256) + 24 * j`, and deallocates the old
    `Poly` buffer in `slot` if `oldCap != 0`, emitting a `FreeOnlyEvs` event sequence. -/
theorem deallocOldPolySlot_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j n : Nat) (hn : n ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 n)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ (evs : List AllocEvent) s1 oldCap oldPtr,
      FreeOnlyEvs evs →
      s1.pc = (blkPl_416).base + 4048#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = BitVec.ofNat 64 n →
      s1.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j) →
      s1.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  have hcmn := cmn_one_ne_zero hn
  have hmul24 : BitVec.ofNat 64 j * 24#64 = BitVec.ofNat 64 (24 * j) := by bv_omega
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (polyOf_empty_unfold A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro oldCap
  apply SepWP.exists_elim; intro oldPtr
  have hpull :
      A.pool lim st s ∗
      (⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp
        else A.repAlloc.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2))) ∗
      stackAt fsp allocHookStack ∗ Frame =
      ⌜oldCap.toNat * 2 < 2 ^ 63 ∧ oldPtr ≠ 0#64⌝ ∗
      (A.pool lim st s ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       (if oldCap = 0#64 then emp
        else A.repAlloc.live oldPtr (oldCap.toNat * 2) 2 ∗ memRegion oldPtr (oldCap.toNat * 2)) ∗
       stackAt fsp allocHookStack ∗ Frame) := by
    sep_ac_rfl
  rw [hpull]
  apply SepWP.pure_elim; rintro ⟨holdCap_lt, holdPtr_ne⟩
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  by_cases hcap0 : oldCap = 0#64
  · subst hcap0
    simp only [↓reduceIte, sepConj_emp]
    apply sepWP_seg_416 (mid := (blkPl_416).base + 4048#64)
    intro _m_strip
    wp_steps 7
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn])
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.weaken_pre
      (by try simp only [arm64_norm, wp_norm, hrun, hsp]
          exact Entails.of_eq (by sep_ac_rfl))
      (hcont [] _ 0#64 oldPtr FreeOnlyEvs.nil
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn])
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, Reg.x19, hrun, hsp, hx19])
        (by simp only [arm64_norm, wp_norm, Reg.x20, hrun, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm, Reg.x21, hrun, hsp, hx20, hx28, hmul24])
        (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx28])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp]))
  · have hcap_beq : (oldCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap0
    obtain ⟨hshl_nat, hshl_bv, hshl_toNat⟩ := shl1_oldCap_eq holdCap_lt
    simp only [hcap0, ↓reduceIte]
    apply sepWP_seg_416 (mid := lsρ spqrRustDeallocSym)
    intro _m_strip0
    wp_steps 11
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn, hcap_beq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn, hcap_beq,
            Bool.false_eq_true, ↓reduceIte])
      fun _m_real0 _hnsp0 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp0.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn, hcap_beq,
              Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    wp_conv_pre =>
      simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx28, hmul24, hcmn, hcap_beq,
        Bool.false_eq_true, ↓reduceIte, hshl_nat, hshl_bv]
    wp_call hdealloc (oldPtr, oldCap.toNat * 2, 2, st)
    clear hdealloc
    have htr_sf : sf.trace = s.trace := by
      have ht := (by assumption : AllocCallPreserved _ sf).2.1
      simpa [arm64_norm, wp_norm, hsp] using ht
    have hsp_sf : sf.sp = fsp := by
      simp only [arm64_norm, wp_norm, hsp, *]
    have hevs : FreeOnlyEvs (rustDeallocEvents (oldCap.toNat * 2) 2) :=
      FreeOnlyEvs.singleton 2 (oldCap.toNat * 2)
    refine SepWP.weaken_pre
      (by try simp only [arm64_norm, wp_norm, hsp]
          exact Entails.of_eq (by sep_ac_rfl))
      (hcont (rustDeallocEvents (oldCap.toNat * 2) 2) sf oldCap oldPtr hevs hpc_sf hrun_sf hsp_sf
        htr_sf
        (by simp only [arm64_norm, wp_norm, hrun, hsp, *])
        (by simp only [arm64_norm, wp_norm, Reg.x19, hrun, hsp, hx19, *])
        (by simp only [arm64_norm, wp_norm, Reg.x20, hrun, hsp, hx20, hx28, hmul24, *])
        (by simp only [arm64_norm, wp_norm, Reg.x21, hrun, hsp, hx20, hx28, hmul24, *])
        (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hsp, *])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp, *])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx28, *])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp, *]))

/-- Budget-threaded sub-block 2 (`+4048 -> +4088`):
    writes the new `Poly` header `(n, newPtr, n)` into `slot = (fsp + 256) + 24 * j`,
    folds `polyOf A.repAlloc slot (pointToPolyPure pt)`, and deallocates
    `ptVecBufAt A.repAlloc ptVecPtr pt.value`, emitting a `FreeOnlyEvs` event sequence. -/
theorem storeNewPolyAndFreePtVec_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s : State) (fsp oldCap oldPtr newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4048#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = (fsp + 256#64) + BitVec.ofNat 64 (24 * j))
    (hx21 : s.readReg64 .x21 = ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ (evs : List AllocEvent) s1,
      FreeOnlyEvs evs →
      s1.pc = (blkPl_416).base + 4088#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
       ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
       newPolyBufAt A.repAlloc newPtr pt ∗
       ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hdealloc hcont ⊢
  by_cases hn0 : pt.value.length = 0
  · have hpoly0 :=
      polyOf_of_newPolyBufAt A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hpoly0
    apply sepWP_seg_416 (mid := (blkPl_416).base + 4088#64)
    intro _m_strip
    wp_steps 6
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hn0])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hn0])
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hn0]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    apply SepWP.fold hpoly0 (by sep_frame)
    simp only [hn0, BitVec.ofNat_eq_ofNat] at hcont ⊢
    refine SepWP.weaken_pre
      (Entails.trans (Entails.of_eq (show _ =
        ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
        (A.pool lim (M.stepEvents [] st) _ ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 40#64) ↦₆₄ 0#64) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ 0#64) ∗
         stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl))
        (ptVecBufAt_zero_drop A.repAlloc ptVecPtr pt.value hn0 _))
      (hcont [] _ FreeOnlyEvs.nil
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hn0])
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hn0])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx28])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp]))
  · have hn_pos : 0 < pt.value.length := by omega
    obtain ⟨hn_beq, hn_bne⟩ := ofNat_pos_ne_zero hn_pos hbound
    obtain ⟨hshl2_nat, hshl2_bv, hshl2_toNat⟩ := shl2_len_eq hbound
    refine SepWP.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left
          (ptVecBufAt_pos_entails A.repAlloc ptVecPtr pt.value hn_pos hbound))))))) ?_
    have hpull :
        A.pool lim st s ∗
        (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
        ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
        newPolyBufAt A.repAlloc newPtr pt ∗
        (⌜ptVecPtr ≠ 0#64⌝ ∗ A.repAlloc.live ptVecPtr (4 * pt.value.length) 2 ∗
          memRegion ptVecPtr (4 * pt.value.length)) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        ((fsp + 640#64) ↦₆₄ newPtr) ∗
        ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
        stackAt fsp allocHookStack ∗ Frame =
        ⌜ptVecPtr ≠ 0#64⌝ ∗
        (A.pool lim st s ∗
         (((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ↦₆₄ oldCap) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 8#64) ↦₆₄ oldPtr) ∗
         ((((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) + 16#64) ↦₆₄ 0#64) ∗
         newPolyBufAt A.repAlloc newPtr pt ∗
         A.repAlloc.live ptVecPtr (4 * pt.value.length) 2 ∗
         memRegion ptVecPtr (4 * pt.value.length) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) := by
      sep_ac_rfl
    rw [hpull]
    apply SepWP.pure_elim; intro hptVec_ne
    apply sepWP_seg_416 (mid := lsρ spqrRustDeallocSym)
    intro _m_strip0
    wp_steps 10
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hx26, hn_beq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hx26, hn_beq,
            Bool.false_eq_true, ↓reduceIte])
      fun _m_real0 _hnsp0 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp0.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hx26, hn_beq,
              Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    wp_conv_pre =>
      simp only [arm64_norm, wp_norm, hrun, hsp, hx19, hx20, hx21, hx26, hn_beq,
        Bool.false_eq_true, ↓reduceIte, hshl2_nat, hshl2_bv]
    wp_call hdealloc (ptVecPtr, 4 * pt.value.length, 2, st)
    clear hdealloc
    have htr_sf : sf.trace = s.trace := by
      have ht := (by assumption : AllocCallPreserved _ sf).2.1
      simpa [arm64_norm, wp_norm, hsp] using ht
    have hsp_sf : sf.sp = fsp := by
      simp only [arm64_norm, wp_norm, hsp, *]
    have hevs : FreeOnlyEvs (rustDeallocEvents (4 * pt.value.length) 2) :=
      FreeOnlyEvs.singleton 2 (4 * pt.value.length)
    apply SepWP.fold
      (polyOf_of_newPolyBufAt A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) newPtr pt hbound)
      (by sep_frame)
    refine SepWP.weaken_pre
      (by try simp only [arm64_norm, wp_norm, hsp]
          exact Entails.of_eq (by sep_ac_rfl))
      (hcont (rustDeallocEvents (4 * pt.value.length) 2) sf hevs hpc_sf hrun_sf hsp_sf htr_sf
        (by simp only [arm64_norm, wp_norm, hrun, hsp, *])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp, *])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx28, *])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp, *]))

/-- Budget-threaded full per-iteration cleanup (`+4004 -> +976 / +4424`):
    deallocates the dummy `Poly` buffer in `slot j`, writes the newly constructed `Poly` into
    `slot j`, deallocates `ptVecBufAt`, reloads `x20 = j + 1` and `x19 = ptsBase`, and branches to
    `+976` (`j < 15`) or `+4424` (`j = 15`), emitting a `FreeOnlyEvs` event sequence. -/
theorem cleanupIter_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s : State) (fsp ptsBase newPtr ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hbound : pt.value.length ≤ 0x0555555555555555)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 4004#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 pt.value.length)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hcont : ∀ (evs : List AllocEvent) s1,
      FreeOnlyEvs evs →
      s1.pc = (if j == 15 then (blkPl_416).base + 4424#64 else (blkPl_416).base + 976#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = ptsBase →
      s1.readReg64 .x20 = BitVec.ofNat 64 (j + 1) →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim (M.stepEvents evs st) s1 ∗
         polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) (pointToPolyPure pt) ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 88#64) ↦₆₄ ptsBase) ∗
         ((fsp + 640#64) ↦₆₄ newPtr) ∗
         ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       polyOf A.repAlloc ((fsp + 256#64) + BitVec.ofNat 64 (24 * j)) ⟨[]⟩ ∗
       newPolyBufAt A.repAlloc newPtr pt ∗
       ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (deallocOldPolySlot_placed_sepWP hA s fsp hfsp_align j pt.value.length hbound
      (newPolyBufAt A.repAlloc newPtr pt ∗
       ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗
       ((fsp + 640#64) ↦₆₄ newPtr) ∗
       ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗ Frame)
      hpc hrun hsp hx19 hx20 hx28 ?_)
  intro evs1 s1 oldCap oldPtr hevs1 hpc1 hrun1 hsp1 htr1 hvregs1
    hx19_1 hx20_1 hx21_1 hx26_1 hx27_1 hx28_1 hx29_1
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (storeNewPolyAndFreePtVec_placed_sepWP hA (st := M.stepEvents evs1 st)
      s1 fsp oldCap oldPtr newPtr ptVecPtr hfsp_align j pt hbound
      (((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 88#64) ↦₆₄ ptsBase) ∗ Frame)
      hpc1 hrun1 hsp1 hx19_1 hx20_1 hx21_1 (hx26_1.trans hx26) hx28_1 ?_)
  intro evs2 s2 hevs2 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx28_2 hx29_2
  have hstep_app :
      M.stepEvents evs2 (M.stepEvents evs1 st) = M.stepEvents (evs1 ++ evs2) st :=
    (M.stepEvents_append evs1 evs2 st).symm
  have hevs12 : FreeOnlyEvs (evs1 ++ evs2) := FreeOnlyEvs.append hevs1 hevs2
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc2 hcont ⊢
  by_cases hj15 : j = 15
  · subst hj15
    apply sepWP_seg_416 (mid := (blkPl_416).base + 4424#64)
    intro _m_strip
    wp_steps 5
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
      (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.weaken_pre
      (by rw [hstep_app]; exact Entails.of_eq (by sep_ac_rfl))
      (hcont (evs1 ++ evs2) _ hevs12
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm, Reg.x19, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, Reg.x20, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun2, hsp2, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun2, hsp2, hx28_2])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun2, hsp2, hx29_2, hx29_1]))
  · have hj15_beq : (j == 15) = false := beq_eq_false_iff_ne.mpr hj15
    have hcmp_sub : (BitVec.ofNat 64 (j + 1) - 16#64 == 0#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_eq : (BitVec.ofNat 64 (j + 1) == 16#64) = false := by
      apply beq_eq_false_iff_ne.mpr; bv_omega
    have hcmp_bne : (BitVec.ofNat 64 (j + 1) != 16#64) = true := by
      simp [bne, hcmp_eq]
    apply sepWP_seg_416 (mid := (blkPl_416).base + 976#64)
    intro _m_strip
    wp_steps 4
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hcmp_sub, hcmp_eq, hcmp_bne,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hcmp_sub, hcmp_eq, hcmp_bne,
            Bool.false_eq_true, ↓reduceIte])
      fun _m_real _hnsp => ?_
    refine SepWP.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hcmp_sub, hcmp_eq, hcmp_bne,
              Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.weaken_pre
      (by rw [hstep_app]; exact Entails.of_eq (by sep_ac_rfl))
      (hcont (evs1 ++ evs2) _ hevs12
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hj15_beq, hcmp_sub, hcmp_eq, hcmp_bne,
              Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hcmp_sub, hcmp_eq, hcmp_bne,
              Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, htr2, htr1])
        (by simp only [arm64_norm, wp_norm, hrun2, hsp2, hvregs2, hvregs1])
        (by simp only [arm64_norm, wp_norm, Reg.x19, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, Reg.x20, hrun2, hsp2])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun2, hsp2, hx27_2, hx27_1])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun2, hsp2, hx28_2])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun2, hsp2, hx29_2, hx29_1]))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysProofPlacedABudget
