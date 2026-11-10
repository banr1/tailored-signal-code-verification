/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux2
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoopPlaced
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded `Poly::lagrange_sum` Loop

Relocatable `[LibsignalPlacement]` verification of `Poly::lagrange_sum` (`+2608 -> +3908`) and
`lagrangeSumAndFree_gen_placed_sepWPp` (`+2608 -> +4004`) threading `RustCliAllocBudget M`,
`BudgetLimits`, and `LagrangeSumStepEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl sepWP_seq_lscl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt arrayAt_cons)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt parallelMult)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (gf16SliceAt polyListOf polyOf ptAt ptSliceAt ptStride)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare (lagrangePrepareStack)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (addAssignCoeffs_length_eq_pl addAssignCoeffs_nil_left_pl basisVecAt
   lagrangeSumFoldPoly_cons_pl lagrangeSumFoldPoly_nil_left_pl lagrangeSumFoldPoly_pl
   lagrangeSum_eq_foldPoly_pl memRegion24_off_eq_polyHeader_pl
   memRegion_112_fold_sum_pl memRegion_112_split_sum_pl multAssign_length_pl
   parallelMult_length_pl polyListOf_cons_fbl
   sepWPp_seq_lscl_fb shiftSlotsRawAt_pl shiftTablePadAt_pl
   stackAt_lagrangePrepare_split_alloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
   RustCliAllocBudget SeqEnv fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsBudget
  (LagrangeSumStepEnv RepeatSeqEnv lagrangeSumStepEnv_nonempty repeatSeqEnv_nonempty)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1PlacedBudget
  (LagrangeSumCloneEnv addAssignFirst_placed_sepWP addAssignNext_placed_sepWP
   lagrangeSumCloneEvents lagrangeSumClone_placed_sepWPp lagrangeSumDeallocEvents
   lagrangeSumDeallocEvents_freeOnly lagrangeSumDeallocNext_placed_sepWP
   lagrangeSumSetup_placed_sepWP)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux
  (parallelMult_placed_sepWP)
export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudgetAux2
  (basisElemDeallocLoop_placed_sepWP lagrangeSumCleanup_placed_sepWP)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Iteration and Loop Event Sequences and `FitsEnv` Bridges -/

/-- Exact allocator event sequence of one `Poly::lagrange_sum` iteration (`+2668 -> +2668 / +3908`):
    `Poly::clone` (`2 * n` bytes, align `2`) followed by temporary `clonePtr` deallocation. -/
def lagrangeSumIterEvents (n : Nat) : List AllocEvent :=
  lagrangeSumCloneEvents n ++ lagrangeSumDeallocEvents n

/-- `lagrangeSumIterEvents n` inhabits `LagrangeSumStepEnv n`. -/
theorem lagrangeSumIterEvents_satisfies_stepEnv (n : Nat) :
    LagrangeSumStepEnv n (lagrangeSumIterEvents n) :=
  SeqEnv.append rfl (lagrangeSumDeallocEvents_freeOnly n)

/-- `FitsEnv` on `LagrangeSumStepEnv n` entails `FitsEnv` on `LagrangeSumCloneEnv n`. -/
theorem fitsEnv_lagrangeSumClone_of_stepEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (n : Nat) (hfit : FitsEnv M lim st (LagrangeSumStepEnv n)) :
    FitsEnv M lim st (LagrangeSumCloneEnv n) := by
  intro evs hevs
  rw [hevs]
  exact hfit (lagrangeSumCloneEvents n) (Or.inl rfl)

/-- Exact allocator event sequence of `k` iterations of `Poly::lagrange_sum` at degree `n`. -/
def lagrangeSumLoopEvents (k n : Nat) : List AllocEvent :=
  (List.replicate k (lagrangeSumIterEvents n)).flatten

/-- `lagrangeSumLoopEvents k n` inhabits `RepeatSeqEnv k (LagrangeSumStepEnv n)`. -/
theorem lagrangeSumLoopEvents_satisfies_repeatSeqEnv :
    ∀ (k n : Nat), RepeatSeqEnv k (LagrangeSumStepEnv n) (lagrangeSumLoopEvents k n)
  | 0, _ => rfl
  | k + 1, n => by
    unfold lagrangeSumLoopEvents
    rw [List.replicate_succ, List.flatten_cons]
    exact SeqEnv.append (lagrangeSumIterEvents_satisfies_stepEnv n)
      (lagrangeSumLoopEvents_satisfies_repeatSeqEnv k n)

theorem lagrangeSumLoopEvents_succ (k n : Nat) :
    lagrangeSumLoopEvents (k + 1) n = lagrangeSumIterEvents n ++ lagrangeSumLoopEvents k n := by
  unfold lagrangeSumLoopEvents
  rw [List.replicate_succ, List.flatten_cons]

/-- Extract `FitsEnv` for a single step from `RepeatSeqEnv 1 E`. -/
theorem fitsEnv_of_repeatSeqEnv_one {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E : List AllocEvent → Prop} (hfit : FitsEnv M lim st (RepeatSeqEnv 1 E)) :
    FitsEnv M lim st E := by
  intro evs hevs
  have h1 : RepeatSeqEnv 1 E (evs ++ []) := SeqEnv.append hevs rfl
  rw [List.append_nil] at h1
  exact hfit evs h1

/-- Split `FitsEnv` on `RepeatSeqEnv (r + 2) (LagrangeSumStepEnv n)` into the head step and
    continuation `RepeatSeqEnv (r + 1) (LagrangeSumStepEnv n)` after any `evs1` satisfying
    `LagrangeSumStepEnv n`. -/
theorem fitsEnv_repeatSeqEnv_lagrangeSum_succ {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (r n : Nat) (hfit : FitsEnv M lim st (RepeatSeqEnv (r + 2) (LagrangeSumStepEnv n))) :
    FitsEnv M lim st (LagrangeSumStepEnv n) ∧
      ∀ evs1 : List AllocEvent, LagrangeSumStepEnv n evs1 →
        FitsEnv M lim (M.stepEvents evs1 st) (RepeatSeqEnv (r + 1) (LagrangeSumStepEnv n)) := by
  constructor
  · intro evs1 hevs1
    rcases repeatSeqEnv_nonempty (lagrangeSumStepEnv_nonempty n) (r + 1) with ⟨evs2, hevs2⟩
    exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfit _ (SeqEnv.append hevs1 hevs2))).1
  · intro evs1 hevs1 evs2 hevs2
    exact ((fitsEvents_append M lim evs1 evs2 st).mp (hfit _ (SeqEnv.append hevs1 hevs2))).2

example : ∃ evs, RepeatSeqEnv 3 (LagrangeSumStepEnv 8) evs :=
  ⟨lagrangeSumLoopEvents 3 8, lagrangeSumLoopEvents_satisfies_repeatSeqEnv 3 8⟩

example :
    lagrangeSumLoopEvents 3 8 =
      [.alloc 16, .free 2 16, .alloc 16, .free 2 16, .alloc 16, .free 2 16] :=
  rfl

/-! ## 2. Budget-Threaded `Poly::lagrange_sum` Steps & Loop (`+2608 -> +3908`) -/

/-- Budget-threaded iteration `i = 0` of `Poly::lagrange_sum` (`+2668 -> +2668 / +3908`). -/
theorem lagrangeSumStepFirst_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (m n : Nat) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hplen : poly.coefficients.length = n) (h1m : 1 + m = n)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 0)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (LagrangeSumCloneEnv n))
    (hcont : ∀ s1 u112' u136',
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (if m = 0 then
          (blkPl_416).base + 3908#64
        else
          (blkPl_416).base + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 1 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (lagrangeSumIterEvents n) st) s1 ∗
         gf16SliceAt accPtr (Poly.addAssign Poly.zero (poly.multAssign pt.y)).coefficients ∗
         polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt_pl fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       memRegion accPtr (2 * n) ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ 0#64) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hcs_ne : poly.coefficients ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumClone_placed_sepWPp hA 0 n pt poly hn_pos hn hplen
      s0 s hcl fsp basisPtr ptVecPtr v27 u120 u128 hfsp_align
      (memRegion accPtr (2 * n) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) _R
      hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 hfit ?_)
  intro s1 clonePtr hcl1 hclone_ne hpc1 hrun1 hsp1 htr1 hvregs1
    hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_seq_lscl_fb hcl1
    (mid := if m = 0 then (blkPl_416).base + 3908#64 else (blkPl_416).base + 2668#64)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (parallelMult_placed_sepWP
      (M := M) (A := A) (lim := lim) (st := M.stepEvents (lagrangeSumCloneEvents n) st)
      poly.coefficients hcs_ne (by omega) pt.y.value
      s1 hcl1 fsp clonePtr basisPtr (BitVec.ofNat 64 n) ptVecPtr v27 u112 u136 hfsp_align
      (A.live clonePtr (2 * n) 2 ∗ memRegion accPtr (2 * n) ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ 0#64) ∗
       stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 (by rw [hx20_1, hplen]) hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 ?_)
  intro s2 hcl2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u112'
  apply SepWP.exists_elim; intro u136'
  have hpm_len : (parallelMult pt.y poly.coefficients).length = n := by
    rw [parallelMult_length_pl, hplen]
  have hpm_ne : parallelMult pt.y poly.coefficients ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  apply sepWP_seq_lscl (mid := (blkPl_416).base + 2640#64) hcl2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (addAssignFirst_placed_sepWP
      (M := M) (A := A) (lim := lim) (st := M.stepEvents (lagrangeSumCloneEvents n) st)
      (parallelMult pt.y poly.coefficients) n hpm_ne hpm_len hn
      s2 fsp accPtr clonePtr hfsp_align
      (A.live clonePtr (2 * n) 2 ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 0) ∗
       ((fsp + 136#64) ↦₆₄ u136') ∗ shiftSlotsRawAt_pl fsp ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc2 hrun2 hsp2 hx22_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx1_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  apply SepWP.done hpc3 hrun3
  intro hcl3
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumDeallocNext_placed_sepWP hA (parallelMult pt.y poly.coefficients) 0 m n
      hn_pos hn hpm_len h1m s3 hcl3 fsp clonePtr hclone_ne hfsp_align
      (gf16SliceAt accPtr (Poly.addAssignCoeffs [] (parallelMult pt.y poly.coefficients)) ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
      hpc3 hrun3 hsp3 hx1_3 hx22_3 (by rw [hx25_3, hx25_2]) ?_)
  intro s4 _hcl4_inner hpc4 hrun4 hsp4 htr4 hvregs4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  apply SepWP.done hpc4 hrun4
  intro hcl4
  have hscalar : Poly.addAssignCoeffs [] (parallelMult pt.y poly.coefficients) =
      (Poly.addAssign Poly.zero (poly.multAssign pt.y)).coefficients := rfl
  have hstep_iter :
      M.stepEvents (lagrangeSumDeallocEvents n) (M.stepEvents (lagrangeSumCloneEvents n) st) =
        M.stepEvents (lagrangeSumIterEvents n) st :=
    (M.stepEvents_append _ _ st).symm
  rw [hscalar, hstep_iter]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont s4 u112' u136' hcl4 hpc4 hrun4 hsp4
      (by rw [htr4, htr3, htr2, htr1])
      (by rw [hvregs4, hvregs3, hvregs2, hvregs1])
      hx21_4
      (by rw [hx24_4, hx24_3, hx24_2])
      hx25_4
      (by rw [hx26_4, hx26_3, hx26_2])
      (by rw [hx27_4, hx27_3, hx27_2])
      (by rw [hx28_4, hx28_3, hx28_2])
      (by rw [hx29_4, hx29_3, hx29_2, hx29_1]))

/-- Budget-threaded iteration `i > 0` of `Poly::lagrange_sum` (`+2668 -> +2668 / +3908`). -/
theorem lagrangeSumStepNext_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (i m n : Nat) (acc : Poly) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (halen : acc.coefficients.length = n) (hplen : poly.coefficients.length = n)
    (him : (i + 1) + m = n)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2668#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (LagrangeSumCloneEnv n))
    (hcont : ∀ s1 u112' u136',
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (if m = 0 then
          (blkPl_416).base + 3908#64
        else
          (blkPl_416).base + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (lagrangeSumIterEvents n) st) s1 ∗
         gf16SliceAt accPtr (Poly.addAssign acc (poly.multAssign pt.y)).coefficients ∗
         polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt_pl fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       gf16SliceAt accPtr acc.coefficients ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hcs_ne : poly.coefficients ≠ [] := List.ne_nil_of_length_pos (by omega)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumClone_placed_sepWPp hA i n pt poly hn_pos hn hplen
      s0 s hcl fsp basisPtr ptVecPtr v27 u120 u128 hfsp_align
      (gf16SliceAt accPtr acc.coefficients ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame) _R
      hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 hfit ?_)
  intro s1 clonePtr hcl1 hclone_ne hpc1 hrun1 hsp1 htr1 hvregs1
    hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_seq_lscl_fb hcl1
    (mid := if m = 0 then (blkPl_416).base + 3908#64 else (blkPl_416).base + 2668#64)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (parallelMult_placed_sepWP
      (M := M) (A := A) (lim := lim) (st := M.stepEvents (lagrangeSumCloneEvents n) st)
      poly.coefficients hcs_ne (by omega) pt.y.value
      s1 hcl1 fsp clonePtr basisPtr (BitVec.ofNat 64 n) ptVecPtr v27 u112 u136 hfsp_align
      (A.live clonePtr (2 * n) 2 ∗ gf16SliceAt accPtr acc.coefficients ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame)
      hpc1 hrun1 hsp1 (by rw [hx20_1, hplen]) hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 ?_)
  intro s2 hcl2 hpc2 hrun2 hsp2 htr2 hvregs2 hx20_2 hx22_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro u112'
  apply SepWP.exists_elim; intro u136'
  have hpm_len : (parallelMult pt.y poly.coefficients).length = n := by
    rw [parallelMult_length_pl, hplen]
  have hpm_ne : parallelMult pt.y poly.coefficients ≠ [] :=
    List.ne_nil_of_length_pos (by omega)
  apply sepWP_seq_lscl (mid := (blkPl_416).base + 2640#64) hcl2
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (addAssignNext_placed_sepWP
      (M := M) (A := A) (lim := lim) (st := M.stepEvents (lagrangeSumCloneEvents n) st)
      acc.coefficients (parallelMult pt.y poly.coefficients) n
      hpm_ne halen hpm_len hn s2 fsp accPtr clonePtr hfsp_align
      (A.live clonePtr (2 * n) 2 ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       ((fsp + 136#64) ↦₆₄ u136') ∗ shiftSlotsRawAt_pl fsp ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc2 hrun2 hsp2 hx22_2 ?_)
  intro s3 hpc3 hrun3 hsp3 htr3 hvregs3 hx1_3 hx22_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
  apply SepWP.done hpc3 hrun3
  intro hcl3
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumDeallocNext_placed_sepWP hA (parallelMult pt.y poly.coefficients) i m n
      hn_pos hn hpm_len him s3 hcl3 fsp clonePtr hclone_ne hfsp_align
      (gf16SliceAt accPtr (Poly.addAssignCoeffs acc.coefficients (parallelMult pt.y poly.coefficients)) ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ Frame)
      hpc3 hrun3 hsp3 hx1_3 hx22_3 (by rw [hx25_3, hx25_2]) ?_)
  intro s4 _hcl4_inner hpc4 hrun4 hsp4 htr4 hvregs4 hx21_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4
  apply SepWP.done hpc4 hrun4
  intro hcl4
  have hscalar : Poly.addAssignCoeffs acc.coefficients (parallelMult pt.y poly.coefficients) =
      (Poly.addAssign acc (poly.multAssign pt.y)).coefficients := rfl
  have hstep_iter :
      M.stepEvents (lagrangeSumDeallocEvents n) (M.stepEvents (lagrangeSumCloneEvents n) st) =
        M.stepEvents (lagrangeSumIterEvents n) st :=
    (M.stepEvents_append _ _ st).symm
  rw [hscalar, hstep_iter]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont s4 u112' u136' hcl4 hpc4 hrun4 hsp4
      (by rw [htr4, htr3, htr2, htr1])
      (by rw [hvregs4, hvregs3, hvregs2, hvregs1])
      hx21_4
      (by rw [hx24_4, hx24_3, hx24_2])
      hx25_4
      (by rw [hx26_4, hx26_3, hx26_2])
      (by rw [hx27_4, hx27_3, hx27_2])
      (by rw [hx28_4, hx28_3, hx28_2])
      (by rw [hx29_4, hx29_3, hx29_2, hx29_1]))

/-- Budget-threaded inductive tail loop of `Poly::lagrange_sum` for `i ≥ 1` (`+2668 -> +3908`). -/
theorem lagrangeSumTailLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext) :
    ∀ (ptsRest : List Pt) (polysRest : List Poly) (i n : Nat) (acc : Poly) {st : M.σ}
      (hrest_ne : ptsRest ≠ []) (hlen_eq : ptsRest.length = polysRest.length)
      (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
      (halen : acc.coefficients.length = n)
      (hplen : ∀ p ∈ polysRest, p.coefficients.length = n)
      (hin : i + ptsRest.length = n)
      (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
      (fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136 : BitVec 64)
      (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame _R : SepProp)
      (hpc : s.pc = (blkPl_416).base + 2668#64)
      (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
      (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 i)
      (hx24 : s.readReg64 .x24 = basisPtr)
      (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
      (hx26 : s.readReg64 .x26 = ptVecPtr)
      (hx27 : s.readReg64 .x27 = v27)
      (hx28 : s.readReg64 .x28 = 24#64)
      (hx29 : s.readReg64 .x29 = fsp + 1104#64)
      (hfit : FitsEnv M lim st (RepeatSeqEnv ptsRest.length (LagrangeSumStepEnv n)))
      (hcont : ∀ s1 u112' u120' u128' u136',
        LibsignalCodeLoaded lsmpl s1.mem →
        s1.pc = (blkPl_416).base + 3908#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x24 = basisPtr →
        s1.readReg64 .x25 = BitVec.ofNat 64 n →
        s1.readReg64 .x26 = ptVecPtr →
        s1.readReg64 .x27 = v27 →
        s1.readReg64 .x28 = 24#64 →
        s1.readReg64 .x29 = fsp + 1104#64 →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) s1
          (A.pool lim (M.stepEvents (lagrangeSumLoopEvents ptsRest.length n) st) s1 ∗
           gf16SliceAt accPtr (lagrangeSumFoldPoly_pl acc ptsRest polysRest).coefficients ∗
           polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) polysRest ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ptsRest ∗
           ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
           ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
           ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
           shiftSlotsRawAt_pl fsp ∗
           ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q Q_panic),
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s
        (A.pool lim st s ∗
         gf16SliceAt accPtr acc.coefficients ∗
         polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) polysRest ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ptsRest ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
         ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
         shiftSlotsRawAt_pl fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic
  | [], _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    absurd rfl hne
  | _ :: _, [], _, _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by
    simp at hlen
  | pt :: ptsTail, poly :: polysTail, i, n, acc, st, _, hlen_eq, hn_pos, hn, halen, hplen, hin,
    s0, s, hcl, fsp, accPtr, basisPtr, ptVecPtr, v27, u112, u120, u128, u136,
    hfsp_align, Frame, _R, hpc, hrun, hsp, htrace,
    hx21, hx24, hx25, hx26, hx27, hx28, hx29, hfit, hcont => by
    have hpoly_len : poly.coefficients.length = n := hplen poly (List.mem_cons_self ..)
    have htail_len : ∀ p ∈ polysTail, p.coefficients.length = n :=
      fun p hp => hplen p (List.mem_cons_of_mem poly hp)
    have him : (i + 1) + ptsTail.length = n := by simp at hin; omega
    have hbasis_add : (basisPtr + BitVec.ofNat 64 (24 * i)) + 24#64 =
        basisPtr + BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show 24 * (i + 1) = 24 * i + 24 by omega, BitVec.ofNat_add]; bv_omega
    have hpt_add : (ptVecPtr + BitVec.ofNat 64 (4 * i)) + 4#64 =
        ptVecPtr + BitVec.ofNat 64 (4 * (i + 1)) := by
      rw [show 4 * (i + 1) = 4 * i + 4 by omega, BitVec.ofNat_add]; bv_omega
    have hpoly_cons :
        polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) (poly :: polysTail) =
        (polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) polysTail) := by
      rw [polyListOf_cons_fbl, hbasis_add]
    have hpt_cons :
        ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * i)) (pt :: ptsTail) =
        (ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * (i + 1))) ptsTail) := by
      simp only [ptSliceAt, arrayAt, ptStride, BitVec.ofNat_eq_ofNat, hpt_add]
    have hfit_clone : FitsEnv M lim st (LagrangeSumCloneEnv n) := by
      cases ptsTail with
      | nil =>
        exact fitsEnv_lagrangeSumClone_of_stepEnv n (fitsEnv_of_repeatSeqEnv_one hfit)
      | cons _ _ =>
        exact fitsEnv_lagrangeSumClone_of_stepEnv n
          (fitsEnv_repeatSeqEnv_lagrangeSum_succ _ n hfit).1
    rw [hpoly_cons, hpt_cons]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (lagrangeSumStepNext_placed_sepWPp hA i ptsTail.length n acc pt poly
        hn_pos hn halen hpoly_len him s0 s hcl fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136
        hfsp_align
        (polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) polysTail ∗
         ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * (i + 1))) ptsTail ∗ Frame) _R
        hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 hfit_clone ?_)
    intro s1 u112' u136' hcl1 hpc1 hrun1 hsp1 htr1 hvregs1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
    cases ptsTail with
    | nil =>
      cases polysTail with
      | nil =>
        simp only [List.length_nil, ↓reduceIte] at hpc1
        simp only [lagrangeSumFoldPoly_cons_pl, lagrangeSumFoldPoly_nil_left_pl] at hcont
        have hloop1 : lagrangeSumLoopEvents [pt].length n = lagrangeSumIterEvents n := by
          simp [lagrangeSumLoopEvents]
        refine SepWPp.weaken_pre
          (by rw [hpoly_cons, hpt_cons, hloop1]; exact Entails.of_eq (by sep_ac_rfl))
          (hcont s1 u112' (BitVec.ofNat 64 i) (BitVec.ofNat 64 (2 * n)) u136' hcl1
            hpc1 hrun1 hsp1 htr1 hvregs1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)
      | cons _ _ => simp at hlen_eq
    | cons pt2 ptsTail' =>
      cases polysTail with
      | nil => simp at hlen_eq
      | cons poly2 polysTail' =>
        have hne' : pt2 :: ptsTail' ≠ [] := List.cons_ne_nil _ _
        have hlen_eq' : (pt2 :: ptsTail').length = (poly2 :: polysTail').length := by
          simp at hlen_eq ⊢; omega
        have halen' : (Poly.addAssign acc (poly.multAssign pt.y)).coefficients.length = n := by
          unfold Poly.addAssign
          rw [addAssignCoeffs_length_eq_pl (by rw [halen, multAssign_length_pl, hpoly_len]), halen]
        have hfit_tail : FitsEnv M lim (M.stepEvents (lagrangeSumIterEvents n) st)
            (RepeatSeqEnv (pt2 :: ptsTail').length (LagrangeSumStepEnv n)) :=
          (fitsEnv_repeatSeqEnv_lagrangeSum_succ ptsTail'.length n hfit).2
            (lagrangeSumIterEvents n) (lagrangeSumIterEvents_satisfies_stepEnv n)
        simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc1
        refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
          (lagrangeSumTailLoop_placed_sepWPp hA (pt2 :: ptsTail') (poly2 :: polysTail') (i + 1) n
            (Poly.addAssign acc (poly.multAssign pt.y))
            (st := M.stepEvents (lagrangeSumIterEvents n) st)
            hne' hlen_eq' hn_pos hn halen' htail_len him
            s0 s1 hcl1 fsp accPtr basisPtr ptVecPtr v27 u112' (BitVec.ofNat 64 i)
            (BitVec.ofNat 64 (2 * n)) u136' hfsp_align
            (polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
             ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗ Frame) _R
            hpc1 hrun1 hsp1 htr1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hfit_tail ?_)
        intro s2 u112'' u120'' u128'' u136'' hcl2 hpc2 hrun2 hsp2 htr2 hvregs2
          hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
        simp only [lagrangeSumFoldPoly_cons_pl] at hcont
        have hstep_loop :
            M.stepEvents (lagrangeSumLoopEvents (pt2 :: ptsTail').length n)
              (M.stepEvents (lagrangeSumIterEvents n) st) =
              M.stepEvents (lagrangeSumLoopEvents (pt :: pt2 :: ptsTail').length n) st := by
          simp only [List.length_cons]
          rw [lagrangeSumLoopEvents_succ (ptsTail'.length + 1) n, M.stepEvents_append]
        refine SepWPp.weaken_pre
          (by rw [hpoly_cons, hpt_cons, hstep_loop]; exact Entails.of_eq (by sep_ac_rfl))
          (hcont s2 u112'' u120'' u128'' u136'' hcl2
            hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2)

/-- Budget-threaded full `Poly::lagrange_sum` loop (`+2608 -> +3908`). -/
theorem lagrangeSumLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (pts : List Pt) (polys : List Poly) (n : Nat)
    (hpts_ne : pts ≠ []) (hpts_len : pts.length = n) (hpolys_len : polys.length = n)
    (hn : n ≤ 0x0555555555555555)
    (hplen : ∀ p ∈ polys, p.coefficients.length = n)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u112 u120 u128 u136 u656 u664 u672 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hfit : FitsEnv M lim st (RepeatSeqEnv n (LagrangeSumStepEnv n)))
    (hcont : ∀ s1 u112' u120' u128' u136',
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (blkPl_416).base + 3908#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (lagrangeSumLoopEvents n n) st) s1 ∗
         gf16SliceAt accPtr (Poly.lagrangeSum pts polys).coefficients ∗
         polyListOf A.repAlloc basisPtr polys ∗
         ptSliceAt ptVecPtr pts ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
         ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
         shiftSlotsRawAt_pl fsp ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       memRegion accPtr (2 * n) ∗
       polyListOf A.repAlloc basisPtr polys ∗
       ptSliceAt ptVecPtr pts ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
       shiftSlotsRawAt_pl fsp ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗ ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  rcases pts with _ | ⟨pt0, ptsTail⟩
  · contradiction
  · rcases polys with _ | ⟨poly0, polysTail⟩
    · simp at hpts_len hpolys_len; omega
    · have hn_pos : 0 < n := by simp at hpts_len; omega
      have h1m : 1 + ptsTail.length = n := by simp at hpts_len; omega
      have hpoly0_len : poly0.coefficients.length = n := hplen poly0 (List.mem_cons_self ..)
      have htail_len : ∀ p ∈ polysTail, p.coefficients.length = n :=
        fun p hp => hplen p (List.mem_cons_of_mem poly0 hp)
      have hb0 : basisPtr + BitVec.ofNat 64 (24 * 0) = basisPtr := by bv_omega
      have hp0 : ptVecPtr + BitVec.ofNat 64 (4 * 0) = ptVecPtr := by bv_omega
      have hpoly_cons0 :
          polyListOf A.repAlloc basisPtr (poly0 :: polysTail) =
          (polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly0 ∗
           polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 1)) polysTail) := by
        rw [polyListOf_cons_fbl, hb0]
      have hpt_cons0 :
          ptSliceAt ptVecPtr (pt0 :: ptsTail) =
          (ptAt pt0 (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * 1)) ptsTail) := by
        unfold ptSliceAt; rw [arrayAt_cons, hp0]
      have hn_pts : n = ptsTail.length + 1 := by simp at hpts_len; omega
      have hfit' : FitsEnv M lim st (RepeatSeqEnv (ptsTail.length + 1) (LagrangeSumStepEnv n)) := by
        have hrep : RepeatSeqEnv n (LagrangeSumStepEnv n) =
            RepeatSeqEnv (ptsTail.length + 1) (LagrangeSumStepEnv n) :=
          congrArg (fun k => RepeatSeqEnv k (LagrangeSumStepEnv n)) hn_pts
        rwa [hrep] at hfit
      have hfit_clone0 : FitsEnv M lim st (LagrangeSumCloneEnv n) := by
        cases ptsTail with
        | nil =>
          exact fitsEnv_lagrangeSumClone_of_stepEnv n (fitsEnv_of_repeatSeqEnv_one hfit')
        | cons _ _ =>
          exact fitsEnv_lagrangeSumClone_of_stepEnv n
            (fitsEnv_repeatSeqEnv_lagrangeSum_succ _ n hfit').1
      apply sepWPp_seq_lscl_fb hcl (mid := (blkPl_416).base + 2668#64)
      refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (lagrangeSumSetup_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          n s fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
          u16 u64 u72 u80 u656 u664 u672
          (memRegion accPtr (2 * n) ∗
           polyListOf A.repAlloc basisPtr (poly0 :: polysTail) ∗
           ptSliceAt ptVecPtr (pt0 :: ptsTail) ∗
           ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 112#64) ↦₆₄ u112) ∗ ((fsp + 120#64) ↦₆₄ u120) ∗
           ((fsp + 128#64) ↦₆₄ u128) ∗ ((fsp + 136#64) ↦₆₄ u136) ∗
           shiftSlotsRawAt_pl fsp ∗ tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
           stackAt fsp allocHookStack ∗ Frame)
          hpc hrun hsp hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      apply SepWP.done hpc1 hrun1
      intro hcl1
      rw [hpoly_cons0, hpt_cons0]
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (lagrangeSumStepFirst_placed_sepWPp hA ptsTail.length n pt0 poly0
          hn_pos hn hpoly0_len h1m s0 s1 hcl1 fsp accPtr basisPtr ptVecPtr v27 u112 u120 u128 u136
          hfsp_align
          (polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 1)) polysTail ∗
           ptSliceAt (ptVecPtr + BitVec.ofNat 64 (4 * 1)) ptsTail ∗
           ((fsp + 16#64) ↦₆₄ cIdx) ∗ Frame) _R
          hpc1 hrun1 hsp1 (by rw [htr1, htrace])
          hx21_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hfit_clone0 ?_)
      intro s2 u112' u136' hcl2 hpc2 hrun2 hsp2 htr2 hvregs2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2
      cases ptsTail with
      | nil =>
        cases polysTail with
        | nil =>
          simp only [List.length_nil, ↓reduceIte] at hpc2
          have hn1 : n = 1 := by simp at hpts_len; omega
          have hsum_eq : Poly.lagrangeSum [pt0] [poly0] =
              Poly.addAssign Poly.zero (poly0.multAssign pt0.y) := by
            rw [lagrangeSum_eq_foldPoly_pl]; rfl
          have hloop1 : lagrangeSumLoopEvents n n = lagrangeSumIterEvents n := by
            rw [hn1]; simp [lagrangeSumLoopEvents]
          rw [← hsum_eq]
          refine SepWPp.weaken_pre
            (by rw [hpoly_cons0, hpt_cons0, hloop1]; exact Entails.of_eq (by sep_ac_rfl))
            (hcont s2 u112' (BitVec.ofNat 64 0) (BitVec.ofNat 64 (2 * n)) u136' hcl2
              hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1) hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2)
        | cons _ _ => simp at hpts_len hpolys_len; omega
      | cons pt1 ptsTail' =>
        cases polysTail with
        | nil => simp at hpts_len hpolys_len; omega
        | cons poly1 polysTail' =>
          have hne' : pt1 :: ptsTail' ≠ [] := List.cons_ne_nil _ _
          have hlen_eq' : (pt1 :: ptsTail').length = (poly1 :: polysTail').length := by
            simp at hpts_len hpolys_len ⊢; omega
          have halen' : (Poly.addAssign Poly.zero (poly0.multAssign pt0.y)).coefficients.length = n := by
            unfold Poly.addAssign Poly.zero
            rw [addAssignCoeffs_nil_left_pl, multAssign_length_pl, hpoly0_len]
          have hfit_tail : FitsEnv M lim (M.stepEvents (lagrangeSumIterEvents n) st)
              (RepeatSeqEnv (pt1 :: ptsTail').length (LagrangeSumStepEnv n)) :=
            (fitsEnv_repeatSeqEnv_lagrangeSum_succ ptsTail'.length n hfit').2
              (lagrangeSumIterEvents n) (lagrangeSumIterEvents_satisfies_stepEnv n)
          simp only [List.length_cons, Nat.succ_ne_zero, ↓reduceIte] at hpc2
          refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
            (lagrangeSumTailLoop_placed_sepWPp hA (pt1 :: ptsTail') (poly1 :: polysTail') 1 n
              (Poly.addAssign Poly.zero (poly0.multAssign pt0.y))
              (st := M.stepEvents (lagrangeSumIterEvents n) st)
              hne' hlen_eq' hn_pos hn halen' htail_len h1m
              s0 s2 hcl2 fsp accPtr basisPtr ptVecPtr v27 u112' (BitVec.ofNat 64 0)
              (BitVec.ofNat 64 (2 * n)) u136' hfsp_align
              (polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0)) poly0 ∗
               ptAt pt0 (ptVecPtr + BitVec.ofNat 64 (4 * 0)) ∗
               ((fsp + 16#64) ↦₆₄ cIdx) ∗ Frame) _R
              hpc2 hrun2 hsp2 htr2 hx21_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hfit_tail ?_)
          intro s3 u112'' u120'' u128'' u136'' hcl3 hpc3 hrun3 hsp3 htr3 hvregs3
            hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
          have hsum_eq : Poly.lagrangeSum (pt0 :: pt1 :: ptsTail') (poly0 :: poly1 :: polysTail') =
              lagrangeSumFoldPoly_pl (Poly.addAssign Poly.zero (poly0.multAssign pt0.y))
                (pt1 :: ptsTail') (poly1 :: polysTail') := by
            rw [lagrangeSum_eq_foldPoly_pl, lagrangeSumFoldPoly_cons_pl]
          have hstep_loop :
              M.stepEvents (lagrangeSumLoopEvents (pt1 :: ptsTail').length n)
                (M.stepEvents (lagrangeSumIterEvents n) st) =
                M.stepEvents (lagrangeSumLoopEvents n n) st := by
            have hn_eq : n = (ptsTail'.length + 1) + 1 := by simp at hpts_len; omega
            have hloop_eq : lagrangeSumLoopEvents n n =
                lagrangeSumLoopEvents ((ptsTail'.length + 1) + 1) n :=
              congrArg (fun k => lagrangeSumLoopEvents k n) hn_eq
            simp only [List.length_cons]
            rw [hloop_eq, lagrangeSumLoopEvents_succ (ptsTail'.length + 1) n, M.stepEvents_append]
          rw [← hsum_eq]
          refine SepWPp.weaken_pre
            (by rw [hpoly_cons0, hpt_cons0, hstep_loop]; exact Entails.of_eq (by sep_ac_rfl))
            (hcont s3 u112'' u120'' u128'' u136'' hcl3
              hpc3 hrun3 hsp3 htr3 (hvregs3.trans (hvregs2.trans hvregs1))
              hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3)

/-! ## 3. Parameterized Top-Level `lagrangeSumAndFree_gen_placed_sepWPp` (`+2608 -> +4004`) -/

/-- Budget-threaded combined `Poly::lagrange_sum` + `polys` deallocation (`+2608 -> +4004`),
    stepping `st` along `SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs`
    under `FitsEnv M lim st (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length))`. -/
theorem lagrangeSumAndFree_gen_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (pts : List Pt) (polys : List Poly)
    (hpts_ne : pts ≠ []) (hbound : pts.length ≤ 0x0555555555555555)
    (hpolys_len : polys.length = pts.length)
    (hplen : ∀ p ∈ polys, p.coefficients.length = pts.length)
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
         gf16SliceAt accPtr (Poly.lagrangeSum pts polys).coefficients ∗
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
         tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
         stackAt fsp lagrangePrepareStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ptSliceAt ptVecPtr pts ∗
       basisVecAt A.repAlloc basisPtr polys ∗
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
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       stackAt fsp lagrangePrepareStack ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hpolys_ne : polys ≠ [] := List.ne_nil_of_length_pos (by omega)
  unfold basisVecAt
  rw [stackAt_lagrangePrepare_split_alloc fsp, memRegion24_off_eq_polyHeader_pl fsp]
  refine SepWPp.weaken_pre
    (Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 112#64) 120 ∗
      (A.pool lim st s ∗ ptSliceAt ptVecPtr pts ∗
       (⌜basisPtr ≠ 0#64⌝ ∗ A.repAlloc.live basisPtr (24 * polys.length) 8 ∗
        polyListOf A.repAlloc basisPtr polys) ∗
       A.live accPtr (2 * pts.length) 2 ∗ memRegion accPtr (2 * pts.length) ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗ ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       (∃∗ u16' : BitVec 64, ∃∗ u8' : BitVec 64, ∃∗ u0' : BitVec 64,
         ((fsp + 656#64) ↦₆₄ u0') ∗ ((fsp + 664#64) ↦₆₄ u8') ∗ ((fsp + 672#64) ↦₆₄ u16')) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       (stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack)) ∗ Frame) by sep_ac_rfl))
      (sepConj_mono_left (memRegion_112_split_sum_pl fsp))) ?_
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  apply SepWPp.exists_elim; intro u672
  apply SepWPp.exists_elim; intro u664
  apply SepWPp.exists_elim; intro u656
  apply SepWPp.exists_elim; intro u112
  apply SepWPp.exists_elim; intro u120
  apply SepWPp.exists_elim; intro u128
  apply SepWPp.exists_elim; intro u136
  apply SepWPp.pure_left; intro hbasis_ne
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumLoop_placed_sepWPp hA pts polys pts.length
      hpts_ne rfl hpolys_len hbound hplen
      s0 s hcl fsp accPtr basisPtr ptVecPtr cIdx v27 hfsp_align
      u16 u64 u72 u80 u112 u120 u128 u136 u656 u664 u672
      (A.repAlloc.live basisPtr (24 * polys.length) 8 ∗
       A.live accPtr (2 * pts.length) 2 ∗
       ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗ ((fsp + 648#64) ↦₆₄ u648) ∗
       shiftTablePadAt_pl fsp ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame) _R
      hpc hrun hsp htrace hx0 hx20 hx24 hx25 hx26 hx27 hx28 hx29 hfit ?_)
  intro s1 u112' u120' u128' u136' hcl1 hpc1 hrun1 hsp1 htr1 hvregs1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  apply sepWPp_seq_lscl_fb hcl1 (mid := (blkPl_416).base + 4004#64)
  refine SepWP.weaken_pre ?_
    (lagrangeSumCleanup_placed_sepWP hA
      (st := M.stepEvents (lagrangeSumLoopEvents pts.length pts.length) st)
      polys pts.length hpolys_ne hpolys_len hn_pos hbound hplen
      s1 fsp accPtr basisPtr ptVecPtr cIdx v27 u640 u648 hfsp_align
      (gf16SliceAt accPtr (Poly.lagrangeSum pts polys).coefficients ∗
       ptSliceAt ptVecPtr pts ∗
       A.live accPtr (2 * pts.length) 2 ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
       ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt_pl fsp ∗ shiftTablePadAt_pl fsp ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
         (lagrangePrepareStack - allocHookStack) ∗ Frame)
      hpc1 hrun1 hsp1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 ?_)
  · unfold basisVecAt
    simp only [← sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc]
    exact Entails.pure_right hbasis_ne (Entails.of_eq (by sep_ac_rfl))
  · intro evsFree s2 hfree hpc2 hrun2 hsp2 htr2 hvregs2 hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2
    apply SepWP.done hpc2 hrun2
    intro hcl2
    have hstep_all :
        M.stepEvents evsFree (M.stepEvents (lagrangeSumLoopEvents pts.length pts.length) st) =
          M.stepEvents (lagrangeSumLoopEvents pts.length pts.length ++ evsFree) st :=
      (M.stepEvents_append _ _ st).symm
    have henv_all :
        SeqEnv (RepeatSeqEnv pts.length (LagrangeSumStepEnv pts.length)) FreeOnlyEvs
          (lagrangeSumLoopEvents pts.length pts.length ++ evsFree) :=
      SeqEnv.append (lagrangeSumLoopEvents_satisfies_repeatSeqEnv pts.length pts.length) hfree
    refine SepWPp.weaken_pre ?_
      (hcont (lagrangeSumLoopEvents pts.length pts.length ++ evsFree) s2
        (BitVec.ofNat 64 pts.length) accPtr (BitVec.ofNat 64 pts.length)
        henv_all hcl2 hpc2 hrun2 hsp2
        (by rw [htr2, htr1]) (by rw [hvregs2, hvregs1])
        hx19_2 hx20_2 hx26_2 hx27_2 hx28_2 hx29_2)
    rw [stackAt_lagrangePrepare_split_alloc fsp, hstep_all]
    refine Entails.trans (Entails.of_eq (show _ =
      (((fsp + 112#64) ↦₆₄ u112') ∗ ((fsp + 120#64) ↦₆₄ u120') ∗
       ((fsp + 128#64) ↦₆₄ u128') ∗ ((fsp + 136#64) ↦₆₄ u136') ∗
       shiftSlotsRawAt_pl fsp ∗ shiftTablePadAt_pl fsp) ∗
      (A.pool lim (M.stepEvents (lagrangeSumLoopEvents pts.length pts.length ++ evsFree) st) s2 ∗
       ptSliceAt ptVecPtr pts ∗
       A.live accPtr (2 * pts.length) 2 ∗
       gf16SliceAt accPtr (Poly.lagrangeSum pts polys).coefficients ∗
       ((fsp + 16#64) ↦₆₄ cIdx) ∗ ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 64#64) ↦₆₄ v27) ∗ ((fsp + 72#64) ↦₆₄ basisPtr) ∗
       ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 640#64) ↦₆₄ accPtr) ∗ ((fsp + 648#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗ ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
       (stackAt fsp allocHookStack ∗
        memRegion (fsp - BitVec.ofNat 64 lagrangePrepareStack)
          (lagrangePrepareStack - allocHookStack)) ∗ Frame) by sep_ac_rfl)) ?_
    exact Entails.trans (sepConj_mono_left (memRegion_112_fold_sum_pl fsp u112' u120' u128' u136'))
      (Entails.of_eq (by sep_ac_rfl))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumPlacedBudget
