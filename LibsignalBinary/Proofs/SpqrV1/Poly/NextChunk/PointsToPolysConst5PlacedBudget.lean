/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5Placed
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Constant Basis `n = 5` and Loop Exit

Relocatable `[LibsignalPlacement]` verification of `basis_n5_placed_sepWPp` (`+1136 -> +2608`) and
`basis_loop_exit_placed_sepWPp` (`+2456 -> +2608`) threading `RustCliAllocBudget M`, `BudgetLimits`,
`BasisN5Env`, and `BasisLoopExitEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 blkPl_416_ρ lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt vecOf)
open CryptoVerification.LibsignalSpqrV1
  (COMPLETE_POINTS_POLYS_5 PolyConst constPolysToPolys)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (polyListOf polyOf vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (align8_add_of_mod8_eq_zero align8_of_mod8_eq_zero basisVecAt bv_add_lit_add_lit
   completePointsPolys5PlacedAt completePointsPolys5PlacedAt_split
   completePointsPolys5RestPlacedAt completePointsPolys5Sym completePointsPolys5_eq
   cp5Polys exists_pow_two_eq_eight exists_pow_two_eq_two extractCompletePolys
   ls_resolve_completePointsPolys5 ls_resolve_completePointsPolys30
   ls_resolve_completePointsPolys34 ls_resolve_completePointsPolys36
   memRegion_split_basis5 memRegion_split_deg4 memRegion_split_polyHeader
   memRegion_split_polyHeader_off polyOf_deg4_intro polyOf_deg4_intro_off)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416 sepWPp_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec noAllocShimSpec)

export CryptoVerification.SpqrV1.Poly.NextChunk
  (ls_resolve_completePointsPolys5 ls_resolve_completePointsPolys30
   ls_resolve_completePointsPolys34 ls_resolve_completePointsPolys36)

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
  exists_pow_two_eq_two exists_pow_two_eq_eight
attribute [local simp, local arm64_norm, local wp_norm]
  bv_add_lit_add_lit ls_resolve_completePointsPolys5
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem shl_one_eq_two_mul_placed (x : BitVec 64) : x <<< (1 : Nat) = 2#64 * x := by
  bv_robdd
private theorem shl_one_bv_eq_two_mul_placed (x : BitVec 64) : x <<< 1#64 = 2#64 * x := by
  bv_robdd

/-! ## 1. Exact Allocator Event Envelopes for `n = 5` and Shared Loop Exit -/

/-- Exact allocator event sequence for the `n = 5` constant basis path (`+1136..+2608`):
    `120` bytes (align `8`) for `basisPtr`, five `10`-byte (align `2`) buffers for `basis[0..4]`,
    and `10` bytes (align `2`) for `accPtr`. -/
def basisN5Events : List AllocEvent :=
  rustAllocEvents 120 8 ++ rustAllocEvents 10 2 ++ rustAllocEvents 10 2 ++
    rustAllocEvents 10 2 ++ rustAllocEvents 10 2 ++ rustAllocEvents 10 2 ++
    rustAllocEvents 10 2

theorem basisN5Events_eq_replicate :
    basisN5Events =
      rustAllocEvents (24 * 5) 8 ++ (List.replicate (5 + 1) (rustAllocEvents (2 * 5) 2)).flatten :=
  rfl

def BasisN5Env (evs : List AllocEvent) : Prop :=
  evs = basisN5Events

theorem fitsEnv_basisN5_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BasisN5Env ↔ FitsEvents M lim st basisN5Events := by
  constructor
  · intro h; exact h basisN5Events rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for the shared loop exit (`+2456..+2608`):
    `2 * n` bytes (align `2`) for `accPtr`. -/
def basisLoopExitEvents (n : Nat) : List AllocEvent :=
  rustAllocEvents (2 * n) 2

def BasisLoopExitEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = basisLoopExitEvents n

theorem fitsEnv_basisLoopExit_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (n : Nat) :
    FitsEnv M lim st (BasisLoopExitEnv n) ↔ FitsEvents M lim st (basisLoopExitEvents n) := by
  constructor
  · intro h; exact h (basisLoopExitEvents n) rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BasisN5Env := by
  rw [fitsEnv_basisN5_iff]
  dsimp only [basisN5Events, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  iterate 7 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (BasisLoopExitEnv 30) := by
  rw [fitsEnv_basisLoopExit_iff]
  dsimp only [basisLoopExitEvents, rustAllocEvents, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-! ## 2. Budget-Threaded Constant Basis `n = 5` & Shared Loop Exit -/

set_option maxHeartbeats 1600000 in
/-- `n = 5` constant basis case (`+1136 -> +2608`) under `[LibsignalPlacement]`. -/
theorem basis_n5_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 5#64)
    (hfit : FitsEnv M lim st BasisN5Env)
    (hcont : ∀ s1 basisPtr accPtr,
      basisPtr ≠ 0#64 →
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = 5#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents basisN5Events st) s1 ∗
         completePointsPolys5PlacedAt ∗
         basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_5) ∗
         A.live accPtr 10 2 ∗ memRegion accPtr 10 ∗
         ((fsp + 24#64) ↦₆₄ 5#64) ∗
         ((fsp + 96#64) ↦₆₄ 5#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       completePointsPolys5PlacedAt ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hlayout120_8 : RustLayoutOk 120 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have hlayout10_2 : RustLayoutOk 10 2 := ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩
  have h120_toNat : (120#64 : BitVec 64).toNat = 120 := rfl
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  have h10_toNat : (10#64 : BitVec 64).toNat = 10 := rfl
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  let e1 := rustAllocEvents 120 8
  let e2 := rustAllocEvents 10 2
  have hfit_ev : FitsEvents M lim st ((((((e1 ++ e2) ++ e2) ++ e2) ++ e2) ++ e2) ++ e2) :=
    (fitsEnv_basisN5_iff).mp hfit
  have hf16_7 := (fitsEvents_append M lim (((((e1 ++ e2) ++ e2) ++ e2) ++ e2) ++ e2) e2 st).mp hfit_ev
  have hf15_6 := (fitsEvents_append M lim ((((e1 ++ e2) ++ e2) ++ e2) ++ e2) e2 st).mp hf16_7.1
  have hf14_5 := (fitsEvents_append M lim (((e1 ++ e2) ++ e2) ++ e2) e2 st).mp hf15_6.1
  have hf13_4 := (fitsEvents_append M lim ((e1 ++ e2) ++ e2) e2 st).mp hf14_5.1
  have hf12_3 := (fitsEvents_append M lim (e1 ++ e2) e2 st).mp hf13_4.1
  have hf1_2 := (fitsEvents_append M lim e1 e2 st).mp hf12_3.1
  have hf3 : FitsEvents M lim (M.stepEvents e2 (M.stepEvents e1 st)) e2 := by
    rw [← M.stepEvents_append e1 e2 st]; exact hf12_3.2
  have hf4 : FitsEvents M lim (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))) e2 := by
    rw [← M.stepEvents_append e1 e2 st, ← M.stepEvents_append (e1 ++ e2) e2 st]; exact hf13_4.2
  have hf5 :
      FitsEvents M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))) e2 := by
    rw [← M.stepEvents_append e1 e2 st,
        ← M.stepEvents_append (e1 ++ e2) e2 st,
        ← M.stepEvents_append ((e1 ++ e2) ++ e2) e2 st]
    exact hf14_5.2
  have hf6 :
      FitsEvents M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))))) e2 := by
    rw [← M.stepEvents_append e1 e2 st,
        ← M.stepEvents_append (e1 ++ e2) e2 st,
        ← M.stepEvents_append ((e1 ++ e2) ++ e2) e2 st,
        ← M.stepEvents_append (((e1 ++ e2) ++ e2) ++ e2) e2 st]
    exact hf15_6.2
  have hf7 :
      FitsEvents M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2
          (M.stepEvents e2 (M.stepEvents e1 st)))))) e2 := by
    rw [← M.stepEvents_append e1 e2 st,
        ← M.stepEvents_append (e1 ++ e2) e2 st,
        ← M.stepEvents_append ((e1 ++ e2) ++ e2) e2 st,
        ← M.stepEvents_append (((e1 ++ e2) ++ e2) ++ e2) e2 st,
        ← M.stepEvents_append ((((e1 ++ e2) ++ e2) ++ e2) ++ e2) e2 st]
    exact hf16_7.2
  rcases (by simpa [e1, rustAllocEvents] using hf1_2.1 : FitsEvent M lim st (.alloc 120) ∧ True) with
    ⟨⟨_hw1, henf1, hram1, hva1⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf1_2.2 :
      FitsEvent M lim (M.stepEvents e1 st) (.alloc 10) ∧ True) with
    ⟨⟨_hw2, henf2, hram2, hva2⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf3 :
      FitsEvent M lim (M.stepEvents e2 (M.stepEvents e1 st)) (.alloc 10) ∧ True) with
    ⟨⟨_hw3, henf3, hram3, hva3⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf4 :
      FitsEvent M lim (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))) (.alloc 10) ∧ True) with
    ⟨⟨_hw4, henf4, hram4, hva4⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf5 :
      FitsEvent M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))) (.alloc 10) ∧ True) with
    ⟨⟨_hw5, henf5, hram5, hva5⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf6 :
      FitsEvent M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))))
        (.alloc 10) ∧ True) with
    ⟨⟨_hw6, henf6, hram6, hva6⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf7 :
      FitsEvent M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2
          (M.stepEvents e2 (M.stepEvents e1 st)))))) (.alloc 10) ∧ True) with
    ⟨⟨_hw7, henf7, hram7, hva7⟩, _⟩
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  rw [completePointsPolys5PlacedAt_split]
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2608#64)
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf0 : sf.trace = s0.trace := by simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (120, 8, st)
  have hoom1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have halign1 : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 8 = 0 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  have halign_basis0 : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
    align8_of_mod8_eq_zero halign1
  have halign_basis24 : ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have halign_basis48 : ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have halign_basis72 : ((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have halign_basis96 : ((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  rw [memRegion_split_basis5 (sf_1.readReg64 (Reg.gpr 0#5))]
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf2 : sf_2.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr1, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2, M.stepEvents e1 st)
  have hoom2 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  have htr2 : sf_3.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_3).2.1
    simpa [arm64_norm, wp_norm, htr_sf2] using ht
  have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x0, Reg.x24, *]
  rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
      memRegion_split_deg4 (sf_3.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u0_len
  apply SepWP.exists_left; intro u0_ptr
  apply SepWP.exists_left; intro u0_cap
  apply SepWP.exists_left; intro u0_c4
  apply SepWP.exists_left; intro u0_w03
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip2; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf4 : sf_4.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr2, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2, M.stepEvents e2 (M.stepEvents e1 st))
  have hoom3 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
  have htr3 : sf_5.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_5).2.1
    simpa [arm64_norm, wp_norm, htr_sf4] using ht
  have hx19_sf5 : sf_5.readReg64 (Reg.gpr 19#5) = 5#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, *]
  have hx24_sf5 : sf_5.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf3, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg4 (sf_5.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u1_len
  apply SepWP.exists_left; intro u1_ptr
  apply SepWP.exists_left; intro u1_cap
  apply SepWP.exists_left; intro u1_c4
  apply SepWP.exists_left; intro u1_w03
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip3; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real3 _hnsp3 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp3.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf6 : sf_6.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr3, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2, M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))
  have hoom4 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq4 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
  have htr4 : sf_7.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_7).2.1
    simpa [arm64_norm, wp_norm, htr_sf6] using ht
  have hx19_sf7 : sf_7.readReg64 (Reg.gpr 19#5) = 5#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, hx19_sf5, *]
  have hx24_sf7 : sf_7.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf5, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg4 (sf_7.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u2_len
  apply SepWP.exists_left; intro u2_ptr
  apply SepWP.exists_left; intro u2_cap
  apply SepWP.exists_left; intro u2_c4
  apply SepWP.exists_left; intro u2_w03
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip4; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq4, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq4, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real4 _hnsp4 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp4.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq4, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf8 : sf_8.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr4, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2, M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))))
  have hoom5 : sf_9.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq5 : (sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
  have htr5 : sf_9.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_9).2.1
    simpa [arm64_norm, wp_norm, htr_sf8] using ht
  have hx19_sf9 : sf_9.readReg64 (Reg.gpr 19#5) = 5#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, hx19_sf7, *]
  have hx24_sf9 : sf_9.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf7, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 72#64 80#64 88#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg4 (sf_9.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u3_len
  apply SepWP.exists_left; intro u3_ptr
  apply SepWP.exists_left; intro u3_cap
  apply SepWP.exists_left; intro u3_c4
  apply SepWP.exists_left; intro u3_w03
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip5; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real5 _hnsp5 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp5.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf10 : sf_10.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr5, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2,
    M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))))
  have hoom6 : sf_11.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq6 : (sf_11.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom6
  have htr6 : sf_11.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_11).2.1
    simpa [arm64_norm, wp_norm, htr_sf10] using ht
  have hx19_sf11 : sf_11.readReg64 (Reg.gpr 19#5) = 5#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, hx19_sf9, *]
  have hx24_sf11 : sf_11.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf9, *]
  have hx25_sf11 : sf_11.readReg64 (Reg.gpr 25#5) = 5#64 := by
    simp only [arm64_norm, wp_norm, Reg.x25, *]
  have hsp_sf11 : sf_11.sp = fsp := by
    simp only [arm64_norm, wp_norm, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 96#64 104#64 112#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg4 (sf_11.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u4_len
  apply SepWP.exists_left; intro u4_ptr
  apply SepWP.exists_left; intro u4_cap
  apply SepWP.exists_left; intro u4_c4
  apply SepWP.exists_left; intro u4_w03
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip6; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq6, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq6, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real6 _hnsp6 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp6.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq6, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf12 : sf_12.trace = s0.trace := by simp only [arm64_norm, wp_norm, htr6, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (10, 2,
    M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2
      (M.stepEvents e2 (M.stepEvents e1 st))))))
  have hoom7 : sf_13.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq7 : (sf_13.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom7
  have htr7 : sf_13.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_13).2.1
    simpa [arm64_norm, wp_norm, htr_sf12] using ht
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2608#64)
  intro _m_strip7; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real7 _hnsp7 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp7.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte, *]) ?_
  have hstep_eq :
      M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))))) =
        M.stepEvents basisN5Events st := by
    dsimp only [e1, e2]
    rw [← M.stepEvents_append (rustAllocEvents 120 8) (rustAllocEvents 10 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 10 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 10 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 10 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 10 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 10 2) st]
    rfl
  have hpoly0 := polyOf_deg4_intro A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) 0x78039605b4050001#64
    0x0001#16 0xb405#16 0x9605#16 0x7803#16 0x5a02#16
    hoom2 rfl rfl rfl rfl
  have hpoly1 := polyOf_deg4_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
    (sf_5.readReg64 (Reg.gpr 0#5)) 0x7803c00750030000#64
    0x0000#16 0x5003#16 0xc007#16 0x7803#16 0xe806#16
    (by bv_arith) (by bv_arith) hoom3 rfl rfl rfl rfl
  have hpoly2 := polyOf_deg4_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
    (sf_7.readReg64 (Reg.gpr 0#5)) 0x78031400f0060000#64
    0x0000#16 0xf006#16 0x1400#16 0x7803#16 0x9c05#16
    (by bv_arith) (by bv_arith) hoom4 rfl rfl rfl rfl
  have hpoly3 := polyOf_deg4_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 72#64 80#64 88#64
    (sf_9.readReg64 (Reg.gpr 0#5)) 0x7803f0069b680000#64
    0x0000#16 0x9b68#16 0xf006#16 0x7803#16 0x136d#16
    (by bv_arith) (by bv_arith) hoom5 rfl rfl rfl rfl
  have hpoly4 := polyOf_deg4_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 96#64 104#64 112#64
    (sf_11.readReg64 (Reg.gpr 0#5)) 0x0000b2048f680000#64
    0x0000#16 0x8f68#16 0xb204#16 0x0000#16 0x3d6c#16
    (by bv_arith) (by bv_arith) hoom6 rfl rfl rfl rfl
  have hbasis :
      (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 120 8 ∗
       (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 5#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 5#64) ∗
        A.live (sf_3.readReg64 (Reg.gpr 0#5)) 10 2 ∗
        ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78039605b4050001#64) ∗
        ((sf_3.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x5a02#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 5#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 5#64) ∗
        A.live (sf_5.readReg64 (Reg.gpr 0#5)) 10 2 ∗
        ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803c00750030000#64) ∗
        ((sf_5.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0xe806#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 5#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 5#64) ∗
        A.live (sf_7.readReg64 (Reg.gpr 0#5)) 10 2 ∗
        ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78031400f0060000#64) ∗
        ((sf_7.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x9c05#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ 5#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ sf_9.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ 5#64) ∗
        A.live (sf_9.readReg64 (Reg.gpr 0#5)) 10 2 ∗
        ((sf_9.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803f0069b680000#64) ∗
        ((sf_9.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x136d#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ 5#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 104#64) ↦₆₄ sf_11.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 112#64) ↦₆₄ 5#64) ∗
        A.live (sf_11.readReg64 (Reg.gpr 0#5)) 10 2 ∗
        ((sf_11.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x0000b2048f680000#64) ∗
        ((sf_11.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x3d6c#16))) ⊢
      basisVecAt A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5))
        (extractCompletePolys COMPLETE_POINTS_POLYS_5) := by
    rw [completePointsPolys5_eq]
    unfold extractCompletePolys cp5Polys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
    simp only [List.map, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      arrayAt, vecHeaderBytes, BitVec.ofNat_eq_ofNat, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.pure_right hoom1 ?_
    exact sepConj_mono_right
      (sepConj_mono hpoly0
        (sepConj_mono hpoly1
          (sepConj_mono hpoly2
            (sepConj_mono hpoly3 hpoly4))))
  refine SepWPp.weaken_pre ?_
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_13.readReg64 (Reg.gpr 0#5))
      hoom1 hoom7
      (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hbeq7, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, htr7])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf11, *])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf11, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))
  have hsp_sf10 : sf_10.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  have hsp_sf12 : sf_12.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  simp only [arm64_norm, wp_norm, hstep_eq,
    hx19_sf11, hx19_sf9, hx19_sf7, hx19_sf5,
    hx24_sf11, hx24_sf9, hx24_sf7, hx24_sf5, hx24_sf3,
    hx25_sf11, hsp_sf12, hsp_sf11, hsp_sf10,
    h120_toNat, h8_toNat, h10_toNat, h2_toNat,
    blkPl_416_ρ, BitVec.add_assoc, BitVec.reduceAdd,
    completePointsPolys5PlacedAt_split, *]
  generalize lsρ completePointsPolys5Sym = roBase
  refine Entails.trans (Entails.of_eq (show _ =
    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 120 8 ∗
     (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 5#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 5#64) ∗
      A.live (sf_3.readReg64 (Reg.gpr 0#5)) 10 2 ∗
      ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78039605b4050001#64) ∗
      ((sf_3.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x5a02#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 5#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 5#64) ∗
      A.live (sf_5.readReg64 (Reg.gpr 0#5)) 10 2 ∗
      ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803c00750030000#64) ∗
      ((sf_5.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0xe806#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 5#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 5#64) ∗
      A.live (sf_7.readReg64 (Reg.gpr 0#5)) 10 2 ∗
      ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x78031400f0060000#64) ∗
      ((sf_7.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x9c05#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 72#64) ↦₆₄ 5#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 80#64) ↦₆₄ sf_9.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 88#64) ↦₆₄ 5#64) ∗
      A.live (sf_9.readReg64 (Reg.gpr 0#5)) 10 2 ∗
      ((sf_9.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x7803f0069b680000#64) ∗
      ((sf_9.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x136d#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 96#64) ↦₆₄ 5#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 104#64) ↦₆₄ sf_11.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 112#64) ↦₆₄ 5#64) ∗
      A.live (sf_11.readReg64 (Reg.gpr 0#5)) 10 2 ∗
      ((sf_11.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x0000b2048f680000#64) ∗
      ((sf_11.readReg64 (Reg.gpr 0#5) + 8#64) ↦₁₆ 0x3d6c#16))) ∗
    (A.pool lim (M.stepEvents basisN5Events st) _ ∗
     (roBase ↦₆₄ᵣ 0x78039605b4050001#64) ∗
     ((roBase + 10#64) ↦₆₄ᵣ 0x7803c00750030000#64) ∗
     ((roBase + 20#64) ↦₆₄ᵣ 0x78031400f0060000#64) ∗
     ((roBase + 30#64) ↦₆₄ᵣ 0x7803f0069b680000#64) ∗
     completePointsPolys5RestPlacedAt ∗
     A.live (sf_13.readReg64 (Reg.gpr 0#5)) 10 2 ∗
     memRegion (sf_13.readReg64 (Reg.gpr 0#5)) 10 ∗
     ((fsp + 24#64) ↦₆₄ 5#64) ∗
     ((fsp + 96#64) ↦₆₄ 5#64) ∗
     stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hbasis) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- Shared exit block (`+2456 -> +2608`) for `n ∈ {30, 34, 36}` under `[LibsignalPlacement]`,
    threading `A.pool lim st` across `basisLoopExitEvents n`. -/
theorem basis_loop_exit_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp basisPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn_ne : BitVec.ofNat 64 n ≠ 0#64) (hn_bound : 2 * n < 2 ^ 63)
    (u24 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2456#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hfit : FitsEnv M lim st (BasisLoopExitEnv n))
    (hcont : ∀ s1 accPtr,
      accPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2608#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = accPtr →
      s1.readReg64 .x20 = s.readReg64 .x23 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (basisLoopExitEvents n) st) s1 ∗
         A.live accPtr (2 * n) 2 ∗ memRegion accPtr (2 * n) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ basisPtr) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd rfl hn_ne
    · exact h
  have hpos : 0 < 2 * n := by omega
  have h2pow63 : (2 : Nat) ^ 63 = 9223372036854775808 := rfl
  have hlayout : RustLayoutOk (2 * n) 2 := ⟨⟨hpos, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have hfit_evs : FitsEvents M lim st (rustAllocEvents (2 * n) 2) :=
    (fitsEnv_basisLoopExit_iff n).mp hfit
  have hfit_ev : FitsEvent M lim st (.alloc (2 * n)) := by
    have hle2 : 2 ≤ 2 * n := by omega
    simpa [rustAllocEvents, hle2] using hfit_evs
  rcases hfit_ev with ⟨_hwmax, henf, hram, hva⟩
  have hbeq_n : (BitVec.ofNat 64 n == 0#64) = false := beq_eq_false_iff_ne.mpr hn_ne
  have hcond_n : ¬(BitVec.ofNat 64 n == 0#64) = true := by simpa [beq_iff_eq] using hn_ne
  have hshl : BitVec.ofNat 64 n <<< (1 : Nat) = BitVec.ofNat 64 (2 * n) := by
    rw [shl_one_eq_two_mul_placed, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        ← BitVec.ofNat_mul]
  have hshl' : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 (2 * n) := by
    rw [shl_one_bv_eq_two_mul_placed, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        ← BitVec.ofNat_mul]
  have htoNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply SepWPp.of_sepWP (mid := (blkPl_416).base + 2608#64)
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2584#64)
  intro _m_strip0; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, hrun])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, hrun])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, htrace, *]
  have hsp_sf0 : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, hsp, *]
  have hx25_sf0 : sf.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 n := by
    simp only [arm64_norm, wp_norm, Reg.x25, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2 * n, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2608#64)
  intro _m_strip2; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte, *]) ?_
  refine SepWPp.weaken_pre ?_
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
      (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hbeq, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, hsp_sf0, *])
      (by simp only [arm64_norm, wp_norm, htr1])
      (by simp only [arm64_norm, wp_norm, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, Reg.x23, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, hx25, hbeq_n, hcond_n, Bool.false_eq_true, ↓reduceIte, *]))
  dsimp only [basisLoopExitEvents]
  simp only [arm64_norm, wp_norm, hsp_sf0, hsp, hx25, hbeq_n, hcond_n, hshl, hshl', htoNat, h2_toNat,
    hbeq, Bool.false_eq_true, ↓reduceIte, *]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget
