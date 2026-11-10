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
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Constant Basis Cases (`n = 0, 1, 3`)

Relocatable `[LibsignalPlacement]` verification of the constant Lagrange basis cases `n ∈ {0, 1, 3}`
(`+1136..+2608` / `+4004`) threading `RustCliAllocBudget M`, `BudgetLimits`, `BasisN1Env`, and
`BasisN3Env`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt vecOf)
open CryptoVerification.LibsignalSpqrV1
  (COMPLETE_POINTS_POLYS_1 COMPLETE_POINTS_POLYS_3 GF16 PolyConst constPolysToPolys)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (polyListOf polyOf vecHeaderBytes)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (align8_add_of_mod8_eq_zero align8_of_mod8_eq_zero basisVecAt bv_add_lit_add_lit
   completePointsPolys1_eq completePointsPolys3_eq
   exists_pow_two_eq_eight exists_pow_two_eq_two extractCompletePolys
   memRegion_split_basis3 memRegion_split_deg2 memRegion_split_polyHeader
   memRegion_split_polyHeader_off polyAt_const_one_intro polyOf_deg2_intro
   polyOf_deg2_intro_off)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416 sepWPp_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec noAllocShimSpec)

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
attribute [local simp, local arm64_norm, local wp_norm] bv_add_lit_add_lit
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Exact Allocator Event Envelopes for `n = 1` and `n = 3` -/

/-- Exact allocator event sequence for the `n = 1` constant basis path (`+1136..+2608`):
    `24` bytes (align `8`) for `basisPtr`, `2` bytes (align `2`) for `basis[0]`,
    and `2` bytes (align `2`) for `accPtr`. -/
def basisN1Events : List AllocEvent :=
  rustAllocEvents 24 8 ++ rustAllocEvents 2 2 ++ rustAllocEvents 2 2

def BasisN1Env (evs : List AllocEvent) : Prop :=
  evs = basisN1Events

theorem fitsEnv_basisN1_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BasisN1Env ↔ FitsEvents M lim st basisN1Events := by
  constructor
  · intro h; exact h basisN1Events rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for the `n = 3` constant basis path (`+1136..+2608`):
    `72` bytes (align `8`) for `basisPtr`, three `6`-byte (align `2`) buffers for `basis[0..2]`,
    and `6` bytes (align `2`) for `accPtr`. -/
def basisN3Events : List AllocEvent :=
  rustAllocEvents 72 8 ++ rustAllocEvents 6 2 ++ rustAllocEvents 6 2 ++
    rustAllocEvents 6 2 ++ rustAllocEvents 6 2

def BasisN3Env (evs : List AllocEvent) : Prop :=
  evs = basisN3Events

theorem fitsEnv_basisN3_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BasisN3Env ↔ FitsEvents M lim st basisN3Events := by
  constructor
  · intro h; exact h basisN3Events rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BasisN1Env := by
  rw [fitsEnv_basisN1_iff]
  dsimp only [basisN1Events, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  iterate 3 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BasisN3Env := by
  rw [fitsEnv_basisN3_iff]
  dsimp only [basisN3Events, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  iterate 5 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

/-! ## 2. Budget-Threaded Constant Basis Cases `n = 1`, `n = 3`, and `n = 0` -/

set_option maxHeartbeats 800000 in
/-- `n = 1` constant basis case (`+1136 -> +2608`). -/
theorem basis_n1_placed_sepWPp [LibsignalPlacement]
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
    (hx25 : s.readReg64 .x25 = 1#64)
    (hfit : FitsEnv M lim st BasisN1Env)
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
      s1.readReg64 .x25 = 1#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents basisN1Events st) s1 ∗
         basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_1) ∗
         A.live accPtr 2 2 ∗ memRegion accPtr 2 ∗
         ((fsp + 24#64) ↦₆₄ 1#64) ∗
         ((fsp + 96#64) ↦₆₄ 1#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hlayout24_8 : RustLayoutOk 24 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have hlayout2_2 : RustLayoutOk 2 2 := ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩
  have h24_toNat : (24#64 : BitVec 64).toNat = 24 := rfl
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  let e1 := rustAllocEvents 24 8
  let e2 := rustAllocEvents 2 2
  have hfit_ev : FitsEvents M lim st ((e1 ++ e2) ++ e2) :=
    (fitsEnv_basisN1_iff).mp hfit
  have hf12_3 := (fitsEvents_append M lim (e1 ++ e2) e2 st).mp hfit_ev
  have hf1_2 := (fitsEvents_append M lim e1 e2 st).mp hf12_3.1
  have hf3 : FitsEvents M lim (M.stepEvents e2 (M.stepEvents e1 st)) e2 := by
    rw [← M.stepEvents_append e1 e2 st]; exact hf12_3.2
  rcases (by simpa [e1, rustAllocEvents] using hf1_2.1 : FitsEvent M lim st (.alloc 24) ∧ True) with
    ⟨⟨_hw1, henf1, hram1, hva1⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf1_2.2 :
      FitsEvent M lim (M.stepEvents e1 st) (.alloc 2) ∧ True) with
    ⟨⟨_hw2, henf2, hram2, hva2⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf3 :
      FitsEvent M lim (M.stepEvents e2 (M.stepEvents e1 st)) (.alloc 2) ∧ True) with
    ⟨⟨_hw3, henf3, hram3, hva3⟩, _⟩
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
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
  wp_call halloc (24, 8, st)
  have hoom1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have halign1 : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 8 = 0 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  have halign_basis : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
    align8_of_mod8_eq_zero halign1
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
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
  wp_call halloc (2, 2, M.stepEvents e1 st)
  have hoom2 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  have htr2 : sf_3.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_3).2.1
    simpa [arm64_norm, wp_norm, htr_sf2] using ht
  have hx19_sf3 : sf_3.readReg64 (Reg.gpr 19#5) = 1#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, *]
  have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x0, Reg.x24, *]
  have hx25_sf3 : sf_3.readReg64 (Reg.gpr 25#5) = 1#64 := by
    simp only [arm64_norm, wp_norm, Reg.x25, *]
  rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
      ProofLib.memRegion_two (sf_3.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u_len
  apply SepWP.exists_left; intro u_ptr
  apply SepWP.exists_left; intro u_cap
  apply SepWP.exists_left; intro u_c0
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
  wp_call halloc (2, 2, M.stepEvents e2 (M.stepEvents e1 st))
  have hoom3 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
  have htr3 : sf_5.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_5).2.1
    simpa [arm64_norm, wp_norm, htr_sf4] using ht
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2608#64)
  intro _m_strip3; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real3 _hnsp3 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp3.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte, *]) ?_
  have hstep_eq :
      M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)) =
        M.stepEvents basisN1Events st := by
    dsimp only [e1, e2]
    rw [← M.stepEvents_append (rustAllocEvents 24 8) (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st]
    rfl
  have hpoly0 :
      (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
       ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
       ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
       A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
       ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16)) ⊢
      polyOf A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) ⟨[GF16.ONE]⟩ := by
    refine Entails.trans (polyAt_const_one_intro A.repAlloc _ _ hoom2) ?_
    unfold polyOf vecOf
    exact Entails.sepExists_right 1#64
      (Entails.sepExists_right (sf_3.readReg64 (Reg.gpr 0#5)) (Entails.refl _))
  have hbasis :
      (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 24 8 ∗
       (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
        A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
        ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16))) ⊢
      basisVecAt A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5))
        (extractCompletePolys COMPLETE_POINTS_POLYS_1) := by
    rw [completePointsPolys1_eq]
    unfold extractCompletePolys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
    simp only [List.map, List.length_singleton, Nat.mul_one, arrayAt, sepConj_emp, GF16.ONE]
    exact Entails.pure_right hoom1 (sepConj_mono_right hpoly0)
  refine SepWPp.weaken_pre ?_
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_5.readReg64 (Reg.gpr 0#5))
      hoom1 hoom3
      (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, htr3])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf3, *])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf3, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))
  have hsp_sf4 : sf_4.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  simp only [arm64_norm, wp_norm, hstep_eq, hx19_sf3, hx24_sf3, hx25_sf3, hsp_sf4,
    h24_toNat, h8_toNat, h2_toNat, *]
  refine Entails.trans (Entails.of_eq (show _ =
    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 24 8 ∗
     (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 1#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 1#64) ∗
      A.live (sf_3.readReg64 (Reg.gpr 0#5)) 2 2 ∗
      ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₁₆ 1#16))) ∗
    (A.pool lim (M.stepEvents basisN1Events st) _ ∗
     A.live (sf_5.readReg64 (Reg.gpr 0#5)) 2 2 ∗
     memRegion (sf_5.readReg64 (Reg.gpr 0#5)) 2 ∗
     ((fsp + 24#64) ↦₆₄ 1#64) ∗
     ((fsp + 96#64) ↦₆₄ 1#64) ∗
     stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hbasis) ?_
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 1600000 in
/-- `n = 3` constant basis case (`+1136 -> +2608`). -/
theorem basis_n3_placed_sepWPp [LibsignalPlacement]
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
    (hx25 : s.readReg64 .x25 = 3#64)
    (hfit : FitsEnv M lim st BasisN3Env)
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
      s1.readReg64 .x25 = 3#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents basisN3Events st) s1 ∗
         basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_3) ∗
         A.live accPtr 6 2 ∗ memRegion accPtr 6 ∗
         ((fsp + 24#64) ↦₆₄ 3#64) ∗
         ((fsp + 96#64) ↦₆₄ 3#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hlayout72_8 : RustLayoutOk 72 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have hlayout6_2 : RustLayoutOk 6 2 := ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩
  have h72_toNat : (72#64 : BitVec 64).toNat = 72 := rfl
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  have h6_toNat : (6#64 : BitVec 64).toNat = 6 := rfl
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  let e1 := rustAllocEvents 72 8
  let e2 := rustAllocEvents 6 2
  have hfit_ev : FitsEvents M lim st ((((e1 ++ e2) ++ e2) ++ e2) ++ e2) :=
    (fitsEnv_basisN3_iff).mp hfit
  have hf14_5 := (fitsEvents_append M lim (((e1 ++ e2) ++ e2) ++ e2) e2 st).mp hfit_ev
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
  rcases (by simpa [e1, rustAllocEvents] using hf1_2.1 : FitsEvent M lim st (.alloc 72) ∧ True) with
    ⟨⟨_hw1, henf1, hram1, hva1⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf1_2.2 :
      FitsEvent M lim (M.stepEvents e1 st) (.alloc 6) ∧ True) with
    ⟨⟨_hw2, henf2, hram2, hva2⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf3 :
      FitsEvent M lim (M.stepEvents e2 (M.stepEvents e1 st)) (.alloc 6) ∧ True) with
    ⟨⟨_hw3, henf3, hram3, hva3⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf4 :
      FitsEvent M lim (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))) (.alloc 6) ∧ True) with
    ⟨⟨_hw4, henf4, hram4, hva4⟩, _⟩
  rcases (by simpa [e2, rustAllocEvents] using hf5 :
      FitsEvent M lim
        (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))) (.alloc 6) ∧ True) with
    ⟨⟨_hw5, henf5, hram5, hva5⟩, _⟩
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
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
  wp_call halloc (72, 8, st)
  have hoom1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have halign1 : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 8 = 0 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  have halign_basis0 : (sf_1.readReg64 (Reg.gpr 0#5) &&& 7#64 == 0#64) = true :=
    align8_of_mod8_eq_zero halign1
  have halign_basis24 : ((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have halign_basis48 : ((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) &&& 7#64 == 0#64) = true :=
    align8_add_of_mod8_eq_zero halign1 (by decide)
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  rw [memRegion_split_basis3 (sf_1.readReg64 (Reg.gpr 0#5))]
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
  wp_call halloc (6, 2, M.stepEvents e1 st)
  have hoom2 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq2 : (sf_3.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  have htr2 : sf_3.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_3).2.1
    simpa [arm64_norm, wp_norm, htr_sf2] using ht
  have hx24_sf3 : sf_3.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x0, Reg.x24, *]
  rw [memRegion_split_polyHeader (sf_1.readReg64 (Reg.gpr 0#5)),
      memRegion_split_deg2 (sf_3.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u0_len
  apply SepWP.exists_left; intro u0_ptr
  apply SepWP.exists_left; intro u0_cap
  apply SepWP.exists_left; intro u0_c2
  apply SepWP.exists_left; intro u0_w01
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
  wp_call halloc (6, 2, M.stepEvents e2 (M.stepEvents e1 st))
  have hoom3 : sf_5.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_5.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom3
  have htr3 : sf_5.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_5).2.1
    simpa [arm64_norm, wp_norm, htr_sf4] using ht
  have hx19_sf5 : sf_5.readReg64 (Reg.gpr 19#5) = 3#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, *]
  have hx24_sf5 : sf_5.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf3, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg2 (sf_5.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u1_len
  apply SepWP.exists_left; intro u1_ptr
  apply SepWP.exists_left; intro u1_cap
  apply SepWP.exists_left; intro u1_c2
  apply SepWP.exists_left; intro u1_w01
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
  wp_call halloc (6, 2, M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))
  have hoom4 : sf_7.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq4 : (sf_7.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom4
  have htr4 : sf_7.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_7).2.1
    simpa [arm64_norm, wp_norm, htr_sf6] using ht
  have hx19_sf7 : sf_7.readReg64 (Reg.gpr 19#5) = 3#64 := by
    simp only [arm64_norm, wp_norm, Reg.x19, hx19_sf5, *]
  have hx24_sf7 : sf_7.readReg64 (Reg.gpr 24#5) = sf_1.readReg64 (Reg.gpr 0#5) := by
    simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf5, *]
  have hx25_sf7 : sf_7.readReg64 (Reg.gpr 25#5) = 3#64 := by
    simp only [arm64_norm, wp_norm, Reg.x25, *]
  rw [memRegion_split_polyHeader_off (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
        (by bv_arith) (by bv_arith),
      memRegion_split_deg2 (sf_7.readReg64 (Reg.gpr 0#5))]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_left; intro u2_len
  apply SepWP.exists_left; intro u2_ptr
  apply SepWP.exists_left; intro u2_cap
  apply SepWP.exists_left; intro u2_c2
  apply SepWP.exists_left; intro u2_w01
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
  wp_call halloc (6, 2, M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st))))
  have hoom5 : sf_9.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq5 : (sf_9.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom5
  have htr5 : sf_9.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_9).2.1
    simpa [arm64_norm, wp_norm, htr_sf8] using ht
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2608#64)
  intro _m_strip5; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real5 _hnsp5 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp5.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte, *]) ?_
  have hstep_eq :
      M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e2 (M.stepEvents e1 st)))) =
        M.stepEvents basisN3Events st := by
    dsimp only [e1, e2]
    rw [← M.stepEvents_append (rustAllocEvents 72 8) (rustAllocEvents 6 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 6 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 6 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 6 2) st]
    rfl
  have hpoly0 := polyOf_deg2_intro A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5))
    (sf_3.readReg64 (Reg.gpr 0#5)) 0x88040001#32 0x0001#16 0x8804#16 0x8805#16
    hoom2 rfl rfl
  have hpoly1 := polyOf_deg2_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 24#64 32#64 40#64
    (sf_5.readReg64 (Reg.gpr 0#5)) 0xf0070000#32 0x0000#16 0xf007#16 0xf006#16
    (by bv_arith) (by bv_arith) hoom3 rfl rfl
  have hpoly2 := polyOf_deg2_intro_off A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5)) 48#64 56#64 64#64
    (sf_7.readReg64 (Reg.gpr 0#5)) 0x78030000#32 0x0000#16 0x7803#16 0x7803#16
    (by bv_arith) (by bv_arith) hoom4 rfl rfl
  have hbasis :
      (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 8 ∗
       (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 3#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 3#64) ∗
        A.live (sf_3.readReg64 (Reg.gpr 0#5)) 6 2 ∗
        ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x88040001#32) ∗
        ((sf_3.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x8805#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 3#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 3#64) ∗
        A.live (sf_5.readReg64 (Reg.gpr 0#5)) 6 2 ∗
        ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0xf0070000#32) ∗
        ((sf_5.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0xf006#16)) ∗
       (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 3#64) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
        ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 3#64) ∗
        A.live (sf_7.readReg64 (Reg.gpr 0#5)) 6 2 ∗
        ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x78030000#32) ∗
        ((sf_7.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x7803#16))) ⊢
      basisVecAt A.repAlloc (sf_1.readReg64 (Reg.gpr 0#5))
        (extractCompletePolys COMPLETE_POINTS_POLYS_3) := by
    rw [completePointsPolys3_eq]
    unfold extractCompletePolys constPolysToPolys PolyConst.toPoly basisVecAt polyListOf
    simp only [List.map, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
      arrayAt, vecHeaderBytes, BitVec.ofNat_eq_ofNat, sepConj_emp,
      BitVec.add_assoc, BitVec.reduceAdd]
    refine Entails.pure_right hoom1 ?_
    exact sepConj_mono_right (sepConj_mono hpoly0 (sepConj_mono hpoly1 hpoly2))
  refine SepWPp.weaken_pre ?_
    (hcont _ (sf_1.readReg64 (Reg.gpr 0#5)) (sf_9.readReg64 (Reg.gpr 0#5))
      hoom1 hoom5
      (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte, *])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, htr5])
      (by simp only [arm64_norm, wp_norm, *])
      (by simp only [arm64_norm, wp_norm, Reg.x0, *])
      (by simp only [arm64_norm, wp_norm, Reg.x20, *])
      (by simp only [arm64_norm, wp_norm, Reg.x24, hx24_sf7, *])
      (by simp only [arm64_norm, wp_norm, Reg.x25, hx25_sf7, *])
      (by simp only [arm64_norm, wp_norm, Reg.x26, *])
      (by simp only [arm64_norm, wp_norm, Reg.x27, *])
      (by simp only [arm64_norm, wp_norm, Reg.x28, *])
      (by simp only [arm64_norm, wp_norm, Reg.x29, *]))
  have hsp_sf8 : sf_8.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  simp only [arm64_norm, wp_norm, hstep_eq, hx19_sf7, hx19_sf5, hx24_sf7, hx24_sf5, hx24_sf3,
    hx25_sf7, hsp_sf8, h72_toNat, h8_toNat, h6_toNat, h2_toNat, *]
  refine Entails.trans (Entails.of_eq (show _ =
    (A.live (sf_1.readReg64 (Reg.gpr 0#5)) 72 8 ∗
     (((sf_1.readReg64 (Reg.gpr 0#5)) ↦₆₄ 3#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ sf_3.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ 3#64) ∗
      A.live (sf_3.readReg64 (Reg.gpr 0#5)) 6 2 ∗
      ((sf_3.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x88040001#32) ∗
      ((sf_3.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x8805#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 24#64) ↦₆₄ 3#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 32#64) ↦₆₄ sf_5.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 40#64) ↦₆₄ 3#64) ∗
      A.live (sf_5.readReg64 (Reg.gpr 0#5)) 6 2 ∗
      ((sf_5.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0xf0070000#32) ∗
      ((sf_5.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0xf006#16)) ∗
     (((sf_1.readReg64 (Reg.gpr 0#5) + 48#64) ↦₆₄ 3#64) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 56#64) ↦₆₄ sf_7.readReg64 (Reg.gpr 0#5)) ∗
      ((sf_1.readReg64 (Reg.gpr 0#5) + 64#64) ↦₆₄ 3#64) ∗
      A.live (sf_7.readReg64 (Reg.gpr 0#5)) 6 2 ∗
      ((sf_7.readReg64 (Reg.gpr 0#5)) ↦₃₂ 0x78030000#32) ∗
      ((sf_7.readReg64 (Reg.gpr 0#5) + 4#64) ↦₁₆ 0x7803#16))) ∗
    (A.pool lim (M.stepEvents basisN3Events st) _ ∗
     A.live (sf_9.readReg64 (Reg.gpr 0#5)) 6 2 ∗
     memRegion (sf_9.readReg64 (Reg.gpr 0#5)) 6 ∗
     ((fsp + 24#64) ↦₆₄ 3#64) ∗
     ((fsp + 96#64) ↦₆₄ 3#64) ∗
     stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hbasis) ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-- `n = 0` empty basis case (`+1136 -> +4004`), threading `A.pool lim st` with zero allocator events. -/
theorem basis_n0_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u640 u648 u664 u672 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 0#64)
    (hcont : ∀ s1,
      s1.pc = (blkPl_416).base + 4004#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = 0#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = 8#64 →
      s1.readReg64 .x25 = 0#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim st s1 ∗
         ((fsp + 24#64) ↦₆₄ 0#64) ∗
         ((fsp + 96#64) ↦₆₄ 0#64) ∗
         ((fsp + 640#64) ↦₆₄ 2#64) ∗
         ((fsp + 648#64) ↦₆₄ 0#64) ∗
         ((fsp + 664#64) ↦₆₄ 2#64) ∗
         ((fsp + 672#64) ↦₆₄ 0#64) ∗
         Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 640#64) ↦₆₄ u640) ∗
       ((fsp + 648#64) ↦₆₄ u648) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       Frame)
      Q Q_panic := by
  apply sepWPp_seg_416 (mid := (blkPl_416).base + 4004#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont _
      (by wp_norm_goal)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      (by simp only [arm64_norm, wp_norm])
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by simp only [arm64_norm, wp_norm, hx25])
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs)
      (by wp_norm_lhs))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstPlacedBudget
