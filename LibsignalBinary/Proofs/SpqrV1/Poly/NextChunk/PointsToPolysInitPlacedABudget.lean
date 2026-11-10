/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Block A Init (Part A)

Relocatable `[LibsignalPlacement]` verification of initial 2-byte `Poly::zero()` allocations
`0..10` (`+436 -> +704`) threading `RustCliAllocBudget M`, `BudgetLimits`, `BlockAAlloc05Env`, and
`BlockAAlloc610Env`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedABudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (bv_add_lit_add_lit exists_pow_two_eq_eight exists_pow_two_eq_two)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
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

/-! ## 1. Exact Allocator Event Envelopes for Block A (`0..5` and `6..10`) -/

/-- Exact allocator event sequence for a pair of `2`-byte, alignment-`2` `Poly` allocations. -/
def blockAAllocPairEvents : List AllocEvent :=
  rustAllocEvents 2 2 ++ rustAllocEvents 2 2

def BlockAAllocPairEnv (evs : List AllocEvent) : Prop :=
  evs = blockAAllocPairEvents

theorem fitsEnv_blockAAllocPair_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BlockAAllocPairEnv ↔ FitsEvents M lim st blockAAllocPairEvents := by
  constructor
  · intro h; exact h blockAAllocPairEvents rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for Block A allocations `0..5` (`6` allocations of `2` bytes, align `2`). -/
def blockAAlloc05Events : List AllocEvent :=
  blockAAllocPairEvents ++ blockAAllocPairEvents ++ blockAAllocPairEvents

def BlockAAlloc05Env (evs : List AllocEvent) : Prop :=
  evs = blockAAlloc05Events

theorem fitsEnv_blockAAlloc05_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BlockAAlloc05Env ↔ FitsEvents M lim st blockAAlloc05Events := by
  constructor
  · intro h; exact h blockAAlloc05Events rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for Block A allocations `6..10` (`5` allocations of `2` bytes, align `2`). -/
def blockAAlloc610Events : List AllocEvent :=
  rustAllocEvents 2 2 ++ rustAllocEvents 2 2 ++ rustAllocEvents 2 2 ++
    rustAllocEvents 2 2 ++ rustAllocEvents 2 2

def BlockAAlloc610Env (evs : List AllocEvent) : Prop :=
  evs = blockAAlloc610Events

theorem fitsEnv_blockAAlloc610_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BlockAAlloc610Env ↔ FitsEvents M lim st blockAAlloc610Events := by
  constructor
  · intro h; exact h blockAAlloc610Events rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BlockAAllocPairEnv := by
  rw [fitsEnv_blockAAllocPair_iff]
  dsimp only [blockAAllocPairEvents, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BlockAAlloc05Env := by
  rw [fitsEnv_blockAAlloc05_iff]
  dsimp only [blockAAlloc05Events, blockAAllocPairEvents, rustAllocEvents, List.cons_append,
    List.nil_append, FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc,
    AllocCostModel.step]
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩,
      ⟨⟨by decide, by decide, by decide, by decide⟩,
        ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨⟨by decide, by decide, by decide, by decide⟩,
            ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩⟩⟩⟩⟩

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BlockAAlloc610Env := by
  rw [fitsEnv_blockAAlloc610_iff]
  dsimp only [blockAAlloc610Events, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩,
      ⟨⟨by decide, by decide, by decide, by decide⟩,
        ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩⟩⟩⟩

/-! ## 2. Private Single-Allocation `SepWP` Building Blocks (`0..10`) -/

private theorem rustLayoutOk_2_2 : RustLayoutOk 2 2 :=
  ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩

private theorem alloc0_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u224 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p0 : BitVec 64),
      p0 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 460#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = p0 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
            (A.live p0 2 2 ∗ memRegion p0 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 460#64) s
      (A.pool lim st s ∗ ((fsp + 8#64) ↦₆₄ u8) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  wp_steps_sync_416 ((blkPl_416).base + 460#64)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, hsp, Reg.x24, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc1_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p0 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp0 : p0 ≠ 0#64) (u216 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 460#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p0)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s2 : State) (P2 : SepProp) (p1 : BitVec 64),
      p1 ≠ 0#64 →
      s2.pc = (blkPl_416).base + 488#64 → s2.status = .Running → s2.sp = fsp →
      s2.trace = s0.trace → calleeSavedVRegs s2 = calleeSavedVRegs s →
      s2.readReg64 .x27 = s.readReg64 .x27 → s2.readReg64 .x29 = s.readReg64 .x29 →
      (P2 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s2 ∗
            ((fsp + 216#64) ↦₆₄ p1) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
            stackAt fsp allocHookStack ∗ Frame) →
      post s2 P2) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 488#64) s
      (A.pool lim st s ∗ ((fsp + 216#64) ↦₆₄ u216) ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p0 from hx0]
    exact beq_eq_false_iff_ne.mpr hp0
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 488#64)
  intro _m_strip1
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc2_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u208 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 488#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p2 : BitVec 64),
      p2 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 508#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = p2 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            ((fsp + 208#64) ↦₆₄ p2) ∗ (A.live p2 2 2 ∗ memRegion p2 2) ∗
            stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 508#64) s
      (A.pool lim st s ∗ ((fsp + 208#64) ↦₆₄ u208) ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  wp_steps_sync_416 ((blkPl_416).base + 508#64)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc3_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p2 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp2 : p2 ≠ 0#64) (u200 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 508#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p2)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s4 : State) (P4 : SepProp) (p3 : BitVec 64),
      p3 ≠ 0#64 →
      s4.pc = (blkPl_416).base + 536#64 → s4.status = .Running → s4.sp = fsp →
      s4.trace = s0.trace → calleeSavedVRegs s4 = calleeSavedVRegs s →
      s4.readReg64 .x27 = s.readReg64 .x27 → s4.readReg64 .x29 = s.readReg64 .x29 →
      (P4 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s4 ∗
            ((fsp + 200#64) ↦₆₄ p3) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
            stackAt fsp allocHookStack ∗ Frame) →
      post s4 P4) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 536#64) s
      (A.pool lim st s ∗ ((fsp + 200#64) ↦₆₄ u200) ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p2 from hx0]
    exact beq_eq_false_iff_ne.mpr hp2
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq3 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 536#64)
  intro _m_strip1
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq3, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc4_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u192 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 536#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p4 : BitVec 64),
      p4 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 556#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = p4 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            ((fsp + 192#64) ↦₆₄ p4) ∗ (A.live p4 2 2 ∗ memRegion p4 2) ∗
            stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 556#64) s
      (A.pool lim st s ∗ ((fsp + 192#64) ↦₆₄ u192) ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  wp_steps_sync_416 ((blkPl_416).base + 556#64)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc5_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p4 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp4 : p4 ≠ 0#64) (u184 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 556#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p4)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s6 : State) (P6 : SepProp) (p5 : BitVec 64),
      p5 ≠ 0#64 →
      s6.pc = (blkPl_416).base + 584#64 → s6.status = .Running → s6.sp = fsp →
      s6.trace = s0.trace → calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 → s6.readReg64 .x29 = s.readReg64 .x29 →
      (P6 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s6 ∗
            ((fsp + 184#64) ↦₆₄ p5) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
            stackAt fsp allocHookStack ∗ Frame) →
      post s6 P6) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 584#64) s
      (A.pool lim st s ∗ ((fsp + 184#64) ↦₆₄ u184) ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p4 from hx0]
    exact beq_eq_false_iff_ne.mpr hp4
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq5 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 584#64)
  intro _m_strip1
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq5, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, hsp1, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc6_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 584#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p6 : BitVec 64),
      p6 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 600#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = p6 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p6 2 2 ∗ memRegion p6 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 600#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs) hsp1 htr1
    (by simp only [arm64_norm, wp_norm, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  rw [show sf.sp = fsp by simp only [arm64_norm, wp_norm, *]]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc7_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p6 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp6 : p6 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 600#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p6)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p7 : BitVec 64),
      p7 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 624#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = p6 → s1.readReg64 .x0 = p7 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p7 2 2 ∗ memRegion p7 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 624#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p6 from hx0]; exact beq_eq_false_iff_ne.mpr hp6
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs) hsp1 htr1
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x21, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc8_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p7 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp7 : p7 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 624#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p7)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p8 : BitVec 64),
      p8 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 648#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = p7 → s1.readReg64 .x0 = p8 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p8 2 2 ∗ memRegion p8 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 648#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p7 from hx0]; exact beq_eq_false_iff_ne.mpr hp7
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs) hsp1 htr1
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x22, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc9_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p8 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp8 : p8 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 648#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p8)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p9 : BitVec 64),
      p9 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 672#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x19 = p8 → s1.readReg64 .x0 = p9 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p9 2 2 ∗ memRegion p9 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 672#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p8 from hx0]; exact beq_eq_false_iff_ne.mpr hp8
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by wp_norm_goal) (by wp_norm_lhs) hsp1 htr1
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x19, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc10_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p9 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp9 : p9 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 672#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p9)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p10 : BitVec 64),
      p10 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 704#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x28 = p9 → s1.readReg64 .x20 = p10 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p10 2 2 ∗ memRegion p10 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 704#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p9 from hx0]; exact beq_eq_false_iff_ne.mpr hp9
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq_in, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2, 2, st)
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq10 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 704#64)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq10, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq10, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq10, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Public Budget-Threaded Block A Theorems (`+436..+704`) -/

/-- Block A part 1a (`+436 -> +488`):
    spills `x24` to `[fsp + 8]` and performs allocations `0..1` (`2` bytes, align `2`),
    spilling `p0..p1` to `[fsp + 224]` and `[fsp + 216]`. -/
theorem blockA_alloc_0_1_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u216 u224 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAllocPairEnv)
    (hcont : ∀ s2 (p0 p1 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 →
      s2.pc = (blkPl_416).base + 488#64 →
      s2.status = .Running →
      s2.sp = fsp →
      s2.trace = s0.trace →
      calleeSavedVRegs s2 = calleeSavedVRegs s →
      s2.readReg64 .x27 = s.readReg64 .x27 →
      s2.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s2
        (A.pool lim (M.stepEvents blockAAllocPairEvents st) s2 ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_both :=
    (fitsEvents_append M lim (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).mp
      ((fitsEnv_blockAAllocPair_iff).mp hfit)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (alloc0_seg hA s0 s fsp hfsp_align u8 u224 (((fsp + 216#64) ↦₆₄ u216) ∗ Frame)
        hpc hrun hsp htrace hfit_both.1 ?_))
  intro s1 P1 p0 hp0 hpc1 hrun1 hsp1 htr1 hvregs1 hx0_1 hx27_1 hx29_1 hent1
  refine SepWPp.weaken_pre (Entails.trans hent1 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc1_seg hA s0 s1 fsp p0 hfsp_align hp0 u216
        (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗ Frame)
        hpc1 hrun1 hsp1 htr1 hx0_1 hfit_both.2 ?_))
  intro s2 P2 p1 hp1 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx29_2 hent2
  have hstep_eq :
      M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st) =
        M.stepEvents blockAAllocPairEvents st :=
    (M.stepEvents_append (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).symm
  refine SepWPp.weaken_pre (Entails.trans hent2 ?_)
    (hcont s2 p0 p1 hp0 hp1 hpc2 hrun2 hsp2 htr2 (hvregs2.trans hvregs1)
      (hx27_2.trans hx27_1) (hx29_2.trans hx29_1))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Block A part 1b (`+488 -> +536`):
    performs allocations `2..3` (`2` bytes, align `2`),
    spilling `p2..p3` to `[fsp + 208]` and `[fsp + 200]`. -/
theorem blockA_alloc_2_3_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u200 u208 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 488#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAllocPairEnv)
    (hcont : ∀ s4 (p2 p3 : BitVec 64),
      p2 ≠ 0#64 → p3 ≠ 0#64 →
      s4.pc = (blkPl_416).base + 536#64 →
      s4.status = .Running →
      s4.sp = fsp →
      s4.trace = s0.trace →
      calleeSavedVRegs s4 = calleeSavedVRegs s →
      s4.readReg64 .x27 = s.readReg64 .x27 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s4
        (A.pool lim (M.stepEvents blockAAllocPairEvents st) s4 ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_both :=
    (fitsEvents_append M lim (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).mp
      ((fitsEnv_blockAAllocPair_iff).mp hfit)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (alloc2_seg hA s0 s fsp hfsp_align u208 (((fsp + 200#64) ↦₆₄ u200) ∗ Frame)
        hpc hrun hsp htrace hfit_both.1 ?_))
  intro s3 P3 p2 hp2 hpc3 hrun3 hsp3 htr3 hvregs3 hx0_3 hx27_3 hx29_3 hent3
  refine SepWPp.weaken_pre (Entails.trans hent3 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc3_seg hA s0 s3 fsp p2 hfsp_align hp2 u200
        (((fsp + 208#64) ↦₆₄ p2) ∗ (A.live p2 2 2 ∗ memRegion p2 2) ∗ Frame)
        hpc3 hrun3 hsp3 htr3 hx0_3 hfit_both.2 ?_))
  intro s4 P4 p3 hp3 hpc4 hrun4 hsp4 htr4 hvregs4 hx27_4 hx29_4 hent4
  have hstep_eq :
      M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st) =
        M.stepEvents blockAAllocPairEvents st :=
    (M.stepEvents_append (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).symm
  refine SepWPp.weaken_pre (Entails.trans hent4 ?_)
    (hcont s4 p2 p3 hp2 hp3 hpc4 hrun4 hsp4 htr4 (hvregs4.trans hvregs3)
      (hx27_4.trans hx27_3) (hx29_4.trans hx29_3))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Block A part 1c (`+536 -> +584`):
    performs allocations `4..5` (`2` bytes, align `2`),
    spilling `p4..p5` to `[fsp + 192]` and `[fsp + 184]`. -/
theorem blockA_alloc_4_5_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u184 u192 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 536#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAllocPairEnv)
    (hcont : ∀ s6 (p4 p5 : BitVec 64),
      p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (blkPl_416).base + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool lim (M.stepEvents blockAAllocPairEvents st) s6 ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_both :=
    (fitsEvents_append M lim (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).mp
      ((fitsEnv_blockAAllocPair_iff).mp hfit)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (alloc4_seg hA s0 s fsp hfsp_align u192 (((fsp + 184#64) ↦₆₄ u184) ∗ Frame)
        hpc hrun hsp htrace hfit_both.1 ?_))
  intro s5 P5 p4 hp4 hpc5 hrun5 hsp5 htr5 hvregs5 hx0_5 hx27_5 hx29_5 hent5
  refine SepWPp.weaken_pre (Entails.trans hent5 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc5_seg hA s0 s5 fsp p4 hfsp_align hp4 u184
        (((fsp + 192#64) ↦₆₄ p4) ∗ (A.live p4 2 2 ∗ memRegion p4 2) ∗ Frame)
        hpc5 hrun5 hsp5 htr5 hx0_5 hfit_both.2 ?_))
  intro s6 P6 p5 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6 hent6
  have hstep_eq :
      M.stepEvents (rustAllocEvents 2 2) (M.stepEvents (rustAllocEvents 2 2) st) =
        M.stepEvents blockAAllocPairEvents st :=
    (M.stepEvents_append (rustAllocEvents 2 2) (rustAllocEvents 2 2) st).symm
  refine SepWPp.weaken_pre (Entails.trans hent6 ?_)
    (hcont s6 p4 p5 hp4 hp5 hpc6 hrun6 hsp6 htr6 (hvregs6.trans hvregs5)
      (hx27_6.trans hx27_5) (hx29_6.trans hx29_5))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Block A part 1 (`+436 -> +584`):
    spills `x24` to `[fsp + 8]` and performs allocations `0..5` (`2` bytes, align `2`),
    spilling `p0..p5` to `[fsp + 224]` down to `[fsp + 184]`. -/
theorem blockA_alloc_0_5_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u8 u184 u192 u200 u208 u216 u224 : BitVec 64)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAlloc05Env)
    (hcont : ∀ s6 (p0 p1 p2 p3 p4 p5 : BitVec 64),
      p0 ≠ 0#64 → p1 ≠ 0#64 → p2 ≠ 0#64 → p3 ≠ 0#64 → p4 ≠ 0#64 → p5 ≠ 0#64 →
      s6.pc = (blkPl_416).base + 584#64 →
      s6.status = .Running →
      s6.sp = fsp →
      s6.trace = s0.trace →
      calleeSavedVRegs s6 = calleeSavedVRegs s →
      s6.readReg64 .x27 = s.readReg64 .x27 →
      s6.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s6
        (A.pool lim (M.stepEvents blockAAlloc05Events st) s6 ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
         ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
         ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
         (A.live p0 2 2 ∗ memRegion p0 2) ∗
         (A.live p1 2 2 ∗ memRegion p1 2) ∗
         (A.live p2 2 2 ∗ memRegion p2 2) ∗
         (A.live p3 2 2 ∗ memRegion p3 2) ∗
         (A.live p4 2 2 ∗ memRegion p4 2) ∗
         (A.live p5 2 2 ∗ memRegion p5 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗
       ((fsp + 216#64) ↦₆₄ u216) ∗ ((fsp + 224#64) ↦₆₄ u224) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_ev :
      FitsEvents M lim st ((blockAAllocPairEvents ++ blockAAllocPairEvents) ++ blockAAllocPairEvents) :=
    (fitsEnv_blockAAlloc05_iff).mp hfit
  have hfit03_45 :=
    (fitsEvents_append M lim (blockAAllocPairEvents ++ blockAAllocPairEvents) blockAAllocPairEvents st).mp hfit_ev
  have hfit01_23 :=
    (fitsEvents_append M lim blockAAllocPairEvents blockAAllocPairEvents st).mp hfit03_45.1
  have hfit01 : FitsEnv M lim st BlockAAllocPairEnv :=
    (fitsEnv_blockAAllocPair_iff).mpr hfit01_23.1
  have hfit23 : FitsEnv M lim (M.stepEvents blockAAllocPairEvents st) BlockAAllocPairEnv :=
    (fitsEnv_blockAAllocPair_iff).mpr hfit01_23.2
  have hfit45 :
      FitsEnv M lim (M.stepEvents blockAAllocPairEvents (M.stepEvents blockAAllocPairEvents st))
        BlockAAllocPairEnv := by
    rw [← M.stepEvents_append blockAAllocPairEvents blockAAllocPairEvents st]
    exact (fitsEnv_blockAAllocPair_iff).mpr hfit03_45.2
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_0_1_placed hA s0 s fsp hfsp_align u8 u216 u224
      (((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 200#64) ↦₆₄ u200) ∗ ((fsp + 208#64) ↦₆₄ u208) ∗ Frame)
      R hpc hrun hsp htrace hfit01 ?_)
  intro s2 p0 p1 hp0 hp1 hpc2 hrun2 hsp2 htr2 hvregs2 hx27_2 hx29_2
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_2_3_placed hA s0 s2 fsp hfsp_align u200 u208
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 184#64) ↦₆₄ u184) ∗ ((fsp + 192#64) ↦₆₄ u192) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗ Frame)
      R hpc2 hrun2 hsp2 htr2 hfit23 ?_)
  intro s4 p2 p3 hp2 hp3 hpc4 hrun4 hsp4 htr4 hvregs4 hx27_4 hx29_4
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_4_5_placed hA s0 s4 fsp hfsp_align u184 u192
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗ Frame)
      R hpc4 hrun4 hsp4 htr4 hfit45 ?_)
  intro s6 p4 p5 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  have hstep_eq :
      M.stepEvents blockAAllocPairEvents
          (M.stepEvents blockAAllocPairEvents (M.stepEvents blockAAllocPairEvents st)) =
        M.stepEvents blockAAlloc05Events st := by
    rw [← M.stepEvents_append blockAAllocPairEvents blockAAllocPairEvents st,
        ← M.stepEvents_append (blockAAllocPairEvents ++ blockAAllocPairEvents) blockAAllocPairEvents st]
    rfl
  refine SepWPp.weaken_pre (by rw [hstep_eq]; exact Entails.of_eq (by sep_ac_rfl))
    (hcont s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6
      (hvregs6.trans (hvregs4.trans hvregs2))
      (hx27_6.trans (hx27_4.trans hx27_2))
      (hx29_6.trans (hx29_4.trans hx29_2)))

/-- Block A part 2 (`+584 -> +704`):
    performs allocations `6..10` (`2` bytes, align `2`), storing pointers `p6..p10`
    into registers `x21, x22, x19, x28, x20`. -/
theorem blockA_alloc_6_10_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAlloc610Env)
    (hcont : ∀ s11 (p6 p7 p8 p9 p10 : BitVec 64),
      p6 ≠ 0#64 → p7 ≠ 0#64 → p8 ≠ 0#64 → p9 ≠ 0#64 → p10 ≠ 0#64 →
      s11.pc = (blkPl_416).base + 704#64 →
      s11.status = .Running →
      s11.sp = fsp →
      s11.trace = s0.trace →
      calleeSavedVRegs s11 = calleeSavedVRegs s →
      s11.readReg64 .x21 = p6 →
      s11.readReg64 .x22 = p7 →
      s11.readReg64 .x19 = p8 →
      s11.readReg64 .x28 = p9 →
      s11.readReg64 .x20 = p10 →
      s11.readReg64 .x27 = s.readReg64 .x27 →
      s11.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s11
        (A.pool lim (M.stepEvents blockAAlloc610Events st) s11 ∗
         (A.live p6 2 2 ∗ memRegion p6 2) ∗
         (A.live p7 2 2 ∗ memRegion p7 2) ∗
         (A.live p8 2 2 ∗ memRegion p8 2) ∗
         (A.live p9 2 2 ∗ memRegion p9 2) ∗
         (A.live p10 2 2 ∗ memRegion p10 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  let e1 := rustAllocEvents 2 2
  have hfit_ev : FitsEvents M lim st ((((e1 ++ e1) ++ e1) ++ e1) ++ e1) :=
    (fitsEnv_blockAAlloc610_iff).mp hfit
  have hf69_10 := (fitsEvents_append M lim (((e1 ++ e1) ++ e1) ++ e1) e1 st).mp hfit_ev
  have hf68_9 := (fitsEvents_append M lim ((e1 ++ e1) ++ e1) e1 st).mp hf69_10.1
  have hf67_8 := (fitsEvents_append M lim (e1 ++ e1) e1 st).mp hf68_9.1
  have hf6_7 := (fitsEvents_append M lim e1 e1 st).mp hf67_8.1
  have hf8 : FitsEvents M lim (M.stepEvents e1 (M.stepEvents e1 st)) e1 := by
    rw [← M.stepEvents_append e1 e1 st]; exact hf67_8.2
  have hf9 : FitsEvents M lim (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st))) e1 := by
    rw [← M.stepEvents_append e1 e1 st, ← M.stepEvents_append (e1 ++ e1) e1 st]; exact hf68_9.2
  have hf10 :
      FitsEvents M lim
        (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st)))) e1 := by
    rw [← M.stepEvents_append e1 e1 st,
        ← M.stepEvents_append (e1 ++ e1) e1 st,
        ← M.stepEvents_append ((e1 ++ e1) ++ e1) e1 st]
    exact hf69_10.2
  refine SepWPp.of_sepWP (alloc6_seg hA s0 s fsp hfsp_align Frame hpc hrun hsp htrace hf6_7.1 ?_)
  intro s7 P7 p6 hp6 hpc7 hrun7 hsp7 htr7 hvregs7 hx0_7 hx27_7 hx29_7 hent7
  refine SepWPp.weaken_pre (Entails.trans hent7 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc7_seg hA s0 s7 fsp p6 hfsp_align hp6 ((A.live p6 2 2 ∗ memRegion p6 2) ∗ Frame)
        hpc7 hrun7 hsp7 htr7 hx0_7 hf6_7.2 ?_))
  intro s8 P8 p7 hp7 hpc8 hrun8 hsp8 htr8 hvregs8 hx21_8 hx0_8 hx27_8 hx29_8 hent8
  refine SepWPp.weaken_pre (Entails.trans hent8 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc8_seg hA s0 s8 fsp p7 hfsp_align hp7
        ((A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗ Frame)
        hpc8 hrun8 hsp8 htr8 hx0_8 hf8 ?_))
  intro s9 P9 p8 hp8 hpc9 hrun9 hsp9 htr9 hvregs9 hx21_9 hx22_9 hx0_9 hx27_9 hx29_9 hent9
  refine SepWPp.weaken_pre (Entails.trans hent9 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc9_seg hA s0 s9 fsp p8 hfsp_align hp8
        ((A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
         (A.live p8 2 2 ∗ memRegion p8 2) ∗ Frame)
        hpc9 hrun9 hsp9 htr9 hx0_9 hf9 ?_))
  intro s10 P10 p9 hp9 hpc10 hrun10 hsp10 htr10 hvregs10 hx21_10 hx22_10 hx19_10 hx0_10
    hx27_10 hx29_10 hent10
  refine SepWPp.weaken_pre (Entails.trans hent10 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc10_seg hA s0 s10 fsp p9 hfsp_align hp9
        ((A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
         (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗ Frame)
        hpc10 hrun10 hsp10 htr10 hx0_10 hf10 ?_))
  intro s11 P11 p10 hp10 hpc11 hrun11 hsp11 htr11 hvregs11 hx21_11 hx22_11 hx19_11
    hx28_11 hx20_11 hx27_11 hx29_11 hent11
  have hstep_eq :
      M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st)))) =
        M.stepEvents blockAAlloc610Events st := by
    dsimp only [e1]
    rw [← M.stepEvents_append (rustAllocEvents 2 2) (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st]
    rfl
  refine SepWPp.weaken_pre (Entails.trans hent11 ?_)
    (hcont s11 p6 p7 p8 p9 p10 hp6 hp7 hp8 hp9 hp10 hpc11 hrun11 hsp11 htr11
      (hvregs11.trans (hvregs10.trans (hvregs9.trans (hvregs8.trans hvregs7))))
      (hx21_11.trans (hx21_10.trans (hx21_9.trans hx21_8)))
      (hx22_11.trans (hx22_10.trans hx22_9))
      (hx19_11.trans hx19_10)
      hx28_11
      hx20_11
      (hx27_11.trans (hx27_10.trans (hx27_9.trans (hx27_8.trans hx27_7))))
      (hx29_11.trans (hx29_10.trans (hx29_9.trans (hx29_8.trans hx29_7)))))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedABudget
