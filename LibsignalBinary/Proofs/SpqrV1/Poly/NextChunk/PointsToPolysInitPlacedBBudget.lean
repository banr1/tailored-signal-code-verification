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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedABudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Block A Init (Part B)

Relocatable `[LibsignalPlacement]` allocations `11..15` (`+704 -> +820`), 16-header `Poly::zero()`
scatter (`+820 -> +976`), and combined `blockA_placed_sepWPp` (`+436 -> +976`) threading
`RustCliAllocBudget M`, `BudgetLimits`, and `BlockAEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedBBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (polyListOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (bv_add_lit_add_lit exists_pow_two_eq_eight exists_pow_two_eq_two
   memRegion_112_fold_spills memRegion_112_split_spills
   sepWP_cells_succ sepWP_cells_zero
   zeroPolySlotAt_intro zeroPolySlotsAt zeroPolySlotsAt_entails_polyListOf)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedABudget
  (BlockAAlloc05Env BlockAAlloc610Env blockAAlloc05Events blockAAlloc610Events
   blockA_alloc_0_5_placed blockA_alloc_6_10_placed fitsEnv_blockAAlloc05_iff
   fitsEnv_blockAAlloc610_iff)
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

private theorem rustLayoutOk_2_2 : RustLayoutOk 2 2 :=
  ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩

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

/-! ## 1. Exact Allocator Event Envelopes for Block A (`11..15` and Complete `0..15`) -/

/-- Exact allocator event sequence for Block A allocations `11..15` (`5` allocations of `2` bytes, align `2`). -/
def blockAAlloc1115Events : List AllocEvent :=
  rustAllocEvents 2 2 ++ rustAllocEvents 2 2 ++ rustAllocEvents 2 2 ++
    rustAllocEvents 2 2 ++ rustAllocEvents 2 2

def BlockAAlloc1115Env (evs : List AllocEvent) : Prop :=
  evs = blockAAlloc1115Events

theorem fitsEnv_blockAAlloc1115_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BlockAAlloc1115Env ↔ FitsEvents M lim st blockAAlloc1115Events := by
  constructor
  · intro h; exact h blockAAlloc1115Events rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for complete Block A (`16` allocations of `2` bytes, align `2`). -/
def blockAEvents : List AllocEvent :=
  blockAAlloc05Events ++ blockAAlloc610Events ++ blockAAlloc1115Events

def BlockAEnv (evs : List AllocEvent) : Prop :=
  evs = blockAEvents

theorem fitsEnv_blockA_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BlockAEnv ↔ FitsEvents M lim st blockAEvents := by
  constructor
  · intro h; exact h blockAEvents rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BlockAAlloc1115Env := by
  rw [fitsEnv_blockAAlloc1115_iff]
  dsimp only [blockAAlloc1115Events, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  refine ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩,
      ⟨⟨by decide, by decide, by decide, by decide⟩,
        ⟨⟨by decide, by decide, by decide, by decide⟩,
          ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩⟩⟩⟩

example :
    FitsEnv coarseCostModel
      { staticCount := 32, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BlockAEnv := by
  rw [fitsEnv_blockA_iff]
  dsimp only [blockAEvents, blockAAlloc05Events, blockAAlloc610Events, blockAAlloc1115Events,
    PointsToPolysInitPlacedABudget.blockAAllocPairEvents, rustAllocEvents, List.cons_append,
    List.nil_append, FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc,
    AllocCostModel.step]
  iterate 16 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

/-! ## 2. Private Per-Allocation Segments (`+704..+820`) -/

private theorem alloc11_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 704#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p11 : BitVec 64),
      p11 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 720#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x0 = p11 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p11 2 2 ∗ memRegion p11 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 720#64) s
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
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  rw [show sf.sp = fsp by simp only [arm64_norm, wp_norm, *]]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc12_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p11 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp11 : p11 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 720#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p11)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p12 : BitVec 64),
      p12 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 744#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x23 = p11 → s1.readReg64 .x0 = p12 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p12 2 2 ∗ memRegion p12 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 744#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p11 from hx0]; exact beq_eq_false_iff_ne.mpr hp11
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
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x23, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc13_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p12 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp12 : p12 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 744#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p12)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p13 : BitVec 64),
      p13 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 768#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = p12 → s1.readReg64 .x0 = p13 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p13 2 2 ∗ memRegion p13 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 768#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p12 from hx0]; exact beq_eq_false_iff_ne.mpr hp12
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
    (by simp only [arm64_norm, wp_norm, Reg.x23, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x24, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc14_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p13 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp13 : p13 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 768#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p13)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p14 : BitVec 64),
      p14 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 792#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = p13 → s1.readReg64 .x0 = p14 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p14 2 2 ∗ memRegion p14 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 792#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p13 from hx0]; exact beq_eq_false_iff_ne.mpr hp13
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
    (by simp only [arm64_norm, wp_norm, Reg.x23, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x25, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem alloc15_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp p14 : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hp14 : p14 ≠ 0#64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 792#64) (hrun : s.status = .Running)
    (hsp : s.sp = fsp) (htrace : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = p14)
    (hfit : FitsEvents M lim st (rustAllocEvents 2 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (p15 : BitVec 64),
      p15 ≠ 0#64 →
      s1.pc = (blkPl_416).base + 820#64 → s1.status = .Running → s1.sp = fsp →
      s1.trace = s0.trace → calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = p14 → s1.readReg64 .x0 = p15 →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢ A.pool lim (M.stepEvents (rustAllocEvents 2 2) st) s1 ∗
            (A.live p15 2 2 ∗ memRegion p15 2) ∗ stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 820#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame) post := by
  have hlayout := rustLayoutOk_2_2
  rcases (by simpa [rustAllocEvents] using hfit : FitsEvent M lim st (.alloc 2) ∧ True) with
    ⟨⟨_hwmax, henf, hram, hva⟩, _⟩
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hbeq_in : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := by
    rw [show s.readReg64 (Reg.gpr 0#5) = p14 from hx0]; exact beq_eq_false_iff_ne.mpr hp14
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
  have hbeq15 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr0] using ht
  have hsp1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 820#64)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq15, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq15, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq15, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x23, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x26, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, *])
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, *]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Public Budget-Threaded Block A Part B & Combined Block A Theorems -/

/-- Block A part 3 (`+704 -> +820`):
    performs allocations `11..15` (`2` bytes, align `2`), storing pointers `p11..p15`
    into registers `x23, x24, x25, x26, x0` while preserving `x19, x20, x21, x22, x27, x28, x29`. -/
theorem blockA_alloc_11_15_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAAlloc1115Env)
    (hcont : ∀ s16 (p11 p12 p13 p14 p15 : BitVec 64),
      p11 ≠ 0#64 → p12 ≠ 0#64 → p13 ≠ 0#64 → p14 ≠ 0#64 → p15 ≠ 0#64 →
      s16.pc = (blkPl_416).base + 820#64 →
      s16.status = .Running →
      s16.sp = fsp →
      s16.trace = s0.trace →
      calleeSavedVRegs s16 = calleeSavedVRegs s →
      s16.readReg64 .x23 = p11 →
      s16.readReg64 .x24 = p12 →
      s16.readReg64 .x25 = p13 →
      s16.readReg64 .x26 = p14 →
      s16.readReg64 .x0 = p15 →
      s16.readReg64 .x19 = s.readReg64 .x19 →
      s16.readReg64 .x20 = s.readReg64 .x20 →
      s16.readReg64 .x21 = s.readReg64 .x21 →
      s16.readReg64 .x22 = s.readReg64 .x22 →
      s16.readReg64 .x27 = s.readReg64 .x27 →
      s16.readReg64 .x28 = s.readReg64 .x28 →
      s16.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s16
        (A.pool lim (M.stepEvents blockAAlloc1115Events st) s16 ∗
         (A.live p11 2 2 ∗ memRegion p11 2) ∗
         (A.live p12 2 2 ∗ memRegion p12 2) ∗
         (A.live p13 2 2 ∗ memRegion p13 2) ∗
         (A.live p14 2 2 ∗ memRegion p14 2) ∗
         (A.live p15 2 2 ∗ memRegion p15 2) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  let e1 := rustAllocEvents 2 2
  have hfit_ev : FitsEvents M lim st ((((e1 ++ e1) ++ e1) ++ e1) ++ e1) :=
    (fitsEnv_blockAAlloc1115_iff).mp hfit
  have hf1114_15 := (fitsEvents_append M lim (((e1 ++ e1) ++ e1) ++ e1) e1 st).mp hfit_ev
  have hf1113_14 := (fitsEvents_append M lim ((e1 ++ e1) ++ e1) e1 st).mp hf1114_15.1
  have hf1112_13 := (fitsEvents_append M lim (e1 ++ e1) e1 st).mp hf1113_14.1
  have hf11_12 := (fitsEvents_append M lim e1 e1 st).mp hf1112_13.1
  have hf13 : FitsEvents M lim (M.stepEvents e1 (M.stepEvents e1 st)) e1 := by
    rw [← M.stepEvents_append e1 e1 st]; exact hf1112_13.2
  have hf14 : FitsEvents M lim (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st))) e1 := by
    rw [← M.stepEvents_append e1 e1 st, ← M.stepEvents_append (e1 ++ e1) e1 st]; exact hf1113_14.2
  have hf15 :
      FitsEvents M lim
        (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st)))) e1 := by
    rw [← M.stepEvents_append e1 e1 st,
        ← M.stepEvents_append (e1 ++ e1) e1 st,
        ← M.stepEvents_append ((e1 ++ e1) ++ e1) e1 st]
    exact hf1114_15.2
  refine SepWPp.of_sepWP (alloc11_seg hA s0 s fsp hfsp_align Frame hpc hrun hsp htrace hf11_12.1 ?_)
  intro s12 P12 p11 hp11 hpc12 hrun12 hsp12 htr12 hvregs12 hx0_12
    hx19_12 hx20_12 hx21_12 hx22_12 hx27_12 hx28_12 hx29_12 hent12
  refine SepWPp.weaken_pre (Entails.trans hent12 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc12_seg hA s0 s12 fsp p11 hfsp_align hp11 ((A.live p11 2 2 ∗ memRegion p11 2) ∗ Frame)
        hpc12 hrun12 hsp12 htr12 hx0_12 hf11_12.2 ?_))
  intro s13 P13 p12 hp12 hpc13 hrun13 hsp13 htr13 hvregs13 hx23_13 hx0_13
    hx19_13 hx20_13 hx21_13 hx22_13 hx27_13 hx28_13 hx29_13 hent13
  refine SepWPp.weaken_pre (Entails.trans hent13 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc13_seg hA s0 s13 fsp p12 hfsp_align hp12
        ((A.live p11 2 2 ∗ memRegion p11 2) ∗ (A.live p12 2 2 ∗ memRegion p12 2) ∗ Frame)
        hpc13 hrun13 hsp13 htr13 hx0_13 hf13 ?_))
  intro s14 P14 p13 hp13 hpc14 hrun14 hsp14 htr14 hvregs14 hx23_14 hx24_14 hx0_14
    hx19_14 hx20_14 hx21_14 hx22_14 hx27_14 hx28_14 hx29_14 hent14
  refine SepWPp.weaken_pre (Entails.trans hent14 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc14_seg hA s0 s14 fsp p13 hfsp_align hp13
        ((A.live p11 2 2 ∗ memRegion p11 2) ∗ (A.live p12 2 2 ∗ memRegion p12 2) ∗
         (A.live p13 2 2 ∗ memRegion p13 2) ∗ Frame)
        hpc14 hrun14 hsp14 htr14 hx0_14 hf14 ?_))
  intro s15 P15 p14 hp14 hpc15 hrun15 hsp15 htr15 hvregs15 hx23_15 hx24_15 hx25_15 hx0_15
    hx19_15 hx20_15 hx21_15 hx22_15 hx27_15 hx28_15 hx29_15 hent15
  refine SepWPp.weaken_pre (Entails.trans hent15 (Entails.of_eq (by sep_ac_rfl)))
    (SepWPp.of_sepWP
      (alloc15_seg hA s0 s15 fsp p14 hfsp_align hp14
        ((A.live p11 2 2 ∗ memRegion p11 2) ∗ (A.live p12 2 2 ∗ memRegion p12 2) ∗
         (A.live p13 2 2 ∗ memRegion p13 2) ∗ (A.live p14 2 2 ∗ memRegion p14 2) ∗ Frame)
        hpc15 hrun15 hsp15 htr15 hx0_15 hf15 ?_))
  intro s16 P16 p15 hp15 hpc16 hrun16 hsp16 htr16 hvregs16 hx23_16 hx24_16 hx25_16
    hx26_16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx27_16 hx28_16 hx29_16 hent16
  have hstep_eq :
      M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 (M.stepEvents e1 st)))) =
        M.stepEvents blockAAlloc1115Events st := by
    dsimp only [e1]
    rw [← M.stepEvents_append (rustAllocEvents 2 2) (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st,
        ← M.stepEvents_append _ (rustAllocEvents 2 2) st]
    rfl
  refine SepWPp.weaken_pre (Entails.trans hent16 ?_)
    (hcont s16 p11 p12 p13 p14 p15 hp11 hp12 hp13 hp14 hp15 hpc16 hrun16 hsp16 htr16
      (hvregs16.trans (hvregs15.trans (hvregs14.trans (hvregs13.trans hvregs12))))
      (hx23_16.trans (hx23_15.trans (hx23_14.trans hx23_13)))
      (hx24_16.trans (hx24_15.trans hx24_14))
      (hx25_16.trans hx25_15)
      hx26_16
      hx0_16
      (hx19_16.trans (hx19_15.trans (hx19_14.trans (hx19_13.trans hx19_12))))
      (hx20_16.trans (hx20_15.trans (hx20_14.trans (hx20_13.trans hx20_12))))
      (hx21_16.trans (hx21_15.trans (hx21_14.trans (hx21_13.trans hx21_12))))
      (hx22_16.trans (hx22_15.trans (hx22_14.trans (hx22_13.trans hx22_12))))
      (hx27_16.trans (hx27_15.trans (hx27_14.trans (hx27_13.trans hx27_12))))
      (hx28_16.trans (hx28_15.trans (hx28_14.trans (hx28_13.trans hx28_12))))
      (hx29_16.trans (hx29_15.trans (hx29_14.trans (hx29_13.trans hx29_12)))))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
/-- Block A part 4 (`+820 -> +976`):
    scatters the 16 `Poly::zero()` headers (`cap = 1, ptr = p_k, len = 0`) into `[fsp + 256 .. fsp + 640)`,
    reloads `x19` from `[fsp + 88]`, sets `x20 = 0`, `x28 = 24`, transports `A.pool lim st`,
    and folds into `polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`. -/
theorem blockA_init_scatter_placed [LibsignalPlacement]
    {M : AllocCostModel} {ext : String → Option (State → State)}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (s : State) (fsp vecsBase : BitVec 64)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 : BitVec 64)
    (hp0 : p0 ≠ 0#64) (hp1 : p1 ≠ 0#64) (hp2 : p2 ≠ 0#64) (hp3 : p3 ≠ 0#64)
    (hp4 : p4 ≠ 0#64) (hp5 : p5 ≠ 0#64) (hp6 : p6 ≠ 0#64) (hp7 : p7 ≠ 0#64)
    (hp8 : p8 ≠ 0#64) (hp9 : p9 ≠ 0#64) (hp10 : p10 ≠ 0#64) (hp11 : p11 ≠ 0#64)
    (hp12 : p12 ≠ 0#64) (hp13 : p13 ≠ 0#64) (hp14 : p14 ≠ 0#64) (hp15 : p15 ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = p15)
    (hx19 : s.readReg64 .x19 = p8)
    (hx20 : s.readReg64 .x20 = p10)
    (hx21 : s.readReg64 .x21 = p6)
    (hx22 : s.readReg64 .x22 = p7)
    (hx23 : s.readReg64 .x23 = p11)
    (hx24 : s.readReg64 .x24 = p12)
    (hx25 : s.readReg64 .x25 = p13)
    (hx26 : s.readReg64 .x26 = p14)
    (hx28 : s.readReg64 .x28 = p9) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 976#64)
      s
      (A.pool lim st s ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame)
      (fun sm Pm =>
        (Pm ⊢
          A.pool lim st sm ∗
          ((fsp + 88#64) ↦₆₄ vecsBase) ∗
          ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
          ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
          ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
          polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
          Frame) ∧
        sm.sp = fsp ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 .x19 = vecsBase ∧
        sm.readReg64 .x20 = 0#64 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = 24#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29) := by
  apply sepWP_seg_416 (mid := (blkPl_416).base + 976#64)
  intro _m_strip
  rw [show
      (A.pool lim st s ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
       (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
       (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
       Frame) =
      (cells (fsp + 256#64) 48 ∗
       (A.pool lim st s ∗
        ((fsp + 88#64) ↦₆₄ vecsBase) ∗
        ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
        ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
        ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
        (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
        (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
        (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
        (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
        (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
        (A.live p10 2 2 ∗ memRegion p10 2) ∗ (A.live p11 2 2 ∗ memRegion p11 2) ∗
        (A.live p12 2 2 ∗ memRegion p12 2) ∗ (A.live p13 2 2 ∗ memRegion p13 2) ∗
        (A.live p14 2 2 ∗ memRegion p14 2) ∗ (A.live p15 2 2 ∗ memRegion p15 2) ∗
        Frame)) by sep_ac_rfl]
  iterate 48 (apply sepWP_cells_succ; intro _)
  apply sepWP_cells_zero
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine ⟨?_, by wp_norm_lhs, by wp_norm_lhs, by simp only [arm64_norm, wp_norm],
    by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs, by wp_norm_lhs⟩
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (zeroPolySlotsAt_entails_polyListOf A.repAlloc 16 (fsp + 256#64)))))))))))
  dsimp only [zeroPolySlotsAt]
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_emp, sepConj_assoc]
  have hz0 := zeroPolySlotAt_intro A.repAlloc (fsp + 256#64) p0 hp0
  have hz1 := zeroPolySlotAt_intro A.repAlloc (fsp + 280#64) p1 hp1
  have hz2 := zeroPolySlotAt_intro A.repAlloc (fsp + 304#64) p2 hp2
  have hz3 := zeroPolySlotAt_intro A.repAlloc (fsp + 328#64) p3 hp3
  have hz4 := zeroPolySlotAt_intro A.repAlloc (fsp + 352#64) p4 hp4
  have hz5 := zeroPolySlotAt_intro A.repAlloc (fsp + 376#64) p5 hp5
  have hz6 := zeroPolySlotAt_intro A.repAlloc (fsp + 400#64) p6 hp6
  have hz7 := zeroPolySlotAt_intro A.repAlloc (fsp + 424#64) p7 hp7
  have hz8 := zeroPolySlotAt_intro A.repAlloc (fsp + 448#64) p8 hp8
  have hz9 := zeroPolySlotAt_intro A.repAlloc (fsp + 472#64) p9 hp9
  have hz10 := zeroPolySlotAt_intro A.repAlloc (fsp + 496#64) p10 hp10
  have hz11 := zeroPolySlotAt_intro A.repAlloc (fsp + 520#64) p11 hp11
  have hz12 := zeroPolySlotAt_intro A.repAlloc (fsp + 544#64) p12 hp12
  have hz13 := zeroPolySlotAt_intro A.repAlloc (fsp + 568#64) p13 hp13
  have hz14 := zeroPolySlotAt_intro A.repAlloc (fsp + 592#64) p14 hp14
  have hz15 := zeroPolySlotAt_intro A.repAlloc (fsp + 616#64) p15 hp15
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz0 hz1 hz2 hz3 hz4 hz5 hz6 hz7
  simp only [bv_add_lit_add_lit, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hz8 hz9 hz10 hz11 hz12 hz13 hz14 hz15
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hz0 (sepConj_mono hz1 (sepConj_mono hz2 (sepConj_mono hz3
          (sepConj_mono hz4 (sepConj_mono hz5 (sepConj_mono hz6 (sepConj_mono hz7
          (sepConj_mono hz8 (sepConj_mono hz9 (sepConj_mono hz10 (sepConj_mono hz11
          (sepConj_mono hz12 (sepConj_mono hz13 (sepConj_mono hz14
          (sepConj_mono_left hz15))))))))))))))))))))))))
  exact Entails.of_eq (by sep_ac_rfl)

/-- Complete Block A (`+436 -> +976`):
    allocates 16 `2`-byte `Poly` buffers under `FitsEnv M lim st BlockAEnv`, stores `self_ptr`
    (`x24`) to `[fsp + 8]`, initializes `[fsp + 256 .. fsp + 640)` to
    `polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩)`, restores `[fsp + 112 .. fsp + 232)`
    to `memRegion (fsp + 112#64) 120`, and sets `x19 = vecsBase`, `x20 = 0`, `x28 = 24`. -/
theorem blockA_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp vecsBase u8 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Frame R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 436#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit : FitsEnv M lim st BlockAEnv)
    (hcont : ∀ s_out,
      s_out.pc = (blkPl_416).base + 976#64 →
      s_out.status = .Running →
      s_out.sp = fsp →
      s_out.trace = s0.trace →
      calleeSavedVRegs s_out = calleeSavedVRegs s →
      s_out.readReg64 .x19 = vecsBase →
      s_out.readReg64 .x20 = 0#64 →
      s_out.readReg64 .x27 = s.readReg64 .x27 →
      s_out.readReg64 .x28 = 24#64 →
      s_out.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s_out
        (A.pool lim (M.stepEvents blockAEvents st) s_out ∗
         ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
         ((fsp + 88#64) ↦₆₄ vecsBase) ∗
         memRegion (fsp + 112#64) 120 ∗
         polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((fsp + 8#64) ↦₆₄ u8) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗
       memRegion (fsp + 112#64) 120 ∗
       memRegion (fsp + 256#64) 384 ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_ev :
      FitsEvents M lim st ((blockAAlloc05Events ++ blockAAlloc610Events) ++ blockAAlloc1115Events) :=
    (fitsEnv_blockA_iff).mp hfit
  have hf010_1115 :=
    (fitsEvents_append M lim (blockAAlloc05Events ++ blockAAlloc610Events) blockAAlloc1115Events st).mp hfit_ev
  have hf05_610 :=
    (fitsEvents_append M lim blockAAlloc05Events blockAAlloc610Events st).mp hf010_1115.1
  have hfit05 : FitsEnv M lim st BlockAAlloc05Env :=
    (fitsEnv_blockAAlloc05_iff).mpr hf05_610.1
  have hfit610 : FitsEnv M lim (M.stepEvents blockAAlloc05Events st) BlockAAlloc610Env :=
    (fitsEnv_blockAAlloc610_iff).mpr hf05_610.2
  have hfit1115 :
      FitsEnv M lim
        (M.stepEvents blockAAlloc610Events (M.stepEvents blockAAlloc05Events st))
        BlockAAlloc1115Env := by
    rw [← M.stepEvents_append blockAAlloc05Events blockAAlloc610Events st]
    exact (fitsEnv_blockAAlloc1115_iff).mpr hf010_1115.2
  have hcells : memRegion (fsp + 256#64) 384 = cells (fsp + 256#64) 48 :=
    ProofLib.memRegion_cells (fsp + 256#64) 48 (by decide)
  rw [hcells]
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_112_split_spills fsp))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWPp.exists_elim; intro _)
  rename_i u184 u192 u200 u208 u216 u224
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_0_5_placed hA s0 s fsp hfsp_align u8 u184 u192 u200 u208 u216 u224
      (((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗ cells (fsp + 256#64) 48 ∗ Frame)
      R hpc hrun hsp htrace hfit05 ?_)
  intro s6 p0 p1 p2 p3 p4 p5 hp0 hp1 hp2 hp3 hp4 hp5 hpc6 hrun6 hsp6 htr6 hvregs6 hx27_6 hx29_6
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_6_10_placed hA s0 s6 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗ Frame)
      R hpc6 hrun6 hsp6 htr6 hfit610 ?_)
  intro s11 p6 p7 p8 p9 p10 hp6 hp7 hp8 hp9 hp10 hpc11 hrun11 hsp11 htr11 hvregs11
    hx21_11 hx22_11 hx19_11 hx28_11 hx20_11 hx27_11 hx29_11
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (blockA_alloc_11_15_placed hA s0 s11 fsp hfsp_align
      (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗
       ((fsp + 88#64) ↦₆₄ vecsBase) ∗ memRegion (fsp + 112#64) 72 ∗
       ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
       ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
       ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
       cells (fsp + 256#64) 48 ∗
       (A.live p0 2 2 ∗ memRegion p0 2) ∗ (A.live p1 2 2 ∗ memRegion p1 2) ∗
       (A.live p2 2 2 ∗ memRegion p2 2) ∗ (A.live p3 2 2 ∗ memRegion p3 2) ∗
       (A.live p4 2 2 ∗ memRegion p4 2) ∗ (A.live p5 2 2 ∗ memRegion p5 2) ∗
       (A.live p6 2 2 ∗ memRegion p6 2) ∗ (A.live p7 2 2 ∗ memRegion p7 2) ∗
       (A.live p8 2 2 ∗ memRegion p8 2) ∗ (A.live p9 2 2 ∗ memRegion p9 2) ∗
       (A.live p10 2 2 ∗ memRegion p10 2) ∗ Frame)
      R hpc11 hrun11 hsp11 htr11 hfit1115 ?_)
  intro s16 p11 p12 p13 p14 p15 hp11 hp12 hp13 hp14 hp15 hpc16 hrun16 hsp16 htr16 hvregs16
    hx23_16 hx24_16 hx25_16 hx26_16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx27_16 hx28_16 hx29_16
  rw [hx19_11] at hx19_16
  rw [hx20_11] at hx20_16
  rw [hx21_11] at hx21_16
  rw [hx22_11] at hx22_16
  rw [hx27_11, hx27_6] at hx27_16
  rw [hx28_11] at hx28_16
  rw [hx29_11, hx29_6] at hx29_16
  rw [hvregs11, hvregs6] at hvregs16
  have hstep_eq :
      M.stepEvents blockAAlloc1115Events
          (M.stepEvents blockAAlloc610Events (M.stepEvents blockAAlloc05Events st)) =
        M.stepEvents blockAEvents st := by
    rw [← M.stepEvents_append blockAAlloc05Events blockAAlloc610Events st,
        ← M.stepEvents_append (blockAAlloc05Events ++ blockAAlloc610Events) blockAAlloc1115Events st]
    rfl
  rw [hstep_eq]
  have hscatter := blockA_init_scatter_placed (ext := ext) A lim (M.stepEvents blockAEvents st)
    s16 fsp vecsBase
    p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15
    hp0 hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
    hfsp_align
    (((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
     stackAt fsp allocHookStack ∗ Frame)
    hpc16 hrun16 hsp16 hx0_16 hx19_16 hx20_16 hx21_16 hx22_16 hx23_16 hx24_16 hx25_16 hx26_16 hx28_16
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP (SepWP.mono hscatter ?_))
  rintro s_out Pm hpc_out hrun_out ⟨hPm, hsp_out, htr_out, hvregs_out, hx19_out, hx20_out, hx27_out, hx28_out, hx29_out⟩
  rw [htr16] at htr_out
  rw [hvregs16] at hvregs_out
  rw [hx27_16] at hx27_out
  rw [hx29_16] at hx29_out
  refine SepWPp.weaken_pre (Entails.trans hPm ?_)
    (hcont s_out hpc_out hrun_out hsp_out htr_out hvregs_out hx19_out hx20_out hx27_out hx28_out hx29_out)
  refine Entails.trans (Entails.of_eq (show
    A.pool lim (M.stepEvents blockAEvents st) s_out ∗
    ((fsp + 88#64) ↦₆₄ vecsBase) ∗
    ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
    ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
    ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0) ∗
    polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
    ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ memRegion (fsp + 112#64) 72 ∗
    stackAt fsp allocHookStack ∗ Frame =
    (memRegion (fsp + 112#64) 72 ∗
     ((fsp + 184#64) ↦₆₄ p5) ∗ ((fsp + 192#64) ↦₆₄ p4) ∗
     ((fsp + 200#64) ↦₆₄ p3) ∗ ((fsp + 208#64) ↦₆₄ p2) ∗
     ((fsp + 216#64) ↦₆₄ p1) ∗ ((fsp + 224#64) ↦₆₄ p0)) ∗
    (A.pool lim (M.stepEvents blockAEvents st) s_out ∗
     ((fsp + 8#64) ↦₆₄ s.readReg64 .x24) ∗ ((fsp + 88#64) ↦₆₄ vecsBase) ∗
     polyListOf A.repAlloc (fsp + 256#64) (List.replicate 16 ⟨[]⟩) ∗
     stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left (memRegion_112_fold_spills fsp p5 p4 p3 p2 p1 p0)) ?_
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInitPlacedBBudget
