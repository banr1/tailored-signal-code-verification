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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlaced
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.RodataPlacedBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysInit
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Constant Basis Loops (`n = 36, 34`)

Relocatable `[LibsignalPlacement]` verification of the `n = 34` constant Lagrange basis copy loop
(`+1136 -> +2608`) and re-exports of `n = 36` from `PointsToPolysConstLoopPlacedBudgetAux`,
threading `RustCliAllocBudget M` and `BudgetLimits`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudget

export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudgetAux
  (BasisN36Env BasisN36LoopEnv basisN36Events basisN36LoopEvents fitsEnv_basisN36_iff)
export LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudgetAux
  (basisN36Events_split basis_n36_loop_placed_sepWPp basis_n36_placed_sepWPp fitsEnv_basisN36Loop_iff)

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 blkPl_416_ρ lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSpqrV1 (COMPLETE_POINTS_POLYS_34 Poly)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (polyListOf polyOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (align8_basis_step basisVecAt bv_add_lit_add_lit
   completePointsPolys34Bytes completePointsPolys34PlacedAt completePointsPolys34Sym
   completePointsPolys34_spec exists_pow_two_eq_eight exists_pow_two_eq_two
   exists_words_68 extractCompletePolys gf16SliceBytes gf16SliceBytes_length
   ls_resolve_completePointsPolys34 memRegion_split_68 memRegion_split_basis_cons
   ofNat_add_one_eq_succ ofNat_beq_ofNat_false ofNat_sub_ofNat_beq_zero_false
   ofNat_succ_add_neg_one ofNat_succ_sub_one polyListOf_cons_off polyOf_of_pointsToBytes
   polysToBytes polysToBytes_cons_ro)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel fitsEvents_append rustAllocEvents
   rustCliAllocNoOomSpec)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWP_seg_416 sepWPp_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConst5PlacedBudget
  (BasisLoopExitEnv basisLoopExitEvents basis_loop_exit_placed_sepWPp fitsEnv_basisLoopExit_iff)
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
attribute [local simp, local arm64_norm, local wp_norm]
  bv_add_lit_add_lit ofNat_succ_sub_one ofNat_succ_add_neg_one ofNat_add_one_eq_succ
  ls_resolve_completePointsPolys34
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

/-! ## 1. Exact Allocator Event Envelopes for `n = 34` -/

/-- Exact allocator event sequence for `k` remaining iterations of the `n = 34` basis copy loop
    (`+2372..+2428 -> +2332..+2368`), allocating `68` bytes (align `2`) per polynomial. -/
def basisN34LoopEvents (k : Nat) : List AllocEvent :=
  (List.replicate k (rustAllocEvents 68 2)).flatten

theorem basisN34LoopEvents_one : basisN34LoopEvents 1 = rustAllocEvents 68 2 := rfl

theorem basisN34LoopEvents_succ (k : Nat) :
    basisN34LoopEvents (k + 1) = rustAllocEvents 68 2 ++ basisN34LoopEvents k := rfl

def BasisN34LoopEnv (k : Nat) (evs : List AllocEvent) : Prop :=
  evs = basisN34LoopEvents k

theorem fitsEnv_basisN34Loop_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (k : Nat) :
    FitsEnv M lim st (BasisN34LoopEnv k) ↔ FitsEvents M lim st (basisN34LoopEvents k) := by
  constructor
  · intro h; exact h (basisN34LoopEvents k) rfl
  · intro h evs hevs; rw [hevs]; exact h

/-- Exact allocator event sequence for the full `n = 34` constant basis path (`+1136..+2608`):
    `816` bytes (align `8`) for `basisPtr`, thirty-four `68`-byte (align `2`) buffers for
    `basis[0..33]`, and `68` bytes (align `2`) for `accPtr`
    (matching `DefsBudget.PointsToPolysIterEnv 34`). -/
def basisN34Events : List AllocEvent :=
  rustAllocEvents (24 * 34) 8 ++ (List.replicate (34 + 1) (rustAllocEvents (2 * 34) 2)).flatten

theorem basisN34Events_split :
    basisN34Events =
      (rustAllocEvents 816 8 ++ basisN34LoopEvents 34) ++ basisLoopExitEvents 34 := rfl

def BasisN34Env (evs : List AllocEvent) : Prop :=
  evs = basisN34Events

theorem fitsEnv_basisN34_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st BasisN34Env ↔ FitsEvents M lim st basisN34Events := by
  constructor
  · intro h; exact h basisN34Events rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (BasisN34LoopEnv 34) := by
  rw [fitsEnv_basisN34Loop_iff]
  dsimp only [basisN34LoopEvents, List.replicate, List.flatten, rustAllocEvents,
    List.cons_append, List.nil_append, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  iterate 34 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

example :
    FitsEnv coarseCostModel
      { staticCount := 64, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init BasisN34Env := by
  rw [fitsEnv_basisN34_iff]
  dsimp only [basisN34Events, List.replicate, List.flatten, rustAllocEvents,
    List.cons_append, List.nil_append, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  iterate 36 refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  exact trivial

/-! ## 2. Segment Allocation Steppers (`+2372 -> +2392` & `+1136 -> +2372`) -/

private theorem allocPoly68_seg_416 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (Rest : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hfit68 : FitsEvents M lim st (rustAllocEvents 68 2))
    (hcont : ∀ s1 P1 (ptr : BitVec 64),
      ptr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2392#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 (Reg.gpr 0#5) = ptr →
      s1.readReg64 (Reg.gpr 19#5) = s.readReg64 .x19 →
      s1.readReg64 (Reg.gpr 20#5) = s.readReg64 .x20 →
      s1.readReg64 (Reg.gpr 21#5) = s.readReg64 .x21 →
      s1.readReg64 (Reg.gpr 22#5) = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢
        A.pool lim (M.stepEvents (rustAllocEvents 68 2) st) s1 ∗
        A.live ptr 68 2 ∗ memRegion ptr 68 ∗
        stackAt fsp allocHookStack ∗ Rest) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 2392#64) s
      (A.pool lim st s ∗ stackAt fsp allocHookStack ∗ Rest)
      post := by
  have hlayout68_2 : RustLayoutOk 68 2 := ⟨⟨by decide, ⟨1, rfl⟩, by decide⟩, by decide⟩
  have h68_toNat : (68#64 : BitVec 64).toNat = 68 := rfl
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hfit_ev : FitsEvent M lim st (.alloc 68) := by simpa [rustAllocEvents] using hfit68
  rcases hfit_ev with ⟨_hwmax, henf, hram, hva⟩
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf0 : sf.trace = s0.trace := by simp only [arm64_norm, wp_norm, htrace, *]
  have hsp_sf0 : sf.sp = fsp := by simp only [arm64_norm, wp_norm, hsp, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (68, 2, st)
  clear halloc
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  have hsp_sf1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf0, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2392#64)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, *]) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, hsp_sf1])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, htr_sf1])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x19, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x22, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x23, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, hbeq0, Bool.false_eq_true, ↓reduceIte, *])
    ?_
  simp only [arm64_norm, wp_norm, h68_toNat, h2_toNat, hsp_sf1, hsp_sf0, hsp,
    hbeq0, Bool.false_eq_true, ↓reduceIte, *]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem allocBasis816_seg_416 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u96 u656 u664 u672 : BitVec 64)
    (Rest : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 34#64)
    (hfit816 : FitsEvents M lim st (rustAllocEvents 816 8))
    (hcont : ∀ s1 P1 (basisPtr : BitVec 64),
      basisPtr ≠ 0#64 →
      basisPtr.toNat % 8 = 0 →
      s1.pc = (blkPl_416).base + 2372#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = basisPtr →
      s1.readReg64 .x20 = 0#64 →
      s1.readReg64 .x21 = lsρ completePointsPolys34Sym →
      s1.readReg64 .x22 = 1#64 →
      s1.readReg64 .x23 = s.readReg64 .x20 →
      s1.readReg64 .x25 = 34#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢
        A.pool lim (M.stepEvents (rustAllocEvents 816 8) st) s1 ∗
        A.live basisPtr 816 8 ∗ memRegion basisPtr 816 ∗
        ((fsp + 96#64) ↦₆₄ 34#64) ∗
        ((fsp + 656#64) ↦₆₄ 34#64) ∗
        ((fsp + 664#64) ↦₆₄ basisPtr) ∗
        ((fsp + 672#64) ↦₆₄ 0#64) ∗
        stackAt fsp allocHookStack ∗ Rest) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 2372#64) s
      (A.pool lim st s ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       stackAt fsp allocHookStack ∗ Rest)
      post := by
  have hlayout816_8 : RustLayoutOk 816 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have h816_toNat : (816#64 : BitVec 64).toNat = 816 := rfl
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  have hfit_ev : FitsEvent M lim st (.alloc 816) := by simpa [rustAllocEvents] using hfit816
  rcases hfit_ev with ⟨_hwmax, henf, hram, hva⟩
  have hshim := hA.noAllocShim_ok
  simp only [noAllocShimSpec, noAllocShimBudgetSpec, BitVec.ofNat_eq_ofNat] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec, Bool.false_eq_true, ↓reduceIte] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0; wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  have htr_sf0 : sf.trace = s0.trace := by simp only [arm64_norm, wp_norm, htrace, *]
  have hsp_sf0 : sf.sp = fsp := by simp only [arm64_norm, wp_norm, hsp, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (816, 8, st)
  clear halloc
  have hoom1 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have halign1 : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 8 = 0 := by assumption
  have hbeq1 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom1
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  have hsp_sf1 : sf_1.sp = fsp := by simp only [arm64_norm, wp_norm, hsp_sf0, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2292#64)
  intro _m_strip1; wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2372#64)
  intro _m_strip2; simp only [State.setMem_setMem]; wp_steps
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm])) (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom1 halign1
    (by wp_norm_goal)
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, hsp_sf1, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, htr_sf1, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x19, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x20, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x21, blkPl_416_ρ, completePointsPolys34Sym,
          BitVec.add_zero, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x22, hbeq1, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x23, Reg.x20, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, hx25, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, hbeq1, Bool.false_eq_true, ↓reduceIte, *])
    ?_
  simp only [arm64_norm, wp_norm, h816_toNat, h8_toNat, hsp_sf1, hsp_sf0, hsp, hx25,
    hbeq1, Bool.false_eq_true, ↓reduceIte, *]
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Budget-Threaded `n = 34` Constant Basis Loop & Top Theorem -/

/-- Loop body (`+2372..+2428 -> +2332..+2368`) for `n = 34`, inducted over `rest : List Poly`
    and threading `A.pool lim st` across `basisN34LoopEvents rest.length`. -/
theorem basis_n34_loop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 : State) (fsp basisPtr roBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hbasis_mod : basisPtr.toNat % 8 = 0)
    (_R : SepProp) :
    ∀ (rest : List Poly) (i : Nat) (st : M.σ),
      rest ≠ [] →
      i + rest.length = 34 →
      (∀ p ∈ rest, p.coefficients.length = 34) →
      FitsEnv M lim st (BasisN34LoopEnv rest.length) →
      ∀ (s : State) (u672 : BitVec 64) (Frame : SepProp),
        s.pc = (blkPl_416).base + 2372#64 →
        s.status = .Running →
        s.sp = fsp →
        s.trace = s0.trace →
        s.readReg64 .x19 = basisPtr →
        s.readReg64 .x20 = BitVec.ofNat 64 (24 * i) →
        s.readReg64 .x21 = roBase + BitVec.ofNat 64 (68 * i) →
        s.readReg64 .x22 = BitVec.ofNat 64 (i + 1) →
        (∀ s1,
          s1.pc = (blkPl_416).base + 2456#64 →
          s1.status = .Running →
          s1.sp = fsp →
          s1.trace = s0.trace →
          calleeSavedVRegs s1 = calleeSavedVRegs s →
          s1.readReg64 .x23 = s.readReg64 .x23 →
          s1.readReg64 .x25 = s.readReg64 .x25 →
          s1.readReg64 .x26 = s.readReg64 .x26 →
          s1.readReg64 .x27 = s.readReg64 .x27 →
          s1.readReg64 .x28 = s.readReg64 .x28 →
          s1.readReg64 .x29 = s.readReg64 .x29 →
          SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
            (s0.readReg64 (Reg.gpr 30#5)) s1
            (A.pool lim (M.stepEvents (basisN34LoopEvents rest.length) st) s1 ∗
             ((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ polysToBytes rest) ∗
             polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) rest ∗
             ((fsp + 656#64) ↦₆₄ 34#64) ∗
             ((fsp + 672#64) ↦₆₄ 34#64) ∗
             stackAt fsp allocHookStack ∗ Frame)
            Q Q_panic) →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
          (s0.readReg64 (Reg.gpr 30#5)) s
          (A.pool lim st s ∗
           ((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ polysToBytes rest) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * rest.length) ∗
           ((fsp + 656#64) ↦₆₄ 34#64) ∗
           ((fsp + 672#64) ↦₆₄ u672) ∗
           stackAt fsp allocHookStack ∗ Frame)
          Q Q_panic
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | p :: ps', i, st, _, hi_len, hall, hfit => by
    intro s u672 Frame hpc hrun hsp htrace hx19 hx20 hx21 hx22 hcont
    have hlen_cons : (p :: ps').length = ps'.length + 1 := rfl
    have hi_lt : i < 34 := by omega
    have hp_len : p.coefficients.length = 34 := hall p List.mem_cons_self
    have hp_bytes : (gf16SliceBytes p.coefficients).length = 68 := by
      rw [gf16SliceBytes_length, hp_len]
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, hro68, hrw68⟩ := exists_words_68 hp_bytes
    obtain ⟨hal0, hal8, hal16⟩ := align8_basis_step basisPtr hbasis_mod i
    have hfit_evs : FitsEvents M lim st (rustAllocEvents 68 2 ++ basisN34LoopEvents ps'.length) := by
      have hf := (fitsEnv_basisN34Loop_iff (p :: ps').length).mp hfit
      rwa [hlen_cons, basisN34LoopEvents_succ] at hf
    obtain ⟨hfit_cur, hfit_rest_evs⟩ :=
      (fitsEvents_append M lim (rustAllocEvents 68 2) (basisN34LoopEvents ps'.length) st).mp hfit_evs
    have hfit_rest : FitsEnv M lim (M.stepEvents (rustAllocEvents 68 2) st) (BasisN34LoopEnv ps'.length) :=
      (fitsEnv_basisN34Loop_iff ps'.length).mpr hfit_rest_evs
    have hcmp_lt : ¬(BitVec.ofNat 64 i == 34#64) = true := by
      simpa using ofNat_beq_ofNat_false i 34 hi_lt (by decide)
    have hcmp_sub_lt : ¬(BitVec.ofNat 64 i - 34#64 == 0#64) = true := by
      simpa using ofNat_sub_ofNat_beq_zero_false i 34 hi_lt (by decide)
    have hx20_next : BitVec.ofNat 64 (24 * i) + 24#64 = BitVec.ofNat 64 (24 * (i + 1)) := by
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_add]
      congr 1
    have hx21_next : (roBase + BitVec.ofNat 64 (68 * i)) + 68#64 =
        roBase + BitVec.ofNat 64 (68 * (i + 1)) := by
      rw [BitVec.add_assoc, show (68#64 : BitVec 64) = BitVec.ofNat 64 68 from rfl,
          ← BitVec.ofNat_add]
      congr 2
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWPp.of_sepWP
        (allocPoly68_seg_416 hA s0 s fsp hfsp_align
          (((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ polysToBytes (p :: ps')) ∗
           memRegion (basisPtr + BitVec.ofNat 64 (24 * i)) (24 * (p :: ps').length) ∗
           ((fsp + 656#64) ↦₆₄ 34#64) ∗
           ((fsp + 672#64) ↦₆₄ u672) ∗ Frame)
          hpc hrun hsp htrace hfit_cur ?_))
    intro sA PA ptr hoom hpcA hrunA hspA htrA hvregsA
      hx0A hx19A_0 hx20A_0 hx21A_0 hx22A_0 hx23A hx25A hx26A hx27A hx28A hx29A hentA
    have hx19A : sA.readReg64 (Reg.gpr 19#5) = basisPtr := hx19A_0.trans hx19
    have hx20A : sA.readReg64 (Reg.gpr 20#5) = BitVec.ofNat 64 (24 * i) := hx20A_0.trans hx20
    have hx21A : sA.readReg64 (Reg.gpr 21#5) = roBase + BitVec.ofNat 64 (68 * i) := hx21A_0.trans hx21
    have hx22A : sA.readReg64 (Reg.gpr 22#5) = BitVec.ofNat 64 (i + 1) := hx22A_0.trans hx22
    refine SepWPp.weaken_pre hentA ?_
    clear hentA hx19A_0 hx20A_0 hx21A_0 hx22A_0
    rw [show (68 * i : Nat) = 2 * 34 * i by omega,
        polysToBytes_cons_ro roBase 34 i p ps' hp_len,
        show (2 * 34 * i : Nat) = 68 * i by omega,
        show (2 * 34 * (i + 1) : Nat) = 68 * (i + 1) by omega,
        hro68 (roBase + BitVec.ofNat 64 (68 * i)),
        memRegion_split_68 ptr,
        hlen_cons,
        memRegion_split_basis_cons basisPtr i ps'.length (by omega)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWPp.exists_elim; intro u_cap
    apply SepWPp.exists_elim; intro u_ptr
    apply SepWPp.exists_elim; intro u_len
    apply SepWPp.exists_elim; intro u0
    apply SepWPp.exists_elim; intro u8
    apply SepWPp.exists_elim; intro u16
    apply SepWPp.exists_elim; intro u24
    apply SepWPp.exists_elim; intro u32
    apply SepWPp.exists_elim; intro u40
    apply SepWPp.exists_elim; intro u48
    apply SepWPp.exists_elim; intro u56
    apply SepWPp.exists_elim; intro u64
    apply sepWPp_seg_416
      (mid := if (BitVec.ofNat 64 (i + 1 + 1) == 35#64) = true
              then (blkPl_416).base + 2456#64 else (blkPl_416).base + 2372#64)
    intro _m_strip1; wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hx22A, hcmp_lt, hcmp_sub_lt, ↓reduceIte])
      (by wp_norm_lhs)
      fun _m_real1 _hnsp1 => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp1.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hx22A, hcmp_lt, hcmp_sub_lt, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    have hpoly_i :
        (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 34#64) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 34#64) ∗
         A.live ptr 68 2 ∗
         (ptr ↦ₛ gf16SliceBytes p.coefficients)) ⊢
        polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) p :=
      polyOf_of_pointsToBytes A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i))
        ptr p 34 (by decide) (by decide) hoom hp_len
    cases ps' with
    | nil =>
      have hi33 : i = 33 := by simp at hi_len; omega
      subst hi33
      simp only [hx0A, hx19A, hx20A, hx21A, hx22A, hspA,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd]
      rw [polyListOf_cons_off A.repAlloc basisPtr 33 p [],
          show polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 34)) [] = emp from rfl,
          show (68 * 33 : Nat) = 2 * 34 * 33 by decide,
          polysToBytes_cons_ro roBase 34 33 p [] hp_len] at hcont
      simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd, sepConj_emp,
        List.length_cons, List.length_nil, basisN34LoopEvents_one] at hcont
      refine SepWPp.weaken_pre ?_
        (hcont _
          (by simp only [arm64_norm, wp_norm, hx22A, ↓reduceIte])
          (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, hspA])
          (by simp only [arm64_norm, wp_norm, htrA])
          (by simp only [arm64_norm, wp_norm, hvregsA])
          (by simp only [arm64_norm, wp_norm, Reg.x23, hx23A])
          (by simp only [arm64_norm, wp_norm, Reg.x25, hx25A])
          (by simp only [arm64_norm, wp_norm, Reg.x26, hx26A])
          (by simp only [arm64_norm, wp_norm, Reg.x27, hx27A])
          (by simp only [arm64_norm, wp_norm, Reg.x28, hx28A])
          (by simp only [arm64_norm, wp_norm, Reg.x29, hx29A]))
      have hro_eq := (hro68 (roBase + 2244#64)).symm
      have hrw_eq := (hrw68 ptr).symm
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hro_eq hrw_eq hpoly_i
      refine Entails.trans (Entails.of_eq (show _ =
        (((basisPtr + 792#64) ↦₆₄ 34#64) ∗
         ((basisPtr + 800#64) ↦₆₄ ptr) ∗
         ((basisPtr + 808#64) ↦₆₄ 34#64) ∗
         A.live ptr 68 2 ∗
         ((ptr ↦₆₄ w0) ∗
          ((ptr + 8#64) ↦₆₄ w1) ∗
          ((ptr + 16#64) ↦₆₄ w2) ∗
          ((ptr + 24#64) ↦₆₄ w3) ∗
          ((ptr + 32#64) ↦₆₄ w4) ∗
          ((ptr + 40#64) ↦₆₄ w5) ∗
          ((ptr + 48#64) ↦₆₄ w6) ∗
          ((ptr + 56#64) ↦₆₄ w7) ∗
          ((ptr + 64#64) ↦₃₂ w8))) ∗
        (((roBase + 2244#64) ↦₆₄ᵣ w0) ∗
         ((roBase + 2252#64) ↦₆₄ᵣ w1) ∗
         ((roBase + 2260#64) ↦₆₄ᵣ w2) ∗
         ((roBase + 2268#64) ↦₆₄ᵣ w3) ∗
         ((roBase + 2276#64) ↦₆₄ᵣ w4) ∗
         ((roBase + 2284#64) ↦₆₄ᵣ w5) ∗
         ((roBase + 2292#64) ↦₆₄ᵣ w6) ∗
         ((roBase + 2300#64) ↦₆₄ᵣ w7) ∗
         ((roBase + 2308#64) ↦₃₂ᵣ w8)) ∗
        (A.pool lim (M.stepEvents (rustAllocEvents 68 2) st) _ ∗
         ((roBase + 2312#64) ↦ᵣ polysToBytes []) ∗
         memRegion (basisPtr + 816#64) 0 ∗
         ((fsp + 656#64) ↦₆₄ 34#64) ∗
         ((fsp + 672#64) ↦₆₄ 34#64) ∗
         stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      rw [hrw_eq, hro_eq, ProofLib.memRegion_zero]
      simp only [emp_sepConj, sepConj_emp]
      refine Entails.trans (sepConj_mono_left hpoly_i) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    | cons p' ps'' =>
      have hi2_lt : i + 1 + 1 < 35 := by simp at hi_len; omega
      have hcmp_end : ¬(BitVec.ofNat 64 (i + 1 + 1) == 35#64) = true := by
        simpa using ofNat_beq_ofNat_false (i + 1 + 1) 35 hi2_lt (by decide)
      have hro_eq := (hro68 (roBase + BitVec.ofNat 64 (68 * i))).symm
      have hrw_eq := (hrw68 ptr).symm
      have hstep_cons :
          M.stepEvents (basisN34LoopEvents (p' :: ps'').length)
            (M.stepEvents (rustAllocEvents 68 2) st) =
          M.stepEvents (basisN34LoopEvents (p :: p' :: ps'').length) st := by
        rw [← M.stepEvents_append, hlen_cons, basisN34LoopEvents_succ]
      refine SepWPp.weaken_pre ?_
        (basis_n34_loop_placed_sepWPp hA s0 fsp basisPtr roBase hfsp_align hbasis_mod _R
          (p' :: ps'') (i + 1) (M.stepEvents (rustAllocEvents 68 2) st)
          (List.cons_ne_nil _ _) (by simp at hi_len ⊢; omega)
          (fun q hq => hall q (List.mem_cons_of_mem _ hq))
          hfit_rest
          _ (BitVec.ofNat 64 (i + 1))
          (((roBase + BitVec.ofNat 64 (68 * i)) ↦ᵣ gf16SliceBytes p.coefficients) ∗
           polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) p ∗ Frame)
          (by simp only [arm64_norm, wp_norm, hx22A, hcmp_end, Bool.false_eq_true, ↓reduceIte])
          (by wp_norm_lhs)
          (by simp only [arm64_norm, wp_norm, hspA])
          (by simp only [arm64_norm, wp_norm, htrA])
          (by simp only [arm64_norm, wp_norm, Reg.x19, hx19A])
          (by simp only [arm64_norm, wp_norm, Reg.x20, hx20A, hx20_next])
          (by simp only [arm64_norm, wp_norm, Reg.x21, hx21A, hx21_next])
          (by simp only [arm64_norm, wp_norm, Reg.x22, hx22A])
          (fun s1 hpc1 hrun1 hsp1 htr_s1 hvregs_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => by
            refine SepWPp.weaken_pre ?_
              (hcont s1 hpc1 hrun1 hsp1 htr_s1
                (by rw [hvregs_1]; simp only [arm64_norm, wp_norm, hvregsA])
                (by rw [hx23_1]; simp only [arm64_norm, wp_norm, Reg.x23, hx23A])
                (by rw [hx25_1]; simp only [arm64_norm, wp_norm, Reg.x25, hx25A])
                (by rw [hx26_1]; simp only [arm64_norm, wp_norm, Reg.x26, hx26A])
                (by rw [hx27_1]; simp only [arm64_norm, wp_norm, Reg.x27, hx27A])
                (by rw [hx28_1]; simp only [arm64_norm, wp_norm, Reg.x28, hx28A])
                (by rw [hx29_1]; simp only [arm64_norm, wp_norm, Reg.x29, hx29A]))
            rw [hstep_cons,
                show (68 * i : Nat) = 2 * 34 * i by omega,
                polysToBytes_cons_ro roBase 34 i p (p' :: ps'') hp_len,
                show (2 * 34 * i : Nat) = 68 * i by omega,
                show (2 * 34 * (i + 1) : Nat) = 68 * (i + 1) by omega,
                polyListOf_cons_off A.repAlloc basisPtr i p (p' :: ps'')]
            exact Entails.of_eq (by sep_ac_rfl)))
      refine Entails.trans (Entails.of_eq (show _ =
        (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ 34#64) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
         (((basisPtr + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄ 34#64) ∗
         A.live ptr 68 2 ∗
         ((ptr ↦₆₄ w0) ∗
          ((ptr + 8#64) ↦₆₄ w1) ∗
          ((ptr + 16#64) ↦₆₄ w2) ∗
          ((ptr + 24#64) ↦₆₄ w3) ∗
          ((ptr + 32#64) ↦₆₄ w4) ∗
          ((ptr + 40#64) ↦₆₄ w5) ∗
          ((ptr + 48#64) ↦₆₄ w6) ∗
          ((ptr + 56#64) ↦₆₄ w7) ∗
          ((ptr + 64#64) ↦₃₂ w8))) ∗
        (((roBase + BitVec.ofNat 64 (68 * i)) ↦₆₄ᵣ w0) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 8#64) ↦₆₄ᵣ w1) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 16#64) ↦₆₄ᵣ w2) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 24#64) ↦₆₄ᵣ w3) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 32#64) ↦₆₄ᵣ w4) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 40#64) ↦₆₄ᵣ w5) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 48#64) ↦₆₄ᵣ w6) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 56#64) ↦₆₄ᵣ w7) ∗
         (((roBase + BitVec.ofNat 64 (68 * i)) + 64#64) ↦₃₂ᵣ w8)) ∗
        (A.pool lim (M.stepEvents (rustAllocEvents 68 2) st) _ ∗
         ((roBase + BitVec.ofNat 64 (68 * (i + 1))) ↦ᵣ polysToBytes (p' :: ps'')) ∗
         memRegion (basisPtr + BitVec.ofNat 64 (24 * (i + 1))) (24 * (p' :: ps'').length) ∗
         ((fsp + 656#64) ↦₆₄ 34#64) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 (i + 1)) ∗
         stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      rw [hrw_eq, hro_eq]
      refine Entails.trans (sepConj_mono_left hpoly_i) ?_
      exact Entails.of_eq (by sep_ac_rfl)

/-- `n = 34` constant basis case (`+1136 -> +2608`) under `[LibsignalPlacement]`,
    threading `A.pool lim st` across `basisN34Events`. -/
theorem basis_n34_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u24 u96 u656 u664 u672 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = 34#64)
    (hfit : FitsEnv M lim st BasisN34Env)
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
      s1.readReg64 .x25 = 34#64 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents basisN34Events st) s1 ∗
         completePointsPolys34PlacedAt ∗
         basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
         A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
         ((fsp + 24#64) ↦₆₄ 34#64) ∗
         ((fsp + 96#64) ↦₆₄ 34#64) ∗
         ((fsp + 656#64) ↦₆₄ 34#64) ∗
         ((fsp + 664#64) ↦₆₄ basisPtr) ∗
         ((fsp + 672#64) ↦₆₄ 34#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       completePointsPolys34PlacedAt ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hfit_all :
      FitsEvents M lim st
        ((rustAllocEvents 816 8 ++ basisN34LoopEvents 34) ++ basisLoopExitEvents 34) := by
    rw [← basisN34Events_split]
    exact fitsEnv_basisN34_iff.mp hfit
  obtain ⟨hfit_12, hfit_exit_evs⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 816 8 ++ basisN34LoopEvents 34)
      (basisLoopExitEvents 34) st).mp hfit_all
  obtain ⟨hfit_816, hfit_loop_evs⟩ :=
    (fitsEvents_append M lim (rustAllocEvents 816 8) (basisN34LoopEvents 34) st).mp hfit_12
  have hfit_loop :
      FitsEnv M lim (M.stepEvents (rustAllocEvents 816 8) st) (BasisN34LoopEnv 34) :=
    (fitsEnv_basisN34Loop_iff 34).mpr hfit_loop_evs
  have hfit_exit :
      FitsEnv M lim
        (M.stepEvents (basisN34LoopEvents 34) (M.stepEvents (rustAllocEvents 816 8) st))
        (BasisLoopExitEnv 34) := by
    rw [← M.stepEvents_append]
    exact (fitsEnv_basisLoopExit_iff 34).mpr hfit_exit_evs
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (allocBasis816_seg_416 hA s0 s fsp hfsp_align u96 u656 u664 u672
        (completePointsPolys34PlacedAt ∗ ((fsp + 24#64) ↦₆₄ u24) ∗ Frame)
        hpc hrun hsp htrace hx25 hfit_816 ?_))
  intro sInit PInit basisPtr hoom1 halign1 hpcI hrunI hspI htrI hvregsI
    hx19I hx20I hx21I hx22I hx23I hx25I hx26I hx27I hx28I hx29I hentI
  refine SepWPp.weaken_pre hentI ?_
  clear hentI
  obtain ⟨_, hlen34, hall34⟩ := completePointsPolys34_spec
  have hne34 : extractCompletePolys COMPLETE_POINTS_POLYS_34 ≠ [] := by
    intro hnil; rw [hnil] at hlen34; contradiction
  have hro34 : completePointsPolys34PlacedAt =
      (((lsρ completePointsPolys34Sym) + BitVec.ofNat 64 (68 * 0)) ↦ᵣ
        polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_34)) := by
    unfold completePointsPolys34PlacedAt completePointsPolys34Bytes
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hmem34 : memRegion basisPtr 816 =
      memRegion (basisPtr + BitVec.ofNat 64 (24 * 0))
        (24 * (extractCompletePolys COMPLETE_POINTS_POLYS_34).length) := by
    rw [hlen34]; simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
  have hfit_loop34 :
      FitsEnv M lim (M.stepEvents (rustAllocEvents 816 8) st)
        (BasisN34LoopEnv (extractCompletePolys COMPLETE_POINTS_POLYS_34).length) := by
    rwa [hlen34]
  rw [hro34, hmem34]
  refine SepWPp.weaken_pre ?_
    (basis_n34_loop_placed_sepWPp hA s0 fsp basisPtr (lsρ completePointsPolys34Sym)
      hfsp_align halign1 _R
      (extractCompletePolys COMPLETE_POINTS_POLYS_34) 0 (M.stepEvents (rustAllocEvents 816 8) st)
      hne34 (by rw [Nat.zero_add]; exact hlen34) hall34 hfit_loop34
      sInit 0#64
      (A.live basisPtr 816 8 ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 96#64) ↦₆₄ 34#64) ∗
       ((fsp + 664#64) ↦₆₄ basisPtr) ∗ Frame)
      hpcI hrunI hspI htrI hx19I
      (by simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]; exact hx20I)
      (by simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]; exact hx21I)
      (by simp only [Nat.zero_add, BitVec.ofNat_eq_ofNat]; exact hx22I)
      (fun s1 hpc1 hrun1 hsp1 htr_s1 hvregs_1 hx23_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 => by
        have hfit_exit34 :
            FitsEnv M lim
              (M.stepEvents (basisN34LoopEvents (extractCompletePolys COMPLETE_POINTS_POLYS_34).length)
                (M.stepEvents (rustAllocEvents 816 8) st))
              (BasisLoopExitEnv 34) := by
          rwa [hlen34]
        refine SepWPp.weaken_pre ?_
          (basis_loop_exit_placed_sepWPp hA s0 s1 fsp basisPtr hfsp_align
            34 (by decide) (by decide) u24
            (((lsρ completePointsPolys34Sym + BitVec.ofNat 64 (68 * 0)) ↦ᵣ
                polysToBytes (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ∗
             polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0))
               (extractCompletePolys COMPLETE_POINTS_POLYS_34) ∗
             A.live basisPtr 816 8 ∗
             ((fsp + 96#64) ↦₆₄ 34#64) ∗
             ((fsp + 672#64) ↦₆₄ 34#64) ∗ Frame) _R
            hpc1 hrun1 hsp1 htr_s1
            (hx25_1.trans hx25I)
            hfit_exit34
            (fun s2 accPtr hacc hpc2 hrun2 hsp2 htr2 hvregs_2 hx0_2 hx20_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 => by
              have hbasis :
                  (A.live basisPtr 816 8 ∗
                   polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0))
                     (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ⊢
                  basisVecAt A.repAlloc basisPtr (extractCompletePolys COMPLETE_POINTS_POLYS_34) := by
                unfold basisVecAt
                rw [hlen34]
                simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMul]
                exact Entails.pure_right hoom1 (Entails.refl _)
              have hstep_total :
                  M.stepEvents (basisLoopExitEvents 34)
                    (M.stepEvents (basisN34LoopEvents (extractCompletePolys COMPLETE_POINTS_POLYS_34).length)
                      (M.stepEvents (rustAllocEvents 816 8) st)) =
                  M.stepEvents basisN34Events st := by
                rw [hlen34, ← M.stepEvents_append, ← M.stepEvents_append, ← List.append_assoc,
                    ← basisN34Events_split]
              refine SepWPp.weaken_pre ?_
                (hcont s2 basisPtr accPtr hoom1 hacc
                  hpc2 hrun2 hsp2 htr2
                  (hvregs_2.trans (hvregs_1.trans hvregsI))
                  hx0_2
                  (hx20_2.trans (hx23_1.trans hx23I))
                  hx24_2
                  (by simpa only [BitVec.ofNat_eq_ofNat] using hx25_2)
                  (hx26_2.trans (hx26_1.trans hx26I))
                  (hx27_2.trans (hx27_1.trans hx27I))
                  (hx28_2.trans (hx28_1.trans hx28I))
                  (hx29_2.trans (hx29_1.trans hx29I)))
              rw [hstep_total, ← hro34]
              dsimp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul]
              refine Entails.trans (Entails.of_eq (show _ =
                (A.live basisPtr 816 8 ∗
                 polyListOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * 0))
                   (extractCompletePolys COMPLETE_POINTS_POLYS_34)) ∗
                (A.pool lim (M.stepEvents basisN34Events st) s2 ∗
                 completePointsPolys34PlacedAt ∗
                 A.live accPtr 68 2 ∗ memRegion accPtr 68 ∗
                 ((fsp + 24#64) ↦₆₄ 34#64) ∗
                 ((fsp + 96#64) ↦₆₄ 34#64) ∗
                 ((fsp + 656#64) ↦₆₄ 34#64) ∗
                 ((fsp + 664#64) ↦₆₄ basisPtr) ∗
                 ((fsp + 672#64) ↦₆₄ 34#64) ∗
                 stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
              refine Entails.trans (sepConj_mono_left hbasis) ?_
              exact Entails.of_eq (by sep_ac_rfl)))
        exact Entails.of_eq (by sep_ac_rfl)))
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysConstLoopPlacedBudget
