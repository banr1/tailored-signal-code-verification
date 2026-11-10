/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.Proof
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
public meta import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed `Polys` Path

Relocatable `[LibsignalPlacement]` verification of the 16-iteration `EncoderState::Polys` path
threading `RustCliAllocBudget M`, `BudgetLimits`, `PolysLoopEnv`, and `NextChunkPolysEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl withMemEq)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSpqrV1 (Chunk GF16 NUM_POLYS Poly PolyEncoder)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkDataOff chunkIndexOff chunkSize encoderStateAt gf16SliceAt polyEncoderAt
   polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize polyEncoderPointsTag
   polyEncoderPolysTag polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize polyListOf polyOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ComputeAtArgs computeAtPure computeAtStack ofNat_beq_false_of_lt readReg32_setMem_pre
   readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost chunkPolysBytes chunkPolysBytes_length chunkPolysBytes_zero_succ
   localFrameRest lsr8_trunc8_of_trunc16 memRegion_split_two_bytes nextChunkCalleeStack
   nextChunkOnPanic nextChunk_polys_eq ofNat_sub_one_beq_zero ofNat_succ_add_neg1
   ofNat_succ_sub_one' ofNat_two_mul_add_one ofNat_two_mul_add_two pointsToBytes_append_two_bytes
   polyBufBody_eq_slice_rest polyBufRest polyCoefficients_len_bound_of_cap polyListOf_split_idx
   polyNextChunkStack polyOf_fold polyOf_unfold savedCells sepWP_exists_left_sep
   sepWPp_exists_left sepWPp_of_sepWP_lscl setWidth16_mov_w_zext16
   stackAt_nextChunkCallee_split_computeAt trunc8_of_trunc16 x21_add_24_eq x21_sub_8_add_8_eq
   x21_sub_8_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget coarseCostModel fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
  (ComputeAtEnv computeAtAllocEvents computeAtEvents computeAtPlacedSpec computeAtScratchCap
   fitsEnv_computeAt_iff)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
  (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced NextChunkPrologueEnv epilogue_placed_sepWP fitsEnv_nextChunkPrologue_iff
   nextChunkEpilogueEvents nextChunkPrologueEvents prologue_lscl_placed_sepWPp)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
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

attribute [local simp, local arm64_norm, local wp_norm]
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize
  x21_sub_8_eq x21_sub_8_add_8_eq x21_add_24_eq
  ofNat_two_mul_add_one ofNat_two_mul_add_two
  ofNat_succ_add_neg1 ofNat_succ_sub_one'
  setWidth16_mov_w_zext16

/-! ## 1. Exact Allocator Event Envelopes for `Polys` Loop & `EncoderState::Polys` Path -/

/-- Exact allocator event sequence across a list of polynomials evaluated by `<Poly>::compute_at`. -/
def polysLoopEvents : List CryptoVerification.LibsignalSpqrV1.Poly → List AllocEvent
  | [] => []
  | p :: ps => computeAtEvents p.coefficients.length ++ polysLoopEvents ps

@[simp] theorem polysLoopEvents_nil : polysLoopEvents [] = [] := rfl

@[simp] theorem polysLoopEvents_cons (p : CryptoVerification.LibsignalSpqrV1.Poly)
    (ps : List CryptoVerification.LibsignalSpqrV1.Poly) :
    polysLoopEvents (p :: ps) = computeAtEvents p.coefficients.length ++ polysLoopEvents ps := rfl

theorem polysLoopEvents_drop_eq_cons {polys : List CryptoVerification.LibsignalSpqrV1.Poly}
    {i : Nat} (hi : i < polys.length) :
    polysLoopEvents (polys.drop i) =
      computeAtEvents (polys[i]'hi).coefficients.length ++ polysLoopEvents (polys.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem polysLoopEvents_drop_of_ge {polys : List CryptoVerification.LibsignalSpqrV1.Poly}
    {i : Nat} (hi : polys.length ≤ i) :
    polysLoopEvents (polys.drop i) = [] := by
  rw [List.drop_eq_nil_of_le hi]
  rfl

def PolysLoopEnv (polys : List CryptoVerification.LibsignalSpqrV1.Poly)
    (evs : List AllocEvent) : Prop :=
  evs = polysLoopEvents polys

theorem fitsEnv_polysLoop_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (polys : List CryptoVerification.LibsignalSpqrV1.Poly) :
    FitsEnv M lim st (PolysLoopEnv polys) ↔ FitsEvents M lim st (polysLoopEvents polys) := by
  constructor
  · intro h
    exact h (polysLoopEvents polys) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

/-- Full exact allocator event sequence of `<PolyEncoder as Encoder>::next_chunk` on the
    `EncoderState::Polys` path (`+0..+92 -> +136..+220 -> +4484`):
    prologue `32`-byte output buffer allocation, 16 `<Poly>::compute_at` evaluations, and
    epilogue `32`-byte output buffer deallocation. -/
def nextChunkPolysEvents (polys : List CryptoVerification.LibsignalSpqrV1.Poly) : List AllocEvent :=
  nextChunkPrologueEvents ++ polysLoopEvents polys ++ nextChunkEpilogueEvents

def NextChunkPolysEnv (polys : List CryptoVerification.LibsignalSpqrV1.Poly)
    (evs : List AllocEvent) : Prop :=
  evs = nextChunkPolysEvents polys

theorem fitsEnv_nextChunkPolys_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (polys : List CryptoVerification.LibsignalSpqrV1.Poly) :
    FitsEnv M lim st (NextChunkPolysEnv polys) ↔ FitsEvents M lim st (nextChunkPolysEvents polys) := by
  constructor
  · intro h
    exact h (nextChunkPolysEvents polys) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 512 * 1024 * 1024 }
      coarseCostModel.init
      (NextChunkPolysEnv (List.replicate 16 { coefficients := [GF16.ONE, GF16.ONE] })) := by
  rw [fitsEnv_nextChunkPolys_iff]
  dsimp only [nextChunkPolysEvents, nextChunkPrologueEvents, nextChunkEpilogueEvents,
    polysLoopEvents, List.replicate, computeAtEvents, computeAtAllocEvents, computeAtScratchCap,
    List.length_cons, List.length_nil, rustAllocEvents, rustDeallocEvents,
    List.cons_append, List.nil_append, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  repeat refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  trivial

/-! ## 2. Budget-Threaded `compute_at` Call Combinator -/

private theorem call_noPanic_to_sepWPp_lscl [LibsignalPlacement]
    {α : Type} {prog : Program} {entry ret_pc ret : BitVec 64}
    {s : State} {spec : Spec α} {x : α} {φ : Prop} {T F P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withMemEq s.mem spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan : ∀ sf R', sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → False)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R' hm hL
  have hpre : s.mem ⊨ (withMemEq s.mem spec).pre x s ∗ (F ∗ R') := by
    dsimp only [withMemEq]
    rw [hspec, show ((⌜φ⌝ ∗ T) ∗ ⌜s.mem = s.mem⌝) ∗ (F ∗ R') =
      ⌜φ ∧ s.mem = s.mem⌝ ∗ ((T ∗ F) ∗ R') by rw [← pure_sepConj_pure]; sep_ac_rfl,
      ← hP, satisfies_pure_sepConj]
    exact ⟨⟨hφ, rfl⟩, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R') s hpc hrun hpre hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan_st, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hclm := hcl.of_keepsFrozen hsteps.keepsFrozen
    obtain ⟨sf, hsteps', hout'⟩ :=
      (hnext sm hclm hpcm hrunm hspm hcsm) R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpan sm (F ∗ R') hpan_st hpost).elim
  · exact (hexit sm code (F ∗ R') hex hpost).elim
  · exact (hoom sm R' hoom_st hpost).elim

theorem computeAt_pre_split_placed_budget [LibsignalPlacement] (p_coeffs : BitVec 64)
    (poly : CryptoVerification.LibsignalSpqrV1.Poly) (fsp : BitVec 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (P_cap P_ptr P_len P_restBuf P_out P_rem P_live P_outA P_tag P_take P_drop
     P_idx P_pad P_56 P_232 P_240 P_248 P_lfr P_saved : SepProp) :
    A.pool lim st s ∗
      P_cap ∗ P_ptr ∗ P_len ∗ gf16SliceAt p_coeffs poly.coefficients ∗ P_restBuf ∗
      P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
      P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      memRegion (fsp - 17232#64) 12880 ∗ stackAt fsp computeAtStack =
    (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt fsp computeAtStack) ∗
    (P_cap ∗ P_ptr ∗ P_len ∗ P_restBuf ∗
      P_out ∗ P_rem ∗ P_live ∗ P_outA ∗ P_tag ∗ P_take ∗ P_drop ∗
      P_idx ∗ P_pad ∗ P_56 ∗ P_232 ∗ P_240 ∗ P_248 ∗ P_lfr ∗ P_saved ∗
      memRegion (fsp - 17232#64) 12880) := by
  sep_ac_rfl

theorem call_computeAt_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret_pc ret fsp : BitVec 64}
    {s0 s : State} {p_coeffs : BitVec 64}
    {poly : CryptoVerification.LibsignalSpqrV1.Poly} {x_gf : GF16}
    {F P : SepProp} {Q Q_panic : State → SepProp → Prop}
    (hcall : subroutine_ok ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (lsmpl.base 371) (withMemEq s.mem (computeAtPlacedSpec M A lim)))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 371)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = fsp)
    (hfsp_al : fsp &&& 0xf#64 = 0#64)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = p_coeffs)
    (hx1 : s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length)
    (hx2 : (s.readReg64 Reg.x2).truncate 16 = x_gf.value)
    (hlen : 2 * poly.coefficients.length + 2 ≤ 2 ^ 63)
    (hfit_alloc : FitsEvents M lim st (computeAtAllocEvents poly.coefficients.length))
    (hP : P = (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s ∗ stackAt fsp computeAtStack) ∗ F)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = fsp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.trace = s0.trace →
      (sf.readReg64 Reg.x0).truncate 16 = (computeAtPure poly x_gf).value →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret sf
        ((gf16SliceAt p_coeffs poly.coefficients ∗
          tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
          A.pool lim (M.stepEvents (computeAtEvents poly.coefficients.length) st) sf ∗
          stackAt fsp computeAtStack) ∗ F) Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s P Q Q_panic := by
  have hsp_al : s.spAligned = true := by
    simp [State.spAligned, hsp_eq, hfsp_al]
  refine call_noPanic_to_sepWPp_lscl hcl hcall hpc hrun hsp_al hlr
    (x := ({ p_coeffs := p_coeffs, poly := poly, x := x_gf }, st))
    (φ := s.readReg64 Reg.x0 = p_coeffs ∧
      s.readReg64 Reg.x1 = BitVec.ofNat 64 poly.coefficients.length ∧
      (s.readReg64 Reg.x2).truncate 16 = x_gf.value ∧
      2 * poly.coefficients.length + 2 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (computeAtAllocEvents poly.coefficients.length))
    (T := gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ A.pool lim st s ∗ stackAt fsp computeAtStack)
    (by simp only [computeAtPlacedSpec, hsp_eq])
    ⟨hx0, hx1, hx2, hlen, hfit_alloc⟩
    hP
    (fun _ _ _ hm => by simp [computeAtPlacedSpec, satisfies_pure_sepConj] at hm)
    (fun _ _ _ _ hm => by simp [computeAtPlacedSpec, satisfies_pure_sepConj] at hm)
    (fun _ _ _ hm => by simp [computeAtPlacedSpec, satisfies_pure_sepConj] at hm)
    (fun sf hclf hpcf hrunf hspf hcsf => ?_)
  have hspf' : sf.sp = fsp := hspf.trans hsp_eq
  conv => arg 4; simp only [computeAtPlacedSpec, hsp_eq, sepConj_assoc]
  apply SepWPp.pure_left
  rintro ⟨htrf, hx0f⟩
  refine SepWPp.weaken_pre (Entails.of_eq ?_)
    (hnext sf hpcf hrunf hspf' hcsf hclf (htrf.trans htr) hx0f)
  sep_ac_rfl

/-! ## 3. Single Iteration of the `Polys` Loop (`+136..+216 -> +108..+132`) -/

set_option maxHeartbeats 800000 in
theorem polysLoop_step_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List CryptoVerification.LibsignalSpqrV1.Poly)
    (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (_R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (i rem : Nat) (hrem_eq : i + (rem + 1) = 16)
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_416).base + 136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24))
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1))
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hfit_drop : FitsEvents M lim st (polysLoopEvents (polys.drop i)))
    (hnext : ∀ sf : State,
      sf.pc = (if rem == 0 then
          (blkPl_416).base + 4484#64
        else
          (blkPl_416).base + 136#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * (i + 1) + 24) →
      sf.readReg64 .x22 = BitVec.ofNat 64 rem →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      FitsEvents M lim
        (M.stepEvents (computeAtEvents (polys[i]'(by omega)).coefficients.length) st)
        (polysLoopEvents (polys.drop (i + 1))) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A.repAlloc (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim
           (M.stepEvents (computeAtEvents (polys[i]'(by omega)).coefficients.length) st) sf ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A.repAlloc (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFrameRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q Q_panic := by
  have hi16 : i < 16 := by omega
  have hi_len : i < polys.length := by omega
  rw [polysLoopEvents_drop_eq_cons hi_len, fitsEvents_append] at hfit_drop
  rcases hfit_drop with ⟨hfit_cur, hfit_rest⟩
  have hfit_alloc : FitsEvents M lim st (computeAtAllocEvents (polys[i]'hi_len).coefficients.length) := by
    unfold computeAtEvents at hfit_cur
    exact ((fitsEvents_append M lim _ _ st).mp hfit_cur).1
  rw [polyListOf_split_idx A.repAlloc (x.encA + 8#64) polys i hi_len]
  apply SepWPp.fold
    (polyOf_unfold A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull :
      ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
        (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest =
          ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [polyBufBody_eq_slice_rest A.repAlloc cap ptr (polys[i]'hi_len) hlen_cap]
  have hlen_bound : 2 * (polys[i]'hi_len).coefficients.length + 2 ≤ 2 ^ 63 :=
    polyCoefficients_len_bound_of_cap hlen_cap hcap_bound
  refine sepWPp_of_sepWP_lscl (mid := lsmpl.base 371) hcl ?_
  apply sepWP_seg_416 (mid := lsmpl.base 371)
  intro _m_strip1
  wp_steps 3
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl_call
  have hcomp := hA.computeAt_blk_ok hcl_call
  clear hA
  rw [stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
  have hsp_al : s0.sp - 1200#64 &&& 15#64 = 0#64 := by revert hsp0; bv_bits
  refine call_computeAt_placed_sepWPp (s0 := s0) hcomp hcl_call
    (ret_pc := (blkPl_416).base + 148#64)
    (x_gf := GF16.new (x.enc.idx.setWidth 16))
    ?_ ?_ ?_ hsp_al ?_ ?_ ?_ ?_ ?_ hlen_bound hfit_alloc
    (computeAt_pre_split_placed_budget ptr (polys[i]'hi_len) (s0.sp - 1200#64) A lim st _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    ?_
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using htr
  · wp_norm_lhs
  · wp_norm_lhs
  · simp [GF16.new, arm64_norm, wp_norm, hx27]
  intro sf1 hpc1 hrun1 hsp1' hcs1 hcl1 htr1' hx0_1
  rcases hcs1 with ⟨_, _, hx21_cs, hx22_cs, _, hx24_cs, _, _, hx27_cs, _, _, hvregs_cs⟩
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by
    rw [hvregs_cs]; simpa [arm64_norm, wp_norm] using hvregs
  have hx21_1 : sf1.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) := by
    rw [Reg.x21, hx21_cs]; simpa [arm64_norm, wp_norm] using hx21
  have hx22_1 : sf1.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) := by
    rw [Reg.x22, hx22_cs]; simpa [arm64_norm, wp_norm] using hx22
  have hx24_1 : sf1.readReg64 .x24 = x.encA := by
    rw [Reg.x24, hx24_cs]; simpa [arm64_norm, wp_norm] using hx24
  have hx27_1 : sf1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 := by
    rw [Reg.x27, hx27_cs]; simpa [arm64_norm, wp_norm] using hx27
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_sub_one_beq_zero (rem := rem) (by omega) with ⟨hsubs_z1, hsubs_z2⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  refine sepWPp_of_sepWP_lscl
    (mid := if rem == 0 then (blkPl_416).base + 4484#64 else (blkPl_416).base + 136#64) hcl1 ?_
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  apply sepWP_seg_416
    (mid := if rem == 0 then (blkPl_416).base + 4484#64 else (blkPl_416).base + 136#64)
  intro _m_strip2
  wp_steps 20
  refine SepWP.done
    (by cases hrem0 : (rem == 0) <;>
        simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
          hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
    (by cases hrem0 : (rem == 0) <;>
        simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
          hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
    fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  have hb0_eq :
      BitVec.truncate 8 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)) >>> 8) =
        BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8) := by
    rw [← lsr8_trunc8_of_trunc16 hx0_1]
    bv_bits
  have hb1_eq :
      BitVec.zeroExtend 8 (sf1.readReg64 (Reg.gpr 0#5)) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_of_trunc16 hx0_1
  wp_conv_pre =>
    rw [hb0_eq, hb1_eq]
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value) ⊢
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 (i + 1)) := by
    rw [chunkPolysBytes_zero_succ (x.enc.idx.setWidth 16) polys i hi_len]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) i
      (chunkPolysBytes_length (x.enc.idx.setWidth 16) polys 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_poly :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (polys[i]'hi_len).coefficients.length) ∗
        gf16SliceAt ptr (polys[i]'hi_len).coefficients ∗
        polyBufRest A.repAlloc cap ptr (polys[i]'hi_len) ⊢
        polyOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) :=
    polyOf_fold A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (polys[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_poly (by sep_focus)
  have hfold_list :
      polyListOf A.repAlloc (x.encA + 8#64) (polys.take i) ∗
        polyOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) ∗
        polyListOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1)) ⊢
        polyListOf A.repAlloc (x.encA + 8#64) polys := by
    rw [← polyListOf_split_idx A.repAlloc (x.encA + 8#64) polys i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  have hfold_stk :
      memRegion (s0.sp - 18432#64) 12880 ∗
        stackAt (s0.sp - 1200#64) computeAtStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    have hsub : s0.sp - 18432#64 = (s0.sp - 1200#64) - 17232#64 := by bv_omega
    rw [hsub, ← stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
    exact Entails.refl _
  apply SepWP.fold hfold_stk (by sep_focus)
  refine SepWP.done
    (by cases hrem0 : (rem == 0) <;>
        simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
          hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
    (by cases hrem0 : (rem == 0) <;>
        simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
          hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte]) ?_
  intro hcl_end
  refine SepWPp.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
    (hnext _
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hrun1, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, htr1', hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hvregs_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      hcl_end
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hx21_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hx24_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      (by cases hrem0 : (rem == 0) <;>
          simp only [arm64_norm, wp_norm, hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub,
            hsubs_z1, hsubs_z2, hsp1', hx22_1, hx27_1, hrem0, Bool.false_eq_true, ↓reduceIte])
      hfit_rest)

/-! ## 4. Full 16-Iteration `Polys` Loop and `EncoderState::Polys` Path -/

theorem polysLoop_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List CryptoVerification.LibsignalSpqrV1.Poly)
    (hlen_polys : polys.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64) :
    ∀ (rem i : Nat) (_hrem_eq : i + (rem + 1) = 16) (st : M.σ) (s : State),
      LibsignalCodeLoaded lsmpl s.mem →
      s.pc = (blkPl_416).base + 136#64 →
      s.status = .Running →
      s.sp = s0.sp - 1200#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x21 = x.encA + BitVec.ofNat 64 (24 * i + 24) →
      s.readReg64 .x22 = BitVec.ofNat 64 (rem + 1) →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      FitsEvents M lim st (polysLoopEvents (polys.drop i)) →
      (∀ sf : State,
        sf.pc = (blkPl_416).base + 4484#64 →
        sf.status = .Running →
        sf.sp = s0.sp - 1200#64 →
        sf.trace = s0.trace →
        calleeSavedVRegs sf = calleeSavedVRegs s0 →
        LibsignalCodeLoaded lsmpl sf.mem →
        sf.readReg64 .x20 = 32#64 →
        sf.readReg64 .x24 = x.encA →
        sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
        SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
          ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16) ∗
           A.live out_ptr 32 1 ∗
           memRegion x.outA chunkSize ∗
           (x.encA ↦₆₄ polyEncoderPolysTag) ∗
           polyListOf A.repAlloc (x.encA + 8#64) polys ∗
           ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
           memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
           (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
           (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
           (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
           (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
           localFrameRest (s0.sp - 1200#64) ∗
           savedCells s0 ∗
           tokenInitPlacedAt ∗
           reduceTablePlacedAt ∗
           A.pool lim (M.stepEvents (polysLoopEvents (polys.drop i)) st) sf ∗
           stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
          Q Q_panic) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
        ((out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 i) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A.repAlloc (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
         localFrameRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim st s ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic
  | 0, i, hrem_eq, st, s, hcl, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hfit, hdone => by
    have hi15 : i = 15 := by omega
    subst hi15
    have hi_len : 15 < polys.length := by omega
    refine polysLoop_step_placed_sepWPp M A lim st ext hA x polys hlen_polys out_ptr R 15 0 hrem_eq
      s0 s hcl hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 hfit ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f hx20_f _hx21_f _hx22_f hx24_f hx27_f _hfit_rest
    simp only [beq_self_eq_true, ite_true] at hpc_f
    change sf.readReg64 .x20 = 32#64 at hx20_f
    have hdrop15 :
        polysLoopEvents (polys.drop 15) = computeAtEvents (polys[15]'hi_len).coefficients.length := by
      rw [polysLoopEvents_drop_eq_cons hi_len, polysLoopEvents_drop_of_ge (by omega),
        List.append_nil]
    refine SepWPp.weaken_pre ?_
      (hdone sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f hx20_f hx24_f hx27_f)
    rw [hdrop15, show 32 - 2 * (15 + 1) = 0 from rfl, memRegion_zero,
        show BitVec.ofNat 64 (2 * (15 + 1)) = 32#64 from rfl]
    exact Entails.of_eq (by sep_ac_rfl)
  | r + 1, i, hrem_eq, st, s, hcl, hpc, hrun, hsp, htr, hvregs, hx21, hx22, hx24, hx27, hfit, hdone => by
    have hi_len : i < polys.length := by omega
    refine polysLoop_step_placed_sepWPp M A lim st ext hA x polys hlen_polys out_ptr R i (r + 1) hrem_eq
      s0 s hcl hsp0 hpc hrun hsp htr hvregs hx21 hx22 hx24 hx27 hfit ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hcl_f _hx20_f hx21_f hx22_f hx24_f hx27_f hfit_rest
    have hne0 : (r + 1 == 0) = false := rfl
    simp only [hne0, Bool.false_eq_true, ite_false] at hpc_f
    refine polysLoop_placed_sepWPp M A lim ext hA x polys hlen_polys out_ptr R s0 hsp0
      r (i + 1) (by omega)
      (M.stepEvents (computeAtEvents (polys[i]'hi_len).coefficients.length) st)
      sf hcl_f hpc_f hrun_f hsp_f htr_f hvregs_f hx21_f hx22_f hx24_f hx27_f hfit_rest ?_
    intro sf2 hpc2 hrun2 hsp2 htr2 hvregs2 hcl2 hx20_2 hx24_2 hx27_2
    have hstep_eq :
        M.stepEvents (polysLoopEvents (polys.drop (i + 1)))
          (M.stepEvents (computeAtEvents (polys[i]'hi_len).coefficients.length) st) =
          M.stepEvents (polysLoopEvents (polys.drop i)) st := by
      rw [polysLoopEvents_drop_eq_cons hi_len, M.stepEvents_append]
    rw [hstep_eq]
    exact hdone sf2 hpc2 hrun2 hsp2 htr2 hvregs2 hcl2 hx20_2 hx24_2 hx27_2

set_option maxHeartbeats 800000 in
theorem nextChunk_polys_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List CryptoVerification.LibsignalSpqrV1.Poly)
    (hs_polys : x.enc.s = .polys polys)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp) (s0 : State)
    (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st (NextChunkPolysEnv polys)) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s0
      (memRegion x.outA chunkSize ∗
       polyEncoderAt A.repAlloc x.encA x.enc ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s0 ∗
       stackAt s0.sp polyNextChunkStack)
      (fun sf1 P_f =>
        ((sf1.mem ⊨ P_f ∗ R) →
          (sf1.mem ⊨
            ⌜sf1.trace = s0.trace⌝ ∗
             chunkAt x.outA x.chunk ∗
             polyEncoderAt A.repAlloc x.encA x.enc' ∗
             tokenInitPlacedAt ∗
             reduceTablePlacedAt ∗
             A.pool lim (M.stepEvents (nextChunkPolysEvents polys) st) sf1 ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) := by
  have hfit_ev : FitsEvents M lim st (nextChunkPolysEvents polys) :=
    (fitsEnv_nextChunkPolys_iff polys).mp hfit
  unfold nextChunkPolysEvents at hfit_ev
  rw [List.append_assoc, fitsEvents_append] at hfit_ev
  rcases hfit_ev with ⟨hfit_pro, hfit_rest⟩
  rw [fitsEvents_append] at hfit_rest
  rcases hfit_rest with ⟨hfit_loop, _hfit_epi⟩
  have hfit_pro_env : FitsEnv M lim st NextChunkPrologueEnv :=
    fitsEnv_nextChunkPrologue_iff.mpr hfit_pro
  unfold polyEncoderAt encoderStateAt
  rw [hs_polys]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; intro hlen_polys
  have hlen16 : polys.length = 16 := hlen_polys
  have henc_eq : x.enc = { idx := x.enc.idx, s := .polys polys } := by
    cases h : x.enc; simp_all
  have hnc := nextChunk_polys_eq (idx := x.enc.idx) hlen16
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .polys polys := by
    rw [← henc'_eq]
  refine prologue_lscl_placed_sepWPp M A lim st ext hA x polyEncoderPolysTag
    (polyListOf A.repAlloc (x.encA + polyEncoderVecsOff) polys) R s0 hcl0 hpc hrun hsp0 hx0 hx8
    hfit_pro_env ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hcl1 hx9_1 _hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 1#64 at hx9_1
  refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 136#64) hcl1 ?_
  apply sepWP_seg_416 (mid := (blkPl_416).base + 136#64)
  intro _m_strip0
  wp_steps 4
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
  intro hcl2
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPolysBytes (x.enc.idx.setWidth 16) polys 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPolysBytes, pointsToBytes_nil, emp_sepConj]
  refine SepWPp.weaken_pre ?_
    (polysLoop_placed_sepWPp M A lim ext hA x polys hlen16 out_ptr R s0 hsp0 15 0 rfl
      (M.stepEvents nextChunkPrologueEvents st) _ hcl2
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by simpa [List.drop_zero] using hfit_loop) ?_)
  · apply Entails.of_eq
    rw [hinit_buf]
    dsimp only [nextChunkPrologueEvents]
    simp only [arm64_norm]
    sep_ac_rfl
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · simp [arm64_norm, wp_norm, hx24_1]
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _hcl_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPolysTag) ∗ polyListOf A.repAlloc (x.encA + 8#64) polys ⊢
        encoderStateAt A.repAlloc x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (polys.length = NUM_POLYS) = True := propext ⟨fun _ => trivial, fun _ => hlen_polys⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq, List.drop_zero]
  have hstep_final :
      M.stepEvents (rustDeallocEvents 32 1)
        (M.stepEvents (polysLoopEvents polys) (M.stepEvents nextChunkPrologueEvents st)) =
        M.stepEvents (nextChunkPolysEvents polys) st := by
    unfold nextChunkPolysEvents nextChunkEpilogueEvents
    rw [M.stepEvents_append, M.stepEvents_append]
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by simp only [arm64_norm]; sep_ac_rfl))
      (epilogue_placed_sepWP M A lim
        (M.stepEvents (polysLoopEvents polys) (M.stepEvents nextChunkPrologueEvents st))
        ext hA x R s0 sf out_ptr hout_ne hidx_chunk hidx_enc'
        hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f))
    (fun sf1 P_f _ _ ⟨hm1, hsp_sf1, hcs_sf1⟩ => ⟨fun hm => ?_, hsp_sf1, hcs_sf1⟩)
  · rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
    rfl
  · rw [← hstep_final]
    exact hm1 hm

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget
