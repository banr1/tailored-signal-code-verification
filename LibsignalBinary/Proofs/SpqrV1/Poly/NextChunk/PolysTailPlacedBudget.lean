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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFast
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTail
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Polynomial Tail Loop

Relocatable `[LibsignalPlacement]` verification of the polynomial evaluation tail loop
(`+296 -> +4484`) threading `RustCliAllocBudget M`, `BudgetLimits`, and `PolysLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkDataOff chunkIndexOff chunkSize gf16SliceAt polyEncoderIdxOff polyEncoderPadOff
   polyEncoderPadSize polyEncoderPointsTag polyEncoderPolysTag polyEncoderTagOff
   polyEncoderVecsOff polyEncoderVecsSize polyListOf polyOf)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (computeAtPure computeAtStack ofNat_beq_false_of_lt readReg32_setMem_pre
   readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost chunkPolysBytes chunkPolysBytes_add chunkPolysBytes_length
   localFramePointsRest madd_24_eq madd_24_eq' memRegion_split_two_bytes nextChunkCalleeStack
   nextChunkOnPanic ofNat_add_one_beq_16 ofNat_add_one_eq ofNat_two_mul_add_one
   ofNat_two_mul_add_two pointsToBytes_append_two_bytes polyBufBody_eq_slice_rest polyBufRest
   polyCoefficients_len_bound_of_cap polyListOf_split_idx polyOf_fold polyOf_unfold savedCells
   sepWP_exists_left_sep sepWPp_exists_left sepWPp_of_sepWP_lscl
   stackAt_nextChunkCallee_split_computeAt trunc8_of_trunc16 trunc8_zext64_trunc32_of_trunc16
   ubfx8_trunc8_of_trunc16)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget coarseCostModel fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.ComputeAt.DefsBudget
  (computeAtAllocEvents computeAtEvents computeAtScratchCap)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
  (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoopPlacedBudget
  (PolysLoopEnv call_computeAt_placed_sepWPp fitsEnv_polysLoop_iff polysLoopEvents
   polysLoopEvents_drop_eq_cons polysLoopEvents_drop_of_ge)

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
  madd_24_eq madd_24_eq' ofNat_add_one_eq
  ofNat_two_mul_add_one ofNat_two_mul_add_two

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 512 * 1024 * 1024 }
      coarseCostModel.init
      (PolysLoopEnv (List.replicate 16 { coefficients := [GF16.ONE, GF16.ONE] })) := by
  rw [fitsEnv_polysLoop_iff]
  dsimp only [polysLoopEvents, List.replicate, computeAtEvents, computeAtAllocEvents,
    computeAtScratchCap, List.length_cons, List.length_nil, rustAllocEvents, rustDeallocEvents,
    List.cons_append, List.nil_append, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  repeat refine ⟨⟨by decide, by decide, by decide, by decide⟩, ?_⟩
  trivial

/-! ## 1. Placed Budget Precondition Split Helper for `computeAt` in the Tail Loop -/

theorem computeAt_tail_pre_split_placed_budget [LibsignalPlacement] (p_coeffs : BitVec 64)
    (poly : Poly) (fsp : BitVec 64)
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 : SepProp) :
    A.pool lim st s ∗
      F1 ∗ F2 ∗ F3 ∗ gf16SliceAt p_coeffs poly.coefficients ∗ F4 ∗
      F5 ∗ F6 ∗ F7 ∗ F8 ∗ F9 ∗ F10 ∗ F11 ∗ F12 ∗ F13 ∗ F14 ∗ F15 ∗ F16 ∗ F17 ∗ F18 ∗ F19 ∗ F20 ∗ F21 ∗ F22 ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      F23 ∗ stackAt fsp computeAtStack =
    (gf16SliceAt p_coeffs poly.coefficients ∗
      tokenInitPlacedAt ∗
      reduceTablePlacedAt ∗
      A.pool lim st s ∗
      stackAt fsp computeAtStack) ∗
    (F1 ∗ F2 ∗ F3 ∗ F4 ∗ F5 ∗ F6 ∗ F7 ∗ F8 ∗ F9 ∗ F10 ∗
      F11 ∗ F12 ∗ F13 ∗ F14 ∗ F15 ∗ F16 ∗ F17 ∗ F18 ∗ F19 ∗ F20 ∗ F21 ∗ F22 ∗ F23) := by
  sep_ac_rfl

/-! ## 2. Single Step of the Polynomial Evaluation Tail Loop (`+296` -> `+296` / `+4484`) -/

set_option maxHeartbeats 800000 in
theorem polysTailLoop_step_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List Poly) (hlen_polys : polys.length = 16)
    (out_ptr u48 : BitVec 64) (prefix_bytes : List (BitVec 8)) (_R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (i rem : Nat) (hrem_eq : i + (rem + 1) = 16) (hprefix : prefix_bytes.length = 2 * i)
    (s0 s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_416).base + 296#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hfit_drop : FitsEvents M lim st (polysLoopEvents (polys.drop i)))
    (hnext : ∀ sf : State,
      sf.pc = (if rem == 0 then
          (blkPl_416).base + 4484#64
        else
          (blkPl_416).base + 296#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      LibsignalCodeLoaded lsmpl sf.mem →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      FitsEvents M lim
        (M.stepEvents (computeAtEvents (polys[i]'(by omega)).coefficients.length) st)
        (polysLoopEvents (polys.drop (i + 1))) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) sf
        ((out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1)) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A.repAlloc (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
         (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 (if rem == 0 then i else i + 1)) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
         localFramePointsRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim
           (M.stepEvents (computeAtEvents (polys[i]'(by omega)).coefficients.length) st) sf ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ prefix_bytes) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A.repAlloc (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗
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
  wp_steps 4
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
    (ret_pc := (blkPl_416).base + 312#64)
    (x_gf := GF16.new (x.enc.idx.setWidth 16))
    ?_ ?_ ?_ hsp_al ?_ ?_ ?_ ?_ ?_ hlen_bound hfit_alloc
    (computeAt_tail_pre_split_placed_budget ptr (polys[i]'hi_len) (s0.sp - 1200#64) A lim st _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
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
  rcases hcs1 with ⟨_, _, _, _, _, hx24_cs, _, _, hx27_cs, hx28_cs, _, hvregs_cs⟩
  have hvregs_1 : calleeSavedVRegs sf1 = calleeSavedVRegs s0 := by
    rw [hvregs_cs]; simpa [arm64_norm, wp_norm] using hvregs
  have hx24_1 : sf1.readReg64 .x24 = x.encA := by
    rw [Reg.x24, hx24_cs]; simpa [arm64_norm, wp_norm] using hx24
  have hx27_1 : sf1.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 := by
    rw [Reg.x27, hx27_cs]; simpa [arm64_norm, wp_norm] using hx27
  have hx28_1 : sf1.readReg64 .x28 = 24#64 := by
    rw [Reg.x28, hx28_cs]; simpa [arm64_norm, wp_norm] using hx28
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨h16_eq, h16_sub⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  have hb0_eq :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5))) >>> 8 &&& 255#64) =
        BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8) :=
    ubfx8_trunc8_of_trunc16 hx0_1
  have hb1_eq :
      BitVec.zeroExtend 8 (sf1.readReg64 (Reg.gpr 0#5)) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_of_trunc16 hx0_1
  have hb1_eq' :
      BitVec.zeroExtend 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 (sf1.readReg64 (Reg.gpr 0#5)))) =
        BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value :=
    trunc8_zext64_trunc32_of_trunc16 hx0_1
  have hfold_bytes :
      (out_ptr ↦ₛ prefix_bytes) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value) ⊢
        (out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1)) := by
    have h1 : chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1 =
        [BitVec.setWidth 8 ((computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value >>> 8),
         BitVec.setWidth 8 (computeAtPure (polys[i]'hi_len) (GF16.new (x.enc.idx.setWidth 16))).value] := by
      have hp : polys[i]? = some (polys[i]'hi_len) := List.getElem?_eq_getElem hi_len
      simp [chunkPolysBytes, hp]
    rw [h1]
    exact pointsToBytes_append_two_bytes out_ptr prefix_bytes i hprefix _ _
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
  have hfold_list :
      polyListOf A.repAlloc (x.encA + 8#64) (polys.take i) ∗
        polyOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (polys[i]'hi_len) ∗
        polyListOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (polys.drop (i + 1)) ⊢
        polyListOf A.repAlloc (x.encA + 8#64) polys := by
    rw [← polyListOf_split_idx A.repAlloc (x.encA + 8#64) polys i hi_len]
    exact Entails.refl _
  have hfold_stk :
      memRegion (s0.sp - 18432#64) 12880 ∗
        stackAt (s0.sp - 1200#64) computeAtStack ⊢
        stackAt (s0.sp - 1200#64) nextChunkCalleeStack := by
    have hsub : s0.sp - 18432#64 = (s0.sp - 1200#64) - 17232#64 := by bv_omega
    rw [hsub, ← stackAt_nextChunkCallee_split_computeAt (s0.sp - 1200#64)]
    exact Entails.refl _
  by_cases hrem0 : rem = 0
  · have hi15 : i = 15 := by omega
    subst hi15; subst hrem0
    refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 4484#64) hcl1 ?_
    apply SepWP.fold (memRegion_split_two_bytes out_ptr 15 hi16) (by sep_focus)
    apply sepWP_exists_left_sep; intro b0
    apply sepWP_exists_left_sep; intro b1
    apply sepWP_seg_416 (mid := (blkPl_416).base + 4484#64)
    intro _m_strip2
    wp_steps 22
    wp_steps 1
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    wp_conv_pre => simp only [hb0_eq, hb1_eq, hb1_eq']
    apply SepWP.fold hfold_bytes (by sep_focus)
    apply SepWP.fold hfold_poly (by sep_focus)
    apply SepWP.fold hfold_list (by sep_focus)
    apply SepWP.fold hfold_stk (by sep_focus)
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    intro hcl2
    refine SepWPp.weaken_pre
      (Entails.of_eq (by simp only [arm64_norm, beq_self_eq_true, ↓reduceIte]; sep_ac_rfl))
      (hnext _ ?_ ?_ ?_ ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ hfit_rest)
    · simp only [beq_self_eq_true, ↓reduceIte]; wp_norm_goal
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp1'
    · simpa [arm64_norm, wp_norm] using htr1'
    · simpa [arm64_norm, wp_norm] using hvregs_1
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx24_1
    · simpa [arm64_norm, wp_norm] using hx27_1
    · simpa [arm64_norm, wp_norm] using hx28_1
  · have hi15 : i ≠ 15 := by omega
    have hi15_beq : (i == 15) = false := beq_eq_false_iff_ne.mpr hi15
    have hrem0_beq : (rem == 0) = false := beq_eq_false_iff_ne.mpr hrem0
    rw [hi15_beq] at h16_eq h16_sub
    refine sepWPp_of_sepWP_lscl (mid := (blkPl_416).base + 296#64) hcl1 ?_
    apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
    apply sepWP_exists_left_sep; intro b0
    apply sepWP_exists_left_sep; intro b1
    apply sepWP_seg_416 (mid := (blkPl_416).base + 296#64)
    intro _m_strip2
    wp_steps 22
    wp_steps 3
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real2 _hnsp2 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp2.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    wp_conv_pre => simp only [hb0_eq, hb1_eq, hb1_eq']
    apply SepWP.fold hfold_bytes (by sep_focus)
    apply SepWP.fold hfold_poly (by sep_focus)
    apply SepWP.fold hfold_list (by sep_focus)
    apply SepWP.fold hfold_stk (by sep_focus)
    refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
    intro hcl2
    refine SepWPp.weaken_pre
      (Entails.of_eq (by rw [hrem0_beq]; simp only [arm64_norm, Bool.false_eq_true, ↓reduceIte]; sep_ac_rfl))
      (hnext _ ?_ ?_ ?_ ?_ ?_ hcl2 ?_ ?_ ?_ ?_ ?_ ?_ hfit_rest)
    · rw [hrem0_beq]; simp only [Bool.false_eq_true, ↓reduceIte]; wp_norm_goal
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hsp1'
    · simpa [arm64_norm, wp_norm] using htr1'
    · simpa [arm64_norm, wp_norm] using hvregs_1
    · wp_norm_lhs
    · wp_norm_lhs
    · wp_norm_lhs
    · simpa [arm64_norm, wp_norm] using hx24_1
    · simpa [arm64_norm, wp_norm] using hx27_1
    · simpa [arm64_norm, wp_norm] using hx28_1

/-! ## 3. Multi-Step Induction for the Polynomial Evaluation Tail Loop -/

theorem polysTailLoop_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List Poly) (hlen_polys : polys.length = 16)
    (out_ptr u48 : BitVec 64) (R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64) :
    ∀ (rem i : Nat) (prefix_bytes : List (BitVec 8)) (st : M.σ) (s : State),
      LibsignalCodeLoaded lsmpl s.mem →
      i + (rem + 1) = 16 →
      prefix_bytes.length = 2 * i →
      s.pc = (blkPl_416).base + 296#64 →
      s.status = .Running →
      s.sp = s0.sp - 1200#64 →
      s.trace = s0.trace →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x9 = BitVec.ofNat 64 i →
      s.readReg64 .x19 = x.encA + 8#64 →
      s.readReg64 .x24 = x.encA →
      s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      s.readReg64 .x28 = 24#64 →
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
          ((out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i (rem + 1))) ∗
           A.live out_ptr 32 1 ∗
           memRegion x.outA chunkSize ∗
           (x.encA ↦₆₄ polyEncoderPolysTag) ∗
           polyListOf A.repAlloc (x.encA + 8#64) polys ∗
           ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
           memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
           (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
           (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
           (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
           (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
           (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
           (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
           (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
           localFramePointsRest (s0.sp - 1200#64) ∗
           savedCells s0 ∗
           tokenInitPlacedAt ∗
           reduceTablePlacedAt ∗
           A.pool lim (M.stepEvents (polysLoopEvents (polys.drop i)) st) sf ∗
           stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
          Q Q_panic) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
        ((out_ptr ↦ₛ prefix_bytes) ∗
         memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A.repAlloc (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
         (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
         localFramePointsRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim st s ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic
  | 0, i, prefix_bytes, st, s, hcl, hrem_eq, hprefix, hpc, hrun, hsp, htr, hvregs, hx9, hx19, hx24, hx27, hx28, hfit, hnext => by
    have hi : i = 15 := by omega
    subst hi
    have hi_len : 15 < polys.length := by omega
    refine polysTailLoop_step_placed_sepWPp M A lim st ext hA x polys hlen_polys out_ptr u48 prefix_bytes R
      15 0 hrem_eq hprefix s0 s hcl hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx24 hx27 hx28 hfit ?_
    intro sf hpcf hrunf hspf htrf hvregsf hclf _ _ hx20f hx24f hx27f _ _hfit_rest
    simp only [beq_self_eq_true, ↓reduceIte] at hpcf ⊢
    have hdrop15 :
        polysLoopEvents (polys.drop 15) = computeAtEvents (polys[15]'hi_len).coefficients.length := by
      rw [polysLoopEvents_drop_eq_cons hi_len, polysLoopEvents_drop_of_ge (by omega),
        List.append_nil]
    have hrem_zero : 32 - 2 * (15 + 1) = 0 := rfl
    have h2_16 : BitVec.ofNat 64 (2 * (15 + 1)) = 32#64 := rfl
    have h15 : BitVec.ofNat 64 15 = 15#64 := rfl
    rw [hrem_zero, ProofLib.memRegion_zero, h2_16, h15]
    rw [h2_16] at hx20f
    refine SepWPp.weaken_pre ?_
      (hnext sf hpcf hrunf hspf htrf hvregsf hclf hx20f hx24f hx27f)
    rw [hdrop15]
    exact Entails.of_eq (by sep_ac_rfl)
  | rem + 1, i, prefix_bytes, st, s, hcl, hrem_eq, hprefix, hpc, hrun, hsp, htr, hvregs, hx9, hx19, hx24, hx27, hx28, hfit, hnext => by
    have hi_len : i < polys.length := by omega
    refine polysTailLoop_step_placed_sepWPp M A lim st ext hA x polys hlen_polys out_ptr u48 prefix_bytes R
      i (rem + 1) hrem_eq hprefix s0 s hcl hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx24 hx27 hx28 hfit ?_
    intro sf hpcf hrunf hspf htrf hvregsf hclf hx9f hx19f _ hx24f hx27f hx28f hfit_rest
    have hne : ((rem + 1) == 0) = false := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hpcf ⊢
    have hrem' : (i + 1) + (rem + 1) = 16 := by omega
    have hprefix' : (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1).length = 2 * (i + 1) := by
      rw [List.length_append, hprefix, chunkPolysBytes_length]
      omega
    refine polysTailLoop_placed_sepWPp M A lim ext hA x polys hlen_polys out_ptr u48 R s0 hsp0
      rem (i + 1) (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1)
      (M.stepEvents (computeAtEvents (polys[i]'hi_len).coefficients.length) st) sf
      hclf hrem' hprefix' hpcf hrunf hspf htrf hvregsf hx9f hx19f hx24f hx27f hx28f hfit_rest ?_
    intro sf2 hpcf2 hrunf2 hspf2 htrf2 hvregsf2 hclf2 hx20f2 hx24f2 hx27f2
    have happ :
        (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i 1) ++
          chunkPolysBytes (x.enc.idx.setWidth 16) polys (i + 1) (rem + 1) =
        prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i (rem + 1 + 1) := by
      have h1 : 1 + (rem + 1) = rem + 1 + 1 := by omega
      rw [List.append_assoc, ← chunkPolysBytes_add (x.enc.idx.setWidth 16) polys 1 i (rem + 1), h1]
    have hstep_eq :
        M.stepEvents (polysLoopEvents (polys.drop (i + 1)))
          (M.stepEvents (computeAtEvents (polys[i]'hi_len).coefficients.length) st) =
          M.stepEvents (polysLoopEvents (polys.drop i)) st := by
      rw [polysLoopEvents_drop_eq_cons hi_len, M.stepEvents_append]
    rw [happ, hstep_eq]
    exact hnext sf2 hpcf2 hrunf2 hspf2 htrf2 hvregsf2 hclf2 hx20f2 hx24f2 hx27f2

/-- `FitsEnv`-parameterized wrapper around `polysTailLoop_placed_sepWPp` using
    `PolysLoopEnv (polys.drop i)`. -/
theorem polysTailLoop_placed_sepWPp_of_fitsEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (polys : List Poly) (hlen_polys : polys.length = 16)
    (out_ptr u48 : BitVec 64) (R : SepProp)
    {Q : State → SepProp → Prop}
    (s0 : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (rem i : Nat) (prefix_bytes : List (BitVec 8)) (st : M.σ) (s : State)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrem_eq : i + (rem + 1) = 16)
    (hprefix : prefix_bytes.length = 2 * i)
    (hpc : s.pc = (blkPl_416).base + 296#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hfit : FitsEnv M lim st (PolysLoopEnv (polys.drop i)))
    (hnext : ∀ sf : State,
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
        ((out_ptr ↦ₛ (prefix_bytes ++ chunkPolysBytes (x.enc.idx.setWidth 16) polys i (rem + 1))) ∗
         A.live out_ptr 32 1 ∗
         memRegion x.outA chunkSize ∗
         (x.encA ↦₆₄ polyEncoderPolysTag) ∗
         polyListOf A.repAlloc (x.encA + 8#64) polys ∗
         ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
         memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
         (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
         (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
         (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
         (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
         (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
         (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
         (((s0.sp - 1200#64) + 248#64) ↦₆₄ 32#64) ∗
         localFramePointsRest (s0.sp - 1200#64) ∗
         savedCells s0 ∗
         tokenInitPlacedAt ∗
         reduceTablePlacedAt ∗
         A.pool lim (M.stepEvents (polysLoopEvents (polys.drop i)) st) sf ∗
         stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R))) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 Reg.lr) s
      ((out_ptr ↦ₛ prefix_bytes) ∗
       memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
       A.live out_ptr 32 1 ∗
       memRegion x.outA chunkSize ∗
       (x.encA ↦₆₄ polyEncoderPolysTag) ∗
       polyListOf A.repAlloc (x.encA + 8#64) polys ∗
       ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
       memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
       (((s0.sp - 1200#64) + 48#64) ↦₆₄ u48) ∗
       (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
       (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
       (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
       (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
       (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * i)) ∗
       localFramePointsRest (s0.sp - 1200#64) ∗
       savedCells s0 ∗
       tokenInitPlacedAt ∗
       reduceTablePlacedAt ∗
       A.pool lim st s ∗
       stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ nextChunkOnPanic s0 sf ∗ R)) :=
  polysTailLoop_placed_sepWPp M A lim ext hA x polys hlen_polys out_ptr u48 R s0 hsp0
    rem i prefix_bytes st s hcl hrem_eq hprefix hpc hrun hsp htr hvregs hx9 hx19 hx24 hx27 hx28
    ((fitsEnv_polysLoop_iff (polys.drop i)).mp hfit) hnext

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysTailPlacedBudget
