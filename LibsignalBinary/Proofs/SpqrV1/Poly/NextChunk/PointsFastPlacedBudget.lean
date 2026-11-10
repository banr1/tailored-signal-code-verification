/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFast
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PolysLoop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed `Points` Fast Path

Relocatable `[LibsignalPlacement]` verification of the `EncoderState::Points` fast path for
Block `416` threading `RustCliAllocBudget M`, `BudgetLimits`, and `NextChunkPointsFastEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFastPlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSpqrV1 (NUM_POLYS Point)
open CryptoVerification.SpqrV1.GF.Mul2U16 (tokenInitPlacedAt)
open CryptoVerification.SpqrV1.GF.UnacceleratedMul (reduceTablePlacedAt)
open CryptoVerification.SpqrV1.Poly
  (chunkAt chunkDataOff chunkIndexOff chunkSize encoderStateAt gf16SliceAt pointListOf pointOf
   polyEncoderAt polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize polyEncoderPointsTag
   polyEncoderPolysTag polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (ofNat_beq_false_of_lt readReg32_setMem_pre
   readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (PolyNextChunkGhost chunkPointsBytes chunkPointsBytes_length chunkPointsBytes_zero_succ
   cmp_len_idx_gt gf16SliceAt_split_idx localFramePointsRest localFrameRest
   localFrameRest_fold_points localFrameRest_unfold_points lsr8_zext16_eq madd_24_eq madd_24_eq'
   memRegion_split_two_bytes nextChunkCalleeStack nextChunkOnPanic nextChunk_points_all_lt_eq
   ofNat_add_one_beq_16 ofNat_add_one_eq ofNat_two_mul_add_one ofNat_two_mul_add_two
   pointBufBody_eq_slice_rest pointBufRest
   pointListOf_split_idx pointOf_fold pointOf_unfold pointValue_len_lt_two_pow_63
   pointsToBytes_append_two_bytes polyNextChunkStack savedCells sepWP_exists_left_sep
   sepWPp_exists_left sp_sub_1200_add_48 sp_sub_1200_add_48' sp_sub_1200_add_88 sp_sub_1200_add_88'
   sp_sub_1200_add_104 sp_sub_1200_add_104' trunc8_zext16_eq zext16_shl1_bv_eq
   zext16_shl1_nat_eq)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget coarseCostModel fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget (sepWPp_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced NextChunkPrologueEnv epilogue_placed_sepWP fitsEnv_nextChunkPrologue_iff
   nextChunkEpilogueEvents nextChunkPrologueEvents prologue_placed_sepWPp)

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

attribute [local simp, local arm64_norm, local wp_norm]
  sp_sub_1200_add_48 sp_sub_1200_add_48'
  sp_sub_1200_add_88 sp_sub_1200_add_88'
  sp_sub_1200_add_104 sp_sub_1200_add_104'
  polyEncoderTagOff polyEncoderVecsOff polyEncoderVecsSize
  polyEncoderIdxOff polyEncoderPadOff polyEncoderPadSize
  polyEncoderPointsTag polyEncoderPolysTag
  chunkDataOff chunkIndexOff chunkSize
  madd_24_eq madd_24_eq'
  zext16_shl1_bv_eq zext16_shl1_nat_eq
  ofNat_add_one_eq ofNat_two_mul_add_one ofNat_two_mul_add_two
  lsr8_zext16_eq trunc8_zext16_eq

/-! ## 1. Exact Allocator Event Envelope for `Points` Fast Path -/

/-- Exact allocator event sequence of `<PolyEncoder as Encoder>::next_chunk` on the
    `EncoderState::Points` fast path (`+0 -> +92 -> +288..+4484 -> ret`):
    prologue `32`-byte output buffer allocation followed by epilogue `32`-byte deallocation. -/
def nextChunkPointsFastEvents : List AllocEvent :=
  rustAllocEvents 32 1 ++ rustDeallocEvents 32 1

theorem nextChunkPointsFastEvents_eq :
    nextChunkPointsFastEvents = nextChunkPrologueEvents ++ nextChunkEpilogueEvents :=
  rfl

def NextChunkPointsFastEnv (evs : List AllocEvent) : Prop :=
  evs = nextChunkPointsFastEvents

theorem fitsEnv_nextChunkPointsFast_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st NextChunkPointsFastEnv ↔ FitsEvents M lim st nextChunkPointsFastEvents := by
  constructor
  · intro h
    exact h nextChunkPointsFastEvents rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init NextChunkPointsFastEnv := by
  rw [fitsEnv_nextChunkPointsFast_iff]
  dsimp only [nextChunkPointsFastEvents, rustAllocEvents, rustDeallocEvents, List.cons_append,
    List.nil_append, FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc,
    AllocCostModel.step]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩

/-! ## 2. Single Iteration of the Budget-Threaded `Points` Fast-Path Loop (`+288` -> `+288` / `+4484`) -/

set_option maxHeartbeats 800000 in
theorem pointsFastLoop_step_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr : BitVec 64) (_R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (i : Nat) (hi16 : i < 16)
    (hidx_lt : (x.enc.idx.setWidth 16).toNat < (pts[i]'(by omega)).value.length)
    (u104 : BitVec 64)
    (s0 s : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_416).base + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (if i == 15 then
        (blkPl_416).base + 4484#64
      else
        (blkPl_416).base + 288#64) →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x19 = x.encA + 8#64 →
      sf.readReg64 .x20 = BitVec.ofNat 64 (2 * (i + 1)) →
      sf.readReg64 .x21 = 0#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      sf.readReg64 .x28 = 24#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) ∗
          memRegion (out_ptr + BitVec.ofNat 64 (2 * (i + 1))) (32 - 2 * (i + 1)) ∗
          A.live out_ptr 32 1 ∗
          memRegion x.outA chunkSize ∗
          (x.encA ↦₆₄ polyEncoderPointsTag) ∗
          pointListOf A.repAlloc (x.encA + 8#64) pts ∗
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
          memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
          (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
          (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
          (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
          (((s0.sp - 1200#64) + 104#64) ↦₆₄ BitVec.ofNat 64 i) ∗
          (((s0.sp - 1200#64) + 232#64) ↦₆₄ 32#64) ∗
          (((s0.sp - 1200#64) + 240#64) ↦₆₄ out_ptr) ∗
          (((s0.sp - 1200#64) + 248#64) ↦₆₄ BitVec.ofNat 64 (2 * (i + 1))) ∗
          localFramePointsRest (s0.sp - 1200#64) ∗
          savedCells s0 ∗
          tokenInitPlacedAt ∗
          reduceTablePlacedAt ∗
          A.pool lim st sf ∗
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        A.live out_ptr 32 1 ∗
        memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A.repAlloc (x.encA + 8#64) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ u104) ∗
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
  have hi_len : i < pts.length := by omega
  rw [pointListOf_split_idx A.repAlloc (x.encA + 8#64) pts i hi_len]
  apply SepWPp.fold
    (pointOf_unfold A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len))
    (by sep_focus)
  simp only [sepExists_sepConj_left]
  apply sepWPp_exists_left; intro cap
  apply sepWPp_exists_left; intro ptr
  have hpure_pull : ∀ (P_c P_p P_l : SepProp) (φ : Prop) (P_body Rest : SepProp),
      (P_c ∗ P_p ∗ P_l ∗ ⌜φ⌝ ∗ P_body) ∗ Rest = ⌜φ⌝ ∗ ((P_c ∗ P_p ∗ P_l ∗ P_body) ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_pull]
  apply SepWPp.pure_left; rintro ⟨hlen_cap, hcap_bound, hptr_ne⟩
  rw [pointBufBody_eq_slice_rest A.repAlloc cap ptr (pts[i]'hi_len) hlen_cap,
      gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
  have hlen_lt : (pts[i]'hi_len).value.length < 2 ^ 63 :=
    pointValue_len_lt_two_pow_63 hlen_cap hcap_bound
  rcases cmp_len_idx_gt (idx16 := x.enc.idx.setWidth 16) hidx_lt hlen_lt with
    ⟨hult_len, hule_len, hbeq_len, hsub_len⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i) (b := 32) (by omega) (by omega) with
    ⟨hcmp1_eq, hcmp1_sub, _, _⟩
  rcases ofNat_beq_false_of_lt (a := 2 * i + 1) (b := 32) (by omega) (by omega) with
    ⟨hcmp2_eq, hcmp2_sub, _, _⟩
  rcases ofNat_add_one_beq_16 hi16 with ⟨hcmp16_eq, hcmp16_sub⟩
  have h32_eq : (32#64 : BitVec 64) = BitVec.ofNat 64 32 := rfl
  rw [← h32_eq] at hcmp1_eq hcmp1_sub hcmp2_eq hcmp2_sub
  apply sepWPp_seg_416
    (mid := if i == 15 then (blkPl_416).base + 4484#64 else (blkPl_416).base + 288#64)
  intro _m_strip
  apply SepWP.fold (memRegion_split_two_bytes out_ptr i hi16) (by sep_focus)
  apply sepWP_exists_left_sep; intro b0
  apply sepWP_exists_left_sep; intro b1
  wp_steps 30
  have hfold_bytes :
      (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i)) ↦₈
          BitVec.setWidth 8 (((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value >>> 8)) ∗
        ((out_ptr + BitVec.ofNat 64 (2 * i + 1)) ↦₈
          BitVec.setWidth 8 ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ⊢
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 (i + 1)) := by
    rw [chunkPointsBytes_zero_succ (x.enc.idx.setWidth 16) pts i hi_len hidx_lt]
    exact pointsToBytes_append_two_bytes out_ptr
      (chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) i
      (chunkPointsBytes_length (x.enc.idx.setWidth 16) pts 0 i) _ _
  apply SepWP.fold hfold_bytes (by sep_focus)
  have hfold_slice :
      gf16SliceAt ptr ((pts[i]'hi_len).value.take (x.enc.idx.setWidth 16).toNat) ∗
        ((ptr + BitVec.ofNat 64 (2 * (x.enc.idx.setWidth 16).toNat)) ↦₁₆
          ((pts[i]'hi_len).value[(x.enc.idx.setWidth 16).toNat]'hidx_lt).value) ∗
        gf16SliceAt (ptr + BitVec.ofNat 64 (2 * ((x.enc.idx.setWidth 16).toNat + 1)))
          ((pts[i]'hi_len).value.drop ((x.enc.idx.setWidth 16).toNat + 1)) ⊢
        gf16SliceAt ptr (pts[i]'hi_len).value := by
    rw [← gf16SliceAt_split_idx ptr (pts[i]'hi_len).value (x.enc.idx.setWidth 16).toNat hidx_lt]
    exact Entails.refl _
  apply SepWP.fold hfold_slice (by sep_focus)
  have hfold_point :
      (((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 8#64) ↦₆₄ ptr) ∗
        ((((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) + 16#64) ↦₆₄
          BitVec.ofNat 64 (pts[i]'hi_len).value.length) ∗
        gf16SliceAt ptr (pts[i]'hi_len).value ∗
        pointBufRest A.repAlloc cap ptr (pts[i]'hi_len) ⊢
        pointOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) :=
    pointOf_fold A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) cap ptr (pts[i]'hi_len)
      ⟨hlen_cap, hcap_bound, hptr_ne⟩
  apply SepWP.fold hfold_point (by sep_focus)
  have hfold_list :
      pointListOf A.repAlloc (x.encA + 8#64) (pts.take i) ∗
        pointOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * i)) (pts[i]'hi_len) ∗
        pointListOf A.repAlloc ((x.encA + 8#64) + BitVec.ofNat 64 (24 * (i + 1))) (pts.drop (i + 1)) ⊢
        pointListOf A.repAlloc (x.encA + 8#64) pts := by
    rw [← pointListOf_split_idx A.repAlloc (x.encA + 8#64) pts i hi_len]
    exact Entails.refl _
  apply SepWP.fold hfold_list (by sep_focus)
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
          hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub])
    (by wp_norm_lhs)
    fun _m_real _hnsp => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWPp.weaken_pre (Entails.of_eq (by
      conv => lhs; simp only [arm64_norm]
      conv => rhs; simp only [arm64_norm]
      sep_ac_rfl))
    (hnext _ ?_ (by wp_norm_lhs) (by simpa [arm64_norm, wp_norm] using hsp)
      (by simpa [arm64_norm, wp_norm] using htr)
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub, hvregs])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub, hx24])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub, hx27])
      (by simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len, hcmp1_eq,
            hcmp1_sub, hcmp2_eq, hcmp2_sub, hx28]))
  simp only [arm64_norm, wp_norm, hult_len, hule_len, hbeq_len, hsub_len,
    hcmp1_eq, hcmp1_sub, hcmp2_eq, hcmp2_sub, hcmp16_eq, hcmp16_sub]

/-! ## 3. Full 16-Iteration `Points` Fast-Path Loop & `nextChunk_points_fast_placed_sepWPp` -/

theorem pointsFastLoop_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (x : PolyNextChunkGhost) (pts : List Point) (hlen_pts : pts.length = 16)
    (out_ptr : BitVec 64) (R : SepProp)
    {Q Q_panic : State → SepProp → Prop}
    (rem i : Nat) (hrem_eq : i + (rem + 1) = 16)
    (hfast : ∀ k : Nat, (hk : i ≤ k ∧ k < 16) →
      (x.enc.idx.setWidth 16).toNat < (pts[k]'(by omega)).value.length)
    (u104 : BitVec 64)
    (s0 s : State) (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hpc : s.pc = (blkPl_416).base + 288#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 1200#64)
    (htr : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx19 : s.readReg64 .x19 = x.encA + 8#64)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 (2 * i))
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx24 : s.readReg64 .x24 = x.encA)
    (hx27 : s.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hnext : ∀ sf : State,
      sf.pc = (blkPl_416).base + 4484#64 →
      sf.status = .Running →
      sf.sp = s0.sp - 1200#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      sf.readReg64 .x20 = 32#64 →
      sf.readReg64 .x24 = x.encA →
      sf.readReg64 .x27 = (x.enc.idx.setWidth 16).setWidth 64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) sf
        ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 16) ∗
          A.live out_ptr 32 1 ∗
          memRegion x.outA chunkSize ∗
          (x.encA ↦₆₄ polyEncoderPointsTag) ∗
          pointListOf A.repAlloc (x.encA + 8#64) pts ∗
          ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
          memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
          (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
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
          A.pool lim st sf ∗
          stackAt (s0.sp - 1200#64) nextChunkCalleeStack)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s
      ((out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 i) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * i)) (32 - 2 * i) ∗
        A.live out_ptr 32 1 ∗
        memRegion x.outA chunkSize ∗
        (x.encA ↦₆₄ polyEncoderPointsTag) ∗
        pointListOf A.repAlloc (x.encA + 8#64) pts ∗
        ((x.encA + polyEncoderIdxOff) ↦₃₂ x.enc.idx) ∗
        memRegion (x.encA + polyEncoderPadOff) polyEncoderPadSize ∗
        (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 56#64) ↦₆₄ x.outA) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ u104) ∗
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
  induction rem generalizing i s u104 with
  | zero =>
    have hi15 : i = 15 := by omega
    subst hi15
    refine pointsFastLoop_step_placed_sepWPp M A lim st ext x pts hlen_pts out_ptr R 15 (by decide)
      (hfast 15 ⟨by omega, by omega⟩) u104 s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx20 hx21
      hx24 hx27 hx28 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _ _ hx20_f _ hx24_f hx27_f _
    simp only [beq_self_eq_true, ↓reduceIte] at hpc_f
    have h0 : 32 - 2 * (15 + 1) = 0 := rfl
    rw [h0, memRegion_zero, emp_sepConj]
    exact hnext sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f
  | succ r ih =>
    have hi16 : i < 16 := by omega
    have hi15_ne : (i == 15) = false := beq_eq_false_iff_ne.mpr (by omega)
    refine pointsFastLoop_step_placed_sepWPp M A lim st ext x pts hlen_pts out_ptr R i hi16
      (hfast i ⟨by omega, hi16⟩) u104 s0 s hsp0 hpc hrun hsp htr hvregs hx9 hx19 hx20 hx21
      hx24 hx27 hx28 ?_
    intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx9_f hx19_f hx20_f hx21_f hx24_f hx27_f hx28_f
    simp only [hi15_ne, Bool.false_eq_true, ↓reduceIte] at hpc_f
    exact ih (i + 1) (by omega) (fun k hk => hfast k ⟨by omega, hk.2⟩) (BitVec.ofNat 64 i) sf
      hpc_f hrun_f hsp_f htr_f hvregs_f hx9_f hx19_f hx20_f hx21_f hx24_f hx27_f hx28_f

set_option maxHeartbeats 800000 in
/-- Complete budget-threaded proof of `<PolyEncoder as Encoder>::next_chunk` (Block `416`) when
    `x.enc.s = .points pts` and `∀ k : Fin 16, (x.enc.idx.setWidth 16).toNat < pts[k].value.length`. -/
theorem nextChunk_points_fast_placed_sepWPp [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ext : String → Option (State → State))
    (hA : AllocContractsPlaced M A lim ext)
    (x : PolyNextChunkGhost) (pts : List Point)
    (hs_pts : x.enc.s = .points pts)
    (hlen_pts : pts.length = NUM_POLYS)
    (hfast_all : ∀ k : Fin NUM_POLYS,
      (x.enc.idx.setWidth 16).toNat < (pts[k.val]'(by have := k.isLt; omega)).value.length)
    (hnext : x.enc.nextChunk = .ok (x.enc', x.chunk))
    (R : SepProp)
    {Q_panic : State → SepProp → Prop}
    (s0 : State)
    (hpc : s0.pc = (blkPl_416).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp &&& 0xf#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.encA)
    (hx8 : s0.readReg64 .x8 = x.outA)
    (hfit : FitsEnv M lim st NextChunkPointsFastEnv) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) (s0.readReg64 .lr) s0
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
             A.pool lim (M.stepEvents nextChunkPointsFastEvents st) sf1 ∗
             stackAt s0.sp polyNextChunkStack ∗ R)) ∧
          sf1.sp = s0.sp ∧ CalleeSavedPreserved s0 sf1)
      Q_panic := by
  have hfit_ev : FitsEvents M lim st (rustAllocEvents 32 1 ++ rustDeallocEvents 32 1) :=
    (fitsEnv_nextChunkPointsFast_iff).mp hfit
  have hfit_pro : FitsEnv M lim st NextChunkPrologueEnv :=
    (fitsEnv_nextChunkPrologue_iff).mpr ((fitsEvents_append M lim _ _ st).mp hfit_ev).1
  conv => arg 4; unfold polyEncoderAt encoderStateAt; rw [hs_pts]
  have hpure_len :
      ∀ (P1 : SepProp) (φ : Prop) (P_tag P_list P_idx P_pad Rest : SepProp),
        P1 ∗ ((⌜φ⌝ ∗ P_tag ∗ P_list) ∗ P_idx ∗ P_pad) ∗ Rest =
          ⌜φ⌝ ∗ (P1 ∗ P_tag ∗ P_list ∗ P_idx ∗ P_pad ∗ Rest) := by
    intros; sep_ac_rfl
  rw [hpure_len]
  apply SepWPp.pure_left; rintro ⟨_, hbounds⟩
  have hlen16 : pts.length = 16 := hlen_pts
  have henc_eq : x.enc = { idx := x.enc.idx, s := .points pts } := by
    rw [← hs_pts]
  have hnc := nextChunk_points_all_lt_eq (idx := x.enc.idx) hlen16
    (fun k hk => hfast_all ⟨k, by omega⟩)
  rw [← henc_eq] at hnc
  rw [hnc, Except.ok.injEq, Prod.mk.injEq] at hnext
  rcases hnext with ⟨henc'_eq, hchunk_eq⟩
  have hdata_eq : x.chunk.data.toList = chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 16 := by
    rw [← hchunk_eq]; rfl
  have hidx_chunk : x.chunk.index = x.enc.idx.setWidth 16 := by
    rw [← hchunk_eq]
  have hidx_enc' : x.enc'.idx = x.enc.idx + 1#32 := by
    rw [← henc'_eq]
  have hs_enc' : x.enc'.s = .points pts := by
    rw [← henc'_eq]
  refine prologue_placed_sepWPp M A lim st ext hA x polyEncoderPointsTag
    (pointListOf A.repAlloc (x.encA + polyEncoderVecsOff) pts) R s0 hpc hrun hsp0 hx0 hx8 hfit_pro ?_
  intro s1 out_ptr hout_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx9_1 hx19_1 hx24_1 hx27_1 _hx29_1
  change s1.readReg64 .x9 = 0#64 at hx9_1
  apply sepWPp_seg_416
    (mid := (blkPl_416).base + 288#64)
  intro _m_strip
  apply SepWP.fold (localFrameRest_unfold_points (s0.sp - 1200#64)) (by sep_focus)
  apply sepWP_exists_left_sep; intro u48
  apply sepWP_exists_left_sep; intro u88
  apply sepWP_exists_left_sep; intro u104
  wp_steps 9
  refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine SepWPp.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  have hinit_buf :
      memRegion out_ptr 32 =
        (out_ptr ↦ₛ chunkPointsBytes (x.enc.idx.setWidth 16) pts 0 0) ∗
        memRegion (out_ptr + BitVec.ofNat 64 (2 * 0)) (32 - 2 * 0) := by
    simp [chunkPointsBytes, pointsToBytes_nil, emp_sepConj]
  have hfast0 : ∀ k : Nat, (hk : 0 ≤ k ∧ k < 16) →
      (x.enc.idx.setWidth 16).toNat < (pts[k]'(by omega)).value.length :=
    fun k hk => hfast_all ⟨k, hk.2⟩
  refine SepWPp.weaken_pre ?_
    (pointsFastLoop_placed_sepWPp M A lim (M.stepEvents (rustAllocEvents 32 1) st) ext x pts hlen16
      out_ptr R 15 0 rfl hfast0 u104 s0 _ hsp0
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · rw [hinit_buf]
    exact Entails.of_eq (by
      conv => lhs; simp only [arm64_norm]
      conv => rhs; simp only [arm64_norm]
      sep_ac_rfl)
  · wp_norm_goal
  · wp_norm_lhs
  · simpa [arm64_norm, wp_norm] using hsp1
  · simpa [arm64_norm, wp_norm] using htr1
  · simpa [arm64_norm, wp_norm] using hvregs1
  · rfl
  · simpa [arm64_norm, wp_norm] using hx19_1
  · rfl
  · rfl
  · simpa [arm64_norm, wp_norm] using hx24_1
  · simpa [arm64_norm, wp_norm] using hx27_1
  · rfl
  intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx27_f
  apply SepWPp.of_sepWP_ret
  have hlfr_fold :
      (((s0.sp - 1200#64) + 48#64) ↦₆₄ 2#64) ∗
        (((s0.sp - 1200#64) + 88#64) ↦₆₄ (x.encA + 8#64)) ∗
        (((s0.sp - 1200#64) + 104#64) ↦₆₄ 15#64) ∗
        localFramePointsRest (s0.sp - 1200#64) ⊢
        localFrameRest (s0.sp - 1200#64) :=
    localFrameRest_fold_points (s0.sp - 1200#64) 2#64 (x.encA + 8#64) 15#64
  apply SepWP.fold hlfr_fold (by sep_focus)
  have henc'_state :
      (x.encA ↦₆₄ polyEncoderPointsTag) ∗ pointListOf A.repAlloc (x.encA + 8#64) pts ⊢
        encoderStateAt A.repAlloc x.encA x.enc'.s := by
    rw [hs_enc']
    unfold encoderStateAt
    dsimp only [polyEncoderVecsOff]
    have htrue : (pts.length = NUM_POLYS ∧ (∀ pt ∈ pts, pt.value.length ≤ 0x0555555555555555)) = True :=
      propext ⟨fun _ => trivial, fun _ => ⟨hlen_pts, hbounds⟩⟩
    rw [htrue, pure_true, emp_sepConj]
    exact Entails.refl _
  apply SepWP.fold henc'_state (by sep_focus)
  rw [← hdata_eq]
  have hstep_eq :
      M.stepEvents (rustDeallocEvents 32 1) (M.stepEvents (rustAllocEvents 32 1) st) =
        M.stepEvents nextChunkPointsFastEvents st :=
    (M.stepEvents_append (rustAllocEvents 32 1) (rustDeallocEvents 32 1) st).symm
  refine SepWP.mono
    (SepWP.weaken_pre (Entails.of_eq (by
        conv => lhs; simp only [arm64_norm]
        conv => rhs; simp only [arm64_norm]
        sep_ac_rfl))
      (epilogue_placed_sepWP M A lim (M.stepEvents (rustAllocEvents 32 1) st) ext hA x R s0 sf
        out_ptr hout_ne hidx_chunk hidx_enc' hpc_f hrun_f hsp_f hsp0 htr_f hx20_f hx24_f ?_ hvregs_f))
    fun sf1 P_f _ _ hpost => ?_
  · rw [hx27_f, BitVec.setWidth_setWidth_of_le (x.enc.idx.setWidth 16) (by decide)]
    rfl
  · rwa [hstep_eq] at hpost

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsFastPlacedBudget
