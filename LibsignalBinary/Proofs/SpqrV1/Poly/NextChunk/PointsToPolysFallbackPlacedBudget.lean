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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallback
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed Fallback Setup

Relocatable `[LibsignalPlacement]` verification of fallback dispatch (`+1136 -> +1804`),
`fillXsLoop` (`+1844 -> +1864`), and `allocXsAndBasis` (`+1804 -> +4116`) threading
`RustCliAllocBudget M`, `BudgetLimits`, and `AllocXsAndBasisEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (allocHookStack arrayAt)
open CryptoVerification.LibsignalSpqrV1 (GF16 Pt)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly (ptAt ptSliceAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (memRegion_split_pt mul24_shl_eq mul24_shl_eq_nat ofNat_add_one_eq_succ_fb
   ofNat_ne_ofNat_false ofNat_succ_add_neg_one_fb ofNat_succ_sub_one_fb sle_four_of_gt
   sle_four_of_le slt_33_of_gt slt_33_of_le toOnePts toOnePts_nil ult_max_pts_false)
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
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setMem_pre pc_setMem_pre status_setMem_pre pstate_setMem_pre trace_setMem_pre
  fs_setMem_pre sigActions_setMem_pre tpidrEl0_setMem_pre brkStart_setMem_pre
  oracle_setMem_pre symtab_setMem_pre calleeSavedVRegs_setMem_pre
  readReg64_setMem_pre readReg32_setMem_pre readReg_setMem_pre
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_fb_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_fb_pl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

attribute [local simp, local arm64_norm, local wp_norm]
  ofNat_succ_sub_one_fb ofNat_succ_add_neg_one_fb ofNat_add_one_eq_succ_fb

/-! ## 1. Exact Allocator Event Envelope for `allocXsAndBasis` (`+1804..+4116`) -/

/-- Exact allocator event sequence of `allocXsAndBasis` (`+1804..+4116`, Block `416`) for `n` points:
    `4 * n` bytes (alignment `2`) for `xsPtr`, followed by `24 * n` bytes (alignment `8`) for `basisPtr`. -/
def allocXsAndBasisEvents (n : Nat) : List AllocEvent :=
  rustAllocEvents (4 * n) 2 ++ rustAllocEvents (24 * n) 8

def AllocXsAndBasisEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = allocXsAndBasisEvents n

theorem fitsEnv_allocXsAndBasis_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (n : Nat) :
    FitsEnv M lim st (AllocXsAndBasisEnv n) ↔ FitsEvents M lim st (allocXsAndBasisEvents n) := by
  constructor
  · intro h
    exact h (allocXsAndBasisEvents n) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (AllocXsAndBasisEnv 8) := by
  rw [fitsEnv_allocXsAndBasis_iff]
  dsimp only [allocXsAndBasisEvents, rustAllocEvents, List.cons_append, List.nil_append,
    FitsEvents, FitsEvent, FitsStep, AllocEvent.withinMaxAlloc, AllocCostModel.step]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩,
    ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩⟩

/-! ## 2. Budget-Threaded Dispatch (`+1136 -> +1804`) -/

theorem dispatch_fallback_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hn3 : n ≠ 3) (hn5 : n ≠ 5)
    (hn30 : n ≠ 30) (hn34 : n ≠ 34) (hn36 : n ≠ 36)
    (hnb : n ≤ 0x0555555555555555)
    (u96 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1136#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ s1,
      s1.pc = (blkPl_416).base + 1804#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x19 = 1#64 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim st s1 ∗ ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ((fsp + 96#64) ↦₆₄ u96) ∗ Frame)
      Q Q_panic := by
  have hn_lt : n < 2 ^ 64 := by omega
  obtain ⟨hne0_a, hne0_bne, hne0_b⟩ := ofNat_ne_ofNat_false hn0 hn_lt (by decide)
  obtain ⟨hne1_a, hne1_bne, hne1_b⟩ := ofNat_ne_ofNat_false hn1 hn_lt (by decide)
  obtain ⟨hne3_a, hne3_bne, hne3_b⟩ := ofNat_ne_ofNat_false hn3 hn_lt (by decide)
  obtain ⟨hne5_a, hne5_bne, hne5_b⟩ := ofNat_ne_ofNat_false hn5 hn_lt (by decide)
  obtain ⟨hne30_a, hne30_bne, hne30_b⟩ := ofNat_ne_ofNat_false hn30 hn_lt (by decide)
  obtain ⟨hne34_a, hne34_bne, hne34_b⟩ := ofNat_ne_ofNat_false hn34 hn_lt (by decide)
  obtain ⟨hne36_a, hne36_bne, hne36_b⟩ := ofNat_ne_ofNat_false hn36 hn_lt (by decide)
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  by_cases hle4 : n ≤ 4
  · have hsge4 := sle_four_of_le hle4
    apply sepWPp_seg_416
      (mid := (blkPl_416).base + 1804#64)
    intro _m_strip
    wp_steps
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hx25, hsge4, hne0_a, hne0_bne, hne0_b,
            hne1_a, hne1_bne, hne1_b, hne3_a, hne3_bne, hne3_b, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    exact hcont _
      (by simp only [arm64_norm, wp_norm, hx25, hsge4, hne0_a, hne0_bne, hne0_b,
            hne1_a, hne1_bne, hne1_b, hne3_a, hne3_bne, hne3_b, Bool.false_eq_true, ↓reduceIte])
      (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
      (by simp only [arm64_norm, wp_norm, htrace])
      (by simp only [arm64_norm, wp_norm])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hx25])
      (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
  · have hgt4 : 4 < n := by omega
    have hsge4 := sle_four_of_gt hgt4 hnb
    by_cases hle33 : n ≤ 33
    · have hslt33 := slt_33_of_le hle33
      apply sepWPp_seg_416
        (mid := (blkPl_416).base + 1804#64)
      intro _m_strip
      wp_steps
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hx25, hsge4, hslt33, hne5_a, hne5_bne, hne5_b,
              hne30_a, hne30_bne, hne30_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        fun _m_real _hnsp => ?_
      refine SepWPp.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      exact hcont _
        (by simp only [arm64_norm, wp_norm, hx25, hsge4, hslt33, hne5_a, hne5_bne, hne5_b,
              hne30_a, hne30_bne, hne30_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        (by simp only [arm64_norm, wp_norm])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hx25])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
    · have hgt33 : 33 < n := by omega
      have hslt33 := slt_33_of_gt hgt33 hnb
      apply sepWPp_seg_416
        (mid := (blkPl_416).base + 1804#64)
      intro _m_strip
      wp_steps
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hx25, hsge4, hslt33, hne34_a, hne34_bne, hne34_b,
              hne36_a, hne36_bne, hne36_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs)
        fun _m_real _hnsp => ?_
      refine SepWPp.transport_budgetPool
        (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      exact hcont _
        (by simp only [arm64_norm, wp_norm, hx25, hsge4, hslt33, hne34_a, hne34_bne, hne34_b,
              hne36_a, hne36_bne, hne36_b, Bool.false_eq_true, ↓reduceIte])
        (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hsp])
        (by simp only [arm64_norm, wp_norm, htrace])
        (by simp only [arm64_norm, wp_norm])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm, hx25])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)

/-! ## 3. Budget-Threaded `fillXsLoop` (`+1844..+1864`) & `allocXsAndBasis` (`+1804..+4116`) -/

/-- One step of the budget-threaded `[(x_i, 1)]` fill loop (`+1844..+1860`). -/
theorem fillXsLoop_step_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (src dst : BitVec 64) (pt : Pt) (rest : List Pt) (Frame : SepProp)
    (hbound : rest.length ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1844#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = dst + 2#64)
    (hx9 : s.readReg64 .x9 = src)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 (rest.length + 1))
    (hx19 : s.readReg64 .x19 = 1#64)
    (hcont : ∀ sf,
      sf.pc = (if rest.length = 0 then (blkPl_416).base + 1864#64 else (blkPl_416).base + 1844#64) →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x8 = (dst + 4#64) + 2#64 →
      sf.readReg64 .x9 = src + 4#64 →
      sf.readReg64 .x10 = BitVec.ofNat 64 rest.length →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sf
        (A.pool lim st sf ∗
         ptAt pt src ∗
         ptAt { x := pt.x, y := GF16.ONE } dst ∗
         memRegion (dst + 4#64) (4 * rest.length) ∗
         Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptAt pt src ∗ memRegion dst (4 * (rest.length + 1)) ∗ Frame)
      Q Q_panic := by
  apply sepWPp_seg_416
    (mid := if rest.length = 0 then (blkPl_416).base + 1864#64 else (blkPl_416).base + 1844#64)
  intro _m_strip
  unfold ptAt
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (memRegion_split_pt dst rest.length hbound)))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro ux
  apply SepWP.exists_elim; intro uy
  have hdst_x : (dst + 2#64) + 0xfffffffffffffffe#64 = dst := by bv_omega
  have hx8_next : (dst + 2#64) + 4#64 = (dst + 4#64) + 2#64 := by bv_omega
  have htrunc : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 pt.x.value)) = pt.x.value := by
    bv_bits
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps
  by_cases hrem : rest.length = 0
  · refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx10, bne_self_eq_false,
            BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
      (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre ?_
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx10, bne_self_eq_false,
              BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx8, hx8_next])
        (by simp only [arm64_norm, wp_norm, hx9])
        (by simp only [arm64_norm, wp_norm, hx10, hrem])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))
    unfold ptAt GF16.ONE
    try simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, htrunc]
    exact Entails.of_eq (by sep_ac_rfl)
  · have hne1 : (BitVec.ofNat 64 (rest.length + 1) != 1#64) = true := by
      have hpos : 0 < rest.length := Nat.pos_of_ne_zero hrem
      obtain ⟨_, hbne, _⟩ :=
        ofNat_ne_ofNat_false (a := rest.length + 1) (b := 1) (by omega) (by omega) (by decide)
      exact hbne
    refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx10, hne1])
      (by wp_norm_lhs)
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre ?_
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx10, hne1])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [arm64_norm, wp_norm])
        (by simp only [arm64_norm, wp_norm, hx8, hx8_next])
        (by simp only [arm64_norm, wp_norm, hx9])
        (by simp only [arm64_norm, wp_norm, hx10])
        (by simp only [arm64_norm, wp_norm, hx19])
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs)
        (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs) (by wp_norm_lhs))
    unfold ptAt GF16.ONE
    try simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend, htrunc]
    exact Entails.of_eq (by sep_ac_rfl)

/-- Full budget-threaded `[(x_i, 1)]` fill loop (`+1844 -> +1864`) over `pts : List Pt`. -/
theorem fillXsLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (s0 s : State) (src dst : BitVec 64) (Frame : SepProp)
    (hbound : pts.length ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1844#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = dst + 2#64)
    (hx9 : s.readReg64 .x9 = src)
    (hx10 : s.readReg64 .x10 = BitVec.ofNat 64 pts.length)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hcont : ∀ sf,
      sf.pc = (blkPl_416).base + 1864#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x19 = 1#64 →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sf
        (A.pool lim st sf ∗
         ptSliceAt src pts ∗
         ptSliceAt dst (toOnePts pts) ∗
         Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗ ptSliceAt src pts ∗ memRegion dst (4 * pts.length) ∗ Frame)
      Q Q_panic := by
  induction pts generalizing s src dst Frame with
  | nil => contradiction
  | cons pt rest ih =>
    have hsrc_cons : ptSliceAt src (pt :: rest) = ptAt pt src ∗ ptSliceAt (src + 4#64) rest := rfl
    have hdst_cons : ptSliceAt dst (toOnePts (pt :: rest)) =
        ptAt { x := pt.x, y := GF16.ONE } dst ∗
        ptSliceAt (dst + 4#64) (toOnePts rest) := rfl
    cases rest with
    | nil =>
      refine SepWPp.weaken_pre
        (by rw [hsrc_cons, List.length_cons, List.length_nil]; exact Entails.of_eq (by sep_ac_rfl))
        (fillXsLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s src dst pt [] (ptSliceAt (src + 4#64) [] ∗ Frame)
          (by simp) hpc hrun hx8 hx9 hx10 hx19 ?_)
      intro sf hpc_sf hrun_sf hsp_sf htr_sf hvregs_sf _ _ _ hx19_sf hx20_sf hx24_sf hx25_sf
        hx26_sf hx27_sf hx28_sf hx29_sf hx30_sf
      simp only [List.length_nil, ↓reduceIte] at hpc_sf
      refine SepWPp.weaken_pre ?_
        (hcont sf hpc_sf hrun_sf hsp_sf htr_sf hvregs_sf hx19_sf hx20_sf hx24_sf hx25_sf
          hx26_sf hx27_sf hx28_sf hx29_sf hx30_sf)
      rw [hsrc_cons, hdst_cons]
      simp only [List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero, toOnePts_nil, ptSliceAt,
        arrayAt]
      exact Entails.of_eq (by sep_ac_rfl)
    | cons pt' rest' =>
      have hlen_ne : (pt' :: rest').length ≠ 0 := by simp
      refine SepWPp.weaken_pre
        (by rw [hsrc_cons, List.length_cons]; exact Entails.of_eq (by sep_ac_rfl))
        (fillXsLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s src dst pt (pt' :: rest') (ptSliceAt (src + 4#64) (pt' :: rest') ∗ Frame)
          (by simp only [List.length_cons] at hbound ⊢; exact Nat.le_of_succ_le hbound)
          hpc hrun hx8 hx9 hx10 hx19 ?_)
      intro sm hpc_sm hrun_sm hsp_m htr_m hvregs_m hx8_m hx9_m hx10_m hx19_m
        hx20_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hx30_m
      simp only [hlen_ne, ↓reduceIte] at hpc_sm
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (ih (List.cons_ne_nil pt' rest') sm (src + 4#64) (dst + 4#64)
          (ptAt pt src ∗ ptAt { x := pt.x, y := GF16.ONE } dst ∗ Frame)
          (by simp only [List.length_cons] at hbound ⊢; exact Nat.le_of_succ_le hbound)
          hpc_sm hrun_sm hx8_m hx9_m hx10_m hx19_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx19_f hx20_f hx24_f hx25_f hx26_f hx27_f
        hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hsrc_cons, hdst_cons]; exact Entails.of_eq (by sep_ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          hx19_f (hx20_f.trans hx20_m) (hx24_f.trans hx24_m) (hx25_f.trans hx25_m)
          (hx26_f.trans hx26_m) (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

set_option maxHeartbeats 800000 in
private theorem allocXs_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn_pos : 0 < n) (hbound : n ≤ 0x0555555555555555)
    (u96 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * n))
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hu96 : u96 = BitVec.ofNat 64 n)
    (hfit4 : FitsEvents M lim st (rustAllocEvents (4 * n) 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (xsPtr : BitVec 64),
      xsPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 1844#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x8 = xsPtr + 2#64 →
      s1.readReg64 .x9 = ptVecPtr →
      s1.readReg64 .x10 = BitVec.ofNat 64 n →
      s1.readReg64 .x19 = 1#64 →
      s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * n) →
      s1.readReg64 .x25 = s.readReg64 .x20 →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢
        A.pool lim (M.stepEvents (rustAllocEvents (4 * n) 2) st) s1 ∗
        A.live xsPtr (4 * n) 2 ∗
        memRegion xsPtr (4 * n) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 1844#64) s
      (A.pool lim st s ∗
       ((fsp + 96#64) ↦₆₄ u96) ∗
       stackAt fsp allocHookStack ∗ Frame)
      post := by
  subst hu96
  have hlayout4 : RustLayoutOk (4 * n) 2 := ⟨⟨by omega, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have hfit4_ev : FitsEvent M lim st (.alloc (4 * n)) := by
    have hle4 : 2 ≤ 4 * n := by omega
    simpa [rustAllocEvents, hle4] using hfit4
  rcases hfit4_ev with ⟨_hwmax4, henf4, hram4, hva4⟩
  have h4n_toNat : (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := Nat.mod_eq_of_lt (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  clear hA
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf0 : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, *]
  have htr_sf0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (4 * n, 2, st)
  clear halloc
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq0 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  have hsp_sf1 : sf_1.sp = fsp := by
    simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416
    (mid := (blkPl_416).base + 1844#64)
  intro _m_strip
  wp_steps
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq0, Bool.false_eq_true, ↓reduceIte])
    (by wp_norm_lhs)
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr_sf1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x8, *])
    (by simp only [arm64_norm, wp_norm, Reg.x9, Reg.x26, *])
    (by simp only [arm64_norm, wp_norm, Reg.x10, hsp_sf1, *])
    (by simp only [arm64_norm, wp_norm, Reg.x19, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, Reg.x25, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, Bool.false_eq_true, ↓reduceIte, h4n_toNat, hsp_sf1, hsp_sf0, hsp]
  exact Entails.of_eq (by sep_ac_rfl)

private theorem preAllocBasis_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn_pos : 0 < n) (hbound : n ≤ 0x0555555555555555)
    (u80 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1864#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hcont : ∀ (sm : State),
      sm.pc = (blkPl_416).base + 1900#64 →
      sm.status = .Running →
      sm.sp = fsp →
      sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x1 = BitVec.ofNat 64 (24 * n) →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = ptVecPtr →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        ((blkPl_416).base + 4116#64) sm
        (A.pool lim st1 sm ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         Frame)
        post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4116#64) s
      (A.pool lim st1 s ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       Frame)
      post := by
  have h24n_eq : (BitVec.ofNat 64 (24 * n) == 0#64) = false :=
    (ofNat_ne_ofNat_false (a := 24 * n) (b := 0) (by omega) (by omega) (by decide)).1
  have hnhi := ult_max_pts_false hbound
  have hmul24 := mul24_shl_eq n
  have hmul24_nat := mul24_shl_eq_nat n
  have hmul24_2n : (BitVec.ofNat 64 n + BitVec.ofNat 64 (2 * n)) <<< 3 = BitVec.ofNat 64 (24 * n) := by
    have h2n : BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 n <<< 1 := by
      change BitVec.ofNat 64 (2 * n) = BitVec.ofNat 64 n <<< 1#64
      have hm : BitVec.ofNat 64 n <<< 1#64 = BitVec.ofNat 64 n * 2#64 := by bv_bits
      rw [hm]; bv_omega
    rw [h2n]; exact hmul24_nat
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
  apply sepWP_seg_416
    (mid := (blkPl_416).base + 1900#64)
  intro _m_strip
  wp_steps 9
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
          Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
          Bool.false_eq_true, ↓reduceIte, hrun])
    fun _m_real _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre
    (Entails.of_eq (by sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte, hrun])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, Reg.x1, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq, hx26,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hsp, hnhi, hmul24, hmul24_nat, hmul24_2n, h24n_eq,
            Bool.false_eq_true, ↓reduceIte]))

set_option maxHeartbeats 800000 in
private theorem allocBasis_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (n : Nat) (hn_pos : 0 < n) (hbound : n ≤ 0x0555555555555555)
    (u24 u80 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1864#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hfit24 : FitsEvents M lim st1 (rustAllocEvents (24 * n) 8))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (basisPtr : BitVec 64),
      basisPtr ≠ 0#64 →
      basisPtr.toNat % 8 = 0 →
      s1.pc = (blkPl_416).base + 4116#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = basisPtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢
        A.pool lim (M.stepEvents (rustAllocEvents (24 * n) 8) st1) s1 ∗
        A.live basisPtr (24 * n) 8 ∗
        memRegion basisPtr (24 * n) ∗
        ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 4116#64) s
      (A.pool lim st1 s ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame)
      post := by
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (preAllocBasis_seg (M := M) (A := A) (lim := lim) (st1 := st1)
      s fsp ptVecPtr hfsp_align n hn_pos hbound u80
      (((fsp + 24#64) ↦₆₄ u24) ∗ stackAt fsp allocHookStack ∗ Frame)
      hpc hrun hsp hx26 ?_)
  intro sm hpcm hrunm hspm htrm hvregsm hx20m hx1m hx24m hx25m hx26m hx27m hx28m hx29m
  have htrm' : sm.trace = s0.trace := htrm.trans htrace
  have hlayout24 : RustLayoutOk (24 * n) 8 := ⟨⟨by omega, ⟨3, rfl⟩, by omega⟩, by decide⟩
  have hfit24_ev : FitsEvent M lim st1 (.alloc (24 * n)) := by
    have hle24 : 8 ≤ 24 * n := by omega
    simpa [rustAllocEvents, hle24] using hfit24
  rcases hfit24_ev with ⟨_hwmax24, henf24, hram24, hva24⟩
  have h24n_toNat : (BitVec.ofNat 64 (24 * n)).toNat = 24 * n := Nat.mod_eq_of_lt (by omega)
  have h8_toNat : (8#64 : BitVec 64).toNat = 8 := rfl
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  clear hA
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (show SepWP _ ((blkPl_416).base + 4116#64) sm
      (A.pool lim st1 sm ∗ stackAt fsp allocHookStack ∗
       (((fsp + 24#64) ↦₆₄ u24) ∗
        ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
        ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)) post from ?_)
  wp_steps_sync_416 (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf0 : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, *]
  have htr_sf0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, htrm', *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (24 * n, 8, st1)
  clear halloc
  have hoom2 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have halign2 : (sf_1.readReg64 (Reg.gpr 0#5)).toNat % 8 = 0 := by assumption
  have hbeq2 : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hoom2
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  have hsp_sf1 : sf_1.sp = fsp := by
    simp only [arm64_norm, wp_norm, *]
  apply sepWP_seg_416
    (mid := (blkPl_416).base + 4116#64)
  intro _m_strip2
  wp_steps 12
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte, *])
    fun _m_real2 _hnsp2 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp2.toVmPreserved (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte, *]) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom2 halign2
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq2, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, htr_sf1])
    (by simp only [arm64_norm, wp_norm, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, *])
    ?_
  simp only [arm64_norm, wp_norm, Bool.false_eq_true, ↓reduceIte, h24n_toNat, hsp_sf1, hsp_sf0,
    hspm, hx26m, *]
  exact Entails.of_eq (by sep_ac_rfl)

/-- `+1804 -> +4116`: budget-threaded allocation of `xsPtr` (`4 * n` bytes, align `2`),
    fill of `[(x_i, 1)]`, check `n ≤ 0x0555555555555555`, and allocation of `basisPtr`
    (`24 * n` bytes, align `8`). -/
theorem allocXsAndBasis_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp ptVecPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (pts : List Pt) (hpts_ne : pts ≠ [])
    (hbound : pts.length ≤ 0x0555555555555555)
    (u24 u80 : BitVec 64) (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 1804#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length))
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hfit : FitsEnv M lim st (AllocXsAndBasisEnv pts.length))
    (hcont : ∀ s1 xsPtr basisPtr,
      xsPtr ≠ 0#64 →
      basisPtr ≠ 0#64 →
      basisPtr.toNat % 8 = 0 →
      s1.pc = (blkPl_416).base + 4116#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = xsPtr →
      s1.readReg64 .x21 = basisPtr →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * pts.length) →
      s1.readReg64 .x25 = s.readReg64 .x20 →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (allocXsAndBasisEvents pts.length) st) s1 ∗
         ptSliceAt ptVecPtr pts ∗
         A.live xsPtr (4 * pts.length) 2 ∗
         ptSliceAt xsPtr (toOnePts pts) ∗
         A.live basisPtr (24 * pts.length) 8 ∗
         memRegion basisPtr (24 * pts.length) ∗
         ((fsp + 24#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ptSliceAt ptVecPtr pts ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  have hn_pos : 0 < pts.length := List.length_pos_iff.mpr hpts_ne
  have hfit_both :
      FitsEvents M lim st (rustAllocEvents (4 * pts.length) 2) ∧
        FitsEvents M lim (M.stepEvents (rustAllocEvents (4 * pts.length) 2) st)
          (rustAllocEvents (24 * pts.length) 8) :=
    (fitsEvents_append M lim _ _ st).mp ((fitsEnv_allocXsAndBasis_iff pts.length).mp hfit)
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (allocXs_seg hA s0 s fsp ptVecPtr hfsp_align pts.length hn_pos hbound
        (BitVec.ofNat 64 pts.length)
        (ptSliceAt ptVecPtr pts ∗ ((fsp + 24#64) ↦₆₄ u24) ∗ ((fsp + 80#64) ↦₆₄ u80) ∗ Frame)
        hpc hrun hsp htrace hx19 hx24 hx26 rfl hfit_both.1 ?_))
  intro s1 P1 xsPtr hxs_ne hpc1 hrun1 hsp1 htr1 hvregs1 hx8_1 hx9_1 hx10_1 hx19_1 hx20_1
    hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hent1
  refine SepWPp.weaken_pre (Entails.trans hent1 (Entails.of_eq (by sep_ac_rfl)))
    (fillXsLoop_placed_sepWPp (M := M) (A := A) (lim := lim)
      (st := M.stepEvents (rustAllocEvents (4 * pts.length) 2) st) (ext := ext)
      pts hpts_ne s0 s1 ptVecPtr xsPtr
      (A.live xsPtr (4 * pts.length) 2 ∗
       ((fsp + 24#64) ↦₆₄ u24) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 96#64) ↦₆₄ BitVec.ofNat 64 pts.length) ∗
       stackAt fsp allocHookStack ∗ Frame)
      hbound hpc1 hrun1 hx8_1 hx9_1 hx10_1 hx19_1 ?_)
  intro sFill hpcFill hrunFill hspFill htrFill hvregsFill _hx19Fill hx20Fill hx24Fill hx25Fill
    hx26Fill hx27Fill hx28Fill hx29Fill _hx30Fill
  have hspFill' : sFill.sp = fsp := hspFill.trans hsp1
  have htrFill' : sFill.trace = s0.trace := htrFill.trans htr1
  have hx26Fill' : sFill.readReg64 .x26 = ptVecPtr := hx26Fill.trans hx26_1
  refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (SepWPp.of_sepWP
      (allocBasis_seg hA s0 sFill fsp ptVecPtr hfsp_align pts.length hn_pos hbound u24 u80
        (ptSliceAt ptVecPtr pts ∗ A.live xsPtr (4 * pts.length) 2 ∗
         ptSliceAt xsPtr (toOnePts pts) ∗ Frame)
        hpcFill hrunFill hspFill' htrFill' hx26Fill' hfit_both.2 ?_))
  intro sOut POut basisPtr hbasis_ne hbasis_align hpcOut hrunOut hspOut htrOut hvregsOut
    hx20Out hx21Out hx24Out hx25Out hx26Out hx27Out hx28Out hx29Out hentOut
  have hstep_eq :
      M.stepEvents (rustAllocEvents (24 * pts.length) 8)
          (M.stepEvents (rustAllocEvents (4 * pts.length) 2) st) =
        M.stepEvents (allocXsAndBasisEvents pts.length) st :=
    (M.stepEvents_append (rustAllocEvents (4 * pts.length) 2)
      (rustAllocEvents (24 * pts.length) 8) st).symm
  refine SepWPp.weaken_pre (Entails.trans hentOut ?_)
    (hcont sOut xsPtr basisPtr hxs_ne hbasis_ne hbasis_align hpcOut hrunOut hspOut htrOut
      (hvregsOut.trans (hvregsFill.trans hvregs1))
      (hx20Out.trans (hx20Fill.trans hx20_1))
      hx21Out
      (hx24Out.trans (hx24Fill.trans hx24_1))
      (hx25Out.trans (hx25Fill.trans hx25_1))
      hx26Out
      (hx27Out.trans (hx27Fill.trans hx27_1))
      (hx28Out.trans (hx28Fill.trans hx28_1))
      (hx29Out.trans (hx29Fill.trans hx29_1)))
  rw [hstep_eq]
  exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackPlacedBudget
