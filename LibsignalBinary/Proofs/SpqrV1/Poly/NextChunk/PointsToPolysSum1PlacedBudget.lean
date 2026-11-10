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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysDefs
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1Placed
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysFallbackLoop
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSumMult1Placed
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded `Poly::lagrange_sum` Helpers

Relocatable `[LibsignalPlacement]` verification of `Poly::add_assign` loops and `Poly::lagrange_sum`
setup, clone, and deallocation helpers threading `RustCliAllocBudget M`, `BudgetLimits`,
`LagrangeSumCloneEnv`, and `LagrangeSumDeallocEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement blkPC_416 blkPl_416 lsmpl lsρ sepWP_seq_lscl)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap (RustAlloc allocHookStack arrayAt)
open CryptoVerification.LibsignalTripleRatchet (sessionMemcpySpec)
open CryptoVerification.LibsignalSpqrV1 (GF16 Poly Pt)
open CryptoVerification.SpqrV1.Alloc
  (spqrMemcpySym spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly
  (gf16At gf16SliceAt polyOf ptAt)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre
   spqrRustDeallocSym)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (add1_ofNat_sum_pl addAssignCoeffs_cons_pl addAssignCoeffs_nil_left_pl beq_2m1_two_sum_pl
   beq_i1_n_sum_pl beq_lt_false_sum_pl bne_2m1_two_sum_pl
   extractLsb_hi_concat_sum_pl extractLsb_lo_concat_sum_pl gf16SliceAt_cons_pl
   gf16SliceAt_eq_pointsToBytes gf16SliceBytes gf16SliceBytes_length
   madd_basis_addr_sum_pl ofNat_pos_ne_zero polyOf_expose_sum_pl polyOf_fold_sum_pl
   sepWPp_seq_lscl_sum shl1_ofNat_sum_pl shl2_ofNat_sum_nat_pl shl2_ofNat_sum_pl
   sub2_ofNat_sum_add_pl sub2_ofNat_sum_pl ult_self_false_sum_pl xor_zext64_gf16_sum_pl
   zext16_trunc32_xor_zext64_gf16_sum_pl)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   FreeOnlyEvs RustCliAllocBudget RustLayoutOk coarseCostModel rustAllocEvents
   rustCliAllocNoOomSpec rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Block416SegBudget
  (sepWP_seg_416)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.EpiloguePlacedBudget
  (AllocContractsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (noAllocShimBudgetSpec noAllocShimSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyBudgetSpec)

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

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_sum1_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_eight_sum1_pl :
    (∃ k : Nat, 8 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨3, rfl⟩

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

attribute [local arm64_norm, local wp_norm]
  shl1_ofNat_sum_pl add1_ofNat_sum_pl sub2_ofNat_sum_pl sub2_ofNat_sum_add_pl
  xor_zext64_gf16_sum_pl zext16_trunc32_xor_zext64_gf16_sum_pl
  ult_self_false_sum_pl madd_basis_addr_sum_pl
  shl2_ofNat_sum_pl shl2_ofNat_sum_nat_pl
  extractLsb_lo_concat_sum_pl extractLsb_hi_concat_sum_pl

private theorem ptr_add_two_mul_succ (ptr : BitVec 64) (j : Nat) :
    (ptr + BitVec.ofNat 64 (2 * j)) + 2#64 = ptr + BitVec.ofNat 64 (2 * (j + 1)) := by
  have h2 : (2#64 : BitVec 64) = BitVec.ofNat 64 2 := rfl
  rw [show 2 * (j + 1) = 2 * j + 2 by omega, BitVec.ofNat_add, ← h2, BitVec.add_assoc]

/-! ## 1. Exact Allocator Event Envelopes for `lagrange_sum` Clone & Dealloc -/

/-- Per-iteration `Poly::clone` allocation event sequence (`+2668 -> +2736`, Block `416`):
    `2 * n` bytes at alignment `2`. -/
def lagrangeSumCloneEvents (n : Nat) : List AllocEvent :=
  rustAllocEvents (2 * n) 2

def LagrangeSumCloneEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = lagrangeSumCloneEvents n

theorem fitsEnv_lagrangeSumClone_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (n : Nat) :
    FitsEnv M lim st (LagrangeSumCloneEnv n) ↔ FitsEvents M lim st (lagrangeSumCloneEvents n) := by
  constructor
  · intro h
    exact h (lagrangeSumCloneEvents n) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (LagrangeSumCloneEnv 8) := by
  rw [fitsEnv_lagrangeSumClone_iff]
  dsimp only [lagrangeSumCloneEvents, rustAllocEvents, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-- Per-iteration `clonePtr` deallocation event sequence (`+2640 -> +2668 / +3908`, Block `416`):
    `2 * n` bytes at alignment `2`. -/
def lagrangeSumDeallocEvents (n : Nat) : List AllocEvent :=
  rustDeallocEvents (2 * n) 2

def LagrangeSumDeallocEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = lagrangeSumDeallocEvents n

theorem lagrangeSumDeallocEvents_freeOnly (n : Nat) : FreeOnlyEvs (lagrangeSumDeallocEvents n) :=
  FreeOnlyEvs.singleton 2 (2 * n)

theorem fitsEnv_lagrangeSumDealloc_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (n : Nat) :
    FitsEnv M lim st (LagrangeSumDeallocEnv n) ↔
      FitsEvents M lim st (lagrangeSumDeallocEvents n) := by
  constructor
  · intro h
    exact h (lagrangeSumDeallocEvents n) rfl
  · intro h evs hevs
    rw [hevs]
    exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (LagrangeSumDeallocEnv 8) := by
  rw [fitsEnv_lagrangeSumDealloc_iff]
  dsimp only [lagrangeSumDeallocEvents, rustDeallocEvents, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-! ## 2. Budget-Threaded `Poly::add_assign` Loops (`+3784 -> +2640`) -/

set_option maxHeartbeats 800000 in
/-- Budget-threaded `Poly::add_assign` push loop (`+3836 -> +3888 -> +2640`, `i = 0`). -/
theorem addAssignPushLoop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (pRest : List GF16) (j n : Nat)
      (_hne : pRest ≠ []) (_hjn : j + pRest.length = n) (_hn : n ≤ 0x0555555555555555)
      (s : State) (fsp accPtr clonePtr : BitVec 64)
      (_hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (_hpc : s.pc = (blkPl_416).base + 3836#64)
      (_hrun : s.status = .Running) (_hsp : s.sp = fsp)
      (_hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
      (_hx19 : s.readReg64 .x19 = BitVec.ofNat 64 j)
      (_hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
      (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * pRest.length))
      (_hx22 : s.readReg64 .x22 = clonePtr)
      (_hcont : ∀ s1 : State,
        s1.pc = (blkPl_416).base + 2640#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
        s1.readReg64 .x22 = clonePtr →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
          (A.pool lim st s1 ∗
           gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗
           ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post),
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
        (A.pool lim st s ∗
         memRegion (accPtr + BitVec.ofNat 64 (2 * j)) (2 * pRest.length) ∗
         gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 j) ∗ Frame) post
  | [], _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | p :: pTail, j, n, _, hjn, hn, s, fsp, accPtr, clonePtr, hfsp_align, Frame,
    hpc, hrun, hsp, hx1, hx19, hx20, hx21, hx22, hcont => by
    have hj_lt : j < n := by simp at hjn; omega
    have hult := ult_self_false_sum_pl j
    have hbeq := beq_lt_false_sum_pl hj_lt hn
    have hsub2 := sub2_ofNat_sum_pl pTail.length
    have hsub2_add := sub2_ofNat_sum_add_pl pTail.length
    have hbne2 := bne_2m1_two_sum_pl (m := pTail.length) (by simp at hjn; omega)
    have hacc_add : (accPtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        accPtr + BitVec.ofNat 64 (2 * (j + 1)) := ptr_add_two_mul_succ accPtr j
    have hclone_add : (clonePtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        clonePtr + BitVec.ofNat 64 (2 * (j + 1)) := ptr_add_two_mul_succ clonePtr j
    rw [List.length_cons] at hx21
    rw [show 2 * (p :: pTail).length = 2 + 2 * pTail.length by simp; omega,
        ProofLib.memRegion_split' (b := accPtr + BitVec.ofNat 64 (2 * j))
          (n := 2) (k := 2 * pTail.length) (b' := accPtr + BitVec.ofNat 64 (2 * (j + 1)))
          rfl hacc_add.symm (by simp at hjn; omega),
        ProofLib.memRegion_two (accPtr + BitVec.ofNat 64 (2 * j)),
        gf16SliceAt_cons_pl (clonePtr + BitVec.ofNat 64 (2 * j)) p pTail, hclone_add]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro u_acc
    unfold gf16At
    cases pTail with
    | nil =>
      apply sepWP_seg_416 (mid := (blkPl_416).base + 2640#64)
      intro _m_strip
      wp_steps 14
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
              List.length_nil, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
              List.length_nil, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ↓reduceIte])
        fun _m_real _hnsp => ?_
      refine SepWP.transport_budgetPool
        (_hnsp.toVmPreserved
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      have hj1 : j + 1 = n := by simp at hjn; omega
      simp only [gf16SliceAt_cons_pl, gf16SliceAt, arrayAt, gf16At, List.length_nil,
        Nat.mul_zero, Nat.zero_mul, ProofLib.memRegion_zero, sepConj_emp] at hcont ⊢
      refine SepWP.weaken_pre
        (by try simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2, hj1,
              List.length_nil, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ↓reduceIte]
            exact Entails.of_eq (by sep_ac_rfl))
        (hcont _
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx1, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx22, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_nil, ne_eq, not_true_eq_false, decide_false,
                Bool.false_eq_true, ↓reduceIte]))
    | cons p2 pTail' =>
      apply sepWP_seg_416 (mid := (blkPl_416).base + 3836#64)
      intro _m_strip
      wp_steps 13
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
              List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
              not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
              List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
              not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
        fun _m_real _hnsp => ?_
      refine SepWP.transport_budgetPool
        (_hnsp.toVmPreserved
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
      have hjn' : (j + 1) + (p2 :: pTail').length = n := by simp at hjn ⊢; omega
      refine SepWP.weaken_pre
        (by try simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
              List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
              not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]
            exact Entails.of_eq (by sep_ac_rfl))
        (addAssignPushLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
          (p2 :: pTail') (j + 1) n hne' hjn' hn _ fsp accPtr clonePtr hfsp_align
          (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           ((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗ Frame)
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx1, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx22, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]) ?_)
      intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
      have hacc_cons :
          gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
          (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
        rw [gf16SliceAt_cons_pl, gf16At, hacc_add]
      have hclone_cons :
          gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
          (((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
        rw [gf16SliceAt_cons_pl, gf16At, hclone_add]
      refine SepWP.weaken_pre
        (Entails.of_eq (by rw [hacc_cons, hclone_cons]; sep_ac_rfl))
        (hcont s1 hpc1 hrun1 hsp1
          (by rw [htr1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hvregs1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          hx1_1 hx22_1
          (by rw [hx24_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hx25_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hx26_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hx27_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hx28_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by rw [hx29_1]; simp only [arm64_norm, wp_norm, hsp, hult, hbeq, hsub2, hsub2_add, hbne2,
                List.length_cons, ne_eq, Nat.succ_ne_zero, Nat.add_one_ne_zero,
                not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]))

set_option maxHeartbeats 800000 in
/-- Budget-threaded `Poly::add_assign` XOR loop (`+3804 -> +2640`, `i > 0`). -/
theorem addAssignXorLoop_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop} :
    ∀ (outRest pRest : List GF16) (j n : Nat)
      (_hne : pRest ≠ []) (_hlen_eq : outRest.length = pRest.length)
      (_hjn : j + pRest.length = n) (_hn : n ≤ 0x0555555555555555)
      (s : State) (fsp accPtr clonePtr : BitVec 64)
      (_hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
      (_hpc : s.pc = (blkPl_416).base + 3804#64)
      (_hrun : s.status = .Running) (_hsp : s.sp = fsp)
      (_hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
      (_hx19 : s.readReg64 .x19 = BitVec.ofNat 64 j)
      (_hx20 : s.readReg64 .x20 = BitVec.ofNat 64 n)
      (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 (2 * pRest.length))
      (_hx22 : s.readReg64 .x22 = clonePtr)
      (_hcont : ∀ s1 : State,
        s1.pc = (blkPl_416).base + 2640#64 →
        s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
        s1.readReg64 .x22 = clonePtr →
        s1.readReg64 .x24 = s.readReg64 .x24 →
        s1.readReg64 .x25 = s.readReg64 .x25 →
        s1.readReg64 .x26 = s.readReg64 .x26 →
        s1.readReg64 .x27 = s.readReg64 .x27 →
        s1.readReg64 .x28 = s.readReg64 .x28 →
        s1.readReg64 .x29 = s.readReg64 .x29 →
        SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
          (A.pool lim st s1 ∗
           gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) (Poly.addAssignCoeffs outRest pRest) ∗
           gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
           ((fsp + 664#64) ↦₆₄ accPtr) ∗ Frame) post),
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
        (A.pool lim st s ∗
         gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j)) outRest ∗
         gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) pRest ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗ Frame) post
  | _, [], _, _, hne, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | [], _ :: _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by simp at hlen
  | o :: oTail, p :: pTail, j, n, _, hlen_eq, hjn, hn, s, fsp, accPtr, clonePtr,
    hfsp_align, Frame, hpc, hrun, hsp, hx1, hx19, hx20, hx21, hx22, hcont => by
    have hsub2 := sub2_ofNat_sum_pl pTail.length
    have hsub2_add := sub2_ofNat_sum_add_pl pTail.length
    have hbeq2 := beq_2m1_two_sum_pl (m := pTail.length) (by simp at hjn; omega)
    have hacc_add : (accPtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        accPtr + BitVec.ofNat 64 (2 * (j + 1)) := ptr_add_two_mul_succ accPtr j
    have hclone_add : (clonePtr + BitVec.ofNat 64 (2 * j)) + 2#64 =
        clonePtr + BitVec.ofNat 64 (2 * (j + 1)) := ptr_add_two_mul_succ clonePtr j
    rw [List.length_cons] at hx21
    rw [gf16SliceAt_cons_pl (accPtr + BitVec.ofNat 64 (2 * j)) o oTail, hacc_add,
        gf16SliceAt_cons_pl (clonePtr + BitVec.ofNat 64 (2 * j)) p pTail, hclone_add]
    unfold gf16At
    cases pTail with
    | nil =>
      cases oTail with
      | nil =>
        apply sepWP_seg_416 (mid := (blkPl_416).base + 2640#64)
        intro _m_strip
        wp_steps 8
        refine SepWP.done
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
          fun _m_real _hnsp => ?_
        refine SepWP.transport_budgetPool
          (_hnsp.toVmPreserved
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte]))
          (hnext := ?_)
        simp only [State.setMem_setMem]
        simp only [addAssignCoeffs_cons_pl, addAssignCoeffs_nil_left_pl,
          gf16SliceAt_cons_pl, gf16SliceAt, arrayAt, gf16At, sepConj_emp] at hcont ⊢
        refine SepWP.weaken_pre
          (by try simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte]
              exact Entails.of_eq (by sep_ac_rfl))
          (hcont _
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx1, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx22, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hsub2, hsub2_add, hbeq2,
                  List.length_nil, decide_true, Bool.false_eq_true, ↓reduceIte]))
      | cons _ _ => simp at hlen_eq
    | cons p2 pTail' =>
      cases oTail with
      | nil => simp at hlen_eq
      | cons o2 oTail' =>
        have hne' : p2 :: pTail' ≠ [] := List.cons_ne_nil _ _
        have hlen_eq' : (o2 :: oTail').length = (p2 :: pTail').length := by
          simp at hlen_eq ⊢; omega
        have hjn' : (j + 1) + (p2 :: pTail').length = n := by simp at hjn ⊢; omega
        have hj1_lt : j + 1 < n := by simp at hjn'; omega
        have hult1 : (BitVec.ofNat 64 (j + 1)).ult (BitVec.ofNat 64 n) = true := by
          simp only [BitVec.ult, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), decide_eq_true_eq]
          omega
        apply sepWP_seg_416 (mid := (blkPl_416).base + 3804#64)
        intro _m_strip
        wp_steps 8
        conv =>
          arg 3
          simp only [arm64_norm, wp_norm, hsub2, hsub2_add, hbeq2, List.length_cons,
            Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]
        wp_steps 2
        refine SepWP.done
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
          fun _m_real _hnsp => ?_
        refine SepWP.transport_budgetPool
          (_hnsp.toVmPreserved
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]))
          (hnext := ?_)
        simp only [State.setMem_setMem]
        refine SepWP.weaken_pre
          (by try simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]
              exact Entails.of_eq (by sep_ac_rfl))
          (addAssignXorLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
            (o2 :: oTail') (p2 :: pTail') (j + 1) n
            hne' hlen_eq' hjn' hn _ fsp accPtr clonePtr hfsp_align
            (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (GF16.add o p).value) ∗
             ((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗ Frame)
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx1, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by simp only [arm64_norm, wp_norm, hrun, hsp, hx20, hx22, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]) ?_)
        intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
        have hacc_cons :
            gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * j))
              (Poly.addAssignCoeffs (o :: o2 :: oTail') (p :: p2 :: pTail')) =
            (((accPtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ (GF16.add o p).value) ∗
             gf16SliceAt (accPtr + BitVec.ofNat 64 (2 * (j + 1)))
               (Poly.addAssignCoeffs (o2 :: oTail') (p2 :: pTail'))) := by
          rw [addAssignCoeffs_cons_pl, gf16SliceAt_cons_pl, gf16At, hacc_add]
        have hclone_cons :
            gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * j)) (p :: p2 :: pTail') =
            (((clonePtr + BitVec.ofNat 64 (2 * j)) ↦₁₆ p.value) ∗
             gf16SliceAt (clonePtr + BitVec.ofNat 64 (2 * (j + 1))) (p2 :: pTail')) := by
          rw [gf16SliceAt_cons_pl, gf16At, hclone_add]
        refine SepWP.weaken_pre
          (Entails.of_eq (by rw [hacc_cons, hclone_cons]; sep_ac_rfl))
          (hcont s1 hpc1 hrun1 hsp1
            (by rw [htr1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hvregs1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            hx1_1 hx22_1
            (by rw [hx24_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hx25_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hx26_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hx27_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hx28_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte])
            (by rw [hx29_1]; simp only [arm64_norm, wp_norm, hsp, hx20, hsub2, hsub2_add, hbeq2, hult1,
                  List.length_cons, Nat.succ_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte]))

/-- Budget-threaded entry to `Poly::add_assign` (`+3784 -> +2640`) on iteration `i = 0`. -/
theorem addAssignFirst_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (pCs : List GF16) (n : Nat)
    (hne : pCs ≠ []) (hlen : pCs.length = n) (hn : n ≤ 0x0555555555555555)
    (s : State) (fsp accPtr clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3784#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_416).base + 2640#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16SliceAt accPtr (Poly.addAssignCoeffs [] pCs) ∗
         gf16SliceAt clonePtr pCs ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       memRegion accPtr (2 * n) ∗
       gf16SliceAt clonePtr pCs ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ 0#64) ∗ Frame) post := by
  have hacc0 : accPtr + BitVec.ofNat 64 (2 * 0) = accPtr := BitVec.add_zero accPtr
  have hclone0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := BitVec.add_zero clonePtr
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3836#64)
  intro _m_strip
  wp_steps 5
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre
    (by try simp only [arm64_norm, wp_norm, hrun, hsp]
        rw [← hlen, ← hacc0, ← hclone0]
        exact Entails.of_eq (by sep_ac_rfl))
    (addAssignPushLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
      pCs 0 n hne (by omega) hn _ fsp accPtr clonePtr hfsp_align
      (((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * pCs.length)) ∗ Frame)
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hlen])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hlen])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx22]) ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hacc0, hclone0, hlen]
  simp only [addAssignCoeffs_nil_left_pl] at hcont
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont s1 hpc1 hrun1 hsp1
      (by rw [htr1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hvregs1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      hx1_1 hx22_1
      (by rw [hx24_1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hx25_1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hx26_1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hx27_1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hx28_1]; simp only [arm64_norm, wp_norm, hrun, hsp])
      (by rw [hx29_1]; simp only [arm64_norm, wp_norm, hrun, hsp]))

/-- Budget-threaded entry to `Poly::add_assign` (`+3784 -> +2640`) on iterations `i > 0`. -/
theorem addAssignNext_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (outCs pCs : List GF16) (n : Nat)
    (hne : pCs ≠ []) (hout_len : outCs.length = n) (hp_len : pCs.length = n)
    (hn : n ≤ 0x0555555555555555)
    (s : State) (fsp accPtr clonePtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 3784#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_416).base + 2640#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x1 = BitVec.ofNat 64 (2 * n) →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         gf16SliceAt accPtr (Poly.addAssignCoeffs outCs pCs) ∗
         gf16SliceAt clonePtr pCs ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       gf16SliceAt accPtr outCs ∗
       gf16SliceAt clonePtr pCs ∗
       ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 664#64) ↦₆₄ accPtr) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame) post := by
  have hn_pos : 0 < n := by have := List.length_pos_iff.mpr hne; omega
  have hult0 : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 n) = true := by
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 0 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), decide_eq_true_eq]
    omega
  have hacc0 : accPtr + BitVec.ofNat 64 (2 * 0) = accPtr := BitVec.add_zero accPtr
  have hclone0 : clonePtr + BitVec.ofNat 64 (2 * 0) = clonePtr := BitVec.add_zero clonePtr
  apply sepWP_seg_416 (mid := (blkPl_416).base + 3804#64)
  intro _m_strip
  wp_steps 7
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre
    (by try simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte]
        rw [← hacc0, ← hclone0]
        exact Entails.of_eq (by sep_ac_rfl))
    (addAssignXorLoop_placed_sepWP (M := M) (A := A) (lim := lim) (st := st)
      outCs pCs 0 n hne (by omega) (by omega) hn
      _ fsp accPtr clonePtr hfsp_align
      (((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
       ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 672#64) ↦₆₄ BitVec.ofNat 64 n) ∗ Frame)
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hult0, hp_len, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx22, hult0, ↓reduceIte]) ?_)
  intro s1 hpc1 hrun1 hsp1 htr1 hvregs1 hx1_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1
  rw [hacc0, hclone0]
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hcont s1 hpc1 hrun1 hsp1
      (by rw [htr1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hvregs1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      hx1_1 hx22_1
      (by rw [hx24_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hx25_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hx26_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hx27_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hx28_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte])
      (by rw [hx29_1]; simp only [arm64_norm, wp_norm, hrun, hsp, hult0, ↓reduceIte]))

/-! ## 3. Budget-Threaded `Poly::lagrange_sum` Setup, Clone, and Dealloc Helpers -/

/-- Budget-threaded setup block of `Poly::lagrange_sum` (`+2608 -> +2668`, Block `416`). -/
theorem lagrangeSumSetup_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {ret : BitVec 64} {post : State → SepProp → Prop}
    (n : Nat)
    (s : State) (fsp accPtr basisPtr ptVecPtr cIdx v27 : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (u16 u64 u72 u80 u656 u664 u672 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2608#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx0 : s.readReg64 .x0 = accPtr)
    (hx20 : s.readReg64 .x20 = cIdx)
    (hx24 : s.readReg64 .x24 = basisPtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : s.readReg64 .x26 = ptVecPtr)
    (hx27 : s.readReg64 .x27 = v27)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hx29 : s.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ s1 : State,
      s1.pc = (blkPl_416).base + 2668#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 0 →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim st s1 ∗
         ((fsp + 16#64) ↦₆₄ cIdx) ∗
         ((fsp + 64#64) ↦₆₄ v27) ∗
         ((fsp + 72#64) ↦₆₄ basisPtr) ∗
         ((fsp + 80#64) ↦₆₄ ptVecPtr) ∗
         ((fsp + 656#64) ↦₆₄ BitVec.ofNat 64 n) ∗
         ((fsp + 664#64) ↦₆₄ accPtr) ∗
         ((fsp + 672#64) ↦₆₄ 0#64) ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       ((fsp + 16#64) ↦₆₄ u16) ∗
       ((fsp + 64#64) ↦₆₄ u64) ∗
       ((fsp + 72#64) ↦₆₄ u72) ∗
       ((fsp + 80#64) ↦₆₄ u80) ∗
       ((fsp + 656#64) ↦₆₄ u656) ∗
       ((fsp + 664#64) ↦₆₄ u664) ∗
       ((fsp + 672#64) ↦₆₄ u672) ∗ Frame) post := by
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2668#64)
  intro _m_strip
  wp_steps 8
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    fun _m_real _hnsp => ?_
  refine SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.weaken_pre
    (by try simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx20, hx24, hx25, hx26, hx27]
        exact Entails.of_eq (by sep_ac_rfl))
    (hcont _
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx24])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx25])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx26])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx27])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx28])
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx29]))

set_option maxHeartbeats 800000 in
private theorem lagrangeSumClone_alloc_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (i n : Nat) (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (s0 s : State) (fsp basisPtr ptVecPtr v27 cap ptr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
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
    (hcont : ∀ (sm : State) (Pm : SepProp) (clonePtr : BitVec 64),
      clonePtr ≠ 0#64 →
      sm.pc = (blkPl_416).base + 2704#64 →
      sm.status = .Running → sm.sp = fsp → sm.trace = s0.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x0 = clonePtr →
      sm.readReg64 .x19 = ptr →
      sm.readReg64 .x20 = BitVec.ofNat 64 n →
      sm.readReg64 .x21 = BitVec.ofNat 64 i →
      sm.readReg64 .x23 = BitVec.ofNat 64 (2 * n) →
      sm.readReg64 .x24 = basisPtr →
      sm.readReg64 .x25 = BitVec.ofNat 64 n →
      sm.readReg64 .x26 = ptVecPtr →
      sm.readReg64 .x27 = v27 →
      sm.readReg64 .x28 = 24#64 →
      sm.readReg64 .x29 = fsp + 1104#64 →
      (Pm ⊢
        A.pool lim (M.stepEvents (lagrangeSumCloneEvents n) st) sm ∗
        A.live clonePtr (2 * n) 2 ∗
        memRegion clonePtr (2 * n) ∗
        ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
        ((basisPtr + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ ptr) ∗
        ((basisPtr + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        stackAt fsp allocHookStack ∗ Frame) →
      post sm Pm) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 2704#64) s
      (A.pool lim st s ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ ptr) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       stackAt fsp allocHookStack ∗ Frame)
      post := by
  obtain ⟨hn_ne0, _h2n_ne0⟩ := ofNat_pos_ne_zero hn_pos hn
  have hn_eq0 : (BitVec.ofNat 64 n == 0#64) = false := hn_ne0
  have hlayout2n : RustLayoutOk (2 * n) 2 := ⟨⟨by omega, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have hfit_evs : FitsEvents M lim st (rustAllocEvents (2 * n) 2) :=
    (fitsEnv_lagrangeSumClone_iff n).mp hfit
  have hfit_ev : FitsEvent M lim st (.alloc (2 * n)) := by
    have hle2 : 2 ≤ 2 * n := by omega
    simpa [rustAllocEvents, hle2] using hfit_evs
  rcases hfit_ev with ⟨_hwmax, henf, hram, hva⟩
  have h2n_toNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := Nat.mod_eq_of_lt (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0
  wp_steps 8
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf0 : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *]
  have htr_sf0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  wp_steps_sync_416 (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc (2 * n, 2, st)
  clear halloc
  have hoom : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have htr_sf1 : sf_1.trace = s0.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf_1).2.1
    simpa [arm64_norm, wp_norm, htr_sf0] using ht
  have hsp_sf1 : sf_1.sp = fsp := by
    simp only [arm64_norm, wp_norm, hsp_sf0, *]
  refine SepWP.done hpc_sf_1 hrun_sf_1 ?_
  refine hcont sf_1 _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom hpc_sf_1 hrun_sf_1 hsp_sf1 htr_sf1
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    rfl
    (by simp only [arm64_norm, wp_norm, Reg.x19, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x23, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp, hx21, hx24, hn_eq0, Bool.false_eq_true, ↓reduceIte, *])
    ?_
  dsimp only [lagrangeSumCloneEvents]
  try simp only [arm64_norm, wp_norm, Bool.false_eq_true, ↓reduceIte, h2n_toNat, hsp_sf1, hsp_sf0]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem lagrangeSumClone_memcpy_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st1 : M.σ}
    {ext : String → Option (State → State)}
    {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (i n : Nat) (pt : Pt) (poly : Poly)
    (hn : n ≤ 0x0555555555555555) (hplen : poly.coefficients.length = n)
    (s0 sm : State) (fsp basisPtr ptVecPtr v27 clonePtr ptr u120 u128 : BitVec 64)
    (hclone_ne : clonePtr ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : sm.pc = (blkPl_416).base + 2704#64)
    (hrun : sm.status = .Running) (hsp : sm.sp = fsp) (htrace : sm.trace = s0.trace)
    (hx0 : sm.readReg64 .x0 = clonePtr)
    (hx19 : sm.readReg64 .x19 = ptr)
    (hx20 : sm.readReg64 .x20 = BitVec.ofNat 64 n)
    (hx21 : sm.readReg64 .x21 = BitVec.ofNat 64 i)
    (hx23 : sm.readReg64 .x23 = BitVec.ofNat 64 (2 * n))
    (hx24 : sm.readReg64 .x24 = basisPtr)
    (hx25 : sm.readReg64 .x25 = BitVec.ofNat 64 n)
    (hx26 : sm.readReg64 .x26 = ptVecPtr)
    (hx27 : sm.readReg64 .x27 = v27)
    (hx28 : sm.readReg64 .x28 = 24#64)
    (hx29 : sm.readReg64 .x29 = fsp + 1104#64)
    (hcont : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = (blkPl_416).base + 2736#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs sm →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 pt.y.value →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      (P1 ⊢
        A.pool lim st1 s1 ∗
        gf16SliceAt clonePtr poly.coefficients ∗
        (ptr ↦ₛ gf16SliceBytes poly.coefficients) ∗
        ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
        ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
        ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
        stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 2736#64) sm
      (A.pool lim st1 sm ∗
       memRegion clonePtr (2 * n) ∗
       (ptr ↦ₛ gf16SliceBytes poly.coefficients) ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗
       stackAt fsp allocHookStack ∗ Frame)
      post := by
  have hbeq_oom : (clonePtr == 0#64) = false := beq_eq_false_iff_ne.mpr hclone_ne
  have h2n_toNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := Nat.mod_eq_of_lt (by omega)
  have hlen_bytes : (gf16SliceBytes poly.coefficients).length = 2 * n := by
    rw [gf16SliceBytes_length, hplen]
  have hmemcpy := hA.session_memcpy_ok 4096
  dsimp only [sessionMemcpyBudgetSpec, sessionMemcpySpec] at hmemcpy
  clear hA
  unfold ptAt
  rw [← hlen_bytes]
  apply sepWP_seg_416 (mid := lsρ spqrMemcpySym)
  intro _m_strip0
  wp_steps 7
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hmemcpy (clonePtr, ptr, gf16SliceBytes poly.coefficients)
  clear hmemcpy
  have hsp_sf : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *]
  have htr_sf : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *]
  refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
  apply sepWP_seg_416 (mid := (blkPl_416).base + 2736#64)
  intro _m_strip1
  wp_steps 2
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved (by simp only [arm64_norm, wp_norm, hsp_sf, *]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    (by simp only [arm64_norm, wp_norm, hsp_sf, *]) ?_
  refine hcont _ _
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    (by simp only [arm64_norm, wp_norm, hsp_sf, *])
    (by simp only [arm64_norm, wp_norm, htr_sf, *])
    (by simp only [arm64_norm, wp_norm, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x21, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x0, Reg.x22, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hsp, hx0, hx21, hx23, hbeq_oom, Bool.false_eq_true, ↓reduceIte, *])
    ?_
  rw [← gf16SliceAt_eq_pointsToBytes clonePtr poly.coefficients]
  have hfold_pt :
      (((ptVecPtr + BitVec.ofNat 64 (4 * i)) ↦₁₆ pt.x.value) ∗
       ((ptVecPtr + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ pt.y.value)) =
      ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) := rfl
  try simp only [arm64_norm, wp_norm, hsp_sf, hsp, hx21, hx23]
  rw [← hfold_pt]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Budget-threaded per-iteration clone and `pt.y` load (`+2668 -> +2736`, Block `416`). -/
theorem lagrangeSumClone_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (i n : Nat) (pt : Pt) (poly : Poly)
    (hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555) (hplen : poly.coefficients.length = n)
    (s0 s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp basisPtr ptVecPtr v27 u120 u128 : BitVec 64)
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
    (hcont : ∀ s1 clonePtr,
      LibsignalCodeLoaded lsmpl s1.mem →
      clonePtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 2736#64 →
      s1.status = .Running → s1.sp = fsp → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 n →
      s1.readReg64 .x21 = BitVec.zeroExtend 64 pt.y.value →
      s1.readReg64 .x22 = clonePtr →
      s1.readReg64 .x24 = basisPtr →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = v27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = fsp + 1104#64 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (lagrangeSumCloneEvents n) st) s1 ∗
         A.live clonePtr (2 * n) 2 ∗
         gf16SliceAt clonePtr poly.coefficients ∗
         polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
         ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
         ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       polyOf A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_left
      (polyOf_expose_sum_pl A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) poly n hn_pos hplen))) ?_
  conv =>
    arg 4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  apply SepWPp.exists_elim; intro cap
  apply SepWPp.exists_elim; intro ptr
  apply SepWPp.pure_left; rintro ⟨hle, hcap_lt, hptr, hcap⟩
  apply sepWPp_seq_lscl_sum hcl (mid := (blkPl_416).base + 2704#64)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumClone_alloc_seg hA i n hn_pos hn s0 s fsp basisPtr ptVecPtr v27 cap ptr
      hfsp_align
      (A.repAlloc.live ptr (cap.toNat * 2) 2 ∗
       (ptr ↦ₛ gf16SliceBytes poly.coefficients) ∗
       memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ∗
       ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
       ((fsp + 120#64) ↦₆₄ u120) ∗
       ((fsp + 128#64) ↦₆₄ u128) ∗ Frame)
      hpc hrun hsp htrace hx21 hx24 hx25 hx26 hx27 hx28 hx29 hfit ?_)
  intro sm Pm clonePtr hclone hpcm hrunm hspm htrm hvregsm hx0m hx19m hx20m hx21m hx23m
    hx24m hx25m hx26m hx27m hx28m hx29m hPm hcl1
  refine SepWPp.weaken_pre hPm ?_
  apply sepWPp_seq_lscl_sum hcl1 (mid := (blkPl_416).base + 2736#64)
  refine SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (lagrangeSumClone_memcpy_seg hA i n pt poly hn hplen s0 sm
      fsp basisPtr ptVecPtr v27 clonePtr ptr u120 u128
      hclone hfsp_align
      (A.live clonePtr (2 * n) 2 ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ ptr) ∗
       ((basisPtr + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       A.repAlloc.live ptr (cap.toNat * 2) 2 ∗
       memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2) ∗ Frame)
      hpcm hrunm hspm htrm hx0m hx19m hx20m hx21m hx23m hx24m hx25m hx26m hx27m hx28m hx29m ?_)
  intro s1 P1 hpc1 hrun1 hsp1 htr1 hvregs1 hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1
    hx28_1 hx29_1 hP1 hcl2
  have hfold_poly := polyOf_fold_sum_pl A.repAlloc (basisPtr + BitVec.ofNat 64 (24 * i)) cap ptr
    poly n hplen hle hcap_lt hptr hcap
  refine SepWPp.weaken_pre (Entails.trans hP1 ?_)
    (hcont s1 clonePtr hcl2 hclone hpc1 hrun1 hsp1 htr1 (hvregs1.trans hvregsm)
      hx20_1 hx21_1 hx22_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1)
  refine Entails.trans (Entails.of_eq (show _ =
    (((basisPtr + BitVec.ofNat 64 (24 * i)) ↦₆₄ cap) ∗
     ((basisPtr + BitVec.ofNat 64 (24 * i) + 8#64) ↦₆₄ ptr) ∗
     ((basisPtr + BitVec.ofNat 64 (24 * i) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
     A.repAlloc.live ptr (cap.toNat * 2) 2 ∗
     (ptr ↦ₛ gf16SliceBytes poly.coefficients) ∗
     memRegion (ptr + BitVec.ofNat 64 (n * 2)) ((cap.toNat - n) * 2)) ∗
    (A.pool lim (M.stepEvents (lagrangeSumCloneEvents n) st) s1 ∗
     A.live clonePtr (2 * n) 2 ∗
     gf16SliceAt clonePtr poly.coefficients ∗
     ptAt pt (ptVecPtr + BitVec.ofNat 64 (4 * i)) ∗
     ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
     ((fsp + 128#64) ↦₆₄ BitVec.ofNat 64 (2 * n)) ∗
     stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  exact Entails.trans (sepConj_mono_left hfold_poly) (Entails.of_eq (by sep_ac_rfl))

set_option maxHeartbeats 800000 in
/-- Budget-threaded per-iteration deallocation of `clonePtr` and loop counter step
    (`+2640 -> +2668 / +3908`, Block `416`), preserving `LibsignalCodeLoaded`. -/
theorem lagrangeSumDeallocNext_placed_sepWP [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {ret : BitVec 64} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (cs : List GF16) (i m n : Nat)
    (_hn_pos : 0 < n) (hn : n ≤ 0x0555555555555555)
    (hcs_len : cs.length = n) (him : (i + 1) + m = n)
    (s : State) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (fsp clonePtr : BitVec 64)
    (_hclone_ne : clonePtr ≠ 0#64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 2640#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 (2 * n))
    (hx22 : s.readReg64 .x22 = clonePtr)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ s1 : State,
      LibsignalCodeLoaded lsmpl s1.mem →
      s1.pc = (if m = 0 then
          (blkPl_416).base + 3908#64
        else
          (blkPl_416).base + 2668#64) →
      s1.status = .Running → s1.sp = fsp → s1.trace = s.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x21 = BitVec.ofNat 64 (i + 1) →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s1
        (A.pool lim (M.stepEvents (lagrangeSumDeallocEvents n) st) s1 ∗
         ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
         stackAt fsp allocHookStack ∗ Frame) post) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext)) ret s
      (A.pool lim st s ∗
       A.live clonePtr (2 * n) 2 ∗
       gf16SliceAt clonePtr cs ∗
       ((fsp + 120#64) ↦₆₄ BitVec.ofNat 64 i) ∗
       stackAt fsp allocHookStack ∗ Frame) post := by
  apply sepWP_seq_lscl
    (mid := if m = 0 then (blkPl_416).base + 3908#64 else (blkPl_416).base + 2668#64) hcl
  have hdealloc := hA.dealloc_ok
  dsimp only [rustCliDeallocBudgetSpec] at hdealloc
  clear hA
  have h2n_toNat : (BitVec.ofNat 64 (2 * n)).toNat = 2 * n := Nat.mod_eq_of_lt (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hmem : gf16SliceAt clonePtr cs ⊢ memRegion clonePtr (2 * n) := by
    rw [gf16SliceAt_eq_pointsToBytes]
    have hlen : (gf16SliceBytes cs).length = 2 * n := by rw [gf16SliceBytes_length, hcs_len]
    rw [← hlen]
    exact pointsToBytes_entails_memRegion clonePtr _
  have hbeq := beq_i1_n_sum_pl him hn
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hmem))) ?_
  apply sepWP_seg_416 (mid := lsρ spqrRustDeallocSym)
  intro _m_strip0
  wp_steps 4
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    (by simp only [arm64_norm, wp_norm, hrun, hsp])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved (by simp only [arm64_norm, wp_norm, hrun, hsp]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_conv_pre => simp only [arm64_norm, wp_norm, hrun, hsp]
  wp_call hdealloc (clonePtr, 2 * n, 2, st)
  clear hdealloc
  have htr_sf : sf.trace = s.trace := by
    have ht := (by assumption : AllocCallPreserved _ sf).2.1
    simpa [arm64_norm, wp_norm, hsp] using ht
  have hsp_sf : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hsp, *]
  have hx25_sf : sf.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 n := by
    simp only [arm64_norm, wp_norm, Reg.x25, hsp, hx25, *]
  apply sepWP_seg_416
    (mid := if m = 0 then (blkPl_416).base + 3908#64 else (blkPl_416).base + 2668#64)
  intro _m_strip1
  wp_steps 4
  by_cases hm0 : m = 0
  · subst hm0
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
      fun _m_real1 _hnsp1 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp1.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte]) ?_
    intro hcl1
    dsimp only [lagrangeSumDeallocEvents] at hcont
    refine SepWP.weaken_pre
      (by try simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte]
          exact Entails.of_eq (by sep_ac_rfl))
      (hcont _ hcl1
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, htr_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, Reg.x24, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x25, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, decide_true, ↓reduceIte, *]))
  · refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
            decide_false, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
            decide_false, Bool.false_eq_true, ↓reduceIte])
      fun _m_real1 _hnsp1 => ?_
    refine SepWP.transport_budgetPool
      (_hnsp1.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
            decide_false, Bool.false_eq_true, ↓reduceIte])
      (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
            decide_false, Bool.false_eq_true, ↓reduceIte]) ?_
    intro hcl1
    dsimp only [lagrangeSumDeallocEvents] at hcont
    refine SepWP.weaken_pre
      (by try simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
            decide_false, Bool.false_eq_true, ↓reduceIte]
          exact Entails.of_eq (by sep_ac_rfl))
      (hcont _ hcl1
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, htr_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, hrun_sf, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, Reg.x24, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x25, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x26, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x27, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x28, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *])
        (by simp only [arm64_norm, wp_norm, Reg.x29, hrun, hrun_sf, hsp, hsp_sf, hx25_sf, hbeq, hm0,
              decide_false, Bool.false_eq_true, ↓reduceIte, *]))

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSum1PlacedBudget
