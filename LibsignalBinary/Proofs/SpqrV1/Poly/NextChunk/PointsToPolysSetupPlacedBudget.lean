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
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetup
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlaced
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SpqrV1.Poly.LagrangePrepare.Loop
import ProofLib.SepLogic.WPp

/-!
# `<PolyEncoder as Encoder>::next_chunk` (Block `416`): Budget-Threaded Placed `pt_vec` Setup

Relocatable `[LibsignalPlacement]` verification of `fillPtVecLoop`, `checkPtVecLoop`, and
`setupPtVec_placed_sepWPp` (`+976 -> +1136`) threading `RustCliAllocBudget M`, `BudgetLimits`, and
`SetupPtVecEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification
  (LibsignalPlacement blkPC_416 blkPl_416 lsρ)
open scoped CryptoVerification
open scoped CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
  (allocHookStack arrayAt vecAt vecBuf vecHeader vecOf)
open CryptoVerification.LibsignalSpqrV1 (GF16 Point PolyEncoder)
open CryptoVerification.SpqrV1.Alloc (spqrRustAllocSym spqrRustNoAllocShimSym)
open CryptoVerification.SpqrV1.Poly
  (gf16Align gf16At gf16SliceAt gf16Stride pointOf ptAt ptSliceAt ptStride)
open CryptoVerification.SpqrV1.Poly.ComputeAt
  (readReg32_setMem_pre readReg64_setMem_pre readReg_setMem_pre sp_setMem_pre)
open CryptoVerification.SpqrV1.Poly.LagrangePrepare
  (readReg32_setMem_setPC_pre readReg32_setPC_pre readReg64_setMem_setPC_pre readReg64_setPC_pre
   readReg_setMem_setPC_pre readReg_setPC_pre sp_setMem_setPC_pre sp_setPC_pre)
open CryptoVerification.SpqrV1.Poly.NextChunk
  (memRegion_split_pt ptVecBufAt ptVecBufAt_nil sepWPp_pure_mid)
open LibsignalBinary.Heap
  (AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvent FitsEvents FitsStep
   RustCliAllocBudget RustLayoutOk coarseCostModel rustAllocEvents rustCliAllocNoOomSpec)
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

@[local arm64_norm, local wp_norm] private theorem exists_pow_two_eq_two_setup_pl :
    (∃ k : Nat, 2 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨1, rfl⟩

private theorem bv_shl1_eq_mul2 (v : BitVec 64) : v <<< 1#64 = v * 2#64 := by bv_bits
private theorem bv_shl2_eq_mul4 (v : BitVec 64) : v <<< 2#64 = v * 4#64 := by bv_bits

private theorem ofNat64_beq_false {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  apply Bool.eq_false_iff.mpr; intro h0
  have h1 := congrArg BitVec.toNat (eq_of_beq h0)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact hne h1

private theorem ofNat64_bne_true {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = true := by
  rw [bne_iff_ne]; intro h0
  have h1 := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact hne h1

private theorem ofNat64_sub_beq_zero_false {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0#64) = false := by
  apply Bool.eq_false_iff.mpr; intro h0
  have h1 : BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 b = 0#64 + BitVec.ofNat 64 b :=
    congrArg (· + BitVec.ofNat 64 b) (eq_of_beq h0)
  rw [BitVec.sub_add_cancel, BitVec.zero_add] at h1
  have h2 := congrArg BitVec.toNat h1
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact hne h2

/-! ## 1. Exact Allocator Event Envelope for `setupPtVec` (`+976..+1136`) -/

/-- Exact allocator event sequence of `setupPtVec` (`+976..+1136`, Block `416`) for a `Point`
    of length `n`: zero events when `n = 0`, and `rustAllocEvents (4 * n) 2` when `n > 0`. -/
def setupPtVecEvents (n : Nat) : List AllocEvent :=
  if n = 0 then [] else rustAllocEvents (4 * n) 2

def SetupPtVecEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = setupPtVecEvents n

theorem fitsEnv_setupPtVec_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} (n : Nat) :
    FitsEnv M lim st (SetupPtVecEnv n) ↔ FitsEvents M lim st (setupPtVecEvents n) := by
  constructor
  · intro h; exact h (setupPtVecEvents n) rfl
  · intro h evs hevs; rw [hevs]; exact h

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (SetupPtVecEnv 0) := by
  rw [fitsEnv_setupPtVec_iff]
  dsimp only [setupPtVecEvents, ↓reduceIte, FitsEvents]
  trivial

example :
    FitsEnv coarseCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024, physCap := 256 * 1024 * 1024 }
      coarseCostModel.init (SetupPtVecEnv 8) := by
  rw [fitsEnv_setupPtVec_iff]
  dsimp only [setupPtVecEvents, rustAllocEvents, FitsEvents, FitsEvent, FitsStep,
    AllocEvent.withinMaxAlloc, AllocCostModel.step]
  exact ⟨⟨by decide, by decide, by decide, by decide⟩, trivial⟩

/-! ## 2. Budget-Threaded `fillPtVecLoop` & `checkPtVecLoop` (`+1064..+1136`) -/

/-- One step of the budget-threaded `enumeratePts` fill loop (`+1064..+1084`). -/
theorem fillPtVecLoop_step_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (srcBase dstBase : BitVec 64)
    (i n : Nat) (y : GF16) (rest : List GF16)
    (Frame : SepProp)
    (hn_eq : n = i + (rest.length + 1))
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1064#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * i) + 2#64)
    (hx19 : s.readReg64 .x19 = srcBase)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ sf,
      sf.pc = (if rest.length = 0 then (blkPl_416).base + 1088#64 else (blkPl_416).base + 1064#64) →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x8 = BitVec.ofNat 64 (i + 1) →
      sf.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) + 2#64 →
      sf.readReg64 .x19 = srcBase →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = BitVec.ofNat 64 n →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sf
        (A.pool lim st sf ∗
         ((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
         ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗
         memRegion (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (4 * rest.length) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
       memRegion (dstBase + BitVec.ofNat 64 (4 * i)) (4 * (rest.length + 1)) ∗ Frame)
      Q Q_panic := by
  apply sepWPp_seg_416
    (mid := if rest.length = 0 then (blkPl_416).base + 1088#64 else (blkPl_416).base + 1064#64)
  intro _m_strip
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (memRegion_split_pt (dstBase + BitVec.ofNat 64 (4 * i)) rest.length (by omega))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro ux
  apply SepWP.exists_elim; intro uy
  have hsrc : srcBase + (BitVec.ofNat 64 i <<< 1#64) = srcBase + BitVec.ofNat 64 (2 * i) := by
    rw [bv_shl1_eq_mul2, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
        ← BitVec.ofNat_mul, Nat.mul_comm]
  have hdst_x : (dstBase + BitVec.ofNat 64 (4 * i) + 2#64) + 0xfffffffffffffffe#64 =
      dstBase + BitVec.ofNat 64 (4 * i) := by
    rw [BitVec.add_assoc, show (2#64 : BitVec 64) + 0xfffffffffffffffe#64 = 0#64 by decide,
        BitVec.add_zero]
  have hdst_next : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 =
      dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
    rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        ← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
  have hx9_next : (dstBase + BitVec.ofNat 64 (4 * i) + 2#64) + 4#64 =
      dstBase + BitVec.ofNat 64 (4 * (i + 1)) + 2#64 := by
    rw [BitVec.add_assoc,
        show (2#64 : BitVec 64) + 4#64 = 4#64 + 2#64 by decide,
        ← BitVec.add_assoc (dstBase + BitVec.ofNat 64 (4 * i)) 4#64 2#64, hdst_next]
  have hx8_next : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  have hx8_16' : BitVec.setWidth 16 (BitVec.setWidth 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 16 i := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_mod_of_dvd _ (by decide : 2 ^ 16 ∣ 2 ^ 32)]
  have hx8_16 : BitVec.truncate 16 (BitVec.truncate 32 (BitVec.ofNat 64 i)) = BitVec.ofNat 16 i :=
    hx8_16'
  have hy16 : BitVec.truncate 16 (BitVec.zeroExtend 32 y.value) = y.value := by bv_bits
  have hy16' : BitVec.setWidth 16 (BitVec.setWidth 32 y.value) = y.value := by bv_bits
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps 8
  by_cases hrem : rest.length = 0
  · have hn1 : n = i + 1 := by omega
    refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
            bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
            bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, hrun])
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre ?_
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, hrun])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, hx9, hx9_next])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true, hx19])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq, hn1,
              bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true]))
    unfold ptAt GF16.new
    simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx9, hx19, hx25, ← hn_eq, hn1,
      bne_self_eq_false, BitVec.sub_self, beq_self_eq_true, Bool.false_eq_true,
      hsrc, hdst_x, hdst_next, hx8_next, hx8_16, hx8_16', hy16, hy16']
    exact Entails.of_eq (by sep_ac_rfl)
  · have hne : (BitVec.ofNat 64 n != BitVec.ofNat 64 (i + 1)) = true :=
      ofNat64_bne_true (by omega) (by omega) (by omega)
    have hsub_ne : (BitVec.ofNat 64 n - BitVec.ofNat 64 (i + 1) == 0#64) = false :=
      ofNat64_sub_beq_zero_false (by omega) (by omega) (by omega)
    refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
            hne, hsub_ne, Bool.false_eq_true])
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
            hne, hsub_ne, Bool.false_eq_true, hrun])
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre ?_
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hrun])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hx9, hx9_next])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hx19])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx25, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true]))
    unfold ptAt GF16.new
    simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx9, hx19, hx25, ← hn_eq,
      hne, hsub_ne, Bool.false_eq_true,
      hsrc, hdst_x, hdst_next, hx8_next, hx8_16, hx8_16', hy16, hy16']
    exact Entails.of_eq (by sep_ac_rfl)

/-- Full budget-threaded `enumeratePts` fill loop (`+1064 -> +1088`) over non-empty `ys`. -/
theorem fillPtVecLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (ys : List GF16) (hne : ys ≠ [])
    (s0 s : State) (srcBase dstBase : BitVec 64)
    (i n : Nat) (Frame : SepProp)
    (hn_eq : n = i + ys.length)
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1064#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 i)
    (hx9 : s.readReg64 .x9 = dstBase + BitVec.ofNat 64 (4 * i) + 2#64)
    (hx19 : s.readReg64 .x19 = srcBase)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 n)
    (hcont : ∀ sf,
      sf.pc = (blkPl_416).base + 1088#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = BitVec.ofNat 64 n →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sf
        (A.pool lim st sf ∗
         gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) ys ∗
         ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) ys ∗
       memRegion (dstBase + BitVec.ofNat 64 (4 * i)) (4 * ys.length) ∗ Frame)
      Q Q_panic := by
  induction ys generalizing s i Frame with
  | nil => contradiction
  | cons y rest ih =>
    have hgf : gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * i)) (y :: rest) =
        ((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
        gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * (i + 1))) rest := by
      have haddr : srcBase + BitVec.ofNat 64 (2 * i) + 2#64 = srcBase + BitVec.ofNat 64 (2 * (i + 1)) := by
        rw [BitVec.add_assoc, show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl,
            ← BitVec.ofNat_add, show 2 * i + 2 = 2 * (i + 1) by omega]
      simp only [gf16SliceAt, arrayAt, gf16At, gf16Stride, BitVec.ofNat_eq_ofNat, haddr]
    have hpt : ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i (y :: rest)) =
        ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗
        ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) rest) := by
      have haddr : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
        rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
            ← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
      simp only [PolyEncoder.enumeratePts, ptSliceAt, arrayAt, ptStride, BitVec.ofNat_eq_ofNat, haddr]
    cases rest with
    | nil =>
      refine SepWPp.weaken_pre
        (by rw [hgf, List.length_cons, List.length_nil]; exact Entails.of_eq (by sep_ac_rfl))
        (fillPtVecLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s srcBase dstBase i n y []
          (gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * (i + 1))) [] ∗ Frame)
          (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx19 hx25 ?_)
      intro sf hpc_sf hrun_sf hsp_sf htr_sf hvregs_sf _ _ _ hx20_sf hx24_sf hx25_sf
        hx26_sf hx27_sf hx28_sf hx29_sf hx30_sf
      simp only [List.length_nil, ↓reduceIte] at hpc_sf
      refine SepWPp.weaken_pre ?_
        (hcont sf hpc_sf hrun_sf hsp_sf htr_sf hvregs_sf hx20_sf hx24_sf hx25_sf
          hx26_sf hx27_sf hx28_sf hx29_sf hx30_sf)
      rw [hgf, hpt]
      simp only [List.length_nil, Nat.mul_zero, ProofLib.memRegion_zero,
        PolyEncoder.enumeratePts, ptSliceAt, arrayAt]
      exact Entails.of_eq (by sep_ac_rfl)
    | cons y' rest' =>
      have hlen_ne : (y' :: rest').length ≠ 0 := by simp
      refine SepWPp.weaken_pre
        (by rw [hgf, List.length_cons]; exact Entails.of_eq (by sep_ac_rfl))
        (fillPtVecLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s srcBase dstBase i n y (y' :: rest')
          (gf16SliceAt (srcBase + BitVec.ofNat 64 (2 * (i + 1))) (y' :: rest') ∗ Frame)
          (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx19 hx25 ?_)
      intro sm hpc_sm hrun_sm hsp_m htr_m hvregs_m hx8_m hx9_m hx19_m
        hx20_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hx30_m
      simp only [hlen_ne, ↓reduceIte] at hpc_sm
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (ih (List.cons_ne_nil y' rest') sm (i + 1)
          (((srcBase + BitVec.ofNat 64 (2 * i)) ↦₁₆ y.value) ∗
           ptAt { x := GF16.new (BitVec.ofNat 16 i), y := y } (dstBase + BitVec.ofNat 64 (4 * i)) ∗ Frame)
          (by simp only [List.length_cons] at hn_eq ⊢; omega)
          hpc_sm hrun_sm hx8_m hx9_m hx19_m hx25_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f
        hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hgf, hpt]; exact Entails.of_eq (by sep_ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          (hx20_f.trans hx20_m) (hx24_f.trans hx24_m) hx25_f
          (hx26_f.trans hx26_m) (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

/-- One step of the budget-threaded `checkCompletePoints` loop (`+1112 -> +1136/+1112`). -/
theorem checkPtVecLoop_step_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (s0 s : State) (dstBase : BitVec 64)
    (i n : Nat) (y : GF16) (rest : List GF16)
    (Frame : SepProp)
    (hn_eq : n = i + (rest.length + 1))
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1112#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (4 * i))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * n))
    (hx26 : s.readReg64 .x26 = dstBase)
    (hcont : ∀ sm,
      sm.pc = (if rest.length = 0 then (blkPl_416).base + 1136#64 else (blkPl_416).base + 1112#64) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .x8 = BitVec.ofNat 64 (4 * (i + 1)) →
      sm.readReg64 .x9 = BitVec.ofNat 64 (i + 1) →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x24 = BitVec.ofNat 64 (4 * n) →
      sm.readReg64 .x25 = s.readReg64 .x25 →
      sm.readReg64 .x26 = dstBase →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s.readReg64 .x29 →
      sm.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sm
        (A.pool lim st sm ∗
         ((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
         ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
       ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame)
      Q Q_panic := by
  apply sepWPp_seg_416
    (mid := if rest.length = 0 then (blkPl_416).base + 1136#64 else (blkPl_416).base + 1112#64)
  intro _m_strip
  have hx8_next : BitVec.ofNat 64 (4 * i) + 4#64 = BitVec.ofNat 64 (4 * (i + 1)) := by
    have h4 : (4#64 : BitVec 64) = BitVec.ofNat 64 4 := rfl
    rw [h4, ← BitVec.ofNat_add]; congr 1
  have hx9_next : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
    have h1 : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
    rw [h1, ← BitVec.ofNat_add]
  try dsimp only [BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_steps 8
  by_cases hrem : rest.length = 0
  · have hn1 : n = i + 1 := by omega
    refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
            beq_self_eq_true])
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
            beq_self_eq_true, hrun])
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true, hrun])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true, hx9, hx9_next])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true, hx26])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq, hn1,
              beq_self_eq_true]))
  · have hne : (BitVec.ofNat 64 (4 * n) == BitVec.ofNat 64 (4 * (i + 1))) = false :=
      ofNat64_beq_false (by omega) (by omega) (by omega)
    have hsub_ne : (BitVec.ofNat 64 (4 * n) - BitVec.ofNat 64 (4 * (i + 1)) == 0#64) = false :=
      ofNat64_sub_beq_zero_false (by omega) (by omega) (by omega)
    refine SepWP.done
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
            hne, hsub_ne, Bool.false_eq_true])
      (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
            hne, hsub_ne, Bool.false_eq_true, hrun])
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hcont _
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hrun])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hx9, hx9_next])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true, hx26])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true])
        (by simp only [hrem, ↓reduceIte, arm64_norm, wp_norm, hx8, hx24, hx8_next, ← hn_eq,
              hne, hsub_ne, Bool.false_eq_true]))

/-- Verification loop (`+1112 -> +1136`) over non-empty `ys`. -/
theorem checkPtVecLoop_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (ys : List GF16) (hne : ys ≠ [])
    (s0 s : State) (dstBase : BitVec 64)
    (i n : Nat) (Frame : SepProp)
    (hn_eq : n = i + ys.length)
    (hn_bound : n ≤ 0x0555555555555555)
    (hpc : s.pc = (blkPl_416).base + 1112#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (4 * i))
    (hx9 : s.readReg64 .x9 = BitVec.ofNat 64 i)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (4 * n))
    (hx26 : s.readReg64 .x26 = dstBase)
    (hcont : ∀ sf,
      sf.pc = (blkPl_416).base + 1136#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      sf.trace = s.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x24 = BitVec.ofNat 64 (4 * n) →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = dstBase →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      sf.readReg64 (Reg.gpr 30#5) = s.readReg64 (Reg.gpr 30#5) →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) sf
        (A.pool lim st sf ∗
         ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i ys) ∗ Frame)
      Q Q_panic := by
  induction ys generalizing s i Frame with
  | nil => contradiction
  | cons y rest ih =>
    have hpt : ptSliceAt (dstBase + BitVec.ofNat 64 (4 * i)) (PolyEncoder.enumeratePts i (y :: rest)) =
        ((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
        ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗
        ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) rest) := by
      have haddr : dstBase + BitVec.ofNat 64 (4 * i) + 4#64 = dstBase + BitVec.ofNat 64 (4 * (i + 1)) := by
        rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
            ← BitVec.ofNat_add, show 4 * i + 4 = 4 * (i + 1) by omega]
      simp only [PolyEncoder.enumeratePts, ptSliceAt, arrayAt, ptAt, GF16.new, ptStride,
        BitVec.ofNat_eq_ofNat, haddr]
      sep_ac_rfl
    cases rest with
    | nil =>
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by sep_ac_rfl))
        (checkPtVecLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s dstBase i n y []
          (ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) []) ∗ Frame)
          (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx24 hx26 ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f _ _ hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
      simp only [List.length_nil, ↓reduceIte] at hpc_f
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by sep_ac_rfl))
        (hcont sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f)
    | cons y' rest' =>
      have hlen_ne : (y' :: rest').length ≠ 0 := by simp
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by sep_ac_rfl))
        (checkPtVecLoop_step_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st) (ext := ext)
          s0 s dstBase i n y (y' :: rest')
          (ptSliceAt (dstBase + BitVec.ofNat 64 (4 * (i + 1))) (PolyEncoder.enumeratePts (i + 1) (y' :: rest')) ∗ Frame)
          (by simpa using hn_eq) hn_bound hpc hrun hx8 hx9 hx24 hx26 ?_)
      intro sm hpc_sm hrun_sm hsp_m htr_m hvregs_m hx8_m hx9_m
        hx20_m hx24_m hx25_m hx26_m hx27_m hx28_m hx29_m hx30_m
      simp only [hlen_ne, ↓reduceIte] at hpc_sm
      refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (ih (List.cons_ne_nil y' rest') sm (i + 1)
          (((dstBase + BitVec.ofNat 64 (4 * i)) ↦₁₆ BitVec.ofNat 16 i) ∗
           ((dstBase + BitVec.ofNat 64 (4 * i) + 2#64) ↦₁₆ y.value) ∗ Frame)
          (by simp only [List.length_cons] at hn_eq ⊢; omega)
          hpc_sm hrun_sm hx8_m hx9_m hx24_m hx26_m ?_)
      intro sf hpc_f hrun_f hsp_f htr_f hvregs_f hx20_f hx24_f hx25_f hx26_f hx27_f hx28_f hx29_f hx30_f
      refine SepWPp.weaken_pre (by rw [hpt]; exact Entails.of_eq (by sep_ac_rfl))
        (hcont sf hpc_f hrun_f (hsp_f.trans hsp_m) (htr_f.trans htr_m) (hvregs_f.trans hvregs_m)
          (hx20_f.trans hx20_m) hx24_f (hx25_f.trans hx25_m)
          hx26_f (hx27_f.trans hx27_m) (hx28_f.trans hx28_m)
          (hx29_f.trans hx29_m) (hx30_f.trans hx30_m))

/-! ## 3. Budget-Threaded Full Per-Polynomial Setup (`+976 -> +1136`) -/

set_option maxHeartbeats 800000 in
private theorem allocPtVec_seg [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)} {post : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp ptsBase ptCap ptPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j n : Nat) (hj : j < 16) (hn_pos : 0 < n) (hn_bound : n ≤ 0x0555555555555555)
    (u40 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hfit : FitsEvents M lim st (rustAllocEvents (4 * n) 2))
    (hcont : ∀ (s1 : State) (P1 : SepProp) (ptVecPtr : BitVec 64),
      ptVecPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 1064#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x8 = 0#64 →
      s1.readReg64 .x9 = ptVecPtr + 2#64 →
      s1.readReg64 .x19 = ptPtr →
      s1.readReg64 .x20 = BitVec.ofNat 64 j →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * n) →
      s1.readReg64 .x25 = BitVec.ofNat 64 n →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (P1 ⊢
        A.pool lim (M.stepEvents (rustAllocEvents (4 * n) 2) st) s1 ∗
        ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
        ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
        ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        A.live ptVecPtr (4 * n) 2 ∗
        memRegion ptVecPtr (4 * n) ∗
        ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 n) ∗
        ((fsp + 48#64) ↦₆₄ 2#64) ∗
        stackAt fsp allocHookStack ∗ Frame) →
      post s1 P1) :
    SepWP ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      ((blkPl_416).base + 1064#64) s
      (A.pool lim st s ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 n) ∗
       ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       stackAt fsp allocHookStack ∗ Frame)
      post := by
  have hlayout : RustLayoutOk (4 * n) 2 := ⟨⟨by omega, ⟨1, rfl⟩, by omega⟩, by decide⟩
  have hfit_ev : FitsEvent M lim st (.alloc (4 * n)) := by
    have hle4 : 2 ≤ 4 * n := by omega
    simpa [rustAllocEvents, hle4] using hfit
  rcases hfit_ev with ⟨_hwmax, henf, hram, hva⟩
  have hmadd : ptsBase + BitVec.ofNat 64 j * 24#64 = ptsBase + BitVec.ofNat 64 (24 * j) := by
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, ← BitVec.ofNat_mul, Nat.mul_comm]
  have hlsl : BitVec.ofNat 64 n <<< 2#64 = BitVec.ofNat 64 (4 * n) := by
    rw [bv_shl2_eq_mul4, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        ← BitVec.ofNat_mul, Nat.mul_comm]
  have hlsl_nat : BitVec.ofNat 64 n <<< 2 = BitVec.ofNat 64 (4 * n) := hlsl
  have hsz_toNat : (BitVec.ofNat 64 (4 * n)).toNat = 4 * n := Nat.mod_eq_of_lt (by omega)
  have hnhi : (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 (4 * n)) = false := by
    apply Bool.eq_false_iff.mpr; intro h0
    have h1 : (0x7ffffffffffffffe#64).toNat < (BitVec.ofNat 64 (4 * n)).toNat :=
      BitVec.lt_def.mp (BitVec.ult_iff_lt.mp h0)
    rw [hsz_toNat] at h1
    change 0x7ffffffffffffffe < 4 * n at h1
    omega
  have hnhi_lsl : (0x7ffffffffffffffe#64).ult (BitVec.ofNat 64 n <<< 2) = false := by
    rw [hlsl_nat]; exact hnhi
  have hx24_ne : (BitVec.ofNat 64 (4 * n) == 0#64) = false :=
    ofNat64_beq_false (by omega) (by omega) (by omega)
  have hx25_ne : (BitVec.ofNat 64 n == 0#64) = false :=
    ofNat64_beq_false (by omega) (by omega) (by omega)
  have h2_toNat : (2#64 : BitVec 64).toNat = 2 := rfl
  have hshim := hA.noAllocShim_ok
  dsimp only [noAllocShimSpec, noAllocShimBudgetSpec] at hshim
  have halloc := hA.allocNoOom_ok
  dsimp only [rustCliAllocNoOomSpec] at halloc
  clear hA
  apply sepWP_seg_416 (mid := lsρ spqrRustNoAllocShimSym)
  intro _m_strip0
  wp_steps 14
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, Bool.false_eq_true, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, Bool.false_eq_true, ↓reduceIte, hrun])
    fun _m_real0 _hnsp0 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp0.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
            hx24_ne, Bool.false_eq_true, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  clear hshim
  have hsp_sf0 : sf.sp = fsp := by
    simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat,
      hnhi, hnhi_lsl, hx24_ne, Bool.false_eq_true, ↓reduceIte, hsp, *]
  have htr_sf0 : sf.trace = s0.trace := by
    simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat,
      hnhi, hnhi_lsl, hx24_ne, Bool.false_eq_true, ↓reduceIte, htrace, *]
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
  have hx25_sf1 : sf_1.readReg64 (Reg.gpr 25#5) = BitVec.ofNat 64 n := by
    simp only [arm64_norm, wp_norm, Reg.x25, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat,
      hnhi, hnhi_lsl, hx24_ne, Bool.false_eq_true, ↓reduceIte, *]
  apply sepWP_seg_416 (mid := (blkPl_416).base + 1064#64)
  intro _m_strip1
  wp_steps 12
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, *])
    fun _m_real1 _hnsp1 => ?_
  refine SepWP.transport_budgetPool
    (_hnsp1.toVmPreserved
      (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
            Bool.not_false, ↓reduceIte]))
    (hnext := ?_)
  simp only [State.setMem_setMem]
  refine SepWP.done
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, *]) ?_
  refine hcont _ _ (sf_1.readReg64 (Reg.gpr 0#5)) hoom
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, *])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hsp_sf1])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, htr_sf1])
    (by simp only [arm64_norm, wp_norm, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x8, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x9, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x19, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x20, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x24, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x25, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x26, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte])
    (by simp only [arm64_norm, wp_norm, Reg.x27, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x28, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    (by simp only [arm64_norm, wp_norm, Reg.x29, hbeq0, hx25_sf1, hx25_ne, Bool.false_eq_true,
          Bool.not_false, ↓reduceIte, hx19, hx20, hx28, hmadd, hlsl, hlsl_nat, hnhi, hnhi_lsl,
          hx24_ne, *])
    ?_
  simp only [arm64_norm, wp_norm, Bool.false_eq_true, ↓reduceIte, hlsl, hlsl_nat, hsz_toNat,
    hmadd, hsp_sf1, hsp_sf0, hsp, hx19, hx20, hx28, hnhi, hnhi_lsl, hx24_ne, hbeq0, hx25_sf1,
    hx25_ne, Bool.not_false]
  exact Entails.of_eq (by sep_ac_rfl)

/-- Full budget-threaded per-polynomial setup (`+976 -> +1136`):
    reads `pt = pts[j]` from `ptsBase + 24 * j`, allocates & populates `pt_vec`,
    verifies `checkCompletePoints`, stores `j + 1` at `[fsp + 32]` and `pt.value.length`
    at `[fsp + 40]`, advances `A.pool lim st` by `setupPtVecEvents pt.value.length`,
    and produces `ptVecBufAt A.repAlloc ptVecPtr pt.value`. -/
theorem setupPtVec_placed_sepWPp [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ext : String → Option (State → State)}
    {Q Q_panic : State → SepProp → Prop}
    (hA : AllocContractsPlaced M A lim ext)
    (s0 s : State) (fsp ptsBase : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (j : Nat) (hj : j < 16)
    (pt : Point) (hpt_bound : pt.value.length ≤ 0x0555555555555555)
    (u32 u40 : BitVec 64)
    (Frame _R : SepProp)
    (hpc : s.pc = (blkPl_416).base + 976#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = fsp)
    (htrace : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = ptsBase)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 j)
    (hx28 : s.readReg64 .x28 = 24#64)
    (hfit : FitsEnv M lim st (SetupPtVecEnv pt.value.length))
    (hcont : ∀ s1 (ptVecPtr : BitVec 64),
      ptVecPtr ≠ 0#64 →
      s1.pc = (blkPl_416).base + 1136#64 →
      s1.status = .Running →
      s1.sp = fsp →
      s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      s1.readReg64 .x20 = BitVec.ofNat 64 j →
      s1.readReg64 .x24 = BitVec.ofNat 64 (4 * pt.value.length) →
      s1.readReg64 .x25 = BitVec.ofNat 64 pt.value.length →
      s1.readReg64 .x26 = ptVecPtr →
      s1.readReg64 .x27 = s.readReg64 .x27 →
      s1.readReg64 .x28 = 24#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
        (s0.readReg64 (Reg.gpr 30#5)) s1
        (A.pool lim (M.stepEvents (setupPtVecEvents pt.value.length) st) s1 ∗
         pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
         ptVecBufAt A.repAlloc ptVecPtr pt.value ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        Q Q_panic) :
    SepWPp ((blkPC_416).rebase (blkPl_416).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (A.pool lim st s ∗
       pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗
       ((fsp + 40#64) ↦₆₄ u40) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗
       stackAt fsp allocHookStack ∗ Frame)
      Q Q_panic := by
  unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWPp.exists_elim; intro ptCap
  apply SepWPp.exists_elim; intro ptPtr
  refine SepWPp.weaken_pre (Entails.of_eq (show _ =
      A.pool lim st s ∗
      ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
      ⌜pt.value.length ≤ ptCap.toNat ∧ ptCap.toNat * 2 < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝ ∗
      (((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
       (if ptCap = 0#64 then emp
        else A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr pt.value ∗
          memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ∗
       ((fsp + 32#64) ↦₆₄ u32) ∗ ((fsp + 40#64) ↦₆₄ u40) ∗ ((fsp + 48#64) ↦₆₄ 2#64) ∗
       stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
  apply sepWPp_pure_mid; intro ⟨hpt_cap, hpt_cap_bound, hpt_ptr_ne⟩
  have hmadd : ptsBase + BitVec.ofNat 64 j * 24#64 = ptsBase + BitVec.ofNat 64 (24 * j) := by
    have h24 : (24#64 : BitVec 64) = BitVec.ofNat 64 24 := rfl
    rw [h24, ← BitVec.ofNat_mul]; congr 2; omega
  have hj_next : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
    have h1 : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
    rw [h1, ← BitVec.ofNat_add]
  by_cases hys : pt.value = []
  · try dsimp only [BitVec.ofNat_eq_ofNat] at hpc hcont ⊢
    apply sepWPp_seg_416 (mid := (blkPl_416).base + 1136#64)
    intro _m_strip
    wp_steps 28
    refine SepWP.done
      (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
            BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
            BitVec.sub_self])
      (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
            BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
            BitVec.sub_self, hrun])
      fun _m_real _hnsp => ?_
    refine SepWPp.transport_budgetPool
      (_hnsp.toVmPreserved
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self]))
      (hnext := ?_)
    simp only [State.setMem_setMem]
    have hptOf : (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
        ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
        ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
        (if ptCap = 0#64 then emp
         else A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr [] ∗
           memRegion (ptPtr + BitVec.ofNat 64 (0 * 2)) ((ptCap.toNat - 0) * 2))) ⊢
        pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt := by
      unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align
      refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
      simp only [hys, List.length_nil, BitVec.ofNat_eq_ofNat]
      rw [sepConj_pure_left_comm]
      exact Entails.pure_right ⟨by omega, hpt_cap_bound, hpt_ptr_ne⟩ (Entails.of_eq (by sep_ac_rfl))
    refine SepWPp.weaken_pre ?_
      (hcont _ 2#64 (by decide)
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self, hrun])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self, hsp])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self, htrace])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true,
              ↓reduceIte, BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self])
        (by simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hys, List.length_nil,
              BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte,
              BitVec.sub_self]))
    have hstep0 : M.stepEvents (setupPtVecEvents pt.value.length) st = st := by
      simp only [hys, List.length_nil, setupPtVecEvents, ↓reduceIte]; rfl
    rw [hstep0]
    simp only [arm64_norm, wp_norm, hx19, hx20, hx28, hmadd, hj_next, hys, List.length_nil,
      BitVec.ofNat_eq_ofNat, BitVec.shiftLeft_zero, beq_self_eq_true, ↓reduceIte, BitVec.sub_self,
      hsp]
    refine Entails.trans (Entails.of_eq (show _ =
      (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
       ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ 0#64) ∗
       (if ptCap = 0#64 then emp
        else A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗ arrayAt gf16At 2 ptPtr [] ∗
          memRegion (ptPtr + 0#64) ((ptCap.toNat - 0) * 2))) ∗
      emp ∗
      (A.pool lim st _ ∗
       ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
       ((fsp + 40#64) ↦₆₄ 0#64) ∗
       ((fsp + 48#64) ↦₆₄ 2#64) ∗ stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono hptOf (sepConj_mono_left (ptVecBufAt_nil A.repAlloc))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · have hn_pos : 0 < pt.value.length := List.length_pos_iff.mpr hys
    have hlen_ne0 : pt.value.length ≠ 0 := by omega
    have hcap_ne : ptCap ≠ 0#64 := by
      intro hc; subst hc; simp only [BitVec.toNat_ofNat, Nat.zero_mod] at hpt_cap; omega
    simp only [hcap_ne, ↓reduceIte]
    have hfit4 : FitsEvents M lim st (rustAllocEvents (4 * pt.value.length) 2) := by
      have hf := (fitsEnv_setupPtVec_iff pt.value.length).mp hfit
      simpa [setupPtVecEvents, hlen_ne0] using hf
    have hx24_ne : (BitVec.ofNat 64 (4 * pt.value.length) == 0#64) = false :=
      ofNat64_beq_false (by omega) (by decide) (by omega)
    have hx24_sub_ne : (BitVec.ofNat 64 (4 * pt.value.length) - 0#64 == 0#64) = false := by
      simpa using hx24_ne
    refine SepWPp.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (SepWPp.of_sepWP
        (allocPtVec_seg hA s0 s fsp ptsBase ptCap ptPtr hfsp_align j pt.value.length
          hj hn_pos hpt_bound u40
          (A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗
           arrayAt gf16At 2 ptPtr pt.value ∗
           memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
           ((fsp + 32#64) ↦₆₄ u32) ∗ Frame)
          hpc hrun hsp htrace hx19 hx20 hx28 hfit4 ?_))
    intro sAlloc PAlloc ptVecPtr hoom hpcAlloc hrunAlloc hspAlloc htrAlloc hvregsAlloc
      hx8Alloc hx9Alloc hx19Alloc hx20Alloc hx24Alloc hx25Alloc hx26Alloc hx27Alloc hx28Alloc hx29Alloc
      hentAlloc
    let st1 := M.stepEvents (rustAllocEvents (4 * pt.value.length) 2) st
    refine SepWPp.weaken_pre
      (Entails.trans hentAlloc ?_)
      (fillPtVecLoop_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st1) (ext := ext)
        pt.value hys s0 sAlloc ptPtr ptVecPtr 0 pt.value.length
        (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
         ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
         ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗
         memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
         A.live ptVecPtr (4 * pt.value.length) 2 ∗
         ((fsp + 32#64) ↦₆₄ u32) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗ Frame)
        (by omega) hpt_bound hpcAlloc hrunAlloc
        (by simpa using hx8Alloc)
        (by simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]; exact hx9Alloc)
        hx19Alloc hx25Alloc ?_)
    · unfold gf16SliceAt
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro sFill hpcFill hrunFill hspFill htrFill hvregsFill
        hx20Fill hx24Fill hx25Fill hx26Fill hx27Fill hx28Fill hx29Fill _hx30Fill
      have hspFill' : sFill.sp = fsp := hspFill.trans hspAlloc
      have htrFill' : sFill.trace = s0.trace := htrFill.trans htrAlloc
      have hx20Fill' : sFill.readReg64 .x20 = BitVec.ofNat 64 j := hx20Fill.trans hx20Alloc
      have hx24Fill' : sFill.readReg64 .x24 = BitVec.ofNat 64 (4 * pt.value.length) :=
        hx24Fill.trans hx24Alloc
      have hx26Fill' : sFill.readReg64 .x26 = ptVecPtr := hx26Fill.trans hx26Alloc
      have hx28Fill' : sFill.readReg64 .x28 = 24#64 := hx28Fill.trans hx28Alloc
      apply sepWPp_seg_416 (mid := (blkPl_416).base + 1112#64)
      intro _m_stripMid
      wp_steps 10
      refine SepWP.done
        (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte])
        (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte, hrunFill])
        fun _m_realMid _hnspMid => ?_
      refine SepWPp.transport_budgetPool
        (_hnspMid.toVmPreserved
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte]))
        (hnext := ?_)
      simp only [State.setMem_setMem]
      refine SepWPp.weaken_pre
        (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true,
              ↓reduceIte, hspFill', hx20Fill', hj_next, Nat.mul_zero, BitVec.ofNat_eq_ofNat]
            exact Entails.of_eq (by sep_ac_rfl))
        (checkPtVecLoop_placed_sepWPp (M := M) (A := A) (lim := lim) (st := st1) (ext := ext)
          pt.value hys s0 _ ptVecPtr 0 pt.value.length
          (gf16SliceAt (ptPtr + 0#64) pt.value ∗
           ((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
           ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
           ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
           A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗
           memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2) ∗
           A.live ptVecPtr (4 * pt.value.length) 2 ∗
           ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
           ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
           ((fsp + 48#64) ↦₆₄ 2#64) ∗
           stackAt fsp allocHookStack ∗ Frame)
          (by omega) hpt_bound
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte, hrunFill])
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte])
          (by simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne, Bool.false_eq_true, ↓reduceIte, hx26Fill'])
          ?_)
      intro sEnd hpcEnd hrunEnd hspEnd htrEnd hvregsEnd
        hx20End hx24End hx25End hx26End hx27End hx28End hx29End _hx30End
      have hptOf : (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
          ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
          ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
          A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗
          gf16SliceAt (ptPtr + 0#64) pt.value ∗
          memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ⊢
          pointOf A.repAlloc (ptsBase + BitVec.ofNat 64 (24 * j)) pt := by
        unfold pointOf vecOf vecAt vecHeader vecBuf gf16Stride gf16Align gf16SliceAt
        dsimp only [gf16Stride]
        refine Entails.sepExists_right ptCap (Entails.sepExists_right ptPtr ?_)
        simp only [show (0 : BitVec 64) = 0#64 from rfl, hcap_ne, ↓reduceIte, BitVec.add_zero]
        rw [sepConj_pure_left_comm]
        exact Entails.pure_right ⟨hpt_cap, hpt_cap_bound, hpt_ptr_ne⟩ (Entails.of_eq (by sep_ac_rfl))
      have hbuf : (ptSliceAt (ptVecPtr + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
          A.live ptVecPtr (4 * pt.value.length) 2) ⊢
          ptVecBufAt A.repAlloc ptVecPtr pt.value := by
        unfold ptVecBufAt
        simp only [hlen_ne0, ↓reduceIte, BitVec.add_zero]
        exact Entails.pure_right hoom (Entails.of_eq (by sep_ac_rfl))
      have hstep_eq : M.stepEvents (setupPtVecEvents pt.value.length) st = st1 := by
        simp only [setupPtVecEvents, hlen_ne0, ↓reduceIte]; rfl
      refine SepWPp.weaken_pre ?_
        (hcont sEnd ptVecPtr hoom hpcEnd hrunEnd
          (by rw [hspEnd]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte, hspFill'])
          (by rw [htrEnd]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte, htrFill'])
          (by rw [hvregsEnd]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte]; exact hvregsFill.trans hvregsAlloc)
          (by rw [hx20End]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte, hx20Fill'])
          hx24End
          (by rw [hx25End]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte, hx25Fill])
          hx26End
          (by rw [hx27End]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte]; exact hx27Fill.trans hx27Alloc)
          (by rw [hx28End]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte, hx28Fill'])
          (by rw [hx29End]; simp only [arm64_norm, wp_norm, hx24Fill', hx24_ne, hx24_sub_ne,
                Bool.false_eq_true, ↓reduceIte]; exact hx29Fill.trans hx29Alloc))
      rw [hstep_eq]
      simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat]
      refine Entails.trans (Entails.of_eq (show _ =
        (((ptsBase + BitVec.ofNat 64 (24 * j)) ↦₆₄ ptCap) ∗
         ((ptsBase + BitVec.ofNat 64 (24 * j) + 8#64) ↦₆₄ ptPtr) ∗
         ((ptsBase + BitVec.ofNat 64 (24 * j) + 16#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         A.repAlloc.live ptPtr (ptCap.toNat * 2) 2 ∗
         gf16SliceAt (ptPtr + 0#64) pt.value ∗
         memRegion (ptPtr + BitVec.ofNat 64 (pt.value.length * 2)) ((ptCap.toNat - pt.value.length) * 2)) ∗
        (ptSliceAt (ptVecPtr + 0#64) (PolyEncoder.enumeratePts 0 pt.value) ∗
         A.live ptVecPtr (4 * pt.value.length) 2) ∗
        (A.pool lim st1 sEnd ∗
         ((fsp + 32#64) ↦₆₄ BitVec.ofNat 64 (j + 1)) ∗
         ((fsp + 40#64) ↦₆₄ BitVec.ofNat 64 pt.value.length) ∗
         ((fsp + 48#64) ↦₆₄ 2#64) ∗
         stackAt fsp allocHookStack ∗ Frame) by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hptOf (sepConj_mono_left hbuf)) ?_
      exact Entails.of_eq (by sep_ac_rfl)

end LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.PointsToPolysSetupPlacedBudget
