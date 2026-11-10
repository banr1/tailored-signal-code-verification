/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.SpqrV1.Alloc.SpqrAllocCodeSym
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `RawVecInner::finish_grow`

Proves `RustCliAllocBudget M` / `VmPreserved` `[LibsignalPlacement]` contracts for
blocks 361 (generic `(stride, align)`), 160 (`[local#2]`, `stride = 1`),
221 (`[local#4]`, `stride = 1`), and 259 (`[local#6]`, `stride = 32, align = 8`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_160 blkPC_221 blkPC_259 blkPC_361
  blkPl_160 blkPl_221 blkPl_259 blkPl_361 lsρ
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalTripleRatchet (
  FinishGrowCall extHookStack withStack
)
open CryptoVerification.SpqrV1.Alloc (
  spqrRustAllocSym spqrRustNoAllocShimSym spqrRustReallocSym spqr_externAt?_of_mem
  spqr_hook_ok_of_mem
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliReallocBudgetSpec rustReallocEvents
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocNoOomExternSpecWithStack rustCliReallocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_externWithStack_of_hookSat
  subroutine_ok_reallocNoOom_externWithStack_of_hookSat
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  FinishGrowEnv finishGrowEvents finishGrowSpec finishGrowSpecWithStack finishGrowSpecX
  fitsEnv_finishGrow_iff framelessMemcpyBudgetSpec framelessMemcpySpec
  noAllocShimBudgetSpec noAllocShimSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Re-Exported Symbols and Stack Constants -/

abbrev finishGrow8Name : String := CryptoVerification.SpqrV1.Alloc.finishGrow8Name
abbrev finishGrow2Name : String := CryptoVerification.SpqrV1.Alloc.finishGrow2Name
abbrev finishGrow4Name : String := CryptoVerification.SpqrV1.Alloc.finishGrow4Name
abbrev finishGrow7Name : String := CryptoVerification.SpqrV1.Alloc.finishGrow7Name
abbrev finishGrow32Stack : Nat := CryptoVerification.SpqrV1.Alloc.finishGrow32Stack
abbrev finishGrow32StackX : Nat := CryptoVerification.SpqrV1.Alloc.finishGrow32StackX
abbrev FinishGrow1Call := CryptoVerification.SpqrV1.Alloc.FinishGrow1Call

/-! ## `VmPreserved` Shim and `memcpy` Specs -/

/-- Stack-equipped `VmPreserved` no-op shim specification. -/
def session2ShimSpecWithStack (hookStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp hookStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ stackAt s0.sp hookStack

/-- Stack-equipped `VmPreserved` `memcpy` specification. -/
def session2MemcpySpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗ (dst ↦ₛ bs) ∗
      (src ↦ₛ bs) ∗ stackAt s0.sp hookStack

theorem session2ShimWithStack_of_noAllocShim {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr noAllocShimSpec) :
    subroutine_ok prog addr (session2ShimSpecWithStack hookStack) := by
  have h' := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, noAllocShimBudgetSpec, session2ShimSpecWithStack]
      at hpre ⊢
    simpa only [emp_sepConj, sepConj_assoc] using hpre
  exact h'.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout

theorem session2MemcpyWithStack_of_framelessMemcpy {prog : Program} {addr : BitVec 64}
    (hookStack : Nat) (h : subroutine_ok prog addr framelessMemcpySpec) :
    subroutine_ok prog addr (session2MemcpySpecWithStack hookStack) := by
  have h' := CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withStack_of_subroutine_ok h hookStack
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack framelessMemcpySpec hookStack).pre x s0 ∗ R := by
    dsimp only [withStack, framelessMemcpySpec, framelessMemcpyBudgetSpec,
      session2MemcpySpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h'.mono_outcome x R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, framelessMemcpySpec, framelessMemcpyBudgetSpec,
      session2MemcpySpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

/-! ## Arithmetic and Memory Helpers -/

private theorem umulh_stride_eq_zero {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 stride * BitVec.zeroExtend 128 new) >>> 64) =
      0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hs : stride.toNat < 2 ^ 128 := lt_trans stride.isLt (by decide)
  have hn : new.toNat < 2 ^ 128 := lt_trans new.isLt (by decide)
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
  have hprod : stride.toNat * new.toNat < 2 ^ 64 := by rw [Nat.mul_comm]; exact h
  rw [Nat.mod_eq_of_lt (lt_trans hprod (by decide)), Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt hprod]
  rfl

private theorem mul_stride_toNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new).toNat = new.toNat * stride.toNat := by
  rw [BitVec.toNat_mul, Nat.mul_comm, Nat.mod_eq_of_lt h]

private theorem mul_stride_eq_ofNat {new stride : BitVec 64}
    (h : new.toNat * stride.toNat < 2 ^ 64) :
    stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [mul_stride_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem beq_mul_stride_zero_eq_false {new stride : BitVec 64}
    (h0 : 0 < new.toNat * stride.toNat) (hlt : new.toNat * stride.toNat < 2 ^ 64) :
    (stride * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_stride_toNat hlt] at ht
  change new.toNat * stride.toNat = 0 at ht
  omega

private theorem hi_stride_eq_false {new stride align : BitVec 64}
    (h : new.toNat * stride.toNat + align.toNat ≤ 2 ^ 63) :
    (9223372036854775808#64 - align).ult (stride * new) = false := by
  have hlt : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hal : align.toNat ≤ 2 ^ 63 := by omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, not_lt]
  rw [mul_stride_toNat hlt, BitVec.toNat_sub_of_le]
  · change new.toNat * stride.toNat ≤ 2 ^ 63 - align.toNat
    omega
  · rw [BitVec.le_def]
    exact hal

private theorem getLsbD_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new.getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_eq_false {new : BitVec 64} (h : new.toNat < 2 ^ 63) :
    new[63] = false := by
  rw [BitVec.getElem_eq_testBit_toNat]
  exact Nat.testBit_lt_two_pow h

private theorem beq_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat) :
    (new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  change new.toNat = 0 at ht
  omega

private theorem lsr59_eq_zero {new : BitVec 64} (h : new.toNat < 2 ^ 59) :
    new >>> 59 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
  rfl

private theorem lsl5_toNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) :
    (x <<< 5).toNat = x.toNat * 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt h

private theorem lsl5_eq_ofNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) :
    x <<< 5 = BitVec.ofNat 64 (x.toNat * 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [lsl5_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

private theorem hi_32_eq_false {new : BitVec 64} (h : new.toNat * 32 + 8 ≤ 2 ^ 63) :
    (9223372036854775800#64).ult (new <<< 5) = false := by
  have hlt : new.toNat * 32 < 2 ^ 64 := by omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, not_lt, lsl5_toNat hlt]
  change new.toNat * 32 ≤ 9223372036854775800
  omega

private theorem beq_lsl5_zero_eq_false {new : BitVec 64}
    (h0 : 0 < new.toNat) (hlt : new.toNat * 32 < 2 ^ 64) :
    (new <<< 5 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [lsl5_toNat hlt] at ht
  change new.toNat * 32 = 0 at ht
  omega

theorem memRegion_24 (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) :=
  CryptoVerification.SpqrV1.Alloc.memRegion_24 a

private theorem stackAt_finishGrow_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 48) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 :=
  ProofLib.stackAt_split_cells sp hookStack 6 hhook

private theorem stackAt_finishGrow32_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 32) =
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp hookStack 4 hhook

/-! ## Specialized `finishGrow1` and `finishGrow7` Budget Specs -/

/-- Deterministic allocator events of `finish_grow` for `stride = 1, align = 1`. -/
def finishGrow1Events (x : FinishGrow1Call) : List AllocEvent :=
  if x.cap = 0#64 then rustAllocEvents x.new.toNat 1
  else rustReallocEvents x.cap.toNat x.new.toNat 1

def FinishGrow1Env (x : FinishGrow1Call) (evs : List AllocEvent) : Prop :=
  evs = finishGrow1Events x

theorem fitsEnv_finishGrow1_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : FinishGrow1Call) :
    FitsEnv M lim st (FinishGrow1Env x) ↔ FitsEvents M lim st (finishGrow1Events x) :=
  FitsEnv.eq_iff

theorem finishGrow1Events_eq_finishGrowEvents (x : FinishGrow1Call) :
    finishGrow1Events x = finishGrowEvents x.cap.toNat x.new.toNat 1 1 := by
  unfold finishGrow1Events finishGrowEvents
  rw [Nat.mul_one, Nat.mul_one]
  by_cases hcap : x.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : x.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-- Budget contract of `finish_grow [local#2, 4]` (`stride = 1, align = 1`, 32-byte frame). -/
def finishGrow1SpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ x.new) ∗
      A.live p' x.new.toNat 1 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat - x.bs.length) ∗
      A.pool lim (M.stepEvents (finishGrow1Events x) st) sf ∗
      stackAt s0.sp (hookStack + 32)

abbrev finishGrow1Spec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  finishGrow1SpecWithStack M A lim allocHookStack

abbrev finishGrow1SpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  finishGrow1SpecWithStack M A lim extHookStack

/-- Deterministic allocator events of `finish_grow` for `stride = 32, align = 8`. -/
def finishGrow7Events (x : FinishGrow1Call) : List AllocEvent :=
  if x.cap = 0#64 then rustAllocEvents (x.new.toNat * 32) 8
  else rustReallocEvents (x.cap.toNat * 32) (x.new.toNat * 32) 8

def FinishGrow7Env (x : FinishGrow1Call) (evs : List AllocEvent) : Prop :=
  evs = finishGrow7Events x

theorem fitsEnv_finishGrow7_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : FinishGrow1Call) :
    FitsEnv M lim st (FinishGrow7Env x) ↔ FitsEvents M lim st (finishGrow7Events x) :=
  FitsEnv.eq_iff

theorem finishGrow7Events_eq_finishGrowEvents (x : FinishGrow1Call) :
    finishGrow7Events x = finishGrowEvents x.cap.toNat x.new.toNat 8 32 := by
  unfold finishGrow7Events finishGrowEvents
  by_cases hcap : x.cap = 0#64
  · rw [hcap]; rfl
  · have hcap_nat : x.cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    simp only [hcap, hcap_nat, ↓reduceIte]

/-- Budget contract of `finish_grow [local#6]` (`stride = 32, align = 8`, 32-byte frame). -/
def finishGrow7SpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
      s.readReg64 .x3 = x.new ∧
      (x.cap = 0#64 → x.bs = []) ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
      x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (FinishGrow7Env x)⌝ ∗
    memRegion x.out 24 ∗ x.oldBuf32 A.repAlloc ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32)
  post := fun (x, st) s0 sf =>
    ∃∗ p' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0 ∧ sf.trace = s0.trace⌝ ∗
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ p') ∗
      ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * 32)) ∗
      A.live p' (x.new.toNat * 32) 8 ∗ (p' ↦ₛ x.bs) ∗
      memRegion (p' + BitVec.ofNat 64 x.bs.length) (x.new.toNat * 32 - x.bs.length) ∗
      A.pool lim (M.stepEvents (finishGrow7Events x) st) sf ∗
      stackAt s0.sp (hookStack + 32)

abbrev finishGrow7Spec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  finishGrow7SpecWithStack M A lim allocHookStack

abbrev finishGrow7SpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FinishGrow1Call × M.σ) :=
  finishGrow7SpecWithStack M A lim extHookStack

/-! ## Block 361: `finish_grow [local#8]` -/

def finishGrow8AllocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEnv M lim st (FinishGrowEnv x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 48) }

def finishGrow8ReallocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrowCall × M.σ) :=
  { finishGrowSpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ s.readReg64 .x4 = x.align ∧ s.readReg64 .x5 = x.stride ∧
        x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * x.stride.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
        RustLayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
        FitsEnv M lim st (FinishGrowEnv x)⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * x.stride.toNat) x.align.toNat ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length)
        (x.cap.toNat * x.stride.toNat - x.bs.length) ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 48) }

theorem finish_grow_8_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8AllocSpecG M A lim hookStack) := by
  unfold finishGrow8AllocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, 0#64, ptr, new, align, stride, []⟩) := by
    assumption
  have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, BitVec.toNat_zero, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcbz := beq_mul_stride_zero_eq_false hsz_pos hlt64
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat * stride.toNat, align.toNat, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrowEvents, BitVec.toNat_zero, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_8_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrow8ReallocSpecG M A lim hookStack) := by
  unfold finishGrow8ReallocSpecG finishGrowSpecWithStack
  simp only [memRegion_24, stackAt_finishGrow_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, align, stride, bs⟩, st⟩
  dsimp only at *
  have hrlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat := by assumption
  rcases hrlay with ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hstr_pos : 0 < stride.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * stride.toNat := by assumption
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hcap_nat_ne : cap.toNat ≠ 0 := Nat.ne_of_gt hcap_pos
  have hfits_env : FitsEnv M lim st (FinishGrowEnv ⟨out, cap, ptr, new, align, stride, bs⟩) := by
    assumption
  have hfits : FitsEvents M lim st
      (rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat) := by
    simp only [fitsEnv_finishGrow_iff, finishGrowEvents, hcap_nat_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * stride.toNat < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * stride.toNat ≤ new.toNat * stride.toNat :=
    Nat.mul_le_mul_right stride.toNat hcap_le_new
  have hcap_lt64 : cap.toNat * stride.toNat < 2 ^ 64 := by omega
  have hold_pos : 0 < cap.toNat * stride.toNat := Nat.mul_pos hcap_pos hstr_pos
  have humulh := umulh_stride_eq_zero hlt64
  have hhi := hi_stride_eq_false hbound
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hmul : (stride * new).toNat = new.toNat * stride.toNat := mul_stride_toNat hlt64
  have hmul_cap : (stride * cap).toNat = cap.toNat * stride.toNat := mul_stride_toNat hcap_lt64
  have hle_new : bs.length ≤ new.toNat * stride.toNat := by omega
  have hlay_old : RustLayoutOk (cap.toNat * stride.toNat) align.toNat :=
    ⟨⟨hold_pos, hpow, by omega⟩, hal_le⟩
  have hlay : RustLayoutOk (new.toNat * stride.toNat) align.toNat :=
    ⟨⟨hsz_pos, hpow, hbound⟩, hal_le⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat * stride.toNat, align.toNat, new.toNat * stride.toNat, bs, st)
  have hmul_bv : stride * new = BitVec.ofNat 64 (new.toNat * stride.toNat) :=
    mul_stride_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrowEvents, hcap_nat_ne, ↓reduceIte]
  wp_done

theorem finish_grow_8_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 48 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine (finish_grow_8_zero_placed_ok_of_hooks hhook hshim halloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8AllocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_true, emp_sepConj, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hbs0, _, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, trivial, hbs0 trivial, hle, hnew, hstr, hlay, hfits⟩,
      hmem⟩
  · refine (finish_grow_8_ne_placed_ok_of_hooks hhook hrealloc).mono_outcome
      (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrowSpecWithStack, finishGrow8ReallocSpecG,
      FinishGrowCall.oldBuf, hcap0, ite_false, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, _, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hcap0, hbs, hle, hnew, hstr, hlay, hfits⟩, hmem⟩

theorem finish_grow_8_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpec M A lim) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_8_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_361).rebase (blkPl_361).base H)
      (blkPl_361).base
      (finishGrowSpecX M A lim) :=
  finish_grow_8_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

/-! ## Blocks 160 (`[local#2]`) and 221 (`[local#4]`) -/

def finishGrow1AllocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow1SpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32) }

def finishGrow1ReallocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow1SpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat + 1 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow1Env x)⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr x.cap.toNat 1 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat - x.bs.length) ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_1_placed_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow1AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow1ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow1SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1AllocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow1SpecWithStack, finishGrow1ReallocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

theorem finish_grow_2_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1AllocSpecG M A lim hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_2_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1ReallocSpecG M A lim hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, hpow, by omega⟩, by decide⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events, hcap_ne, ↓reduceIte]
  wp_done

theorem finish_grow_2_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecWithStack M A lim hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_2_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_2_ne_placed_ok_of_hooks hhook hrealloc)

theorem finish_grow_2_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1Spec M A lim) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_2_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_160).rebase (blkPl_160).base H)
      (blkPl_160).base
      (finishGrow1SpecX M A lim) :=
  finish_grow_2_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_4_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1AllocSpecG M A lim hookStack) := by
  unfold finishGrow1AllocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcbz := beq_zero_eq_false hnew_pos
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat, 1, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow1Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_4_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1ReallocSpecG M A lim hookStack) := by
  unfold finishGrow1ReallocSpecG finishGrow1SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat + 1 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow1Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents cap.toNat new.toNat 1) := by
    simp only [fitsEnv_finishGrow1_iff, finishGrow1Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hmsb := getLsbD_63_eq_false (new := new) (by omega)
  have hmsb' := getElem_63_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hle_new : bs.length ≤ new.toNat := by omega
  have hpow : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay_old : RustLayoutOk cap.toNat 1 := ⟨⟨hcap_pos, hpow, by omega⟩, by decide⟩
  have hlay : RustLayoutOk new.toNat 1 := ⟨⟨hnew_pos, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat, 1, new.toNat, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow1Events, hcap_ne, ↓reduceIte]
  wp_done

theorem finish_grow_4_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecWithStack M A lim hookStack) :=
  finish_grow_1_placed_of_zero_ne
    (finish_grow_4_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_4_ne_placed_ok_of_hooks hhook hrealloc)

theorem finish_grow_4_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1Spec M A lim) :=
  finish_grow_4_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_4_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_221).rebase (blkPl_221).base H)
      (blkPl_221).base
      (finishGrow1SpecX M A lim) :=
  finish_grow_4_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

/-! ## Block 259: `finish_grow [local#7]` (`stride = 32, align = 8`) -/

def finishGrow7AllocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow7SpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap = 0#64 ∧ x.bs = [] ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow7Env x)⌝ ∗
      memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp (hookStack + 32) }

def finishGrow7ReallocSpecG (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat) : Spec (FinishGrow1Call × M.σ) :=
  { finishGrow7SpecWithStack M A lim hookStack with
    pre := fun (x, st) s =>
      ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.cap ∧ s.readReg64 .x2 = x.ptr ∧
        s.readReg64 .x3 = x.new ∧ x.cap ≠ 0#64 ∧ x.bs.length ≤ x.cap.toNat * 32 ∧
        x.cap.toNat ≤ x.new.toNat ∧ 0 < x.new.toNat ∧ x.new.toNat * 32 + 8 ≤ 2 ^ 63 ∧
        FitsEnv M lim st (FinishGrow7Env x)⌝ ∗
      memRegion x.out 24 ∗
      A.live x.ptr (x.cap.toNat * 32) 8 ∗ (x.ptr ↦ₛ x.bs) ∗
      memRegion (x.ptr + BitVec.ofNat 64 x.bs.length) (x.cap.toNat * 32 - x.bs.length) ∗
      A.pool lim st s ∗ stackAt s.sp (hookStack + 32) }

private theorem finish_grow_7_placed_of_zero_ne {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {addr : BitVec 64} {hookStack : Nat}
    (hz : subroutine_ok P addr (finishGrow7AllocSpecG M A lim hookStack))
    (hne : subroutine_ok P addr (finishGrow7ReallocSpecG M A lim hookStack)) :
    subroutine_ok P addr (finishGrow7SpecWithStack M A lim hookStack) := by
  refine subroutine_ok_outcome_intro fun ⟨x, st⟩ R s0 hpc hrun hpre hsp => ?_
  by_cases hcap0 : x.cap = 0#64
  · refine hz.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow7SpecWithStack, finishGrow7AllocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf32, hcap0, ite_true, emp_sepConj,
      sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hbs0, _, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, trivial, hbs0 trivial, hle, hnew, hlay, hfits⟩, hmem⟩
  · refine hne.mono_outcome (x, st) R s0 hpc hrun ?_ hsp fun _ hout => hout
    simp only [finishGrow7SpecWithStack, finishGrow7ReallocSpecG,
      CryptoVerification.SpqrV1.Alloc.FinishGrow1Call.oldBuf32, hcap0, ite_false, sepConj_assoc,
      satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hbs, hle, hnew, hlay, hfits⟩, hmem⟩
    exact ⟨⟨hx0, hx1, hx2, hx3, hcap0, hbs, hle, hnew, hlay, hfits⟩, hmem⟩

theorem finish_grow_7_zero_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7AllocSpecG M A lim hookStack) := by
  unfold finishGrow7AllocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  rcases ‹cap = 0#64› with rfl
  rcases ‹bs = []› with rfl
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow7Env ⟨out, 0#64, ptr, new, []⟩) := by assumption
  have hfits : FitsEvents M lim st (rustAllocEvents (new.toNat * 32) 8) := by
    simp only [fitsEnv_finishGrow7_iff, finishGrow7Events, ↓reduceIte] at hfits_env
    exact hfits_env
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcbz := beq_lsl5_zero_eq_false hnew_pos (by omega)
  have hlsl : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay : RustLayoutOk (new.toNat * 32) 8 := ⟨⟨by omega, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim ()
  rw [← A.pool_of_vmPreserved hpost]
  wp_steps_sync_pool (lsρ spqrRustAllocSym)
  simp only [State.setMem_setMem]
  simp only [Bool.false_eq_true, ↓reduceIte] at halloc
  wp_call halloc (new.toNat * 32, 8, st)
  have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
  simp only [finishGrow7Events, ↓reduceIte,
    pointsToBytes_nil, List.length_nil, BitVec.add_zero, Nat.sub_zero, emp_sepConj]
  wp_done

theorem finish_grow_7_ne_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hrealloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7ReallocSpecG M A lim hookStack) := by
  unfold finishGrow7ReallocSpecG finishGrow7SpecWithStack
  simp only [memRegion_24, stackAt_finishGrow32_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨⟨out, cap, ptr, new, bs⟩, st⟩
  dsimp only at *
  have hcap_ne : cap ≠ 0#64 := by assumption
  have hbs_le_cap : bs.length ≤ cap.toNat * 32 := by assumption
  have hcap_le_new : cap.toNat ≤ new.toNat := by assumption
  have hnew_pos : 0 < new.toNat := by assumption
  have hnew_bound : new.toNat * 32 + 8 ≤ 2 ^ 63 := by omega
  have hfits_env : FitsEnv M lim st (FinishGrow7Env ⟨out, cap, ptr, new, bs⟩) := by assumption
  have hfits : FitsEvents M lim st (rustReallocEvents (cap.toNat * 32) (new.toNat * 32) 8) := by
    simp only [fitsEnv_finishGrow7_iff, finishGrow7Events, hcap_ne, ↓reduceIte] at hfits_env
    exact hfits_env
  have hcap_pos : 0 < cap.toNat :=
    Nat.pos_of_ne_zero (fun hc => hcap_ne (BitVec.eq_of_toNat_eq hc))
  have hlt64 : new.toNat * 32 < 2 ^ 64 := by omega
  have hcap_le : cap.toNat * 32 ≤ new.toNat * 32 := Nat.mul_le_mul_right 32 hcap_le_new
  have hcap_lt64 : cap.toNat * 32 < 2 ^ 64 := by omega
  have hlsr59 := lsr59_eq_zero (new := new) (by omega)
  have hhi := hi_32_eq_false (new := new) (by omega)
  have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap_ne
  have hlsl_cap : (cap <<< 5).toNat = cap.toNat * 32 := lsl5_toNat hcap_lt64
  have hlsl_new : (new <<< 5).toNat = new.toNat * 32 := lsl5_toNat hlt64
  have hle_new : bs.length ≤ new.toNat * 32 := by omega
  have hpow : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  have hlay_old : RustLayoutOk (cap.toNat * 32) 8 := ⟨⟨by omega, hpow, by omega⟩, by decide⟩
  have hlay : RustLayoutOk (new.toNat * 32) 8 := ⟨⟨by omega, hpow, hnew_bound⟩, by decide⟩
  wp_steps_sync_pool (lsρ spqrRustReallocSym)
  simp only [State.setMem_setMem]
  wp_call hrealloc (ptr, cap.toNat * 32, 8, new.toNat * 32, bs, st)
  have hlsl_bv : new <<< 5 = BitVec.ofNat 64 (new.toNat * 32) := lsl5_eq_ofNat hlt64
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  apply CryptoVerification.LibsignalTripleRatchet.SepWP.instantiate_post_exists (sf.readReg64 Reg.x0)
  simp only [finishGrow7Events, hcap_ne, ↓reduceIte]
  wp_done

theorem finish_grow_7_placed_ok_of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack))
    (hrealloc : subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (lsρ spqrRustReallocSym) (rustCliReallocNoOomExternSpecWithStack M A lim hookStack)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7SpecWithStack M A lim hookStack) :=
  finish_grow_7_placed_of_zero_ne
    (finish_grow_7_zero_placed_ok_of_hooks hhook hshim halloc)
    (finish_grow_7_ne_placed_ok_of_hooks hhook hrealloc)

theorem finish_grow_7_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7Spec M A lim) :=
  finish_grow_7_placed_ok_of_hooks (hookStack := allocHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim allocHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

theorem finish_grow_7_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat H spqrRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok ((blkPC_259).rebase (blkPl_259).base H)
      (blkPl_259).base
      (finishGrow7SpecX M A lim) :=
  finish_grow_7_placed_ok_of_hooks (hookStack := extHookStack) (by decide)
    (session2ShimWithStack_of_noAllocShim extHookStack (spqr_hook_ok_of_mem hshim))
    (subroutine_ok_allocNoOom_externWithStack_of_hookSat halloc spqr_externAt?_of_mem)
    (subroutine_ok_reallocNoOom_externWithStack_of_hookSat hrealloc spqr_externAt?_of_mem)

end LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrowBudget
