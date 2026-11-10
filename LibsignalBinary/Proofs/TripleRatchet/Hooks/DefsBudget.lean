/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge

/-!
# Budget-Threaded Hook Specifications

`VmPreserved`-strengthened contracts for the Rust no-alloc shim and libc memory operations,
together with allocator-budget contracts and event envelopes for
`prost::encoding::varint::decode_varint_slow::<&mut &[u8]>`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget

open Arm64 ProofLib
open CryptoVerification.LibsignalTripleRatchet
  (varintSlow decodeErrorAtStackLen decodeErrorHookStack extHookStack
   sessionShimSpec sessionMemcpyRegionSpec sessionMemcpySpec
   sessionMemmoveSpec sessionMemsetRegionSpec sessionMemsetSpec)
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
   rustAllocEvents allocMemcpyVmSpec)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)

/-! ## `VmPreserved`-strengthened shim and memory contracts -/

def sessionShimBudgetSpec : Spec Unit :=
  { sessionShimSpec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ sessionShimSpec.post x s0 sf }

def sessionMemcpyRegionBudgetSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { sessionMemcpyRegionSpec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ sessionMemcpyRegionSpec.post x s0 sf }

def sessionMemcpyBudgetSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  { sessionMemcpySpec hookStack with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ (sessionMemcpySpec hookStack).post x s0 sf }

def sessionMemmoveBudgetSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
  { sessionMemmoveSpec hookStack with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ (sessionMemmoveSpec hookStack).post x s0 sf }

def sessionMemsetRegionBudgetSpec : Spec (BitVec 64 × BitVec 8 × Nat) :=
  { sessionMemsetRegionSpec with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ sessionMemsetRegionSpec.post x s0 sf }

def sessionMemsetBudgetSpec (hookStack : Nat := 4096) :
    Spec (BitVec 64 × BitVec 8 × Nat) :=
  { sessionMemsetSpec hookStack with
    post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ (sessionMemsetSpec hookStack).post x s0 sf }

theorem subroutine_ok_sessionShimBudget_of_rustAllocShimVm {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a rustAllocShimVmSpec) :
    subroutine_ok P a sessionShimBudgetSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [rustAllocShimVmSpec, sessionShimBudgetSpec, sessionShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1.2.1, hq.2⟩

theorem subroutine_ok_sessionMemcpyRegionBudget_of_allocMemcpyVm {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a allocMemcpyVmSpec) :
    subroutine_ok P a sessionMemcpyRegionBudgetSpec := by
  refine subroutine_ok_mono h ?_ ?_
  · rintro ⟨dst, src, bs⟩ R s0 hp
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec,
      allocMemcpyVmSpec] at hp ⊢
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hp
    rcases hp with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hlt : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 .x2).isLt
    have hx2_bv : s0.readReg64 .x2 = BitVec.ofNat 64 bs.length := by
      rw [← hx2, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2_bv, hlt⟩, ?_⟩
    rwa [sepConj_assoc]
  · rintro ⟨dst, src, bs⟩ R s0 sf hq
    dsimp only [allocMemcpyVmSpec, sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨⟨hx0, hacp, hvm⟩, hm⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hvm, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hacp.2.1⟩, ?_⟩
    rwa [← sepConj_assoc]

/-! ## `decode_varint_slow` budget envelope and specs -/

/-- Stack budget for `decode_varint_slow::<&mut &[u8]>`: 64-byte scratch frame plus
`decodeErrorHookStack` for `DecodeError::from` on the error path. -/
abbrev varintSlowStack : Nat := 64 + decodeErrorHookStack

/-- Exact allocator event sequence of `decode_varint_slow::<&mut &[u8]>`:
    `[]` on `some (v, k)`, and `rustAllocEvents 72 8` (`DecodeError::from`'s 72-byte `Box<Inner>`)
    on `none`. -/
def decodeVarintSlowEvents (bs : List (BitVec 8)) : List AllocEvent :=
  match varintSlow bs with
  | some _ => []
  | none => rustAllocEvents 72 8

def DecodeVarintSlowEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = decodeVarintSlowEvents bs

/-- Allocator-budget contract for `decode_varint_slow::<&mut &[u8]>` under
    `FitsEnv M lim st (DecodeVarintSlowEnv bs)`. Ghost: `(slotA, slot, ptr, bs, st)`. -/
def decodeVarintSlowBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) where
  pre := fun (slotA, slot, ptr, bs, st) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64 ∧
      FitsEnv M lim st (DecodeVarintSlowEnv bs)⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt s.sp varintSlowStack
  post := fun (slotA, slot, ptr, bs, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp varintSlowStack ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))

/-- Stack-parameterized variant of `decodeVarintSlowBudgetSpec`. -/
def decodeVarintSlowBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) where
  pre := fun (slotA, slot, ptr, bs, st) s =>
    ⌜s.readReg64 .x0 = slotA ∧ bs.length < 2 ^ 64 ∧
      FitsEnv M lim st (DecodeVarintSlowEnv bs)⌝ ∗
      (slotA ↦₆₄ slot) ∗ (slot ↦₆₄ ptr) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ A.pool lim st s ∗ stackAt s.sp hookStack
  post := fun (slotA, slot, ptr, bs, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (slotA ↦₆₄ slot) ∗ (ptr ↦ₛ bs) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeVarintSlowEnv bs evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp hookStack ∗
      match varintSlow bs with
      | some (v, k) =>
        ⌜sf.readReg64 .x0 = 0#64 ∧ sf.readReg64 .x1 = v⌝ ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 k)) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - k))
      | none =>
        ⌜sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 ≠ 0#64⌝ ∗
          decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x1) 0 ∗
          (slot ↦₆₄ (ptr + BitVec.ofNat 64 (min 10 bs.length))) ∗
          ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (bs.length - min 10 bs.length))

theorem decodeVarintSlowBudgetSpecWithStack_eq_varintSlowStack
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    decodeVarintSlowBudgetSpecWithStack M A lim varintSlowStack =
      decodeVarintSlowBudgetSpec M A lim :=
  rfl

end LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
