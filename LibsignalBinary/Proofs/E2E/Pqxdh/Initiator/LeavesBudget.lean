/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.Leaves
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.Placed.GenLsBlock

/-!
# Budget-Threaded Specifications and Placed Contracts for PQXDH Initiator Leaves

Defines `RustCliAllocBudget M` allocation envelopes and contracts for `do_reserve_and_handle [local#6]`
(`doReserve6Spec`), `<kem::Ciphertext>::serialize` (`kemCiphertextSerializeSpec`), and
`<kem::Key<Public>>::serialize` (`kemPubKeySerializeSpec`), and proves
`kemCiphertextSerialize_placed_ok` on Block `71`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_71 blkPl_71
  ls_hook_ok_of_mem lsMemcpySym lsRustAllocSym lsRustNoAllocShimSym lsρ
)
open CryptoVerification.RustHeap (allocHookStack vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  DoReserveCall reserveCap doReserveStack tryCloneFromRefStack
)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents RustCliAllocBudget
  VmPreserved rustAllocEvents rustReallocEvents rustCliAllocBudgetSpec
  rustCliAllocNoOomExternSpecWithStack subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  rustAllocShimVmSpec allocMemcpyVmSpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `do_reserve_and_handle [local#6]` (`doReserve6Spec`) -/

/-- Deterministic `AllocEvent` list emitted by `do_reserve_and_handle` (`doReserve6Spec`). -/
def doReserveEvents (x : DoReserveCall) : List AllocEvent :=
  let newCap := reserveCap x.cap.toNat x.bs.length x.additional
  if x.cap = 0#64 then
    rustAllocEvents newCap 1
  else
    rustReallocEvents x.cap.toNat newCap 1

/-- Allocation envelope for `do_reserve_and_handle` (`doReserve6Spec`). -/
def DoReserveEnv (x : DoReserveCall) (evs : List AllocEvent) : Prop :=
  evs = doReserveEvents x

/-- Budget-threaded specification of `do_reserve_and_handle [local#6]` (`onPanic = onOom = ⌜False⌝`). -/
def doReserve6Spec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DoReserveCall × M.σ) where
  pre := fun (x, st) s =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜s.readReg64 .x0 = x.v ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      (s.readReg64 .x2).toNat = x.additional ∧ newCap + 1 ≤ 2 ^ 63 ∧
      FitsEvents M lim st (doReserveEvents x)⌝ ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp doReserveStack
  post := fun (x, st) s0 sf =>
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    ⌜sf.trace = s0.trace⌝ ∗
      (∃∗ p' : BitVec 64, vecU8At A.repAlloc x.v (BitVec.ofNat 64 newCap) p' x.bs) ∗
      A.pool lim (M.stepEvents (doReserveEvents x) st) sf ∗
      stackAt s0.sp doReserveStack

/-! ## 2. `<kem::Ciphertext>::serialize` & `<kem::Key<Public>>::serialize` -/

/-- Deterministic `1569`-byte allocation envelope for KEM ciphertext / public-key serialization. -/
def KemSerialize1569Env (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents 1569 1

private theorem stackAt_kemSerialize48 (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp 4096 6 (by decide)

private theorem memRegion_1569_split (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), memRegion_one]

/-- Budget-threaded specification of `<kem::Ciphertext>::serialize` (Block `71`). -/
def kemCiphertextSerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((hdrPtr, boxPtr, ctBytes), st) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568 ∧
      FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
      (boxPtr ↦ₛ ctBytes) ∗ A.pool lim st s ∗ stackAt s.sp tryCloneFromRefStack
  post := fun ((hdrPtr, boxPtr, ctBytes), st) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧
        sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧
        tempPtr ≠ 0#64⌝ ∗
        (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
        (boxPtr ↦ₛ ctBytes) ∗
        (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 1569 1) st) sf ∗
        stackAt s0.sp tryCloneFromRefStack

/-- Budget-threaded specification of `<kem::Key<Public>>::serialize [local#1]`. -/
def kemPubKeySerializeSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((boxPtr, pkBytes), st) s =>
    ⌜s.readReg64 .x0 = boxPtr ∧ s.readReg64 .x1 = 1568#64 ∧ pkBytes.length = 1568 ∧
      FitsEvents M lim st (rustAllocEvents 1569 1)⌝ ∗
      (boxPtr ↦ₛ pkBytes) ∗ A.pool lim st s ∗ stackAt s.sp tryCloneFromRefStack
  post := fun ((boxPtr, pkBytes), st) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧
        sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧
        tempPtr ≠ 0#64⌝ ∗
        (boxPtr ↦ₛ pkBytes) ∗
        (tempPtr ↦ₛ (8#8 :: pkBytes)) ∗ A.live tempPtr 1569 1 ∗
        A.pool lim (M.stepEvents (rustAllocEvents 1569 1) st) sf ∗
        stackAt s0.sp tryCloneFromRefStack

/-! ## 3. Relocatable `[LibsignalPlacement]` Contract (`kemCiphertextSerialize_placed_ok`) -/

/-- Relocatable `[LibsignalPlacement]` verification of `<kem::Ciphertext>::serialize` (Block `71`)
against `kemCiphertextSerializeSpec M A lim`. -/
theorem kemCiphertextSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym allocMemcpyVmSpec) :
    subroutine_ok ((blkPC_71).rebase (blkPl_71).base H) (blkPl_71).base
      (kemCiphertextSerializeSpec M A lim) := by
  unfold kemCiphertextSerializeSpec
  simp only [stackAt_kemSerialize48]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustNoAllocShimSym) rustAllocShimVmSpec := ls_hook_ok_of_mem hshim
  have halloc0 : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) := ls_hook_ok_of_mem halloc
  have halloc' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false allocHookStack) :=
    subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget halloc0)
  have hmemcpy' : subroutine_ok ((blkPC_71).rebase (blkPl_71).base H)
      (lsρ lsMemcpySym) allocMemcpyVmSpec := ls_hook_ok_of_mem hmemcpy
  dsimp only [rustAllocShimVmSpec] at hshim'
  dsimp only [allocMemcpyVmSpec] at hmemcpy'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  wp_init g s0
  rcases g with ⟨⟨hdrPtr, boxPtr, ctBytes⟩, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = hdrPtr›
  have hfe_raw : FitsEvents M lim st [.alloc 1569] := by
    simpa [rustAllocEvents] using ‹FitsEvents M lim st (rustAllocEvents 1569 1)›
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hpos : 0 < (1569 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (1569 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  have htr_shim : sf.trace = s0.trace := ‹AllocCallPreserved s0 sf›.2.1
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (1569, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_1569_split, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun b0 => ?_
  wp_steps_sync_pool (lsρ lsMemcpySym)
  simp only [State.setMem_setMem]
  have hlen_lt : ctBytes.length < 2 ^ 64 := by rw [‹ctBytes.length = 1568›]; decide
  rw [← ‹ctBytes.length = 1568›]
  wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
  have htr_mc : sf_2.trace = sf_1.trace := ‹AllocCallPreserved _ sf_2›.2.1
  have htr_all : sf_2.trace = s0.trace := by
    rw [htr_mc, ‹sf_1.trace = sf.trace›, htr_shim]
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf_2› (hnext := ?_)
  wp_steps
  simp only [pointsToBytes_cons]
  wp_done

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
