/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerialize
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded Relocatable Proofs for `<PrivateKey>::serialize`

Proves `[LibsignalPlacement]` `RustCliAllocBudget` contracts (`privSerializeSpecWithStack`,
`privSerializeSpec`, and `privSerializeSpecX`) for `<PrivateKey>::serialize`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget

open Arm64 ProofLib
open CryptoVerification (
  LibsignalPlacement blkPC_208 blkPl_208
  lsRustAllocSym lsRustNoAllocShimSym ls_hook_ok_of_mem lsρ
)
open CryptoVerification.RustHeap (allocHookStack vecHeader vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack privSerializeStackX subroutine_ok_withStack_of_subroutine_ok withStack
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FitsEvents RustCliAllocBudget VmPreserved
  rustAllocEvents rustCliAllocBudgetSpec rustCliAllocNoOomExternSpecWithStack
  subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  subroutine_ok_rustCliAllocNoOom_externWithStack
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget (
  PrivSerializeEnv privSerializeEvents privSerializeSpec privSerializeSpecWithStack
  privSerializeSpecX
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_privSerialize_opt {hookStack padBelow totalStack : Nat}
    (htot : (hookStack + padBelow) + 32 = totalStack) (hstack : totalStack ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp totalStack =
      memRegion (sp - 32#64 - BitVec.ofNat 64 (hookStack + padBelow)) padBelow ∗
      stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  subst htot
  rw [stackAt_split_cells sp (hookStack + padBelow) 4 hstack,
    stackAt_split_bottom (sp - 32#64) hookStack padBelow (by omega),
    sepConj_assoc]

private theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [memRegion_split a 8 16 (by decide),
    memRegion_split (a + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        (a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u2) ∗ ((a + 16#64) ↦₆₄ u1) ∗ ((a + 24#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 8 24 (by decide),
    memRegion_split (a + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 8 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private def privSerializeSpec32WithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (totalStack : Nat) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) where
  pre := (privSerializeSpecWithStack M A lim totalStack).pre
  post := fun (k, bs, ret, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (k ↦ₛ bs) ∗
      (∃∗ ptr : BitVec 64, vecU8At A.repAlloc ret 32#64 ptr bs) ∗
      A.pool lim (M.stepEvents privSerializeEvents st) sf ∗ stackAt s0.sp totalStack

private theorem privSerializeSpec32WithStack_post_entails (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (totalStack : Nat)
    (x : BitVec 64 × List (BitVec 8) × BitVec 64 × M.σ) (s0 sf : State) :
    (privSerializeSpec32WithStack M A lim totalStack).post x s0 sf ⊢
      (privSerializeSpecWithStack M A lim totalStack).post x s0 sf := by
  rcases x with ⟨k, bs, ret, st⟩
  dsimp only [privSerializeSpec32WithStack, privSerializeSpecWithStack, vecU8]
  exact sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left
      (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A.repAlloc ret cap ptr bs) 32#64)))

/-- Relocatable `<libsignal_core::curve::PrivateKey>::serialize` (Block `208`) parameterized by
stack-framed shim and no-OOM budget allocator contracts. -/
theorem privSerialize_placed_ok_of_contracts_opt [LibsignalPlacement]
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (H : String → Option (State → State))
    (hookStack padBelow totalStack : Nat)
    (htot : (hookStack + padBelow) + 32 = totalStack)
    (hstack : totalStack ≤ 2 ^ 64 := by decide)
    (hshim : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustNoAllocShimSym) (withStack sessionShimBudgetSpec hookStack))
    (halloc : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustCliAllocNoOomExternSpecWithStack M A lim false hookStack)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpecWithStack M A lim totalStack) := by
  refine subroutine_ok_mono (spec := privSerializeSpec32WithStack M A lim totalStack) ?_
    (fun _ _ _ h => h)
    (fun x _ s0 sf h => Satisfies.mono
      (sepConj_mono_left (privSerializeSpec32WithStack_post_entails M A lim totalStack x s0 sf)) h)
    (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
  have hshim' := hshim
  have halloc' := halloc
  dsimp only [withStack, sessionShimBudgetSpec,
    CryptoVerification.LibsignalTripleRatchet.sessionShimSpec] at hshim'
  dsimp only [rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack,
    LibsignalBinary.Heap.IfaceBudgetLemmas.rustCliAllocNoOomSpecWithStack,
    LibsignalBinary.Heap.RustLayoutOk, CryptoVerification.RustHeap.LayoutOk, ↓reduceIte] at halloc'
  simp only [privSerializeSpec32WithStack, privSerializeSpecWithStack, memRegion_24_cells,
    stackAt_privSerialize_opt htot hstack, sepExists_sepConj_left, sepExists_sepConj_right]
  cells_unfold
  wp_init x s0
  rcases x with ⟨k, bs, ret, st⟩
  dsimp only at *
  subst ‹s0.readReg64 .x0 = k›
  subst ‹s0.readReg64 .x8 = ret›
  have hbs32 : bs.length = 32 := by assumption
  obtain ⟨w0, w1, w2, w3, _, hkey_cells⟩ := exists_unpack64_of_length_32 hbs32
  rw [hkey_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hfits_ev : FitsEvents M lim st (rustAllocEvents 32 1) :=
    ‹LibsignalBinary.Heap.FitsEnv M lim st PrivSerializeEnv› privSerializeEvents rfl
  have hfe_raw : FitsEvents M lim st [.alloc 32] := by
    simpa [rustAllocEvents] using hfits_ev
  rcases hfe_raw with ⟨⟨hwma, henf, hram, hva⟩, -⟩
  have hpow2 : ∃ j, 1 = 2 ^ j := ⟨0, rfl⟩
  have hpos : 0 < (32 : Nat) := by decide
  have hal : (1 : Nat) ≤ 2 ^ 31 := by decide
  have hsum : (32 : Nat) + 1 ≤ 2 ^ 63 := by decide
  wp_steps_sync_pool (lsρ lsRustNoAllocShimSym)
  simp only [State.setMem_setMem]
  wp_call hshim' ()
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_pool (lsρ lsRustAllocSym)
  simp only [State.setMem_setMem]
  wp_call halloc' (32, 1, st)
  have hne : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := by assumption
  have hbeq : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hne
  simp only [memRegion_32_cells, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun u0 => SepWP.exists_elim fun u1 =>
    SepWP.exists_elim fun u2 => SepWP.exists_elim fun u3 => ?_
  have htr_all : sf_1.trace = s0.trace := by
    rw [‹sf_1.trace = sf.trace›, ‹sf.trace = _›]
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem, vecU8At, vecHeader, hbs32, privSerializeEvents,
    RustCliAllocBudget.repAlloc_live,
    (by decide : (32#64 : BitVec 64) = 0 ↔ False),
    ite_false, (by decide : (32#64 : BitVec 64).toNat = 32),
    Nat.sub_self, memRegion_zero, sepConj_emp, hkey_cells]
  wp_done

/-- Relocatable `<libsignal_core::curve::PrivateKey>::serialize` (Block `208`) meets
`privSerializeSpec M A lim` under `sessionShimBudgetSpec` (= `withVmPreserved noAllocShimSpec`). -/
theorem privSerialize_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpec M A lim) :=
  privSerialize_placed_ok_of_contracts_opt A lim H allocHookStack 12256 extHookStack
    (by decide) (by decide)
    (subroutine_ok_withStack_of_subroutine_ok (ls_hook_ok_of_mem hshim) allocHookStack)
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

/-- Relocatable `<libsignal_core::curve::PrivateKey>::serialize` (Block `208`) meets
`privSerializeSpecX M A lim` under `sessionShimBudgetSpec` (= `withVmPreserved noAllocShimSpec`). -/
theorem privSerialize_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpecX M A lim) :=
  privSerialize_placed_ok_of_contracts_opt A lim H extHookStack 0 privSerializeStackX
    (by decide) (by decide)
    (subroutine_ok_withStack_of_subroutine_ok (ls_hook_ok_of_mem hshim) extHookStack)
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := extHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem privSerialize_placed_ok_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpec M A lim) :=
  privSerialize_placed_ok_of_contracts_opt A lim H allocHookStack 12256 extHookStack
    (by decide) (by decide)
    (subroutine_ok_withStack_of_subroutine_ok
      (subroutine_ok_sessionShimBudget_of_rustAllocShimVm (ls_hook_ok_of_mem hshim)) allocHookStack)
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := allocHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

theorem privSerialize_placed_ok_x_of_vm [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : String → Option (State → State)}
    (hshim : HookSat H lsRustNoAllocShimSym rustAllocShimVmSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (blkPl_208).base
      (privSerializeSpecX M A lim) :=
  privSerialize_placed_ok_of_contracts_opt A lim H extHookStack 0 privSerializeStackX
    (by decide) (by decide)
    (subroutine_ok_withStack_of_subroutine_ok
      (subroutine_ok_sessionShimBudget_of_rustAllocShimVm (ls_hook_ok_of_mem hshim)) extHookStack)
    (subroutine_ok_rustCliAllocNoOom_externWithStack (stk := extHookStack)
      (by decide) (by decide) (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_mem halloc)))

end LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PrivateKeySerializeBudget
