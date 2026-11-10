/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import ProofLib.SepLogic.WP.Apply

/-!
# Budget-Threaded and `VmPreserved` Placed Contracts for Small Initiator Callees

Proves `VmPreserved`-strengthened `[LibsignalPlacement]` contracts for
`<kem::Public as KeyKind>::key_length` (Block `110`),
`<SessionState>::set_unacknowledged_kyber_pre_key_id` (Block `34`), and
`<SessionState>::set_kyber_ciphertext` (Block `31`), plus budget-threaded contracts for
`<KyberPreKeyId as Display>::fmt` (Block `81`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  LibsignalHooks LibsignalPlacement blkPC_31 blkPl_31 blkPC_34 blkPl_34
  blkPC_81 blkPl_81 blkPC_110 blkPl_110 lsFmtWriteSym ls_hook_ok_of_mem lsρ
)
open CryptoVerification.RustHeap (vecU8)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.E2E.Pqxdh (
  kemPublicKeyLengthSpec kyberPreKeyIdDisplayStack
  setKyberCiphertextNoneSpec setUnackKyberPreKeyIdSpec
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv fmtWriteBudgetEnvSpec withVmPreserved)

/-! ## 1. `VmPreserved` Leaf Contracts (Blocks `110`, `34`, `31`) -/

private theorem subroutine_ok_withVmPreserved_intro {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → s0.mem ⊨ spec.pre x s0 ∗ R → s0.spAligned →
      SepWP prog (s0.readReg64 .x30) s0 (spec.pre x s0)
        (fun sf P_f => VmPreserved s0 sf ∧
          ((sf.mem ⊨ P_f ∗ R → sf.mem ⊨ spec.post x s0 sf ∗ R) ∧
           sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf))) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  refine subroutine_ok_of_sepWP fun x R s0 hpc hrun hpre hal => ⟨spec.pre x s0, R, hpre, ?_⟩
  refine SepWP.mono (h x R s0 hpc hrun hpre hal) fun sf P_f _ _ hpost => ?_
  rcases hpost with ⟨hvm, hq, hsp, hcs⟩
  refine ⟨fun hm => ?_, hsp, hcs⟩
  dsimp only [withVmPreserved]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hvm, hq hm⟩

def kemPublicKeyLengthBudgetSpec : Spec Unit :=
  withVmPreserved kemPublicKeyLengthSpec

theorem kemPublicKeyLength_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_110).rebase (blkPl_110).base H) (blkPl_110).base
      kemPublicKeyLengthBudgetSpec := by
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [kemPublicKeyLengthSpec] at *
  by_vm_steps (wp_steps; wp_done)

def setUnackKyberPreKeyIdBudgetSpec : Spec (BitVec 64 × BitVec 64 × BitVec 32) :=
  withVmPreserved setUnackKyberPreKeyIdSpec

private theorem cond_eq_adds_1_false {cap : BitVec 64} (hne : cap + 1#64 ≠ 0#64) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [ProofLib.conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

theorem setUnackKyberPreKeyId_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_34).rebase (blkPl_34).base H) (blkPl_34).base
      setUnackKyberPreKeyIdBudgetSpec := by
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  rcases x with ⟨statePtr, cap, kyberPreKeyId⟩
  dsimp only [setUnackKyberPreKeyIdSpec] at *
  by_vm_steps (
    wp_pull_exists
    refine SepWP.pure_elim ?_
    rintro ⟨rfl, rfl, hcap⟩
    have hcond : ConditionHolds .EQ (addsPState64 cap 1#64) = false := cond_eq_adds_1_false hcap
    wp_steps
    wp_done
  )

def setKyberCiphertextNoneBudgetSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) :=
  withVmPreserved setKyberCiphertextNoneSpec

theorem setKyberCiphertext_none_placed_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_31).rebase (blkPl_31).base H) (blkPl_31).base
      setKyberCiphertextNoneBudgetSpec := by
  apply subroutine_ok_withVmPreserved_intro
  intro x R s0 hpc hrun hpre hsp_align
  rcases x with ⟨statePtr, ctPtr, ctLen⟩
  dsimp only [setKyberCiphertextNoneSpec] at *
  cells_unfold
  by_vm_steps (
    wp_pull_exists
    refine SepWP.pure_elim ?_
    rintro ⟨rfl, rfl, rfl⟩
    wp_steps
    wp_done
  )

/-! ## 2. `<KyberPreKeyId as Display>::fmt` (Block `81`) -/

private theorem stackAt_kyberPreKeyIdDisplay (sp : BitVec 64) :
    stackAt sp kyberPreKeyIdDisplayStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 :=
  ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

def kyberPreKeyIdDisplayEnvSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : List AllocEvent → Prop := FmtWriteEnv) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) where
  pre := fun (f, v, vt, bs, st) s =>
    ⌜s.readReg64 .x1 = f ∧ FitsEnv M lim st Env⌝ ∗
      (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗ vecU8 A.repAlloc v bs ∗
      A.pool lim st s ∗ stackAt s.sp kyberPreKeyIdDisplayStack
  post := fun (f, v, vt, _, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
      (f ↦₆₄ v) ∗ ((f + 8#64) ↦₆₄ vt) ∗
      (∃∗ bs' : List (BitVec 8), vecU8 A.repAlloc v bs') ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp kyberPreKeyIdDisplayStack

abbrev kyberPreKeyIdDisplaySpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × M.σ) :=
  kyberPreKeyIdDisplayEnvSpec M A lim FmtWriteEnv

theorem kyberPreKeyIdDisplay_placed_ok_of_contract [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : LibsignalHooks}
    (hwrite : subroutine_ok ((blkPC_81).rebase (blkPl_81).base H)
      (lsρ lsFmtWriteSym) (fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_81).rebase (blkPl_81).base H) (blkPl_81).base
      (kyberPreKeyIdDisplayEnvSpec M A lim Env) := by
  simp only [kyberPreKeyIdDisplayEnvSpec, stackAt_kyberPreKeyIdDisplay]
  simp only [fmtWriteBudgetEnvSpec] at hwrite
  cells_unfold
  wp_init x s0
  rcases x with ⟨f, v, vt, bs, st⟩
  dsimp only at *
  subst h_1
  wp_steps_sync_pool (lsρ lsFmtWriteSym)
  simp only [State.setMem_setMem]
  wp_call hwrite (v, bs, st)
  wp_steps_sync_pool (s0.readReg64 (Reg.gpr 30#5))
  simp only [State.setMem_setMem]
  wp_done

theorem kyberPreKeyIdDisplay_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Env : List AllocEvent → Prop} {H : LibsignalHooks}
    (hW : HookSat H lsFmtWriteSym (fmtWriteBudgetEnvSpec M A lim Env)) :
    subroutine_ok ((blkPC_81).rebase (blkPl_81).base H) (blkPl_81).base
      (kyberPreKeyIdDisplayEnvSpec M A lim Env) :=
  kyberPreKeyIdDisplay_placed_ok_of_contract (ls_hook_ok_of_mem hW)

end LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesBudget
