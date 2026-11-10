/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosure
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget

/-!
# `VmPreserved` Relocatable Contracts for `try_decrypt_from_record::{closure#0}` (Blocks `159` & `462`)

Proves `withVmPreserved logClosurePlacedSpec` on blocks `159` (`HookRng`) and `462` (`Coins`) under
`[LibsignalFullPlacement]`, along with `withLsCodeLoaded`, `libsignalSessionLib.withCodeLoaded`, and
`withLsFrozen` cross-block transfer lemmas for mutated blocks (`159, 462 ∈ libsignalMutatedBlocks`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoVerification (
  IsLsBlockProg LibsignalFullPlacement LibsignalHooks blkPC_159 blkPl_159 blkPC_462 blkPl_462
  extract_withCodeLoaded libsignalSessionLib libsignalSessionLib_blocks_length
  ls_externAt?_blockProgram_eq_of_externs_eq lsProg_159 lsProg_462 lsmpl
  subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchet (extract_withLsFrozen withLsFrozen)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  logClosurePlacedSpec log_closure_coins_placed_ok log_closure_placed_ok
)
open CryptoVerification.LibsignalTripleRatchet.Record (blkPC_197 blkPl_197)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget (ls_subroutine_ok_plain_vmPreserved)

/-! ## 1. Own-Block `withVmPreserved` & `withLsCodeLoaded` Contracts (Blocks `159` & `462`) -/

/-- Block `159` (`try_decrypt_from_record::<HookRng>::{closure#0}`) satisfies
`withVmPreserved logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_vm_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_159).rebase (blkPl_159).base H) (lsmpl.base 159)
      (withVmPreserved logClosurePlacedSpec) :=
  ls_subroutine_ok_plain_vmPreserved
    (progQ := (blkPC_159).rebase (blkPl_159).base (hooksException H))
    (i := 159) (by decide +kernel)
    (hok := log_closure_placed_ok (hooksException H))

/-- Block `462` (`try_decrypt_from_record::<Coins>::{closure#0}`) satisfies
`withVmPreserved logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_coins_vm_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_462).rebase (blkPl_462).base H) (lsmpl.base 462)
      (withVmPreserved logClosurePlacedSpec) :=
  ls_subroutine_ok_plain_vmPreserved
    (progQ := (blkPC_462).rebase (blkPl_462).base (hooksException H))
    (i := 462) (by decide +kernel)
    (hok := log_closure_coins_placed_ok (hooksException H))

/-- Block `159` `withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)` wrapper on its own
block program. -/
theorem log_closure_vm_codeLoaded_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_159).rebase (blkPl_159).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (log_closure_vm_placed_ok H)

/-- Block `462` `withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)` wrapper on its own
block program. -/
theorem log_closure_coins_vm_codeLoaded_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_462).rebase (blkPl_462).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  subroutine_ok_withLsCodeLoaded_of_plain (log_closure_coins_vm_placed_ok H)

/-! ## 2. Cross-Block Transfer for Mutated Blocks (`159, 462 ∈ libsignalMutatedBlocks`) -/

private theorem ls_subroutine_ok_fullCodeLoaded_of_block [LibsignalFullPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hj : j < 619 := by decide) :
    subroutine_ok callerProg entry (libsignalSessionLib.withCodeLoaded lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, hpre0⟩ := extract_withCodeLoaded hpre
  have hlt_blocks : j < libsignalSessionLib.blocks.length := by
    rw [libsignalSessionLib_blocks_length]; omega
  have hQL : calleeProg.CodeLoaded s0.mem := by
    rw [hcallee_prog.eq_blockProgram]
    have h := hcl0 j hlt_blocks
    rwa [Program.codeLoaded_iff] at h ⊢
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre0 hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

private theorem subroutine_ok_withLsFrozen_of_fullCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (libsignalSessionLib.withCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsFrozen pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsFrozen hp
      dsimp only [MultiPlacedLib.withCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.2, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Cross-block transfer of Block `159` (`logClosurePlacedSpec` + `VmPreserved`) onto any
`callerProg` under `libsignalSessionLib.withCodeLoaded lsmpl`. -/
theorem log_closure_fullCodeLoaded_vm_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 159)
      (libsignalSessionLib.withCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  ls_subroutine_ok_fullCodeLoaded_of_block
    (callerProg := callerProg) (calleeProg := lsProg_159 H)
    (log_closure_vm_placed_ok H) (by decide)

/-- Cross-block transfer of Block `462` (`logClosurePlacedSpec` + `VmPreserved`) onto any
`callerProg` under `libsignalSessionLib.withCodeLoaded lsmpl`. -/
theorem log_closure_coins_fullCodeLoaded_vm_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 462)
      (libsignalSessionLib.withCodeLoaded lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  ls_subroutine_ok_fullCodeLoaded_of_block
    (callerProg := callerProg) (calleeProg := lsProg_462 H)
    (log_closure_coins_vm_placed_ok H) (by decide)

/-- Cross-block transfer of Block `159` (`logClosurePlacedSpec` + `VmPreserved`) onto any
`callerProg` under `withLsFrozen lsmpl`. -/
theorem log_closure_frozen_vm_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 159)
      (withLsFrozen lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  subroutine_ok_withLsFrozen_of_fullCodeLoaded
    (log_closure_fullCodeLoaded_vm_placed_ok_of_block (callerProg := callerProg))

/-- Cross-block transfer of Block `462` (`logClosurePlacedSpec` + `VmPreserved`) onto any
`callerProg` (including `(blkPC_463).rebase (blkPl_463).base H`) under `withLsFrozen lsmpl`. -/
theorem log_closure_coins_frozen_vm_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 462)
      (withLsFrozen lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  subroutine_ok_withLsFrozen_of_fullCodeLoaded
    (log_closure_coins_fullCodeLoaded_vm_placed_ok_of_block (callerProg := callerProg))

/-- Block `197` → Block `159` `withLsFrozen lsmpl (withVmPreserved logClosurePlacedSpec)` contract. -/
theorem log_closure_blk197_frozen_vm_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsFrozen lsmpl (withVmPreserved logClosurePlacedSpec)) :=
  log_closure_frozen_vm_placed_ok_of_block
    (callerProg := (blkPC_197).rebase (blkPl_197).base H)

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosureVmPlacedBudget
