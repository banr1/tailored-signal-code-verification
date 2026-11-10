/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.LogClosure
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
import ProofLib.Placed.Multi
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# `withLsFrozen` Wrappers for `try_decrypt_from_record::{closure#0}` (Blocks `159` and `462`)

Provides `withLsFrozen lsmpl logClosurePlacedSpec` contracts under `[LibsignalFullPlacement]`
for the mutated `try_decrypt_from_record` failure-log closures:
- Block `159` (`try_decrypt_from_record::<HookRng>::{closure#0}`)
- Block `462` (`try_decrypt_from_record::<Coins>::{closure#0}`)
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees

open Arm64 Arm64.Obj ProofLib
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

/-- Lift any plain `subroutine_ok` contract to `withLsFrozen pl spec`. -/
theorem subroutine_ok_withLsFrozen_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsFrozen pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsFrozen hp).2) (fun _ _ _ _ hq => hq)

/-- Lift a `withLsFrozen lsmpl` contract from any block `j < 624` (including mutated blocks
`159` and `462`) to any `callerProg` under `[LibsignalFullPlacement]`. -/
theorem ls_subroutine_ok_withLsFrozen_of_block_frc [LibsignalFullPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsFrozen lsmpl spec))
    (hj : j < 624 := by decide) :
    subroutine_ok callerProg entry (withLsFrozen lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hfr0, _⟩ := extract_withLsFrozen hpre
  have hlt_blocks : j < libsignalSessionLib.blocks.length := by
    rw [libsignalSessionLib_blocks_length]; omega
  have hQL : calleeProg.CodeLoaded s0.mem := by
    rw [hcallee_prog.eq_blockProgram]
    have h := hfr0.2 j hlt_blocks
    rwa [Program.codeLoaded_iff] at h ⊢
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

/-- Block `159` own-program `withLsFrozen` contract under `[LibsignalFullPlacement]`. -/
theorem log_closure_frozen_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_159).rebase (blkPl_159).base H) (lsmpl.base 159)
      (withLsFrozen lsmpl logClosurePlacedSpec) :=
  subroutine_ok_withLsFrozen_of_plain (log_closure_placed_ok H)

/-- Block `462` own-program `withLsFrozen` contract under `[LibsignalFullPlacement]`. -/
theorem log_closure_coins_frozen_placed_ok [LibsignalFullPlacement]
    (H : LibsignalHooks) :
    subroutine_ok ((blkPC_462).rebase (blkPl_462).base H) (lsmpl.base 462)
      (withLsFrozen lsmpl logClosurePlacedSpec) :=
  subroutine_ok_withLsFrozen_of_plain (log_closure_coins_placed_ok H)

/-- Lift Block `159` (`try_decrypt_from_record::<HookRng>::{closure#0}`) to any `callerProg`
under `[LibsignalFullPlacement]`. -/
theorem log_closure_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 159)
      (withLsFrozen lsmpl logClosurePlacedSpec) :=
  ls_subroutine_ok_withLsFrozen_of_block_frc (log_closure_frozen_placed_ok H)

/-- Lift Block `462` (`try_decrypt_from_record::<Coins>::{closure#0}`) to any `callerProg`
under `[LibsignalFullPlacement]`. -/
theorem log_closure_coins_frozen_placed_ok_of_block [LibsignalFullPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] :
    subroutine_ok callerProg (lsmpl.base 462)
      (withLsFrozen lsmpl logClosurePlacedSpec) :=
  ls_subroutine_ok_withLsFrozen_of_block_frc (log_closure_coins_frozen_placed_ok H)

end LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees
