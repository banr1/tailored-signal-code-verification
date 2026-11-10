/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Exec
public import ProofLib.CoreLemmas
public import ProofLib.SimpAttrs
import Arm64.Trusted.Spec.SepLogic

/-!
# Deterministic Simulation Soundness

Connects the executable evaluators `stepState`, `execN`, and `execUntilPC` in `ProofLib.Exec` to
the relational small-step semantics `Step` and `Steps` in `Arm64`, and re-exports core
reachability combinators.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Soundness of `stepState`: `stepState prog s = some s'` implies `Step prog s s'`. -/
theorem stepState_sound {prog : Program} {s s' : State} (h_hooks : prog.HooksKeepFrozen)
    (h : stepState prog s = some s') : Step prog s s' := by
  dsimp [stepState] at h
  split at h
  · rename_i h_run
    split at h
    · rename_i f h_ext
      injection h with h_eq
      rw [← h_eq]
      obtain ⟨h_keep, h_sym⟩ := h_hooks _ _ s h_ext
      exact Step.extern h_run h_ext h_keep h_sym
    · rename_i h_ext
      split at h
      · rename_i inst h_fetch
        injection h with h_eq
        rw [← h_eq]
        exact Step.exec h_run h_fetch
      · rename_i h_fetch
        injection h with h_eq
        rw [← h_eq]
        exact Step.halt_unmapped h_run h_fetch h_ext
  · contradiction

/-- Soundness of `execN`: `execN n prog s` is always reachable from `s` via `Steps`. -/
theorem execN_steps (n : Nat) (prog : Program) (s : State) (h_hooks : prog.HooksKeepFrozen) :
    Steps prog s (execN n prog s) := by
  induction n generalizing s with
  | zero => exact Steps.refl s
  | succ n ih =>
    dsimp [execN]
    split
    · rename_i s' h_step
      exact Steps.step (stepState_sound h_hooks h_step) (ih s')
    · exact Steps.refl s

/-- Soundness of `execUntilPC`: `execUntilPC n prog target_pc s` is always reachable from `s` via `Steps`. -/
theorem execUntilPC_steps (n : Nat) (prog : Program) (target_pc : BitVec 64) (s : State)
    (h_hooks : prog.HooksKeepFrozen) :
    Steps prog s (execUntilPC n prog target_pc s) := by
  induction n generalizing s with
  | zero => exact Steps.refl s
  | succ n ih =>
    dsimp [execUntilPC]
    split
    · exact Steps.refl s
    · split
      · rename_i s' h_step
        exact Steps.step (stepState_sound h_hooks h_step) (ih s')
      · exact Steps.refl s

export Arm64 (reaches_pc_refl reaches_pc_step reaches_pc_ite
  reaches_outcome_refl_return reaches_outcome_refl_exit reaches_outcome_refl_panic reaches_outcome_step reaches_outcome_ite
  reaches_outcome_of_reaches_pc reaches_outcome_of_exits_with reaches_pc_of_reaches_outcome
  subroutine_ok_outcome_intro subroutine_ok_apply_outcome subroutine_ok_apply_running
  exits_with_refl exits_with_step exits_with_ite exits_with_mono exits_with_of_reaches_pc exit_ok_intro)

end ProofLib
