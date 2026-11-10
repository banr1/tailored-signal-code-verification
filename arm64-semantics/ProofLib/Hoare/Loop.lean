/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.Simulation
public import ProofLib.Abi.Aapcs
import Arm64.Trusted.Spec.SepLogic

/-!
# Floyd-Hoare Loop Verification Rules

Well-founded `Nat`-measure induction principles over `reaches_pc` (`reaches_pc_cutset` for general
cut sets and `reaches_pc_loop` for single-header loops) and the `subroutine_ok_of_loop` wrapper.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- Well-founded cut-set reachability rule (Floyd's method): any state satisfying `Inv` reaches
    `exit_pc` with `post` if each cut-set step either exits or strictly decreases `measure`. -/
theorem reaches_pc_cutset {prog : Program} (exit_pc : BitVec 64)
    (Inv : State → Prop) (measure : State → Nat) (post : State → Prop)
    {oom : State → Prop}
    (h_step : ∀ s, s.status = .Running → Inv s →
      (∃ s', Steps prog s s' ∧ s'.status = .Running ∧ Inv s' ∧ measure s' < measure s) ∨
      reaches_pc prog exit_pc s post oom)
    (s0 : State) (h_run : s0.status = .Running) (h_inv : Inv s0) :
    reaches_pc prog exit_pc s0 post oom := by
  have h_aux : ∀ m s, measure s ≤ m → s.status = .Running → Inv s → reaches_pc prog exit_pc s post oom := by
    intro m
    induction m with
    | zero =>
      intro s hm hrun hinv
      rcases h_step s hrun hinv with ⟨s', _, _, _, hlt⟩ | h_exit
      · omega
      · exact h_exit
    | succ m ih =>
      intro s hm hrun hinv
      rcases h_step s hrun hinv with ⟨s', hsteps1, hrun', hinv', hlt⟩ | h_exit
      · exact reaches_pc_steps hsteps1 (ih s' (by omega) hrun' hinv')
      · exact h_exit
  exact h_aux (measure s0) s0 (Nat.le_refl _) h_run h_inv

/-- Single-header loop reachability rule at `loop_pc` with `Nat` variant `measure`. -/
theorem reaches_pc_loop {prog : Program} (loop_pc exit_pc : BitVec 64)
    (Inv : State → Prop) (measure : State → Nat) (post : State → Prop)
    {oom1 oom2 : State → Prop}
    (h_step : ∀ s, s.pc = loop_pc → s.status = .Running → Inv s →
      reaches_pc prog loop_pc s (fun s' => Inv s' ∧ measure s' < measure s) oom1 ∨
      reaches_pc prog exit_pc s post oom2)
    (s0 : State) (h_pc : s0.pc = loop_pc) (h_run : s0.status = .Running) (h_inv : Inv s0)
    (h_oom : ∀ sf, sf.status = .OutOfMemory → oom1 sf → oom2 sf := by
      intro _ _ ho; first | exact ho | exact False.elim ho | exact False.elim (not_satisfies_false_sepConj ho)) :
    reaches_pc prog exit_pc s0 post oom2 := by
  have h_aux : ∀ m s, measure s ≤ m → s.pc = loop_pc → s.status = .Running → Inv s →
      reaches_pc prog exit_pc s post oom2 := by
    intro m
    induction m with
    | zero =>
      intro s hm hpc hrun hinv
      rcases h_step s hpc hrun hinv with h_loop | h_exit
      · exact reaches_pc_seq h_loop (fun s' _ _ ⟨_, hlt⟩ => by omega) h_oom
      · exact h_exit
    | succ m ih =>
      intro s hm hpc hrun hinv
      rcases h_step s hpc hrun hinv with h_loop | h_exit
      · exact reaches_pc_seq h_loop (fun s' hpc' hrun' ⟨hinv', hlt⟩ => ih s' (by omega) hpc' hrun' hinv') h_oom
      · exact h_exit
  exact h_aux (measure s0) s0 (Nat.le_refl _) h_pc h_run h_inv

/-- Subroutine Hoare rule for a function containing a loop at header `loop_pc`. -/
theorem subroutine_ok_of_loop {α : Type} {prog : Program} (entry_pc loop_pc : BitVec 64) (spec : Spec α)
    (Inv : α → State → State → Prop)
    (measure : α → State → Nat)
    (h_init : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry_pc → s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) → s0.spAligned = true →
      reaches_pc prog loop_pc s0 (fun sl => Inv x s0 sl ∧ CallingConventionPreserved s0 sl))
    (h_step : ∀ (x : α) (R : SepProp) (s0 s : State), s.pc = loop_pc → s.status = .Running →
      (s0.mem ⊨ spec.pre x s0 ∗ R) →
      Inv x s0 s ∧ CallingConventionPreserved s0 s →
      reaches_pc prog loop_pc s (fun s' =>
        (Inv x s0 s' ∧ CallingConventionPreserved s0 s') ∧ measure x s' < measure x s) ∨
      reaches_pc prog (s0.readReg64 Reg.lr) s (SubroutinePost spec x R s0)) :
    subroutine_ok prog entry_pc spec :=
  subroutine_ok_intro fun x R s0 hpc hrun hpre hsp =>
    reaches_pc_seq (h_init x R s0 hpc hrun hpre hsp) fun sl hpcl hrunl hinvl =>
      reaches_pc_mono
        (reaches_pc_loop loop_pc (s0.readReg64 Reg.lr)
          (fun s => Inv x s0 s ∧ CallingConventionPreserved s0 s)
          (measure x) (SubroutinePost spec x R s0)
          (fun s hpcs hruns hinv => h_step x R s0 s hpcs hruns hpre hinv) sl hpcl hrunl hinvl)
        fun _ _ _ hp => hp

end ProofLib
