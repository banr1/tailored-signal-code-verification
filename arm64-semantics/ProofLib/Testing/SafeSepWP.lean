/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.SafeSepWP

/-!
# Partial-Correctness Separation Logic Tests

Unit tests for `SafeSepWP`: proving `safe_subroutine_ok` on a diverging loop (`spin_safe`),
composing a caller with a diverging callee (`caller_safe`), and closing a terminating function
via `SafeSepWP.ret_of_sepWP` (`ret_safe`).
-/

@[expose] public section

namespace Testing.SafeSepWP

open Arm64 ProofLib

set_option autoImplicit false
arm64_proof_prelude

def spinCode : FnCode :=
  .atAddr "spin" 0x61000#64
    ("d503201f " ++ -- 0x61000: nop
     "17ffffff " ++ -- 0x61004: b 0x61000
     "97fffffe " ++ -- 0x61008: bl 0x61000
     "d65f03c0")    -- 0x6100c: ret

/-- Specification with postcondition `⌜False⌝`, satisfied only by non-returning code. -/
def neverReturns : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ _ _ => ⌜False⌝

theorem spin_safe (prog : Program) (h_code : spinCode.holds prog) :
    safe_subroutine_ok prog 0x61000#64 neverReturns := by
  apply safe_subroutine_ok_of_safeSepWP
  intro x R s0 hpc hrun hpre _
  refine ⟨emp, hpre, ?_⟩
  refine SafeSepWP.loop (fun st P => st.pc = 0x61000#64 ∧ st.status = .Running ∧ P = emp) ?_
    ⟨hpc, hrun, rfl⟩
  rintro st Pst ⟨hpc_s, hrun_s, rfl⟩
  refine SafeSepWP1.of_sepWP (mid := 0x61004#64) (by simp [hpc_s]) ?_
  wp_step
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
  refine SafeSepWP.of_sepWP (mid := 0x61000#64) ?_
  wp_step
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun_s]) ?_
  exact SafeSepWP.done (Or.inl ⟨by simp [wp_norm, arm64_norm],
    by simp [wp_norm, arm64_norm, hrun_s], rfl⟩)

theorem caller_safe (prog : Program) (h_code : spinCode.holds prog) :
    safe_subroutine_ok prog 0x61008#64 neverReturns := by
  apply safe_subroutine_ok_of_safeSepWP
  intro x R s0 hpc hrun hpre hsp
  refine ⟨emp, hpre, ?_⟩
  refine SafeSepWP.of_sepWP (mid := 0x61000#64) ?_
  wp_step
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine SafeSepWP.call_subroutine_frame (spin_safe prog h_code) (x := ()) (F := emp)
    (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (by simpa [wp_norm, arm64_norm] using hsp) rfl
    (fun R hm => by simpa [neverReturns, emp_sepConj] using hm) ?_
  intro sf _ _ _ _
  exact SafeSepWP.pure_elim fun h => h.elim

def retSpec : Spec (BitVec 64) where
  pre := fun v s0 => ⌜s0.readReg64 .x0 = v⌝
  post := fun v _ sf => ⌜sf.readReg64 .x0 = v⌝

theorem ret_safe (prog : Program) (h_code : spinCode.holds prog) :
    safe_subroutine_ok prog 0x6100c#64 retSpec := by
  apply safe_subroutine_ok_of_safeSepWP
  intro v R s0 hpc hrun hpre _
  refine ⟨retSpec.pre v s0, hpre, ?_⟩
  refine SafeSepWP.ret_of_sepWP ?_
  simp only [retSpec]
  refine SepWP.pure_elim_only fun hx0 => ?_
  wp_step
  refine SepWP.done (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨fun hm => ?_, by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  exact ⟨by simpa [wp_norm, arm64_norm] using hx0, by simpa [emp_sepConj] using hm⟩

end Testing.SafeSepWP
