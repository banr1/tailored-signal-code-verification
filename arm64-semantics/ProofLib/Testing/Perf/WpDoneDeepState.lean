/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public meta import ProofLib.Testing.Perf.Budget

/-!
# Performance Regression: `wp_done` on a Deep Uncompacted State

Benchmarks `wp_done` on a final state built from 40 nested `State.writeReg64` updates where
callee-saved registers `x19..x29` are clobbered and restored around writes to `x0..x15`. Verifies
heartbeat budgets on both satisfied postconditions and fast-failing postcondition value mismatches.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.Perf.WpDoneDeepState

open Arm64 _root_.ProofLib

/-- 40 register writes on top of `s`; `x1 = a + 29` and `x19..x29` hold their values from `s`. -/
abbrev deepState (s : State) (a : BitVec 64) : State :=
  s
    |>.writeReg64 (.gpr 19#5) (a + 1#64)
    |>.writeReg64 (.gpr 20#5) (a + 2#64)
    |>.writeReg64 (.gpr 21#5) (a + 3#64)
    |>.writeReg64 (.gpr 22#5) (a + 4#64)
    |>.writeReg64 (.gpr 23#5) (a + 5#64)
    |>.writeReg64 (.gpr 24#5) (a + 6#64)
    |>.writeReg64 (.gpr 25#5) (a + 7#64)
    |>.writeReg64 (.gpr 26#5) (a + 8#64)
    |>.writeReg64 (.gpr 27#5) (a + 9#64)
    |>.writeReg64 (.gpr 28#5) (a + 10#64)
    |>.writeReg64 (.gpr 29#5) (a + 11#64)
    |>.writeReg64 (.gpr 0#5) (a + 12#64)
    |>.writeReg64 (.gpr 1#5) (a + 13#64)
    |>.writeReg64 (.gpr 2#5) (a + 14#64)
    |>.writeReg64 (.gpr 3#5) (a + 15#64)
    |>.writeReg64 (.gpr 4#5) (a + 16#64)
    |>.writeReg64 (.gpr 5#5) (a + 17#64)
    |>.writeReg64 (.gpr 6#5) (a + 18#64)
    |>.writeReg64 (.gpr 7#5) (a + 19#64)
    |>.writeReg64 (.gpr 8#5) (a + 20#64)
    |>.writeReg64 (.gpr 9#5) (a + 21#64)
    |>.writeReg64 (.gpr 10#5) (a + 22#64)
    |>.writeReg64 (.gpr 11#5) (a + 23#64)
    |>.writeReg64 (.gpr 12#5) (a + 24#64)
    |>.writeReg64 (.gpr 13#5) (a + 25#64)
    |>.writeReg64 (.gpr 14#5) (a + 26#64)
    |>.writeReg64 (.gpr 15#5) (a + 27#64)
    |>.writeReg64 (.gpr 0#5) (a + 28#64)
    |>.writeReg64 (.gpr 1#5) (a + 29#64)
    |>.writeReg64 (.gpr 19#5) (s.readReg64 (.gpr 19#5))
    |>.writeReg64 (.gpr 20#5) (s.readReg64 (.gpr 20#5))
    |>.writeReg64 (.gpr 21#5) (s.readReg64 (.gpr 21#5))
    |>.writeReg64 (.gpr 22#5) (s.readReg64 (.gpr 22#5))
    |>.writeReg64 (.gpr 23#5) (s.readReg64 (.gpr 23#5))
    |>.writeReg64 (.gpr 24#5) (s.readReg64 (.gpr 24#5))
    |>.writeReg64 (.gpr 25#5) (s.readReg64 (.gpr 25#5))
    |>.writeReg64 (.gpr 26#5) (s.readReg64 (.gpr 26#5))
    |>.writeReg64 (.gpr 27#5) (s.readReg64 (.gpr 27#5))
    |>.writeReg64 (.gpr 28#5) (s.readReg64 (.gpr 28#5))
    |>.writeReg64 (.gpr 29#5) (s.readReg64 (.gpr 29#5))

-- Return value and callee-saved registers.
#perf_budget 12000 in
example (prog : Program) (pc a : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc (deepState s a) emp (fun sf _ => sf.readReg64 .x1 = a + 29#64 ∧ CalleeSavedPreserved s sf) := by
  wp_done

-- Callee-saved registers only.
#perf_budget 12000 in
example (prog : Program) (pc a : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc (deepState s a) emp (fun sf _ => CalleeSavedPreserved s sf) := by
  wp_done

-- Mismatched return value fails fast.
/--
error: wp_done: postcondition value mismatch:
  actual:   a + 29#64
  expected: a + 30#64
-/
#guard_msgs (error, drop info) in
#perf_budget 6000 in
example (prog : Program) (pc a : BitVec 64) (s : State)
    (hpc : s.pc = pc) (hrun : s.status = .Running) :
    SepWP prog pc (deepState s a) emp (fun sf _ => sf.readReg64 .x1 = a + 30#64 ∧ CalleeSavedPreserved s sf) := by
  wp_done

end Examples.Testing.ProofLib.Perf.WpDoneDeepState
