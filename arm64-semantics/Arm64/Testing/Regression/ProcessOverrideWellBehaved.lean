/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Regression.ProcessOverrides
public import ProofLib.Process.OverrideWellBehaved
public import ProofLib.SepLogic.Region
meta import ProofLib.TestFiles

/-!
# Well-Behaved Override Regression Tests

Positive and negative regression tests for `Override.WellBehaved`, `WellBehaved.hookOk`, and
`WellBehaved.subroutine_ok` across register-only overrides, memory-writing overrides, and
calling-convention violations refuted via `WellBehaved.not_of_probe`.
-/

@[expose] public section

namespace Testing.ProcessOverrideWellBehaved

requires_test_files ["fixtures/overrides_fixture.elf"]

open Arm64 Arm64.Process Arm64.Override ProofLib Testing.ProcessOverrides

def retZero (s : State) : State := (s.writeReg64 .x0 0#64).setPC (s.readReg64 .lr)

theorem retZero_wellBehaved : WellBehaved (fun _ => True) (fun _ _ => False) retZero :=
  WellBehaved.of_regs (fun s => s.writeReg64 .x0 0#64)
    (fun s _ _ => ⟨_, s.vregs, s.pstate, s.fpsr, rfl⟩)
    (fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

abbrev retZeroSpec : Spec Unit :=
  regionSpec 0#64 0 (fun _ => True) (fun _ sf => sf.readReg64 .x0 = 0#64)

theorem retZero_hookOk : HookOk retZero retZeroSpec :=
  retZero_wellBehaved.hookOk (fun _ _ _ _ => trivial) (fun _ _ _ h => h.elim)
    (fun _ _ _ _ => rfl)

theorem cp_retZero_subroutine_ok :
    subroutine_ok (overrideProgram id [("__do_init", retZero)] [0x40e00c])
      0x40e00c#64 retZeroSpec :=
  retZero_wellBehaved.subroutine_ok (os := [("__do_init", retZero)]) (name := "__do_init")
    (resolveAddrs_of_check (bytes := fixtureBytes) (img := fixtureImg) (by decide +kernel)) (List.mem_singleton_self _)
    (fun _ _ _ _ => trivial) (fun _ _ _ h => h.elim) (fun _ _ _ _ => rfl)

def zeroByte (s : State) : State :=
  ({ s with mem := s.mem.write8 (s.readReg64 .x0) 0#8 } : State).setPC (s.readReg64 .lr)

theorem zeroByte_wellBehaved :
    WellBehaved (fun s => s.mem.canWrite (s.readReg64 .x0) 1 = true)
      (fun s a => a = s.readReg64 .x0) zeroByte := by
  intro s _ hw
  refine ⟨⟨s.regs, s.vregs, s.pstate, s.fpsr, _, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    Memory.perm_write8 .., Memory.isAnon_write8 ..,
    fun _ hlf => Memory.isLazyFree_write8_of_false _ _ hlf, fun a hne => ?_⟩
  by_cases ha : a = s.readReg64 .x0
  · exact ⟨ha, ha ▸ hw⟩
  · rcases hne with hne | hne
    · exact absurd (by simp [zeroByte, State.setPC, Memory.read8_write8, ha]) hne
    · exact absurd (by simp [zeroByte, State.setPC, Memory.isLazyFree_write8, ha]) hne

theorem zeroByte_hookOk (p : BitVec 64) :
    HookOk zeroByte (regionSpec p 16 (fun s => s.readReg64 .x0 = p) (fun _ _ => True)) :=
  zeroByte_wellBehaved.hookOk
    (fun s0 _ hx hmem => by
      rw [hx]; simpa using memRegion_canWrite1 (k := 0) hmem (by decide) (by decide))
    (fun s0 hx a ha => by subst ha; rw [hx]; simp [InRegion])
    (fun _ _ _ _ => trivial)

def s₁ : State := ((({} : State).writeReg64 (.gpr 19#5) 1#64).writeReg64 .lr 0x1000#64)

def clobberX19 (s : State) : State := retZero (s.writeReg64 (.gpr 19#5) 7#64)

def jumpElsewhere (s : State) : State := (s.writeReg64 .x0 0#64).setPC 0x2000#64

def moveSp (s : State) : State := retZero (s.writeReg64 .sp (s.sp - 16#64))

def halts (s : State) : State := { retZero s with status := .Halted }

example : probe retZero s₁ = true := by decide
example : probe clobberX19 s₁ = false := by decide

example {fp} : ¬ WellBehaved (fun _ => True) fp clobberX19 :=
  WellBehaved.not_of_probe s₁ rfl trivial (by decide)
example {fp} : ¬ WellBehaved (fun _ => True) fp jumpElsewhere :=
  WellBehaved.not_of_probe s₁ rfl trivial (by decide)
example {fp} : ¬ WellBehaved (fun _ => True) fp moveSp :=
  WellBehaved.not_of_probe s₁ rfl trivial (by decide)
example {fp} : ¬ WellBehaved (fun _ => True) fp halts :=
  WellBehaved.not_of_probe s₁ rfl trivial (by decide)

-- The register-only constructor rejects an update that clobbers `x19`.
/--
error: Tactic `rfl` failed: The left-hand side
  ((s.writeReg64 (Reg.gpr 19#5) 7#64).writeReg64 Reg.x0 0#64).readReg64 (Reg.gpr 19#5)
is not definitionally equal to the right-hand side
  s.readReg64 (Reg.gpr 19#5)

s : State
x✝¹ : s.status = ExecStatus.Running
x✝ : True
⊢ ((s.writeReg64 (Reg.gpr 19#5) 7#64).writeReg64 Reg.x0 0#64).readReg64 (Reg.gpr 19#5) = s.readReg64 (Reg.gpr 19#5)
-/
#guard_msgs (error, drop warning) in
example : WellBehaved (fun _ => True) (fun _ _ => False)
    (fun s => ((s.writeReg64 (.gpr 19#5) 7#64).writeReg64 .x0 0#64).setPC (s.readReg64 .lr)) :=
  WellBehaved.of_regs (fun s => (s.writeReg64 (.gpr 19#5) 7#64).writeReg64 .x0 0#64)
    (fun s _ _ => ⟨_, s.vregs, s.pstate, s.fpsr, rfl⟩)
    (fun s _ _ => ⟨rfl, by rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- info: 'Arm64.Override.WellBehaved.hookOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms WellBehaved.hookOk

/--
info: 'Testing.ProcessOverrideWellBehaved.cp_retZero_subroutine_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms cp_retZero_subroutine_ok

end_requires_test_files

end Testing.ProcessOverrideWellBehaved
