/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import Arm64.Trusted.Process.Overrides
public import ProofLib.Process.Overrides
public meta import ProofLib.Process
meta import ProofLib.TestFiles

/-!
# Symbol-Keyed Override Resolution Tests

Kernel-checked (`decide +kernel`) positive and negative tests for `resolveAddrs` on the
multi-segment static executable fixture `fixtures/overrides_fixture.elf`, covering unique sized
`STT_FUNC` resolution across segments, fail-closed rejection (`ElfRunsToWithOverrides.not_of_check`),
and exact `externAt?` hook dispatch.
-/

@[expose] public section

namespace Testing.ProcessOverrides

open Arm64 Arm64.Process

set_option maxRecDepth 2000000

requires_test_files ["fixtures/overrides_fixture.elf"]

/-- Multi-segment static `ET_EXEC` fixture (`fixtures/overrides_fixture.elf`, 13 KB), built from
`fixtures/overrides_fixture{,2}.s` and `fixtures/overrides_fixture.ld` by `scripts/build-test-elfs.sh`. -/
noncomputable def fixtureBytes : List (BitVec 8) :=
  file_bytes% "fixtures/overrides_fixture.elf"
    sha256 "3d574d809ba0e3bbb7fd663aebbf3c4a9e179bcf6c99d6203086ab8aebeb293d"

noncomputable def fixtureImg : ElfImage := elf_image% "fixtures/overrides_fixture.elf"

set_option maxHeartbeats 2000000 in
theorem fixture_parse : ElfImage.parse fixtureBytes = .ok fixtureImg := ElfImage.parse_of_fastParse rfl

/-! ## Positive -/

/-- Global `main` and local `__do_init` / `__libc_malloc_impl` (`STT_FUNC`) resolve in `overrides_fixture.elf`. -/
example : checkOverrides fixtureBytes fixtureImg ["main", "__do_init", "__libc_malloc_impl"]
    [0x40e010, 0x40e00c, 0x40e018] = true := by decide +kernel

example : resolveAddrs fixtureBytes fixtureImg ["__do_init"] = .ok [0x40e00c] :=
  resolveAddrs_of_check (by decide +kernel)

/-- `main` sits in the entry segment (`0x40e000`); `adler32` sits in the other executable
    segment (`0x400000`). -/
example : checkOverrides fixtureBytes fixtureImg ["adler32", "main"] [0x400000, 0x40e010] = true := by
  decide +kernel

/-- The empty override list resolves. -/
example : checkOverrides fixtureBytes fixtureImg [] [] = true := by decide +kernel

/-! ## Negative cases -/

example : checkOverridesFail fixtureBytes fixtureImg ["no_such_function"] = true := by decide +kernel

example : checkOverridesFail fixtureBytes fixtureImg ["main", "no_such_function"] = true := by decide +kernel

/-- `__malloc_context` is `STT_OBJECT`. -/
example : checkOverridesFail fixtureBytes fixtureImg ["__malloc_context"] = true := by decide +kernel

/-- `_start` has `st_size = 0`. -/
example : checkOverridesFail fixtureBytes fixtureImg ["_start"] = true := by decide +kernel

/-- `$x` has duplicate `.symtab` entries (local `STT_NOTYPE` mapping symbols). -/
example : checkOverridesFail fixtureBytes fixtureImg ["$x"] = true := by decide +kernel

example : checkOverridesFail fixtureBytes fixtureImg ["main", "main"] = true := by decide +kernel

/-- `dummy` has two local `STT_FUNC` `.symtab` entries. -/
example : checkOverridesFail fixtureBytes fixtureImg ["dummy"] = true := by decide +kernel

/-- Failed resolution refutes `ElfRunsToWithOverrides` even under an unsatisfiable precondition,
    since resolution is checked outside `∀ inputs`. -/
example (svc f : State → State) :
    ¬ ElfRunsToWithOverrides svc [("_start", f)] fixtureBytes (fun _ => False) (fun _ _ => True) :=
  ElfRunsToWithOverrides.not_of_check fixture_parse
    (by show checkOverridesFail fixtureBytes fixtureImg ["_start"] = true; decide +kernel)

/-! ## Hook dispatch -/

example (svc f : State → State) :
    (overrideProgram svc [("main", f)] [0x40e010]).externAt? 0x40e010#64 = some f := by
  rw [show overrideProgram svc [("main", f)] [0x40e010] =
      Program.ofSites svc [("main", 0x40e010, f)] from rfl,
    Program.ofSites_externAt _ _ (by show (["main"] : List String).Nodup; decide)]
  simp

example (svc f : State → State) :
    (overrideProgram svc [("main", f)] [0x40e010]).externAt? 0x40e014#64 = none :=
  overrideProgram_externAt_none (bytes := fixtureBytes) (img := fixtureImg)
    (resolveAddrs_of_check
      (by show checkOverrides fixtureBytes fixtureImg ["main"] [0x40e010] = true; decide +kernel))
    (by decide)

end_requires_test_files

end Testing.ProcessOverrides
