/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.StdStartup.OutlineAtomics

/-!
# `__aarch64_cas1_acq` Contract Regression Tests

Verifies that the 12 compiler-rt `__aarch64_cas1_acq` instruction words decode to `cas1AcqInstrs`
and instantiate `cas1Acq_ok`, and that 32-bit `__aarch64_cas4_acq` words (`casa` / `ldaxr`) are
rejected by the byte-width template.
-/

@[expose] public section

namespace ProofLib.Testing.OutlineAtomicsCas1

open Arm64 ProofLib ProofLib.StdStartup

/-- The 12 `__aarch64_cas1_acq` instruction words. -/
def cas1AcqWords : List (BitVec 32) :=
  [ 0x90000130#32, 0x39762210#32, 0x34000070#32, 0x08e07c41#32, 0xd65f03c0#32, 0x53001c10#32,
    0x085ffc40#32, 0x6b10001f#32, 0x54000061#32, 0x08117c41#32, 0x35ffff91#32, 0xd65f03c0#32 ]

theorem cas1AcqWords_decode :
    cas1AcqWords.map decode = (cas1AcqInstrs 0x360000#64 0x384d88#64).map some := by
  decide +kernel

/-- Word-width `cas4` words (`casa` / `ldaxr` at indices 3 and 6) do not match `cas1AcqInstrs`. -/
theorem cas4AcqWords_decode_ne :
    (cas1AcqWords.set 3 0x88e07c41#32 |>.set 6 0x885ffc40#32).map decode ≠
      (cas1AcqInstrs 0x360000#64 0x384d88#64).map some := by
  decide +kernel

example (P : Program) (h : hasInstrs P 0x360000#64 (cas1AcqInstrs 0x360000#64 0x384d88#64)) :
    subroutine_ok P 0x360000#64 (stdCas1Spec 0x384d88#64) :=
  cas1Acq_ok P _ _ h

end ProofLib.Testing.OutlineAtomicsCas1
