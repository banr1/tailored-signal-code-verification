/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import CaseStudies.Hashbrown.Proofs.StdCli.Top
import CaseStudies.Hashbrown.Proofs.CliWitness

/-!
# Concrete `hashbrown_cli.elf` Instantiation (`CaseStudies.Hashbrown.Proofs.CliProof`)

- **Role:** `Role::Proof` (thin final whole-binary instantiation bridge, outside TCB).
- **Architectural Boundary:** Instantiates the 100% placement-generic `StdCli` driver, startup,
  `std::io`, decimal formatter, `mallocng` bridge, and SwissTable library theorems on the concrete
  `hashbrown_cli.elf` layout and `WordTree` certificates from `CliWitness` to establish
  `CaseStudies.Hashbrown.hashbrownCliUniversal_ok : HashbrownCliUniversalStmt`.
-/

set_option autoImplicit false

namespace CaseStudies.Hashbrown

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup ProofLib.ProgramReflection
open CaseStudies.Hashbrown.Proofs CaseStudies.Hashbrown.Proofs.StdCli

/-! ## 1. Assembly of `HbCliCode`, `hashbrownLib.InElf`, and `HbMallocngPlaced` from `CliWitness` -/

private theorem hbRxProg_svc : hbRxProg.svc = Syscall.standard :=
  StdBinaryLayout.rxProgram_svc _ _

private theorem hbRxProg_stubs : hbRxProg.stubs = [] := by
  unfold hbRxProg StdBinaryLayout.rxProgram; split <;> rfl

private theorem hbRxProg_symbols : hbRxProg.symbols = [] := by
  unfold hbRxProg StdBinaryLayout.rxProgram; split <;> rfl

private theorem hbRxProg_externs (sym : String) : (hbRxProg.externs sym).isNone = true := by
  unfold hbRxProg StdBinaryLayout.rxProgram; split <;> rfl

private theorem hbRxProg_overrides (sym : String) : (hbRxProg.overrides sym).isNone = true := by
  unfold hbRxProg StdBinaryLayout.rxProgram; split <;> rfl

private theorem hbSeg3Code_ok :
    checkHbSeg3Code hbCliLayout hbStartupLayout hbRxProg.base hbRxTree = true := by
  unfold checkHbSeg3Code
  rw [hbRxProg_base, hbPreMainCode_check, hbPostMainCode_check, hbShimsCode_check,
    hbMemOpsCode_check, hbSyscallsAndStderrCode_check, hbStdinAndVecCode_check,
    hbStdoutCode_check, hbFmtCode_check, hbUserMainCode_check, hbMainCmdCode_check]
  rfl

theorem hbCliCode_ok : HbCliCode hbRxProg hbCliLayout hbStartupLayout :=
  hbCliCode_of_wordTree 78848 hbRxProg_code hbRxTree_size
    hbRxProg_svc hbRxProg_stubs hbRxProg_symbols hbRxProg_externs hbRxProg_overrides
    hbSeg3Code_ok

theorem hbPlaced_inElf :
    hashbrownLib.Placeable hbCliLayout.hbMpl ∧
      hashbrownLib.InElf hashbrownElf hbCliLayout.hbMpl :=
  ⟨hashbrownLib_ok.1, hashbrownLib_ok.2.1⟩

set_option maxRecDepth 2000000 in
theorem hbMallocngPlaced_ok :
    HbMallocngPlaced hbRxProg hbCliLayout hbMallocngMpl :=
  hbMallocngPlaced_of_inElf hbMallocng_placeable hbMallocng_inElf.2.1 hbMallocngInRx_ok

/-! ## 2. Headline Whole-Binary Theorem (`hashbrownCliUniversal_ok`) -/

set_option maxRecDepth 2000000 in
/-- Headline whole-binary ELF process theorem for `hashbrown_cli.elf`
    (`CaseStudies/Hashbrown/Spec/Top.lean`). -/
theorem hashbrownCliUniversal_ok : HashbrownCliUniversalStmt :=
  ElfRunsTo.intro hashbrownCli_parse fun _ ⟨hvalid, hbudget⟩ =>
    hbCli_runsTo hbCliCode_ok hbCliLayout_valid hbStartupLayout_valid hbExternWiring_ok
      hbMatchesImage_eq rfl hbPlaced_inElf.1 hbPlaced_inElf.2 hbMallocngPlaced_ok
      hvalid hbudget

end CaseStudies.Hashbrown
