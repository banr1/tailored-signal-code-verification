/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk00
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk01
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk02
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk03
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk04
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk05
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk06
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk07
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk08
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk09
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk10
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk11
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk12
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk13
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk14
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk15

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (gamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs (S0 myGhost)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (S0Comp S0_eq_comp myGhostComp myGhost_eq_comp)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
  (CertTable IdTreeSound btMapTerm btMapSkelTerm btMapTerm_branch
   checkSubBytes checkSubBytes_branch idTreeSound_of_cert tableGamma gamma_eq_tableGamma)

abbrev cliTable : CertTable := CliTable.cliTable

theorem cliTable_wire :
    btMapTerm CliTable.cliIdTree =
      btMapSkelTerm 10 CliTable.cliIdTree CliTable.cliIdTree :=
  btMapTerm_branch
    (btMapTerm_branch
      (btMapTerm_branch (btMapTerm_branch Chunk00.chunk00_wire Chunk01.chunk01_wire)
                        (btMapTerm_branch Chunk02.chunk02_wire Chunk03.chunk03_wire))
      (btMapTerm_branch (btMapTerm_branch Chunk04.chunk04_wire Chunk05.chunk05_wire)
                        (btMapTerm_branch Chunk06.chunk06_wire Chunk07.chunk07_wire)))
    (btMapTerm_branch
      (btMapTerm_branch (btMapTerm_branch Chunk08.chunk08_wire Chunk09.chunk09_wire)
                        (btMapTerm_branch Chunk10.chunk10_wire Chunk11.chunk11_wire))
      (btMapTerm_branch (btMapTerm_branch Chunk12.chunk12_wire Chunk13.chunk13_wire)
                        (btMapTerm_branch Chunk14.chunk14_wire Chunk15.chunk15_wire)))

theorem cliTable_bytes :
    checkSubBytes myInterp S0Comp myGhostComp 10
      CliTable.cliIdTree CliTable.cliIdTree = true :=
  checkSubBytes_branch
    (checkSubBytes_branch
      (checkSubBytes_branch (checkSubBytes_branch Chunk00.chunk00_bytes Chunk01.chunk01_bytes)
                            (checkSubBytes_branch Chunk02.chunk02_bytes Chunk03.chunk03_bytes))
      (checkSubBytes_branch (checkSubBytes_branch Chunk04.chunk04_bytes Chunk05.chunk05_bytes)
                            (checkSubBytes_branch Chunk06.chunk06_bytes Chunk07.chunk07_bytes)))
    (checkSubBytes_branch
      (checkSubBytes_branch (checkSubBytes_branch Chunk08.chunk08_bytes Chunk09.chunk09_bytes)
                            (checkSubBytes_branch Chunk10.chunk10_bytes Chunk11.chunk11_bytes))
      (checkSubBytes_branch (checkSubBytes_branch Chunk12.chunk12_bytes Chunk13.chunk13_bytes)
                            (checkSubBytes_branch Chunk14.chunk14_bytes Chunk15.chunk15_bytes)))

theorem cliTable_sound :
    IdTreeSound myInterp S0Comp myGhostComp cliTable.depth cliTable.idTree :=
  idTreeSound_of_cert cliTable_wire cliTable_bytes

noncomputable def cliGamma : DY.Bytes → HwBytes :=
  tableGamma myInterp S0Comp myGhostComp cliTable

theorem gamma_comp_eq_cliGamma : gamma myInterp S0Comp myGhostComp = cliGamma :=
  gamma_eq_tableGamma cliTable_sound

theorem gamma_eq_cliGamma : gamma myInterp S0 myGhost = cliGamma := by
  rw [S0_eq_comp, myGhost_eq_comp]
  exact gamma_comp_eq_cliGamma

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli
