/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
import all DY.Bytes.Basic
import all DY.ALaCarte.Basic
import all DY.ALaCarte.DecidableEq
import all DY.ALaCarte.Ordering
import all DY.Misc.Instances
import all Comparse.Basic
import all Comparse.Formats.Basic
import all Comparse.Formats.Derived
import all DY.Comparse
import all DY.Trace.Basic
import all DY.Trace.Monad
import all DY.Trace.Manipulation
import all DY.Trace.BaseAttackerKnowledge
import all DY.Actions.Network
import all DY.Actions.PersistentLocalState
import all DY.Actions.PersistentGlobalState
import all DY.Actions.ProtocolEvent
import all DY.Actions.Random
import all DY.EquationalTheory.Literal
import all DY.EquationalTheory.Concat
import all DY.EquationalTheory.DiffieHellman
import all DY.EquationalTheory.KdfExtract
import all DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.PQXDH
import Symbolic.Specifications.Model.TripleRatchet
import Symbolic.Specifications.Model.Instance
import all Init.Data.Array.Attach
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Ord.Array
import all Init.Data.Repr
import all Init.Data.String.Bootstrap
import all Init.Data.String.Defs

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk15

set_option maxRecDepth 200000

open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag (S0Comp myGhostComp)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (btMapTerm btMapSkelTerm checkSubBytes)

theorem chunk15_wire :
    btMapTerm Nodes03.sub15 =
      btMapSkelTerm 10 CliTable.cliIdTree Nodes03.sub15 := by rfl

theorem chunk15_bytes :
    checkSubBytes myInterp S0Comp myGhostComp 10
      CliTable.cliIdTree Nodes03.sub15 = true := by
  decide +kernel

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk15
