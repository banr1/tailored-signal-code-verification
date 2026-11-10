/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.ALaCarte.DecidableEq
import DY.ALaCarte.Ordering
import DY.Misc.Instances
import Comparse.Basic
import Comparse.Formats.Basic
import Comparse.Formats.Derived
import DY.Comparse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
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

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse

set_option maxRecDepth 200000

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (gamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (mySemComp mySem_eq_comp ghostOf)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
  (IdTreeSound btMapTerm btMapSkelTerm checkSubBytes idTreeSound_of_cert
   tableGamma gamma_eq_tableGamma)

theorem hsFalse_wire :
    btMapTerm HsFalseNodes.hsFalseIdTree = btMapSkelTerm 8 HsFalseNodes.hsFalseIdTree HsFalseNodes.hsFalseIdTree := by rfl

theorem hsFalse_bytes :
    checkSubBytes myInterp (mySemComp false) (ghostOf false) 8
      HsFalseNodes.hsFalseIdTree HsFalseNodes.hsFalseIdTree = true := by
  decide +kernel

theorem hsFalse_sound :
    IdTreeSound myInterp (mySemComp false) (ghostOf false) HsTables.hsFalseTable.depth HsTables.hsFalseTable.idTree :=
  idTreeSound_of_cert hsFalse_wire hsFalse_bytes

noncomputable def hsFalseGamma : DY.Bytes → HwBytes :=
  tableGamma myInterp (mySemComp false) (ghostOf false) HsTables.hsFalseTable

theorem gamma_comp_eq_hsFalseGamma :
    gamma myInterp (mySemComp false) (ghostOf false) = hsFalseGamma :=
  gamma_eq_tableGamma hsFalse_sound

theorem gamma_eq_hsFalseGamma :
    gamma myInterp (mySem false) (ghostOf false) = hsFalseGamma := by
  rw [mySem_eq_comp]
  exact gamma_comp_eq_hsFalseGamma

end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse
