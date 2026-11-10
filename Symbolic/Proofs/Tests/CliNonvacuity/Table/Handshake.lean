/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertTrue

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake

open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (gamma)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mySem)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (mySemComp ghostOf)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (CertTable IdTreeSound)

abbrev hsTable (withOpk : Bool) : CertTable := HsTables.hsTable withOpk

theorem hsTable_sound (withOpk : Bool) :
    IdTreeSound myInterp (mySemComp withOpk) (ghostOf withOpk)
      (hsTable withOpk).depth (hsTable withOpk).idTree :=
  match withOpk with
  | false => HsCertFalse.hsFalse_sound
  | true => HsCertTrue.hsTrue_sound

noncomputable def hsGamma (withOpk : Bool) : DY.Bytes → HwBytes :=
  if withOpk then HsCertTrue.hsTrueGamma else HsCertFalse.hsFalseGamma

theorem gamma_comp_eq_hsGamma (withOpk : Bool) :
    gamma myInterp (mySemComp withOpk) (ghostOf withOpk) = hsGamma withOpk := by
  cases withOpk
  · exact HsCertFalse.gamma_comp_eq_hsFalseGamma
  · exact HsCertTrue.gamma_comp_eq_hsTrueGamma

theorem gamma_eq_hsGamma (withOpk : Bool) :
    gamma myInterp (mySem withOpk) (ghostOf withOpk) = hsGamma withOpk := by
  cases withOpk
  · exact HsCertFalse.gamma_eq_hsFalseGamma
  · exact HsCertTrue.gamma_eq_hsTrueGamma

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake
