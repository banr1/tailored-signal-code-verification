/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443.Top
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PtDead

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt (IniPrefixStateSecretsInv)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443 (bundleBytes call0RngEvents torsionComp_trace_take_35_eq ptDead35_self not_ptSplitCollisionAt_torsionComp_35_of not_ptSplitCollisionAt_torsionComp_35)
open Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem ptDeadTC : PtDeadTC :=
  fun _ _ g _ hfits hnb hexp hem hcol =>
    ptDead35_self hfits.1.1 hnb (torsionComp_trace_take_35_eq ▸ hexp) hem
      (hcol g ⟨rfl, hexp.1⟩)
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443
