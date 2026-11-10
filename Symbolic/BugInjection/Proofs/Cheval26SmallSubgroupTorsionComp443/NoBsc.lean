/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443.Top
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443.PtDead
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoBobDone
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoFullMatch
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionComp Symbolic.BugInjection.Proofs.Common443
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem census_torsionWireBytes_eq_trace : Census443Defs.torsionWireBytes = CompSmallSubgroupTrace.torsionWireBytes := by
  unfold Census443Defs.torsionWireBytes CompSmallSubgroupTrace.torsionWireBytes; generalize (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []) = ev
  cases ev <;> rfl
theorem recvMsg38_eq_torsionWireBytes : recvMsg38 = Census443Defs.torsionWireBytes := by rw [census_torsionWireBytes_eq_trace, CompSmallSubgroupTrace.torsionWireBytes_eq_hex]; exact recvMsg38_eq_hex
theorem noBsc38TC_of_census (h : CompRX0SS38.NoBsc38TC') : NoBsc38TC := by intro r S g ms p hfits hnb hex hp; rw [recvMsg38_eq_torsionWireBytes] at hp ⊢; exact h r S g ms p hfits hnb hex hp
theorem noBobDone38TC : NoBobDone38TC :=
  fun _ _ _ _ _ hex =>
    Cheval26SmallSubgroupHighBitComp443.bobDone_nil_torsionComp_trace_take38 hex
theorem noFullMatchTC : NoFullMatchTC := Cheval26SmallSubgroupHighBitComp443.noFullMatchTC
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupTorsionComp443
