/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.Top
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoBobDone
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoFullMatch
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.PtDead
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp Symbolic.BugInjection.Proofs.Common443
theorem census_highBitWireBytes_eq_trace : Census443Defs.highBitWireBytes = CompSmallSubgroupTrace.highBitWireBytes := by
  unfold Census443Defs.highBitWireBytes CompSmallSubgroupTrace.highBitWireBytes; generalize (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []) = ev
  cases ev <;> rfl
theorem recvMsg38_eq_highBitWireBytes : recvMsg38 = Census443Defs.highBitWireBytes := by rw [census_highBitWireBytes_eq_trace, CompSmallSubgroupTrace.highBitWireBytes_eq_hex]; exact recvMsg38_eq_hex
theorem noBsc38HB_of_census (h : CompRX0SS38.NoBsc38HB') : NoBsc38HB := by intro r S g ms p hfits hnb hex hp; rw [recvMsg38_eq_highBitWireBytes] at hp ⊢; exact h r S g ms p hfits hnb hex hp
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
