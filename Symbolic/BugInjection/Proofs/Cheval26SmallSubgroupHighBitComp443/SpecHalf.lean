/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoBsc
public import Symbolic.BugInjection.Proofs.Common443.Census443Close

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp Symbolic.BugInjection.Proofs.Common443
theorem noBsc38HB : NoBsc38HB := noBsc38HB_of_census Census443Close.noBsc38HB
theorem not_collisionAt_hb {r : Records} {S : Sem} (hfits : compFitsPinned setup compI0 r) (hnb : ∀ ms, Common443.CompSetupSecrecy.NoBrk r ms) : ¬ CollisionAt compI0 r S who ok trace := not_collisionAt_of ptDeadHB noBobDone38HB noBsc38HB hfits hnb
end Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
