/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Assembly
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open Symbolic.Swarm.COMPOSED.CompTrace (NetMsgAt)
theorem received_pair_of_netMsgAt {tr : ExecTrace} {a b : DY.Bytes} {i j : Nat} (ha : NetMsgAt a i tr) (hb : NetMsgAt b j tr) : received tr [i, j] = [a, b] := by unfold NetMsgAt at ha hb; simp only [received, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.getMessageSentAt_eq_at?, List.filterMap_cons, List.filterMap_nil, ha, hb]
end Symbolic.BugInjection.Proofs.Common443.CompRX0Assembly
