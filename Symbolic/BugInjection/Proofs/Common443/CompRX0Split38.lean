/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0Top
public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0Split38
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.HwEvents
theorem attackerKnows_torsionVariant (v : Fin 4) (t : Fin 8) (tr : ExecTrace) (k : DY.Bytes) (_hk : DY.X25519.x25519Key k = k) (hak : k.AttackerKnows tr) : (DY.X25519.x25519TorsionVariant k v t).AttackerKnows tr :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.attackerKnows_torsionVariant_bridge v t tr k hak
end Symbolic.BugInjection.Proofs.Common443.CompRX0Split38
