/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Swarm.CREF.TR.SrHonestVer
public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Machine-Free Honest SPQR Wire Version Bound

Re-exports the honest-send SPQR ciphertext version bound (`SendsFit` and provenance lemmas) from
`Symbolic.Swarm.CREF.TR.SrHonestVer`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.SrHonestVerPure

cref_open
open DY.Libsignal DY.Libsignal.HwEvents

export Symbolic.Swarm.CREF.TR.SrHonestVer (
  SendsFit
  sent_mem_honest
  exists_honest_sendMsg_of_pqFromHonest_prov
  exists_honest_sendMsg_of_pqFromHonest
)

end Symbolic.Swarm.TRREF.SrHonestVerPure
