/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.Sticky
public import Symbolic.Proofs.Swarm.CREF.Stage1Wire
public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import VCVio.Prelude.Core

/-!
# Turn-State Record and Sent-Message Helpers

Turn-state record and sent-message update projections (`effectiveRecords`, `effectiveSent`) over the
composed model (`DY.Libsignal.Composed`), re-exporting `GhostsPure` and `GhostsSlots`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.TR

cref_open

end Symbolic.Swarm.CREF.TR
