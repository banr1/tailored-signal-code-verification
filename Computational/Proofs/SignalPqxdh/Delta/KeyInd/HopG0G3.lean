/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyIndDefs
import Computational.Proofs.SignalPqxdh.Security.FgGapDhCoupling

/-!
# PQXDH δ key indistinguishability: `G0 → G3` hop

**Checked by Lean.** Proves `kiHopG0G3` (`KIHopG0G3Stmt`, DEV-PQ21) from `keyInd_hop_G0_G3_le`
under `CryptoWellFormedPrimitivesδ`.
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory
open OracleSpec OracleComp
open SignalPqxdh SignalPqxdh.Security
open Proofs.SignalPqxdh.Security
open Proofs.SignalPqxdh.Security.FgGapDh
open Proofs.SignalPqxdh.Security.FgGapDh.Ik
open Proofs.SignalPqxdh.Security.FgGapDh.Opk

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-- Bounds the `G0 → G3` key-indistinguishability hop under `CryptoWellFormedPrimitivesδ`. -/
theorem kiHopG0G3 (S : Setup) : KIHopG0G3Stmt S :=
  fun P hP b A => keyInd_hop_G0_G3_le S P hP b A

end Proofs.SignalPqxdh.Security.PqxdhDelta
