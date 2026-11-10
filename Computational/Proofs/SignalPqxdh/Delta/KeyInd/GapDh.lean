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
# PQXDH δ key indistinguishability: Gap-DH bound

**Checked by Lean.** Proves `kiGapDh` (`KIGapDhStmt`, DEV-PQ21) from
`prob_badKeyIndFgAny4_le_gapDh` under `CryptoWellFormedPrimitivesδ`.
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

/-- Bounds `badKeyIndFgAny4` by the Gap-DH advantage under `CryptoWellFormedPrimitivesδ`. -/
theorem kiGapDh (S : Setup) : KIGapDhStmt S :=
  fun b P hP A => prob_badKeyIndFgAny4_le_gapDh S b P hP A

end Proofs.SignalPqxdh.Security.PqxdhDelta
