/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access
public import ProofLib.SepLogic.WP.StepsCore
public import ProofLib.SepLogic.WP.Syscalls
public import ProofLib.SepLogic.WP.StepsSimd
public import ProofLib.SepLogic.WP.StepsSubword
public import ProofLib.SepLogic.WP.Structural
public import ProofLib.SepLogic.WP.TacticCore
public import ProofLib.SepLogic.WP.PairStep
public import ProofLib.SepLogic.WP.StepTactic
public import ProofLib.SepLogic.WP.StateTransport
public import ProofLib.SepLogic.WP.ControlTactics
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.SliceArray
public import ProofLib.SepLogic.ByteRegion
public import ProofLib.SepLogic.WP.FrameAuto
public import ProofLib.Hoare.FnPtr
import Arm64.Trusted.Spec.SepLogic

/-!
# Separation Logic Weakest Precondition

Re-exports the `ProofLib.SepLogic.WP.*` step lemmas and symbolic execution tactics, and marks
`SepWP` irreducible for downstream proofs.
-/

@[expose] public section

namespace ProofLib

set_option allowUnsafeReducibility true in
attribute [irreducible] SepWP

end ProofLib
