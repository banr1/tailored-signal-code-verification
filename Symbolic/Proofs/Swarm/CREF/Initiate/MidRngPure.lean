/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredModelTraces
public import Symbolic.Specifications.Concrete.ImageSymbols
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Session-Initiate RNG Draw Lengths

Defines `initiateFullDrawLengths`, the sequence of 34 RNG draw byte lengths in `session_initiate`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents
open DY.Libsignal.PQXDH.Refinement (preKeyBundleByteLength)

/-- Sequence of 34 RNG draw byte lengths in `session_initiate`. -/
def initiateFullDrawLengths : List Nat :=
  [32] ++ List.replicate 32 4 ++ [32]

end Symbolic.Swarm.CREF
