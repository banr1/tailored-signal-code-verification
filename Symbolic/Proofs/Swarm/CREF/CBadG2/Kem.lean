/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber
public import Symbolic.Proofs.Swarm.CREF.Stage1Trials

/-!
# KEM and Trial Collision Imports

Re-exports `Stage1Kyber` and `Stage1Trials` for downstream KEM collision modules.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF

open DY DY.Comparse DY.Libsignal ByteSpecs
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open Symbolic.Swarm.CREF.Stage1Kyber
open Symbolic.Swarm.CREF.Stage1Trials

end Symbolic.Swarm.CREF
