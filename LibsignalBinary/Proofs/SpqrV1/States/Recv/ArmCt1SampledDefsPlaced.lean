/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymBasePlaced
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64
open ProofLib
open CryptoVerification

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  CryptoVerification.blkPC_332

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Placed Imports

Configures local irreducibility attributes on `blkPC_332` and imports `CodeSymBasePlaced` for
relocatable `.ct1Sampled` proof modules.
-/

end LibsignalBinary.Proofs.SpqrV1.States.Recv
