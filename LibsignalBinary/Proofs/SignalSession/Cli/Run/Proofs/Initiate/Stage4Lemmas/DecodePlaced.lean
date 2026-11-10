/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.PurePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Stage 4 Instruction Decode Re-exports (`[LibsignalPlacement]`)

Re-exports Block `521` (`signal_session_initiate`) decode, fetch, and step theorems from
`InitiateCodeSym.lean` via `PurePlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open CryptoVerification.CliHandshake.InitiatePlaced

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
