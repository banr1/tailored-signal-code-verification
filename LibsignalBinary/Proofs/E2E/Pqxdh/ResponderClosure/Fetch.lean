/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr -- shake: keep

/-!
# Symbol Name and Entry Offset for `message_decrypt_prekey::<PqxdhRng>::{closure#0}`

Defines `decryptPrekeyClosureName` and `decryptPrekeyClosureOff` (`0x720f0#64`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

set_option maxHeartbeats 0

abbrev decryptPrekeyClosureName : String :=
  "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_pqxdh_e2e::\
    PqxdhRng>::{closure#0}"

abbrev decryptPrekeyClosureOff : BitVec 64 := 0x720f0#64

end Fetch

end CryptoVerification.E2E.Pqxdh.ResponderClosure
