/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module -- shake: keep-all

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import ProofLib.SepLogic.WPp
public import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
public import LibsignalBinary.Proofs.CodeLayout

/-!
# Instruction Decode Lemmas and Range-Fetch Tactics for `libsignal_e2e`

Generates instruction decode theorems and range-fetch tactics for `libsignal_e2e::open`
(`0x43a38..0x43d1c`), `session_send` (`0x47cd8..0x47f20`), and `session_recv` (`0x469c8..0x46c20`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

section Fetch

end Fetch

end CryptoVerification.E2E.Bin
