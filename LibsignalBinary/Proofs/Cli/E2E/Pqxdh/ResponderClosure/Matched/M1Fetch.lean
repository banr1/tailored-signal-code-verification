/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Instruction Decodes for `<SessionRecord>::promote_matching_session`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection

abbrev promoteMatchingSessionName : String :=
  "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session"

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree promoteBinCli [
  (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 0) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 124)]

set_option maxHeartbeats 1200000 in
gen_decodes libsignalSessionCode_tree promoteBinCli [
  (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 128) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 208),
  (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 740) →
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" + 800)]

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
