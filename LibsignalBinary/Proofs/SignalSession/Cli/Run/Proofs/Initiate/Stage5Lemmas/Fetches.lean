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
# Stage 5 Instruction Decode Ranges

Layout-independent `gen_decodes` tables for the `signal_session_handshake::initiate` basic blocks
traversed in Stage 5 (`[848, 896)`, `[4828, 4848)`, `[5252, 5384)`, `[5488, 6060)`, and
`[6096, 6348)`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas

open ProofLib.ProgramReflection

set_option maxRecDepth 2000000 in
gen_decodes CryptoVerification.libsignalSessionCode_tree stage5EpilogueBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 848) →
   (ls_off% "libsignal_cli_handshake::initiate" + 896),
   (ls_off% "libsignal_cli_handshake::initiate" + 4828) →
   (ls_off% "libsignal_cli_handshake::initiate" + 4848),
   (ls_off% "libsignal_cli_handshake::initiate" + 5252) →
   (ls_off% "libsignal_cli_handshake::initiate" + 5384)]

set_option maxRecDepth 2000000 in
gen_decodes CryptoVerification.libsignalSessionCode_tree stage5MidBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 5488) →
   (ls_off% "libsignal_cli_handshake::initiate" + 6060)]

set_option maxRecDepth 2000000 in
gen_decodes CryptoVerification.libsignalSessionCode_tree stage5TailBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 6096) →
   (ls_off% "libsignal_cli_handshake::initiate" + 6348)]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage5Lemmas
