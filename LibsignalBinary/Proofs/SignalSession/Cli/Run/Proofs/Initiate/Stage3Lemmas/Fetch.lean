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
# Symbolic Function-Relative Instruction Decodes for Stage 3

Kernel `Eq.refl` decode lemmas over `libsignalSessionCode_tree` for `signal_session_handshake::initiate`
ranges traversed by Stage 3: epilogue `[0x350, 0x37c]`, main body `[0x760, 0x10a0]`, error/unwind
tail `[0x1508, 0x15f0]`, and OOM handlers `[0x1918, 0x1944]`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 ProofLib CryptoVerification CryptoVerification.CodeLayout

gen_decodes libsignalSessionCode_tree initS3 [
  (ls_off% "libsignal_cli_handshake::initiate" + 0x350) →
    (ls_off% "libsignal_cli_handshake::initiate" + 0x37c),
  (ls_off% "libsignal_cli_handshake::initiate" + 0x760) →
    (ls_off% "libsignal_cli_handshake::initiate" + 0x10a0),
  (ls_off% "libsignal_cli_handshake::initiate" + 0x1508) →
    (ls_off% "libsignal_cli_handshake::initiate" + 0x15f0),
  (ls_off% "libsignal_cli_handshake::initiate" + 0x1918) →
    (ls_off% "libsignal_cli_handshake::initiate" + 0x1944)
]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
