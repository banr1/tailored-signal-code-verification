/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli.RunProofs

theorem cliInitiate_fnOff :
    libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") :=
  ls_lemma% fnOff "libsignal_cli_handshake::initiate"

gen_decodes CryptoVerification.libsignalSessionCode_tree cliInitiateStage1Bin
  [(ls_off% "libsignal_cli_handshake::initiate") →
   (ls_off% "libsignal_cli_handshake::initiate" + 912)]

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
