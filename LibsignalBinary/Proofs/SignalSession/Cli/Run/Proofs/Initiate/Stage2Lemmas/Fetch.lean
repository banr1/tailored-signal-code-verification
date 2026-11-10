/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Stage 2 Instruction Decodes and Callee Offsets

Generates layout-independent instruction decode lemmas (`gen_decodes` over
`libsignalSessionCode_tree`) for the basic-block spans executed by Stage 2 of
`signal_session_handshake::initiate` (`0x0350..0x0380`, `0x0390..0x0470`, `0x0510..0x0760`,
`0x157c..0x15e8`, and `0x1924..0x1930`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

set_option maxRecDepth 200000

section Decodes

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

gen_decodes CryptoVerification.libsignalSessionCode_tree cliInitiateStage2Bin
  [(ls_off% "libsignal_cli_handshake::initiate" + 0x0350) →
     (ls_off% "libsignal_cli_handshake::initiate" + 0x0380),
   (ls_off% "libsignal_cli_handshake::initiate" + 0x0390) →
     (ls_off% "libsignal_cli_handshake::initiate" + 0x0470),
   (ls_off% "libsignal_cli_handshake::initiate" + 0x0510) →
     (ls_off% "libsignal_cli_handshake::initiate" + 0x0760),
   (ls_off% "libsignal_cli_handshake::initiate" + 0x157c) →
     (ls_off% "libsignal_cli_handshake::initiate" + 0x15e8),
   (ls_off% "libsignal_cli_handshake::initiate" + 0x1924) →
     (ls_off% "libsignal_cli_handshake::initiate" + 0x1930)]

end Decodes

theorem cliInitiate_fnOff :
    libsignalSessionCode.fnOff cliInitiateName =
      num% (ls_off% "libsignal_cli_handshake::initiate") :=
  ls_lemma% fnOff "libsignal_cli_handshake::initiate"

abbrev staticSecretDropName : String :=
  "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"

abbrev handleErrorName : String :=
  "alloc::raw_vec::handle_error"

theorem staticSecretDrop_stub :
    libsignalSessionCode.fnOff staticSecretDropName =
      num% (ls_off% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop") :=
  ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop"

theorem rustDealloc_stub :
    libsignalSessionCode.fnOff "__rustc::__rust_dealloc" =
      num% (ls_off% "__rustc::__rust_dealloc") :=
  ls_stub% "__rustc::__rust_dealloc"

theorem rustNoAllocShim_stub :
    libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2" =
      num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") :=
  ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2"

theorem rustAlloc_stub :
    libsignalSessionCode.fnOff "__rustc::__rust_alloc" =
      num% (ls_off% "__rustc::__rust_alloc") :=
  ls_stub% "__rustc::__rust_alloc"

theorem memcpy_stub :
    libsignalSessionCode.fnOff "memcpy" =
      num% (ls_off% "memcpy") :=
  ls_stub% "memcpy"

theorem handleError_stub :
    libsignalSessionCode.fnOff handleErrorName =
      num% (ls_off% "alloc::raw_vec::handle_error") :=
  ls_stub% "alloc::raw_vec::handle_error"

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
