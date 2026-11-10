/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage4Lemmas.Pure -- shake: keep
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Stage 4 Instruction Reflection and Range Fetches

Layout-independent instruction decodes (`gen_decodes` over `ls_off%` relative offsets) for the
`signal_session_handshake::initiate` basic blocks traversed in Stage 4 (`+0x0350..+0x037c`,
`+0x10a4..+0x11b4`, `+0x11e0..+0x1274`, `+0x12c8..+0x13ec`, and `+0x1570..+0x15f0`).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

section Stage4GenDecodes
open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.CodeLayout

gen_decodes CryptoVerification.libsignalSessionCode_tree stage4InitBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 848) →
   (ls_off% "libsignal_cli_handshake::initiate" + 892)]

gen_decodes CryptoVerification.libsignalSessionCode_tree stage4PreBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 4260) →
   (ls_off% "libsignal_cli_handshake::initiate" + 4572)]

gen_decodes CryptoVerification.libsignalSessionCode_tree stage4SpqrBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 4576) →
   (ls_off% "libsignal_cli_handshake::initiate" + 4804)]

gen_decodes CryptoVerification.libsignalSessionCode_tree stage4PostBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 4808) →
   (ls_off% "libsignal_cli_handshake::initiate" + 5100)]

gen_decodes CryptoVerification.libsignalSessionCode_tree stage4CleanupBin
  [(ls_off% "libsignal_cli_handshake::initiate" + 5488) →
   (ls_off% "libsignal_cli_handshake::initiate" + 5616)]

end Stage4GenDecodes

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

macro "stage4_bind_entry " b:term:max H:term:max : tactic =>
  let hId := Lean.mkIdent `fnStart_def
  let xId := Lean.mkIdent `fnStart
  `(tactic| (
    change SepWPp (CryptoVerification.libsignalSessionCode.rebase $b (Rust.withPanics $H)) _ _ _ _ _ _
    generalize_entry $hId:ident :
      (CryptoVerification.libsignalSessionCode.rebase $b (Rust.withPanics $H)).fnAddr
        "libsignal_cli_handshake::initiate" = $xId:ident))

macro "stage4_epilogue_fetches " b:term:max H:term:max : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode stage4InitBin $b (Rust.withPanics $H)
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 848 48)

macro "stage4_pre_fetches " b:term:max H:term:max : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode stage4PreBin $b (Rust.withPanics $H)
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 4260 316)

macro "stage4_spqr_fetches " b:term:max H:term:max : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode stage4SpqrBin $b (Rust.withPanics $H)
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 4576 232)

macro "stage4_post_fetches " b:term:max H:term:max : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode stage4PostBin $b (Rust.withPanics $H)
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 4808 296)

macro "stage4_cleanup_fetches " b:term:max H:term:max : tactic =>
  `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode stage4CleanupBin $b (Rust.withPanics $H)
      cliInitiate_fnOff (num% (ls_off% "libsignal_cli_handshake::initiate")) 5488 132)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage4Lemmas
