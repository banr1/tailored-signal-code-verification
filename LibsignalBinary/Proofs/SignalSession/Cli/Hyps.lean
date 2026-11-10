/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.RecordCodecsBinary.SignedPreKey
public import ProofLib

set_option warningAsError false

/-!
# CLI Binary Proof Hypothesis Bundles

Defines `cliProg img ext` (`Program.ofImage img (Rust.withPanics ext)`) and `CliCodecs img A ext`,
bundling the five record-decoder subroutine contracts invoked by the CLI store callbacks.
-/

@[expose] public section

namespace CryptoVerification.SignalSession.Cli

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
/-- The CLI program of a loaded image `img` with hook table `ext`. -/
abbrev cliProg (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  Program.ofImage img (Rust.withPanics ext)

end CryptoVerification.SignalSession.Cli
