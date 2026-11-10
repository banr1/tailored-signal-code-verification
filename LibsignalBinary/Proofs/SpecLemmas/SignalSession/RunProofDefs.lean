/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.Run
public import Arm64.Trusted.Process.Loader

/-!
# Proof-Side CLI Command-Line and Path Predicates

Defines `PrintableAsciiArg`, `ArgvShapeOk`, `ArgvFitsInitialStack`, `LoadablePath`, and
`CliRejectsMalformedCommandLine` over `LibsignalBinary.Specifications.SignalSession.Run`.
-/

@[expose] public section

set_option autoImplicit false
namespace CryptoVerification.SignalSession

/-- Nonempty printable/NUL-free ASCII string (`0 < c.toNat < 128`), preserved losslessly by `bytesOfString` and C-string parsing. -/
def PrintableAsciiArg (s : String) : Prop := s ≠ "" ∧ ∀ c ∈ s.toList, 0 < c.toNat ∧ c.toNat < 128

/-- Boolean recognizer for valid CLI command-line shapes (`keygen _ _`, `init _ _`, `send _`, `recv _`). -/
def ArgvShapeOk : List String → Bool
  | ["keygen", _, _] => true
  | ["init", _, _] => true
  | ["send", _] => true
  | ["recv", _] => true
  | _ => false

/-- Bounds the serialized `argv` strings (with NUL terminators) and pointer table to 16 KiB
on the CLI's 8 MiB stack (`processInputs`, DEV-CLI7). -/
def ArgvFitsInitialStack (argv : List String) : Prop :=
  (argv.map fun a => a.length + 1 + 8).sum ≤ 16384

/-- Relative path without leading `/` or `..` segments, accepted by `ElfImage.loadState`. -/
def LoadablePath (p : String) : Prop := Arm64.hasLeadingSlash p = false ∧ Arm64.hasDotDot p = false

/-- Specification that malformed command lines (`ArgvShapeOk i.argv = false`) on loadable
inputs within stack bounds exit with code `2`, empty stdout, and unchanged files. -/
def CliRejectsMalformedCommandLine (run : CliRun) : Prop :=
  ∀ i : Inputs, (∀ a ∈ i.argv, PrintableAsciiArg a) → ArgvFitsInitialStack i.argv → ArgvShapeOk i.argv = false →
    (∀ d ∈ i.dirs, LoadablePath d) → (∀ f ∈ i.files, LoadablePath f.1) →
    (∀ f ∈ i.files, f.1 ∉ i.dirs) →
    run i = some (.exited 2 [] (filesOf i.files))

end CryptoVerification.SignalSession
