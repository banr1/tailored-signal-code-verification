/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliRun

@[expose] public section

set_option autoImplicit false


/-!
# Whole-process outcome and input helpers of the `libsignal-cli` CLI

**Trusted: definitions used by the statement.** All four definitions in this file (`sigAbrt`,
`abortOnPanic`, `OutcomeMatchesProcess`, `cliProcessInputs`) are used by the binary-level CLI
statements via `CliBinaryPq.lean` (see `Computational/docs/TRUSTED_BASE.md`).
-/

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process

/-- `SIGABRT`, the signal of musl's `abort` (`6`). -/
def sigAbrt : BitVec 7 := 6#7

/-- Run hook `h`; if it panicked (`.Panicked`), report the panic as death by `SIGABRT`
(`.Signaled 6`, exit status `134`). Every other result of `h` is unchanged. -/
def abortOnPanic (h : State → State) (s : State) : State :=
  let s' := h s
  match s'.status with
  | .Panicked => s'.setStatus (.Signaled sigAbrt)
  | _ => s'


/-- **The engine's outcome observes `o`**: `exited code stdout files` is a normal exit (no signal)
whose exit code has low byte `code`, with stdout `stdout` and the regular files `files`
(`fsView`); `aborted` is death by `SIGABRT` (`signal = some 6`, exit status `134`). -/
def OutcomeMatchesProcess : Outcome → ProcessOutcome → Prop
  | .exited code stdout files, out =>
      out.signal = none ∧ out.exitCode.toNat % 256 = code ∧ out.stdout = stdout ∧
        fsView out.fs = files
  | .aborted, out => out.signal = some 6 ∧ out.exitCode = 134#64

/-- The process inputs of a run on `i`: `argv = "libsignal-cli" :: i.argv`, and `i`'s stdin,
files and directories, with an 8 MiB stack (`processInputs`, `Process.lean`; DEV-CLI7). -/
def cliProcessInputs (i : Inputs) : ProcessInputs :=
  processInputs ("libsignal-cli" :: i.argv) i.stdin i.files i.dirs


end CryptoVerification.SignalSession
