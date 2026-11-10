/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Actions.PersistentLocalState
public import LibsignalBinary.Specifications.SignalSession.Run

/-!
# Concrete Byte Strings and CLI Trace Events

Concrete byte strings (`HwBytes`) and the event alphabet (`CliEvent`) for `signal-session` CLI
execution traces.
-/

@[expose] public section

namespace DY.Libsignal

/-- Concrete byte string, as opposed to symbolic `DY.Bytes` terms. -/
abbrev HwBytes := List (BitVec 8)

end DY.Libsignal

namespace DY.Libsignal.HwEvents

open DY (Participant)
open CryptoVerification.SignalSession (Cmd)

/-- One `signal-session` CLI invocation: caller `party`, command `cmd`, `input` bytes (bundle blob
for `init`, stdin otherwise), `coins` file, and `exit` (`some (code, stdout)` or `none` on abort). -/
structure RunEvent where
  party : Participant
  cmd : Cmd
  input : HwBytes
  coins : HwBytes
  exit : Option (Nat × HwBytes)

/-- Environment events emitted between CLI runs: directory secret leaks, primitive breaks, public-key
inversions, and corrupt identity registrations. -/
inductive EnvEvent where
  | leak (party : Participant) (secret : HwBytes)
  | breakDH
  | breakKEM
  | invertDH (pk sk : HwBytes)
  | invertKEM (pk sk : HwBytes)
  | registerCorrupt (party : Participant) (ikPk : HwBytes)

/-- Whether an environment event is a primitive break or key inversion. -/
def EnvEvent.IsBreakInvert : EnvEvent → Prop
  | .breakDH | .breakKEM | .invertDH .. | .invertKEM .. => True
  | .leak .. | .registerCorrupt .. => False

inductive CliEvent where
  | run (e : RunEvent)
  | env (e : EnvEvent)

end DY.Libsignal.HwEvents
