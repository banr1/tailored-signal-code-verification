/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Stdio
public import Arm64.Trusted.Syscalls.FileIo
public import Arm64.Trusted.Syscalls.Poll
public import Arm64.Trusted.Syscalls.Alloc
public import Arm64.Trusted.Syscalls.Signals
public import Arm64.Trusted.Syscalls.Time
public import Arm64.Trusted.Syscalls.Random
public import Arm64.Trusted.Syscalls.Misc

/-!
# Linux AArch64 Syscall Families Umbrella (`Arm64.Trusted.Syscalls`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Purpose & Key Exports**: Re-exports the modular Linux AArch64 syscall families under
  `Arm64/Trusted/Syscalls/` (`Common`, `Stdio`, `FileIo`, `Poll`, `Alloc`, `Signals`, `Time`,
  `Random`, `Misc`) and defines the empty bundle `Syscall.none`, the full 31-entry dispatch table
  `Syscall.standardTable`, `Syscall.standard`, and the compatibility alias `execSyscall`.
- **When to read**: Read `Arm64/Trusted/Syscalls/README.md` to pick the minimal bundle for a
  specification (`noSyscalls`, `Syscall.stdioCli`, `Syscall.fileIo`, ...) so unused syscall families
  stay outside the theorem statement's transitive constant closure.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Empty dispatch table: every `SVC #0` fails closed with `.Exception "unmodeled syscall (svc)"`. -/
def none : State → State := dispatch []

/-- Complete 31-syscall Linux AArch64 dispatch table combining all modeled families. -/
def standardTable : List (BitVec 64 × (State → State)) :=
  stdioTable ++ fileIoOnlyTable ++ pollTable ++ allocTable ++ signalsTable ++ timeTable ++ randomTable ++ miscTable

/-- Full modeled Linux AArch64 syscall bundle (`31` syscalls across `Stdio`, `FileIo`, `Poll`,
    `Alloc`, `Signals`, `Time`, `Random`, and `Misc`). -/
def standard : State → State := dispatch standardTable

end Syscall

/-- Compatibility alias for `Syscall.standard` (`SVC #0` dispatch over all 31 modeled syscalls). -/
abbrev execSyscall : State → State := Syscall.standard

end Arm64
