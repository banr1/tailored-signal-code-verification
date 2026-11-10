/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Linux Process Termination `exit` & `exit_group` Syscalls (`Arm64.Trusted.Syscalls.Kernel.Exit`)

- **Layer / Role**: `Arm64` Trusted Computing Base (`Role::Spec`, definitions only, 0 theorems).
- **Linux `7.3` Upstream Sources**:
  - `kernel/exit.c:1094` (`SYSCALL_DEFINE1(exit, int, error_code)` -> `do_exit`)
  - `kernel/exit.c:1138` (`SYSCALL_DEFINE1(exit_group, int, error_code)` -> `do_group_exit`)
- **Purpose & Key Exports**: `SYS_EXIT` (`93`), `SYS_EXIT_GROUP` (`94`), and `execExit`.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `exit` syscall number (`__NR_exit = 93`, `include/uapi/asm-generic/unistd.h:258`, `kernel/exit.c:1094`). -/
def SYS_EXIT : BitVec 64 := 93#64

/-- Linux AArch64 `exit_group` syscall number (`__NR_exit_group = 94`, `include/uapi/asm-generic/unistd.h:260`, `kernel/exit.c:1138`). -/
def SYS_EXIT_GROUP : BitVec 64 := 94#64

/-- `exit(status)` (`__NR_exit = 93`, `kernel/exit.c:1094`) and `exit_group(status)`
    (`__NR_exit_group = 94`, `kernel/exit.c:1138`).
    - `[INTENTIONAL_SCOPE]`: In the single-threaded process model, `exit` and `exit_group` have
      identical process-termination semantics (`execExit` stores the full 64-bit `X0` in `.Exited`,
      and `ProcessOutcome.ofState` preserves `code` unmasked rather than masking with `0xff`, so
      `X0 = 256` gives `exitCode = 256` where Linux reports status `0`; specifications constrain
      the full 64-bit `exitCode`). -/
def execExit (s : State) : State :=
  s.setStatus (.Exited (s.readReg64 Reg.x0))

end Arm64
