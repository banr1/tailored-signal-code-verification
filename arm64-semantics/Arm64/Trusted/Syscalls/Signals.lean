/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Kernel.Signal

/-!
# Signal and Abort Syscalls

Re-exports `Arm64.Trusted.Syscalls.Kernel.Signal` (`tkill`, `tgkill`, `sigaltstack`,
`rt_sigaction`, `rt_sigprocmask`) and defines `Syscall.signalsTable` and `Syscall.signals`.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for synchronous signal and abort syscalls (`tkill`, `tgkill`, `sigaltstack`,
    `rt_sigaction`, `rt_sigprocmask`). -/
def signalsTable : List (BitVec 64 × (State → State)) :=
  [(SYS_TKILL, execTkill),
   (SYS_TGKILL, execTgkill),
   (SYS_SIGALTSTACK, execSigaltstack),
   (SYS_RT_SIGACTION, execRtSigaction),
   (SYS_RT_SIGPROCMASK, execRtSigprocmask)]

/-- Syscall dispatch handler for synchronous signal and abort syscalls. -/
def signals : State → State := dispatch signalsTable

end Syscall

end Arm64
