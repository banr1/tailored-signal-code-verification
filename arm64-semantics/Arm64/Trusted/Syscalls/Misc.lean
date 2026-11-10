/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Kernel.Sys

/-!
# Thread Identity and Affinity Syscalls

Trusted syscall dispatch bundle (`Syscall.miscTable`, `Syscall.misc`) re-exporting `Kernel.Sys` for
single-thread `set_tid_address`, `sched_getaffinity`, `getpid`, and `gettid`.
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for single-thread identity and CPU-affinity syscalls (`set_tid_address`,
    `sched_getaffinity`, `getpid`, `gettid`). -/
def miscTable : List (BitVec 64 × (State → State)) :=
  [(SYS_SET_TID_ADDRESS, execSetTidAddress),
   (SYS_SCHED_GETAFFINITY, execSchedGetaffinity),
   (SYS_GETPID, execGetpid),
   (SYS_GETTID, execGetpid)]

/-- Syscall dispatcher for `miscTable`. -/
def misc : State → State := dispatch miscTable

end Syscall

end Arm64
