/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Thread Identity and Affinity Syscalls

Linux AArch64 syscall numbers and transition functions for `set_tid_address` (`96`),
`sched_getaffinity` (`123`), `getpid` (`172`), and `gettid` (`178`), modeled after Linux
`kernel/fork.c`, `kernel/sched/syscalls.c`, and `kernel/sys.c` in a single-process,
single-thread, single-CPU environment.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `set_tid_address` syscall number (`__NR_set_tid_address = 96`, `include/uapi/asm-generic/unistd.h:278`, `kernel/fork.c:1866`). -/
def SYS_SET_TID_ADDRESS : BitVec 64 := 96#64

/-- Linux AArch64 `sched_getaffinity` syscall number (`__NR_sched_getaffinity = 123`, `include/uapi/asm-generic/unistd.h:344`, `kernel/sched/syscalls.c:1395`). -/
def SYS_SCHED_GETAFFINITY : BitVec 64 := 123#64

/-- Linux AArch64 `getpid` syscall number (`__NR_getpid = 172`, `include/uapi/asm-generic/unistd.h:472`, `kernel/sys.c:966`). -/
def SYS_GETPID : BitVec 64 := 172#64

/-- Linux AArch64 `gettid` syscall number (`__NR_gettid = 178`, `include/uapi/asm-generic/unistd.h:487`, `kernel/sys.c:979`). -/
def SYS_GETTID : BitVec 64 := 178#64

/-- 8-byte kernel `cpumask_t` (`CPU 0` online) written by `sched_getaffinity`. -/
def SCHED_AFFINITY_MASK : List (BitVec 8) :=
  [1#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8]

/-- `set_tid_address(tidptr)` (`__NR_set_tid_address = 96`, `kernel/fork.c:1866`): per Linux
    `kernel/fork.c`, records `clear_child_tid` (`[INTENTIONAL_SCOPE]`: no-op in single-threaded
    execution without `CLONE_CHILD_CLEARTID`) without dereferencing `tidptr`, and always succeeds
    returning the caller's thread ID (`SIM_TID = 1`). -/
def execSetTidAddress (s : State) : State :=
  (s.writeReg64 Reg.x0 SIM_TID).advancePC

/-- `getpid()` (`__NR_getpid = 172`, `kernel/sys.c:966`) and `gettid()` (`__NR_gettid = 178`,
    `kernel/sys.c:979`): return the calling process/thread ID (`SIM_TID = 1`) in the
    single-process, single-thread model (`[INTENTIONAL_SCOPE]`). -/
def execGetpid (s : State) : State :=
  (s.writeReg64 Reg.x0 SIM_TID).advancePC

/-- `sched_getaffinity(pid, cpusetsize, mask)` (`__NR_sched_getaffinity = 123`,
    `kernel/sched/syscalls.c:1278,1307` `SYSCALL_DEFINE3(sched_getaffinity, pid_t, pid,
    unsigned int, len, unsigned long __user *, user_mask_ptr)` -> `sched_getaffinity`
    -> `find_process_by_pid` at `kernel/sched/syscalls.c:215`):
    models Linux `kernel/sched/syscalls.c` on a single-CPU AArch64 system
    (`cpumask_size() = 8`, `sizeof(unsigned long) = 8`, CPU 0 online):
    - if 32-bit `unsigned int` `cpusetsize < 8` or `cpusetsize % 8 != 0`, returns `-EINVAL`;
    - if `(pid : Int32) < 0` (`pid.slt 0#32`), returns `-ESRCH` (`find_process_by_pid(pid)`
      returns `NULL` in `kernel/sched/syscalls.c:1284-1286`);
    - `[INTENTIONAL_SCOPE]`: if `pid != 0` (calling thread) and `pid != 1` (`SIM_TID`), fails closed
      with `.Exception "unmodeled sched_getaffinity pid"`;
    - if `!s.mem.canWrite mask 8`, returns `EFAULT_RET` (`-EFAULT`);
    - otherwise writes the 8-byte single-CPU mask (`SCHED_AFFINITY_MASK`) to `mask`
      and returns `8` (`cpumask_size()`). -/
def execSchedGetaffinity (s : State) : State :=
  let pid        := s.readReg32 Reg.x0
  let cpusetsize := (s.readReg32 Reg.x1).toNat
  let mask       := s.readReg64 Reg.x2
  if cpusetsize < 8 || cpusetsize % 8 != 0 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if pid.slt 0#32 then
    (s.writeReg64 Reg.x0 (-ESRCH)).advancePC
  else if pid != 0#32 && pid != 1#32 then
    s.setStatus (.Exception "unmodeled sched_getaffinity pid")
  else if !s.mem.canWrite mask 8 then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else
    ((s.setMem (s.mem.writeBytes mask SCHED_AFFINITY_MASK)).writeReg64 Reg.x0 8#64).advancePC

end Arm64
