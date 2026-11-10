/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Entropy Syscalls

Defines the Linux AArch64 `getrandom` syscall number (`SYS_GETRANDOM = 278`), `GRND_*` flag
constants (`include/uapi/linux/random.h`), and handler `execGetrandom` (`drivers/char/random.c`).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `getrandom` syscall number (`__NR_getrandom = 278`, `include/uapi/asm-generic/unistd.h:762`, `drivers/char/random.c:1395`). -/
def SYS_GETRANDOM : BitVec 64 := 278#64

/-- Linux `getrandom` flags (`include/uapi/linux/random.h:47-49`). -/
def GRND_NONBLOCK   : BitVec 32 := 0x0001#32
def GRND_RANDOM     : BitVec 32 := 0x0002#32
def GRND_INSECURE   : BitVec 32 := 0x0004#32
def GRND_KNOWN_MASK : BitVec 32 := GRND_NONBLOCK ||| GRND_RANDOM ||| GRND_INSECURE

/-- `getrandom(buf, count, flags)` (`__NR_getrandom = 278`, `drivers/char/random.c:1395`):
    - `flags` is `unsigned int` (`W2`): rejects bits outside `GRND_KNOWN_MASK` (`0x7`) and the
      mutually exclusive combination `GRND_INSECURE | GRND_RANDOM` (`0x6`) with `-EINVAL`.
    - `count > MAX_RW_COUNT` (`0x7ffff000`) returns `-EINVAL` without writing memory or advancing
      `oracleIdx` (Linux clamps `count` to `MAX_RW_COUNT` for a short read).
    - Assumes an initialized kernel CRNG, so `GRND_NONBLOCK` never returns `-EAGAIN` and valid
      requests fill `count` bytes from `s.oracle.getrandom s.oracleIdx`.
    - Checks `flags` before checking `s.mem.canWrite buf count.toNat` (`copy_to_user`). -/
def execGetrandom (s : State) : State :=
  let buf := s.readReg64 Reg.x0
  let count := s.readReg64 Reg.x1
  let flags := s.readReg32 Reg.x2
  if (flags &&& ~~~GRND_KNOWN_MASK) != 0#32 ||
      (flags &&& (GRND_RANDOM ||| GRND_INSECURE)) == (GRND_RANDOM ||| GRND_INSECURE) ||
      count.toNat > MAX_RW_COUNT then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if !s.mem.canWrite buf count.toNat then
    (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
  else
    let bytes := (List.range count.toNat).map (s.oracle.getrandom s.oracleIdx)
    (((s.setMem (s.mem.writeBytes buf bytes)).nextOracle).writeReg64 Reg.x0 count).advancePC

end Arm64
