/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Linux `fcntl` Syscall

Models the Linux AArch64 `fcntl` syscall (`__NR_fcntl = 25`, `fs/fcntl.c:590`,
`include/uapi/asm-generic/fcntl.h:111`) for `F_GETFD` (`1`) and `F_SETFD` (`2`, `FD_CLOEXEC = 1`).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `fcntl` syscall number (`__NR_fcntl = 25`, `include/uapi/asm-generic/unistd.h:99`). -/
def SYS_FCNTL : BitVec 64 := 25#64

/-- Linux `fcntl.h` commands `F_GETFD` (`1`) and `F_SETFD` (`2`). -/
def F_GETFD_W32     : BitVec 32 := 1#32
def F_SETFD_W32     : BitVec 32 := 2#32

/-- `fcntl(fd, cmd, arg)`: models `F_GETFD` (`1`) and `F_SETFD` (`2`, updating
    `FdEntry.cloexec := (arg &&& 1) != 0`) on open `.localFile` or `.localDir` descriptors, and
    faults on all other descriptor kinds or commands. -/
def execFcntl (s : State) : State :=
  let rawFd := s.readReg32 Reg.x0
  let cmd   := s.readReg32 Reg.x1
  let arg   := s.readReg64 Reg.x2
  if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
    | some desc =>
      if !(desc.kind == .localFile || desc.kind == .localDir) then s.setStatus (.Exception "unmodeled non-file fd")
      else if cmd == F_GETFD_W32 then
        (s.writeReg64 Reg.x0 (if desc.cloexec then 1#64 else 0#64)).advancePC
      else if cmd == F_SETFD_W32 then
        let fs' := s.fs.setFd fd (some { desc with cloexec := (arg &&& 1#64) != 0#64 })
        ((s.setFs fs').writeReg64 Reg.x0 0#64).advancePC
      else s.setStatus (.Exception "unmodeled fcntl cmd")

end Arm64
