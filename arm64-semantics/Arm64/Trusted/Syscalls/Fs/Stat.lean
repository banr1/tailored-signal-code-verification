/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common

/-!
# Linux `fstat` Syscall

Models AArch64 `fstat` (`__NR_fstat = 80`, Linux `fs/stat.c` `newfstat`) and the 128-byte
little-endian `struct stat` layout (`include/uapi/asm-generic/stat.h`).
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `fstat` syscall number (`__NR_fstat = 80`, `include/uapi/asm-generic/unistd.h:229`). -/
def SYS_FSTAT : BitVec 64 := 80#64

/-- Serialize a 128-byte little-endian Linux AArch64 `struct stat`
(`include/uapi/asm-generic/stat.h:24`, `fs/stat.c:405` `cp_new_stat`). Regular files report mode
`0644` (`0x81a4`), `st_nlink = 1`, byte length `st_size`, and 512-byte sector count `st_blocks`;
permission bits are metadata only and permission checks are not modeled. Directory entries
synthesize fixed metadata (`st_mode = 0x41ed` for `0755`, `st_nlink = 2`, `st_size = 0`,
`st_blocks = 0`) independent of directory contents or filesystem. -/
def encodeLinuxStat (e : FsEntry) : List (BitVec 8) :=
  let (mode, nlink, sz, blks) := match e with
    | .file bs => (0x81a4#32, 1#32, BitVec.ofNat 64 bs.length, BitVec.ofNat 64 ((bs.length + 511) / 512))
    | .dir     => (0x41ed#32, 2#32, 0#64, 0#64)
  leBytes64 0#64 ++ leBytes64 1#64 ++ leBytes32 mode ++ leBytes32 nlink ++
  leBytes32 0#32 ++ leBytes32 0#32 ++ leBytes64 0#64 ++ leBytes64 0#64 ++
  leBytes64 sz ++ leBytes32 4096#32 ++ leBytes32 0#32 ++ leBytes64 blks ++
  List.replicate 56 0#8

/-- Execute `fstat(fd, statbuf)` (`__NR_fstat = 80`, `fs/stat.c:525` `newfstat`). Models
`.localFile` and `.localDir` descriptors, raising `.Exception` on unmodeled `.stdio` or non-file
descriptors. Validates `fd` before checking `statbuf` write permissions (`EFAULT_RET`), matching
`vfs_fstat` followed by `cp_new_stat`. -/
def execFstat (s : State) : State :=
  let rawFd   := s.readReg32 Reg.x0
  let statbuf := s.readReg64 Reg.x1
  if rawFd.slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
  else
    let fd := rawFd.zeroExtend 64
    match s.fs.fds fd with
    | none =>
      if fd < 3#64 then s.setStatus (.Exception "unmodeled stdio fd")
      else (s.writeReg64 Reg.x0 (-EBADF)).advancePC
    | some desc =>
      if desc.kind != .localFile && desc.kind != .localDir then
        s.setStatus (.Exception "unmodeled non-file fd")
      else
        let entry := (s.fs.files desc.path).getD (.file [])
        if !s.mem.canWrite statbuf 128 then (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
        else ((s.setMem (s.mem.writeBytes statbuf (encodeLinuxStat entry))).writeReg64 Reg.x0 0#64).advancePC

end Arm64
