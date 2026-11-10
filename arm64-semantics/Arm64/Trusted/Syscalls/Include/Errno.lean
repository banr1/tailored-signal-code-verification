/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.State

/-!
# Linux UAPI Error Numbers

Linux AArch64 errno constants from `include/uapi/asm-generic/errno-base.h` (`EPERM = 1` ..
`ENOTTY = 25`, `EFAULT_RET = -14`) and `include/uapi/asm-generic/errno.h` (`ENAMETOOLONG = 36`).
-/

@[expose] public section

namespace Arm64

/-- Linux `EPERM` (`1`, `include/uapi/asm-generic/errno-base.h`). -/
def EPERM        : BitVec 64 := 1#64
def ENOENT       : BitVec 64 := 2#64
def ESRCH        : BitVec 64 := 3#64
def ENXIO        : BitVec 64 := 6#64
def EBADF        : BitVec 64 := 9#64
def ENOMEM       : BitVec 64 := 12#64
def EEXIST       : BitVec 64 := 17#64
def ENOTDIR      : BitVec 64 := 20#64
def EISDIR       : BitVec 64 := 21#64
def EINVAL       : BitVec 64 := 22#64
def EMFILE       : BitVec 64 := 24#64
def ENOTTY       : BitVec 64 := 25#64
def ENAMETOOLONG : BitVec 64 := 36#64

/-- Linux `-EFAULT` error return (`-14`, `include/uapi/asm-generic/errno-base.h:18`). -/
def EFAULT_RET : BitVec 64 := -14#64

end Arm64
