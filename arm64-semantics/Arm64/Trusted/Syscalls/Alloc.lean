/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Mm.Mmap
public import Arm64.Trusted.Syscalls.Mm.Mprotect
public import Arm64.Trusted.Syscalls.Mm.Mremap
public import Arm64.Trusted.Syscalls.Mm.Madvise

/-!
# Virtual-Memory Allocator Syscalls

Re-exports the Linux `7.3` virtual-memory syscall models and bundles them into
`Syscall.allocTable` and `Syscall.alloc`:
- [`Arm64.Trusted.Syscalls.Mm.Mmap`](Mm/Mmap.lean) (`mm/mmap.c`, `mm/vma.c`: `brk`, `munmap`, `mmap`)
- [`Arm64.Trusted.Syscalls.Mm.Mprotect`](Mm/Mprotect.lean) (`mm/mprotect.c`: `mprotect`)
- [`Arm64.Trusted.Syscalls.Mm.Mremap`](Mm/Mremap.lean) (`mm/mremap.c`: `mremap`)
- [`Arm64.Trusted.Syscalls.Mm.Madvise`](Mm/Madvise.lean) (`mm/madvise.c`: `madvise`)
-/

@[expose] public section

namespace Arm64

namespace Syscall

/-- Dispatch table for the virtual-memory allocator family (`brk`, `munmap`, `mremap`, `mmap`,
    `mprotect`, `madvise`). -/
def allocTable : List (BitVec 64 × (State → State)) :=
  [(SYS_BRK, execBrk),
   (SYS_MUNMAP, execMunmap),
   (SYS_MREMAP, execMremap),
   (SYS_MMAP, execMmap),
   (SYS_MPROTECT, execMprotect),
   (SYS_MADVISE, execMadvise)]

/-- Bundle permitting virtual-memory allocator syscalls (`6` syscalls). -/
def alloc : State → State := dispatch allocTable

end Syscall

end Arm64
