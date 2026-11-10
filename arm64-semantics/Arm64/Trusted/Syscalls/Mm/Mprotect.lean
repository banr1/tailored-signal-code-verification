/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Syscalls.Mm.Mmap

/-!
# Linux `mprotect` Syscall

Defines `SYS_MPROTECT` (`226`) and `execMprotect`, modeling Linux 7.3 `do_mprotect_pkey`
(`mm/mprotect.c:892`) for `PROT_NONE` and `PROT_READ | PROT_WRITE` on non-frozen mapped memory.
-/

@[expose] public section

namespace Arm64

/-- Linux AArch64 `mprotect` syscall number (`__NR_mprotect = 226`, `include/uapi/asm-generic/unistd.h:616`, `mm/mprotect.c:892`). -/
def SYS_MPROTECT : BitVec 64 := 226#64

/-- Minimal `mprotect(addr, len, prot)` (`__NR_mprotect = 226`, `mm/mprotect.c:892` `do_mprotect_pkey`)
    for `PROT_NONE` (`0x0`) and `PROT_READ | PROT_WRITE` (`0x3`) on non-frozen mapped memory.
    With `size := pageAlignUp len`:
    - `[INTENTIONAL_SCOPE]`: if `prot` is neither `MMAP_PROT_NONE` (`0`) nor `MMAP_PROT_RW` (`3`),
      fails closed with `.Exception "unmodeled mprotect (only PROT_NONE and PROT_READ|PROT_WRITE)"`;
    - if `addr` is not page-aligned (`addr.toNat % PAGE_SIZE != 0`), returns `-EINVAL`;
    - if `[addr, addr + size)` exceeds the 48-bit user virtual address space
      (`addr.toNat + size > 2 ^ 48`), fails closed with
      `.Exception "mprotect range exceeds user VA space"`;
    - if `len == 0`, returns `0` without modifying memory (`mm/mprotect.c:821`);
    - if `[addr, addr + size)` intersects any frozen byte, fails closed with
      `.Exception "mprotect on frozen memory"`;
    - if `[addr, addr + size)` is completely unmapped (`s.mem.canMap addr size`), returns `-ENOMEM`
      without modifying memory (matching Linux `mm/mprotect.c:854` when the first page has no VMA);
    - if `[addr, addr + size)` mixes mapped and unmapped bytes (`!s.mem.allPerm (·.mapped) addr size`
      and `!s.mem.canMap addr size`), fails closed with
      `.Exception "mprotect on partially mapped range"`;
    - otherwise updates the permission of every byte in `[addr, addr + size)` to `Perm.protNone`
      (when `prot == MMAP_PROT_NONE`, with `0` refund to `s.physMemAvail` because `setPermNonFrozen`
      retains resident byte values and Linux `mprotect_fixup` in `mm/mprotect.c:819-820` does not
      un-account resident anonymous pages on write-removal) or `Perm.rw` (when
      `prot == MMAP_PROT_RW`, charging `needed := size - s.mem.countRw addr size` against
      `s.physMemAvail` and transitioning to `ExecStatus.OutOfMemory` if `s.physMemAvail < needed`),
      preserving byte values, and returns `0`. -/
def execMprotect (s : State) : State :=
  let addr := s.readReg64 Reg.x0
  let len := (s.readReg64 Reg.x1).toNat
  let prot := s.readReg64 Reg.x2
  let size := pageAlignUp len
  if prot != MMAP_PROT_NONE && prot != MMAP_PROT_RW then
    s.setStatus (.Exception "unmodeled mprotect (only PROT_NONE and PROT_READ|PROT_WRITE)")
  else if addr.toNat % PAGE_SIZE != 0 then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if !decide (addr.toNat + size ≤ 2 ^ 48) then
    s.setStatus (.Exception "mprotect range exceeds user VA space")
  else if len == 0 then
    (s.writeReg64 Reg.x0 0#64).advancePC
  else if !s.mem.allPerm (fun p => !p.frozen) addr size then
    s.setStatus (.Exception "mprotect on frozen memory")
  else if !s.mem.allPerm (·.mapped) addr size then
    if s.mem.canMap addr size then
      (s.writeReg64 Reg.x0 (-ENOMEM)).advancePC
    else
      s.setStatus (.Exception "mprotect on partially mapped range")
  else
    if prot == MMAP_PROT_NONE then
      ((s.setMem (s.mem.setPermNonFrozen addr size Perm.protNone)).writeReg64 Reg.x0 0#64).advancePC
    else
      let oldRw := s.mem.countRw addr size
      let needed := size - oldRw
      if !decide (needed ≤ s.physMemAvail) then
        s.setStatus .OutOfMemory
      else
        (((s.setMem (s.mem.setPermNonFrozen addr size Perm.rw)).setPhysMemAvail
          (s.physMemAvail - needed)).writeReg64 Reg.x0 0#64).advancePC

end Arm64
