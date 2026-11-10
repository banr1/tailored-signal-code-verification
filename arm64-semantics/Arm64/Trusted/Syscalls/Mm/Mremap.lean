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
# Linux Virtual Memory `mremap` Syscall

Trusted model of the Linux AArch64 `mremap` syscall (`mm/mremap.c`,
`include/uapi/linux/mman.h`), defining `Memory.remapRw`, `SYS_MREMAP`, `MREMAP_MAYMOVE`,
and `execMremap`.
-/

@[expose] public section

namespace Arm64

namespace Memory

/-- Move or resize a non-frozen `Perm.rw` range `[oldBase, oldBase + oldSize)` onto
    `[newBase, newBase + newSize)`:
    - frozen bytes (`(m.perm a).frozen`) are unconditionally preserved;
    - for any non-frozen byte `a` in `[newBase, newBase + newSize)` at offset
      `off := (a - newBase).toNat`, maps `some (some p, b)` where for `off < oldSize` (`src :=
      oldBase + off`) `b = m.read8 src` and `p = { Perm.rw with lazyFree := m.isLazyFree src,
      anon := m.isAnon src }`, and for `off ≥ oldSize` `b = 0#8` and `p = Perm.rw`;
    - for any remaining non-frozen byte `a` in `[oldBase, oldBase + oldSize)`, unmaps (`none`);
    - all other bytes keep `m.cells a`. -/
def remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) : Memory :=
  ⟨fun a =>
    if (m.perm a).frozen then
      m.cells a
    else if (a - newBase).toNat < newSize then
      let off := (a - newBase).toNat
      let src := oldBase + BitVec.ofNat 64 off
      let b := if off < oldSize then m.read8 src else 0#8
      let p := if off < oldSize then
        { Perm.rw with lazyFree := m.isLazyFree src, anon := m.isAnon src }
      else Perm.rw
      some (some p, b)
    else if (a - oldBase).toNat < oldSize then
      none
    else
      m.cells a⟩

end Memory

/-- Linux AArch64 `mremap` syscall number (`__NR_mremap = 216`,
    `include/uapi/asm-generic/unistd.h:597`, `mm/mremap.c:1964`). -/
def SYS_MREMAP : BitVec 64 := 216#64

/-- `mremap` `flags` bit `MREMAP_MAYMOVE` (`1`, `include/uapi/linux/mman.h:8`). -/
def MREMAP_MAYMOVE : BitVec 64 := 1#64

/-- `mremap(old_address, old_size, new_size, flags)` (`__NR_mremap = 216`,
    `SYSCALL_DEFINE5(mremap)` and `vma_to_resize` / `move_vma` in `mm/mremap.c:1964`), modeled for
    `flags == MREMAP_MAYMOVE` (`1`) on a single mapped `Perm.rw` anonymous range:
    - `[INTENTIONAL_SCOPE]`: any `flags ≠ MREMAP_MAYMOVE` fails closed with `.Exception "unmodeled mremap flags"`;
    - `old_address` (`X0`) not page-aligned, `new_size == 0` (`X2 == 0`), or 64-bit `PAGE_ALIGN`
      overflow on `new_size` (`newLen > 2 ^ 64 - PAGE_SIZE`) returns `-EINVAL` (`offset_in_page`
      and `!PAGE_ALIGN(new_len)` in `mm/mremap.c:1819` `check_mremap_params`);
    - `old_size == 0` (`X1 == 0`) fails closed with `.Exception "unmodeled mremap (old_size == 0)"`;
    - with `oldAligned := pageAlignUp oldLen` and `newAligned := pageAlignUp newLen`:
      - if `oldAddr.toNat + oldAligned > USER_VA_LIMIT`, returns `-EINVAL`;
      - if `[oldAddr, oldAddr + oldAligned)` intersects any frozen byte, fails closed with
        `.Exception "mremap on frozen memory"`;
      - if `[oldAddr, oldAddr + oldAligned)` is completely unmapped (`s.mem.canMap oldAddr oldAligned`),
        returns `-EFAULT` (`vma_lookup` miss in `vma_to_resize`, `mm/mremap.c:1110`);
      - if `[oldAddr, oldAddr + oldAligned)` is not uniformly `some Perm.rw`, fails closed with
        `.Exception "unmodeled mremap (range not uniformly PROT_READ|PROT_WRITE)"`;
      - otherwise queries `s.oracleIdx` (`[INTENTIONAL_OVERAPPROX]`):
        - if `s.oracle.mremapFail s.oracleIdx` is `true`, consumes the oracle query (`s.nextOracle`),
          leaves `s.mem` unchanged, and returns `-ENOMEM`;
        - otherwise computes `mUnmapped := s.mem.unmapNonFrozen oldAddr oldAligned` and sanitizes
          `s.oracle.mmap s.oracleIdx` via `sanitizeMmapAddr mUnmapped cand newAligned`. -/
def execMremap (s : State) : State :=
  let oldAddr := s.readReg64 Reg.x0
  let oldLen  := (s.readReg64 Reg.x1).toNat
  let newLen  := (s.readReg64 Reg.x2).toNat
  let flags   := s.readReg64 Reg.x3
  if flags != MREMAP_MAYMOVE then
    s.setStatus (.Exception "unmodeled mremap flags")
  else if oldAddr.toNat % PAGE_SIZE != 0 || newLen == 0 || !decide (newLen ≤ 2 ^ 64 - PAGE_SIZE) then
    (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
  else if oldLen == 0 then
    s.setStatus (.Exception "unmodeled mremap (old_size == 0)")
  else
    let oldAligned := pageAlignUp oldLen
    let newAligned := pageAlignUp newLen
    if !decide (oldAddr.toNat + oldAligned ≤ USER_VA_LIMIT) then
      (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
    else if !s.mem.allPerm (fun p => !p.frozen) oldAddr oldAligned then
      s.setStatus (.Exception "mremap on frozen memory")
    else if s.mem.canMap oldAddr oldAligned then
      (s.writeReg64 Reg.x0 EFAULT_RET).advancePC
    else if !s.mem.allPerm (· == some Perm.rw) oldAddr oldAligned then
      s.setStatus (.Exception "unmodeled mremap (range not uniformly PROT_READ|PROT_WRITE)")
    else if !s.mem.allAnon oldAddr oldAligned then
      s.setStatus (.Exception "unmodeled mremap on non-anonymous memory")
    else if s.oracle.mremapFail s.oracleIdx then
      ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
    else
      let mUnmapped := s.mem.unmapNonFrozen oldAddr oldAligned
      match sanitizeMmapAddr mUnmapped (s.oracle.mmap s.oracleIdx) newAligned with
      | none =>
        ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC
      | some newBase =>
        if !decide (newAligned ≤ s.physMemAvail + oldAligned) then
          s.setStatus .OutOfMemory
        else
          let mem' := s.mem.remapRw oldAddr oldAligned newBase newAligned
          ((((s.setMem mem').setPhysMemAvail
            (s.physMemAvail + oldAligned - newAligned)).nextOracle).writeReg64
            Reg.x0 newBase).advancePC

end Arm64
