/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Invariant
public import ProofLib.Lemmas
public import ProofLib.Process

/-!
# `MADV_FREE` Lazy Reclaim and Anonymous-VMA Conformance Tests

Symbolic theorems and `#eval` trace checks for Linux `MADV_FREE` (`8`) and `MADV_DONTNEED` (`4`)
semantics on `Memory` and `execMadvise` (`include/uapi/asm-generic/mman-common.h`, `mm/madvise.c`,
`mm/rmap.c`): lazy-free marking (`isLazyFree = true`, `canRead = false`), store-triggered
cancellation (`write8`), `mprotect` preservation (`setPermNonFrozen`), synchronous zeroing under
`MADV_DONTNEED`, and fail-closed exceptions on file-backed (`isAnon = false`) or lazy-free reads.
-/

@[expose] public section

namespace Testing.MadvFree

open Arm64 ProofLib

/-! ## Symbolic conformance theorems -/

/-- `madvise(addr, len, MADV_FREE = 8)` on a mapped, non-frozen, anonymous range marks every byte in
    `[addr, addr + pageAlignUp len)` `isLazyFree = true` (`canRead = false`), preserves `.perm` and
    `.isAnon`, leaves outside bytes unchanged, writes `0` to `x0`, and advances `pc`. -/
theorem execMadvise_madv_free_conformance (s : State)
    (hadv : s.readReg64 .x2 = MADV_FREE)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    let addr := s.readReg64 .x0
    let size := pageAlignUp (s.readReg64 .x1).toNat
    let s' := execMadvise s
    s'.status = s.status ∧
    s'.readReg64 .x0 = 0#64 ∧
    s'.pc = s.pc + 4#64 ∧
    s'.mem.perm = s.mem.perm ∧
    s'.mem.isAnon = s.mem.isAnon ∧
    (∀ a : BitVec 64, (a - addr).toNat < size →
      s'.mem.isLazyFree a = true ∧ s'.mem.canRead a 1 = false) ∧
    (∀ a : BitVec 64, ¬ (a - addr).toNat < size →
      s'.mem.isLazyFree a = s.mem.isLazyFree a ∧ s'.mem.read8 a = s.mem.read8 a) := by
  have hexec := execMadvise_free_ok s hadv hal hlen hfit hfrz hmap hanon
  dsimp only
  rw [hexec]
  have hmem : (((s.setMem (s.mem.madvFreeNonFrozen (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64 .x0 0#64).advancePC).mem =
      s.mem.madvFreeNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) := rfl
  refine ⟨by cases s; rfl, by simp, by cases s; rfl, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; exact Memory.perm_madvFreeNonFrozen s.mem _ _
  · rw [hmem]; exact Memory.isAnon_madvFreeNonFrozen s.mem _ _
  · intro a hin
    rw [hmem]
    have ha : s.readReg64 .x0 + BitVec.ofNat 64 (a - s.readReg64 .x0).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hmap_a : (s.mem.perm a).mapped = true := by
      have h := (Memory.allPerm_iff s.mem _ _ _).mp hmap (a - s.readReg64 .x0).toNat hin
      rwa [ha] at h
    have hfrz_a : (!(s.mem.perm a).frozen) = true := by
      have h := (Memory.allPerm_iff s.mem _ _ _).mp hfrz (a - s.readReg64 .x0).toNat hin
      rwa [ha] at h
    have hcond : ((a - s.readReg64 .x0).toNat < pageAlignUp (s.readReg64 .x1).toNat &&
        (s.mem.perm a).mapped && !(s.mem.perm a).frozen) = true := by
      simp only [decide_eq_true hin, hmap_a, hfrz_a, Bool.and_self]
    have hlf : (s.mem.madvFreeNonFrozen (s.readReg64 .x0)
        (pageAlignUp (s.readReg64 .x1).toNat)).isLazyFree a = true := by
      rw [Memory.isLazyFree_madvFreeNonFrozen]; simp only [hcond, ↓reduceIte]
    refine ⟨hlf, ?_⟩
    simp [Memory.canRead, Memory.allNoLazyFree, hlf]
  · intro a hout
    have hcond : ((a - s.readReg64 .x0).toNat < pageAlignUp (s.readReg64 .x1).toNat &&
        (s.mem.perm a).mapped && !(s.mem.perm a).frozen) = false := by
      simp only [decide_eq_false hout, Bool.false_and]
    rw [hmem, Memory.isLazyFree_madvFreeNonFrozen, Memory.read8_madvFreeNonFrozen]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte, and_self]

/-- Storing a byte (`Memory.write8`) on a writable `Perm.rw` cell clears `isLazyFree = false` on the
    written byte, restores `canRead a 1 = true` with `read8 a = v`, and preserves `isLazyFree` on
    every other address `x ≠ a`. -/
theorem write8_cancels_lazyFree_and_restores_canRead (m : Memory) (a : BitVec 64) (v : BitVec 8)
    (hrw : m.perm a = some Perm.rw) :
    (m.write8 a v).isLazyFree a = false ∧
    (m.write8 a v).canRead a 1 = true ∧
    (m.write8 a v).read8 a = v ∧
    (∀ x : BitVec 64, x ≠ a → (m.write8 a v).isLazyFree x = m.isLazyFree x) := by
  have hlf : (m.write8 a v).isLazyFree a = false := by
    simp [Memory.isLazyFree_write8]
  refine ⟨hlf, ?_, ?_, fun x hx => by simp [Memory.isLazyFree_write8, hx]⟩
  · simp [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, hrw, hlf, Perm.rw]
  · exact Memory.read8_write8_same m a v

/-- `setPermNonFrozen` (`mprotect`) preserves `isLazyFree` and `isAnon`, and setting `Perm.ro`
    (`PROT_READ`) on a `lazyFree` byte keeps `canRead a 1 = false` despite `(perm a).r = true`. -/
theorem setPermNonFrozen_preserves_lazyFree_and_anon (m : Memory)
    (base a : BitVec 64) (len : Nat) (p : Perm) :
    (m.setPermNonFrozen base len p).isLazyFree a = m.isLazyFree a ∧
    (m.setPermNonFrozen base len p).isAnon a = m.isAnon a ∧
    (m.isLazyFree a = true → (m.setPermNonFrozen base len Perm.ro).canRead a 1 = false) := by
  have hlf := Memory.isLazyFree_setPermNonFrozen_apply m base len p a
  have han := Memory.isAnon_setPermNonFrozen_apply m base len p a
  refine ⟨hlf, han, fun htrue => ?_⟩
  have hlf_ro := Memory.isLazyFree_setPermNonFrozen_apply m base len Perm.ro a
  simp [Memory.canRead, Memory.allNoLazyFree, hlf_ro, htrue]

/-- `madvise(addr, len, MADV_DONTNEED = 4)` on a `lazyFree` anonymous range synchronously zeroes
    every byte in `[addr, addr + pageAlignUp len)` and clears `isLazyFree = false`. -/
theorem execMadvise_dontneed_clears_lazyFree_and_zeroes (s : State)
    (hadv : s.readReg64 .x2 = MADV_DONTNEED)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (a : BitVec 64)
    (hin : (a - s.readReg64 .x0).toNat < pageAlignUp (s.readReg64 .x1).toNat) :
    (execMadvise s).mem.isLazyFree a = false ∧
    (execMadvise s).mem.read8 a = 0#8 := by
  have hexec := execMadvise_dontneed_ok s hadv hal hlen hfit hfrz hmap hanon
  rw [hexec]
  have hmem : (((s.setMem (s.mem.zeroNonFrozen (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64 .x0 0#64).advancePC).mem =
      s.mem.zeroNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) := rfl
  rw [hmem]
  have ha : s.readReg64 .x0 + BitVec.ofNat 64 (a - s.readReg64 .x0).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  have hmap_a : (s.mem.perm a).mapped = true := by
    have h := (Memory.allPerm_iff s.mem _ _ _).mp hmap (a - s.readReg64 .x0).toNat hin
    rwa [ha] at h
  have hfrz_a : (!(s.mem.perm a).frozen) = true := by
    have h := (Memory.allPerm_iff s.mem _ _ _).mp hfrz (a - s.readReg64 .x0).toNat hin
    rwa [ha] at h
  have hcond : ((a - s.readReg64 .x0).toNat < pageAlignUp (s.readReg64 .x1).toNat &&
      (s.mem.perm a).mapped && !(s.mem.perm a).frozen) = true := by
    simp only [decide_eq_true hin, hmap_a, hfrz_a, Bool.and_self]
  rw [Memory.isLazyFree_zeroNonFrozen, Memory.read8_zeroNonFrozen]
  simp only [hcond, ↓reduceIte, and_self]

/-- Both `MADV_FREE` (`8`) and `MADV_DONTNEED` (`4`) fail closed with
    `.Exception "madvise on non-anonymous memory"` whenever `allAnon = false` on a mapped
    non-frozen range, whereas `MADV_NORMAL` (`0`) succeeds and returns `0`. -/
theorem execMadvise_non_anon_fails_closed (s : State)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : (s.readReg64 .x1).toNat ≠ 0)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hnonanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = false) :
    (s.readReg64 .x2 = MADV_FREE →
      (execMadvise s).status = .Exception "madvise on non-anonymous memory") ∧
    (s.readReg64 .x2 = MADV_DONTNEED →
      (execMadvise s).status = .Exception "madvise on non-anonymous memory") ∧
    (s.readReg64 .x2 = MADV_NORMAL → s.status = .Running →
      (execMadvise s).status = .Running ∧ (execMadvise s).readReg64 .x0 = 0#64) := by
  have hfit64 : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 64 := by omega
  refine ⟨fun hf => ?_, fun hd => ?_, fun hn hrun => ?_⟩
  · simp [execMadvise, MADV_DONTNEED, MADV_FREE, hf, hal, hlen, hfit, hfit64, hfrz, hmap, hnonanon]
  · simp [execMadvise, MADV_DONTNEED, MADV_FREE, hd, hal, hlen, hfit, hfit64, hfrz, hmap, hnonanon]
  · have hexec : execMadvise s = (s.writeReg64 .x0 0#64).advancePC := by
      simp [execMadvise, MADV_NORMAL, MADV_DONTNEED, MADV_FREE, hn, hal, hlen, hfit, hfit64, hfrz, hmap]
    rw [hexec]
    exact ⟨by cases s; exact hrun, by simp⟩

/-- `Snapshot.loadCellAt` marks file-backed ELF bytes (`off < r.nonAnonLen`) with `isAnon = false`
    and pure zero-initialized `.bss` tail bytes (`r.nonAnonLen ≤ off < r.bytes.length`) with
    `isAnon = true` when `r.perm.anon = true`. -/
theorem snapshot_loadCellAt_isAnon_split (r : Snapshot.Region) (a : BitVec 64)
    (hanon_perm : r.perm.anon = true) :
    let m : Memory := ⟨Snapshot.loadCellAt [r]⟩
    ((a - r.start).toNat < r.nonAnonLen → (a - r.start).toNat < r.bytes.length →
      m.isAnon a = false) ∧
    (r.nonAnonLen ≤ (a - r.start).toNat → (a - r.start).toNat < r.bytes.length →
      m.isAnon a = true) := by
  dsimp only
  refine ⟨fun hlt hlen => ?_, fun hge hlen => ?_⟩
  · unfold Memory.isAnon Snapshot.loadCellAt
    dsimp only [List.findSome?_cons, List.findSome?_nil]
    simp only [hlen, ↓reduceDIte, hlt, ↓reduceIte]
  · have hnot : ¬ (a - r.start).toNat < r.nonAnonLen := by omega
    unfold Memory.isAnon Snapshot.loadCellAt
    dsimp only [List.findSome?_cons, List.findSome?_nil]
    simp only [hlen, ↓reduceDIte, hnot, ↓reduceIte, hanon_perm]

/-- `execWrite` to `stdout` (`fd = 1`) fails closed with `.Exception "write from lazy-free memory"`
    (never `-EFAULT`) when readable permission holds (`allPerm (·.r) = true`) while `canRead = false`. -/
theorem execWrite_lazyFree_fails_closed (s : State)
    (hfd : s.readReg64 .x0 = 1#64)
    (hva : (s.readReg64 .x1).toNat + (s.readReg64 .x2).toNat ≤ USER_VA_LIMIT)
    (hcnt : (s.readReg64 .x2).toNat ≤ MAX_RW_COUNT)
    (hperm : s.mem.allPerm (·.r) (s.readReg64 .x1) (s.readReg64 .x2).toNat = true)
    (hcr : s.mem.canRead (s.readReg64 .x1) (s.readReg64 .x2).toNat = false) :
    (execWrite s).status = .Exception "write from lazy-free memory" := by
  have hne0 : s.readReg64 .x2 ≠ 0#64 := by
    intro h0; rw [h0] at hcr; simp [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at hcr
  have hp1 : s.mem.allPerm (·.r) (s.readReg64 .x1) 1 = true := by
    cases h : (s.readReg64 .x2).toNat with
    | zero => exact absurd (BitVec.eq_of_toNat_eq h) hne0
    | succ k =>
      simp only [h, Memory.allPerm, Bool.and_eq_true] at hperm
      simp [Memory.allPerm, hperm.1]
  have hnotva : ¬ (USER_VA_LIMIT < (s.readReg64 .x1).toNat + (s.readReg64 .x2).toNat) :=
    Nat.not_lt.mpr hva
  have hmin : min (s.readReg64 .x2).toNat MAX_RW_COUNT = (s.readReg64 .x2).toNat :=
    Nat.min_eq_left hcnt
  rw [execWrite_stdout s hfd]
  simp [hnotva, hne0, hmin, hcr, hp1, hperm]

/-! ## Concrete ELF and syscall trace checks -/

def callSyscall (s : State) (nr : BitVec 64)
    (x0 : BitVec 64 := 0#64) (x1 : BitVec 64 := 0#64) (x2 : BitVec 64 := 0#64)
    (x3 : BitVec 64 := 0#64) (x4 : BitVec 64 := 0#64) (x5 : BitVec 64 := 0#64) : State :=
  let s := s.writeReg64 .x8 nr
  let s := s.writeReg64 .x0 x0
  let s := s.writeReg64 .x1 x1
  let s := s.writeReg64 .x2 x2
  let s := s.writeReg64 .x3 x3
  let s := s.writeReg64 .x4 x4
  let s := s.writeReg64 .x5 x5
  execSyscall s

def isException (s : State) : Bool :=
  match s.status with
  | .Exception _ => true
  | _            => false

def checkMadvFreeLoadStoreAndSyscallReaders : Bool :=
  let fs0 := (({} : FsState).setFd 1#64
    (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }))
  let p : BitVec 64 := 0x10000#64
  let tspValid : BitVec 64 := 0x20000#64
  let mem0 := (((Memory.empty.mapZero p 4096).mapZero tspValid 4096).write64
    p 0xdeadbeefcafebabe#64).write64 (p + 8#64) 0xfeedfacecafef00d#64
  let sSeed : State := { pc := 0x1000#64, sp := 0x80000#64, physMemAvail := 2 ^ 30, fs := fs0, mem := mem0 }
  let sFree := callSyscall sSeed SYS_MADVISE p 4096#64 MADV_FREE
  let ldrAt0 : Instr := .ldr .W64 .X64 false .x0 (.Offset .x1 0#64)
  let ldrAt8 : Instr := .ldr .W64 .X64 false .x0 (.Offset .x1 8#64)
  let strAt0 : Instr := .str .X64 .x2 (.Offset .x1 0#64)
  let sFreePtr := (sFree.writeReg64 .x1 p).writeReg64 .x2 0x123456789abcdef0#64
  let sBadLdr := execInst ldrAt0 sFreePtr
  let sAfterStr := execInst strAt0 sFreePtr
  let sGoodLdr  := execInst ldrAt0 sAfterStr
  let sAdjLdr   := execInst ldrAt8 sAfterStr
  let u : BitVec 64 := 0x50000000#64
  let sWriteLazy := callSyscall sFree SYS_WRITE 1#64 p 8#64
  let sWriteUnm  := callSyscall sFree SYS_WRITE 1#64 u 8#64
  let sOpenLazy  := callSyscall sFree SYS_OPENAT (-100#64) p 0#64
  let sOpenUnm   := callSyscall sFree SYS_OPENAT (-100#64) u 0#64
  let sPpollTmoLazy := callSyscall sFree SYS_PPOLL 0#64 0#64 p 0#64
  let sPpollTmoUnm  := callSyscall sFree SYS_PPOLL 0#64 0#64 u 0#64
  let sPpollFdsLazy := callSyscall sFree SYS_PPOLL p 1#64 tspValid 0#64 8#64
  let sPpollFdsUnm  := callSyscall sFree SYS_PPOLL u 1#64 tspValid 0#64 8#64
  let sSigpmLazy := callSyscall sFree SYS_RT_SIGPROCMASK 0#64 p 0#64 8#64
  let sSigpmUnm  := callSyscall sFree SYS_RT_SIGPROCMASK 0#64 u 0#64 8#64
  let sSigactLazy := callSyscall sFree SYS_RT_SIGACTION 2#64 p 0#64 8#64
  let sSigactUnm  := callSyscall sFree SYS_RT_SIGACTION 2#64 u 0#64 8#64
  sFree.status == .Running &&
  sFree.readReg64 .x0 == 0#64 &&
  sFree.mem.perm p == some Perm.rw &&
  sFree.mem.isAnon p == true &&
  sFree.mem.isLazyFree p == true &&
  sFree.mem.isLazyFree (p + 8#64) == true &&
  sFree.mem.canRead p 8 == false &&
  sFree.mem.canWrite p 8 == true &&
  sBadLdr.status == .Exception "permission fault" &&
  sAfterStr.status == .Running &&
  sAfterStr.mem.isLazyFree p == false &&
  sAfterStr.mem.isLazyFree (p + 7#64) == false &&
  sAfterStr.mem.isLazyFree (p + 8#64) == true &&
  sAfterStr.mem.canRead p 8 == true &&
  sGoodLdr.status == .Running &&
  sGoodLdr.readReg64 .x0 == 0x123456789abcdef0#64 &&
  sAdjLdr.status == .Exception "permission fault" &&
  isException sWriteLazy && sWriteUnm.status == .Running && sWriteUnm.readReg64 .x0 == EFAULT_RET &&
  isException sOpenLazy && sOpenUnm.status == .Running && sOpenUnm.readReg64 .x0 == EFAULT_RET &&
  isException sPpollTmoLazy && sPpollTmoUnm.status == .Running && sPpollTmoUnm.readReg64 .x0 == EFAULT_RET &&
  isException sPpollFdsLazy && sPpollFdsUnm.status == .Running && sPpollFdsUnm.readReg64 .x0 == EFAULT_RET &&
  isException sSigpmLazy && sSigpmUnm.status == .Running && sSigpmUnm.readReg64 .x0 == EFAULT_RET &&
  isException sSigactLazy && sSigactUnm.status == .Running && sSigactUnm.readReg64 .x0 == EFAULT_RET

/-- info: true -/
#guard_msgs in
#eval checkMadvFreeLoadStoreAndSyscallReaders

def checkMadvFreeMprotectPreservation : Bool :=
  let p : BitVec 64 := 0x10000#64
  let mem0 := (Memory.empty.mapZero p 4096).write64 p 0x55aa55aa55aa55aa#64
  let sSeed : State := { pc := 0x1000#64, sp := 0x80000#64, physMemAvail := 2 ^ 30, mem := mem0 }
  let sFree := callSyscall sSeed SYS_MADVISE p 4096#64 MADV_FREE
  let sNone := callSyscall sFree SYS_MPROTECT p 4096#64 0#64
  let sRw   := callSyscall sNone SYS_MPROTECT p 4096#64 3#64
  let mRo   := sFree.mem.setPermNonFrozen p 4096 Perm.ro
  let ldrAt0 : Instr := .ldr .W64 .X64 false .x0 (.Offset .x1 0#64)
  let strAt0 : Instr := .str .X64 .x2 (.Offset .x1 0#64)
  let sRoLdr   := execInst ldrAt0 ((sFree.setMem mRo).writeReg64 .x1 p)
  let sRwBad   := execInst ldrAt0 (sRw.writeReg64 .x1 p)
  let sRwStr   := execInst strAt0 ((sRw.writeReg64 .x1 p).writeReg64 .x2 0x99#64)
  let sRwLdr   := execInst ldrAt0 sRwStr
  sNone.status == .Running && sNone.readReg64 .x0 == 0#64 &&
  sNone.mem.perm p == some Perm.protNone &&
  sNone.mem.isLazyFree p == true && sNone.mem.isAnon p == true &&
  mRo.perm p == some Perm.ro &&
  (mRo.perm p).r == true &&
  mRo.isLazyFree p == true && mRo.isAnon p == true &&
  mRo.canRead p 1 == false &&
  sRoLdr.status == .Exception "permission fault" &&
  sRw.status == .Running && sRw.readReg64 .x0 == 0#64 &&
  sRw.mem.perm p == some Perm.rw &&
  sRw.mem.isLazyFree p == true && sRw.mem.isAnon p == true &&
  sRwBad.status == .Exception "permission fault" &&
  sRwStr.status == .Running && sRwLdr.status == .Running &&
  sRwLdr.readReg64 .x0 == 0x99#64

/-- info: true -/
#guard_msgs in
#eval checkMadvFreeMprotectPreservation

def checkMadvDontneedOnLazyFree : Bool :=
  let p : BitVec 64 := 0x10000#64
  let mem0 := (Memory.empty.mapZero p 4096).write64 p 0xdeadbeefcafebabe#64
  let sSeed : State := { pc := 0x1000#64, sp := 0x80000#64, physMemAvail := 2 ^ 30, mem := mem0 }
  let sFree := callSyscall sSeed SYS_MADVISE p 4096#64 MADV_FREE
  let sDont := callSyscall sFree SYS_MADVISE p 4096#64 MADV_DONTNEED
  let ldrAt0 : Instr := .ldr .W64 .X64 false .x0 (.Offset .x1 0#64)
  let sLdr := execInst ldrAt0 (sDont.writeReg64 .x1 p)
  sDont.status == .Running &&
  sDont.readReg64 .x0 == 0#64 &&
  sDont.mem.perm p == some Perm.rw &&
  sDont.mem.isAnon p == true &&
  sDont.mem.isLazyFree p == false &&
  sDont.mem.canRead p 8 == true &&
  sLdr.status == .Running &&
  sLdr.readReg64 .x0 == 0#64

/-- info: true -/
#guard_msgs in
#eval checkMadvDontneedOnLazyFree

def checkMadvAnonVsFileBacked : Bool :=
  let textSeg : Snapshot.Region :=
    { start := 0x10000#64, perm := Perm.rx, bytes := List.replicate 4096 0#8, nonAnonLen := 4096 }
  let dataBssSeg : Snapshot.Region :=
    { start := 0x20000#64
      perm := Perm.rw
      bytes := List.replicate 4096 0x42#8 ++ List.replicate 4096 0#8
      nonAnonLen := 4096 }
  let img : Process.ElfImage :=
    { entry := 0x10000#64
      phdrVaddr := 0x10040#64
      phent := 56
      phnum := 2
      segments := [textSeg, dataBssSeg]
      brkStart := 0x22000#64 }
  let stackTop : BitVec 64 := 0x400000#64
  let inputs : Process.ProcessInputs :=
    { argv := [[0x74#8]]
      init := { stackTop := stackTop, stackSize := 4 * 4096, physMemAvail := 2 ^ 30 } }
  match img.loadState inputs with
  | .error _ => false
  | .ok sInit =>
    let dataVa  : BitVec 64 := 0x20000#64
    let bssVa   : BitVec 64 := 0x21000#64
    let stackVa : BitVec 64 := stackTop - 4096#64
    let brkVa   : BitVec 64 := 0x22000#64
    let sDataFree := callSyscall sInit SYS_MADVISE dataVa 4096#64 MADV_FREE
    let sDataDont := callSyscall sInit SYS_MADVISE dataVa 4096#64 MADV_DONTNEED
    let sDataNorm := callSyscall sInit SYS_MADVISE dataVa 4096#64 MADV_NORMAL
    let sBssFree  := callSyscall sInit SYS_MADVISE bssVa 4096#64 MADV_FREE
    let sBssDont  := callSyscall sBssFree SYS_MADVISE bssVa 4096#64 MADV_DONTNEED
    let sStkFree  := callSyscall sInit SYS_MADVISE stackVa 4096#64 MADV_FREE
    let sStkDont  := callSyscall sStkFree SYS_MADVISE stackVa 4096#64 MADV_DONTNEED
    let sBrk      := callSyscall sInit SYS_BRK 0x23000#64
    let sBrkFree  := callSyscall sBrk SYS_MADVISE brkVa 4096#64 MADV_FREE
    let sBrkDont  := callSyscall sBrkFree SYS_MADVISE brkVa 4096#64 MADV_DONTNEED
    let sMm       := callSyscall sInit SYS_MMAP 0#64 4096#64 3#64 0x22#64 (-1#64) 0#64
    let mmVa      := sMm.readReg64 .x0
    let sMmFree   := callSyscall sMm SYS_MADVISE mmVa 4096#64 MADV_FREE
    let sMmDont   := callSyscall sMmFree SYS_MADVISE mmVa 4096#64 MADV_DONTNEED
    sInit.mem.perm dataVa == some Perm.rw &&
    sInit.mem.isLazyFree dataVa == false &&
    sInit.mem.isAnon dataVa == false &&
    sInit.mem.read8 dataVa == 0x42#8 &&
    sDataFree.status == .Exception "madvise on non-anonymous memory" &&
    sDataDont.status == .Exception "madvise on non-anonymous memory" &&
    sDataNorm.status == .Running && sDataNorm.readReg64 .x0 == 0#64 &&
    sInit.mem.perm bssVa == some Perm.rw &&
    sInit.mem.isAnon bssVa == true &&
    sBssFree.status == .Running && sBssFree.readReg64 .x0 == 0#64 &&
    sBssFree.mem.isLazyFree bssVa == true &&
    sBssDont.status == .Running && sBssDont.readReg64 .x0 == 0#64 &&
    sBssDont.mem.isLazyFree bssVa == false &&
    sInit.mem.isAnon stackVa == true &&
    sStkFree.status == .Running && sStkFree.readReg64 .x0 == 0#64 &&
    sStkDont.status == .Running && sStkDont.readReg64 .x0 == 0#64 &&
    sBrk.readReg64 .x0 == 0x23000#64 &&
    sBrk.mem.isAnon brkVa == true &&
    sBrkFree.status == .Running && sBrkFree.readReg64 .x0 == 0#64 &&
    sBrkDont.status == .Running && sBrkDont.readReg64 .x0 == 0#64 &&
    sMm.mem.isAnon mmVa == true &&
    sMmFree.status == .Running && sMmFree.readReg64 .x0 == 0#64 &&
    sMmDont.status == .Running && sMmDont.readReg64 .x0 == 0#64

/-- info: true -/
#guard_msgs in
#eval checkMadvAnonVsFileBacked

end Testing.MadvFree
