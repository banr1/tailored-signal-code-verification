/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process

/-!
# Linux AArch64 Syscall Regression Tests

Kernel-checked conformance and fail-closed `.Exception` regression tests for `execPpoll`,
`execMmap`, `execMremap`, `execRtSigaction`/`execTkill`/`execTgkill`, `FdKind.localDir` VFS
descriptors (`openatPure`, `MAX_LFS_FILESIZE`), and `execSigaltstack`/`MAP_STACK`.
-/

@[expose] public section

namespace Arm64.Testing.Regression.StdSyscalls

open Arm64

set_option maxRecDepth 100000

/-! ## Shared Syscall and Memory Construction Helpers -/

/-- Dispatch a 6-argument Linux AArch64 supervisor call through `execSyscall` (`Syscall.standard`). -/
def callSyscall6 (s : State) (nr x0 x1 x2 x3 x4 x5 : BitVec 64) : State :=
  execSyscall
    (((((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64
      .x3 x3).writeReg64 .x4 x4).writeReg64 .x5 x5)

def isExceptionStatus : ExecStatus → Bool
  | .Exception _ => true
  | _            => false

/-- Serialize one 8-byte `struct pollfd { int fd; short events; short revents; }` in little-endian order. -/
def pollfdBytes (fd : BitVec 32) (events revents : BitVec 16) : List (BitVec 8) :=
  leBytes32 fd ++
    [events.extractLsb' 0 8, events.extractLsb' 8 8,
     revents.extractLsb' 0 8, revents.extractLsb' 8 8]

/-- Serialize a 16-byte `struct __kernel_timespec { int64_t tv_sec; int64_t tv_nsec; }` in little-endian order. -/
def timespecBytes (sec nsec : BitVec 64) : List (BitVec 8) :=
  leBytes64 sec ++ leBytes64 nsec

/-- Build a flat `Memory` directly from non-overlapping `Snapshot.Region`s without nested `write8` closures. -/
def memOfRegions (regions : List Snapshot.Region) : Memory :=
  ⟨Snapshot.cellAt regions⟩

/-- Single mapped `Perm.rw` range `[baseLo, baseHi]` (inclusive) with non-zero byte pattern
    (`0xa5`..`0x5a` on the first 4 KiB page and `0x3c`..`0xc3` above) using primitive `Nat.ble`
    and `cond` so kernel WHNF avoids `BitVec.sub` / `Decidable` overhead per byte. -/
def patternedRwMem (baseLo baseHi : Nat) : Memory :=
  ⟨fun a =>
    let n := a.toNat
    cond (Nat.ble baseLo n && Nat.ble n baseHi)
      (let mask := cond (Nat.ble n (baseLo + PAGE_SIZE - 1)) 0xa5#8 0x3c#8
       some (some Perm.rw, (BitVec.ofNat 8 (n % 256)) ^^^ mask))
      none⟩

/-! ## `ppoll` (`SYS_PPOLL = 73`) -/

/-- Standard stream descriptor entry (`FdKind.stdio`). -/
def stdioDesc (mode : FdAccessMode) : FdEntry :=
  { path := "", accMode := mode, kind := .stdio }

/-- Positive `ppoll` conformance: open descriptors `0, 1, 2` (with `sigsetsize = 8` and `0`),
    closed descriptor `1` (`POLLNVAL`), all three closed (`3`), and `nfds = 0`. -/
def checkPpollValidProbes : Bool :=
  let ufds := 0x20000#64
  let tsp  := 0x20040#64
  -- Pre-populate `revents` with non-zero sentinels (`0x7fff`) to verify `execPpoll` overwrites them.
  let mem0 := memOfRegions
    [{ start := ufds
       perm := .rw
       bytes := pollfdBytes 0#32 0#16 0x7fff#16 ++
                pollfdBytes 1#32 0#16 0x7fff#16 ++
                pollfdBytes 2#32 0#16 0x7fff#16 },
     { start := tsp, perm := .rw, bytes := timespecBytes 0#64 0#64 }]
  let fsAllOpen := (({} : FsState).setFd 0#64 (some (stdioDesc .rdonly)))
    |>.setFd 1#64 (some (stdioDesc .wronly))
    |>.setFd 2#64 (some (stdioDesc .wronly))
  let fsFd1Closed := fsAllOpen.setFd 1#64 none
  let fsAllClosed : FsState := {}
  let sBase : State := { pc := 0x1000#64, mem := mem0, fs := fsAllOpen }
  let sOpen8   := callSyscall6 sBase SYS_PPOLL ufds 3#64 tsp 0#64 8#64 0#64
  let sOpen0   := callSyscall6 sBase SYS_PPOLL ufds 3#64 tsp 0#64 0#64 0#64
  let sBundle  := Syscall.poll
    ((((((sBase.writeReg64 .x8 SYS_PPOLL).writeReg64 .x0 ufds).writeReg64 .x1 3#64).writeReg64
      .x2 tsp).writeReg64 .x3 0#64).writeReg64 .x4 8#64)
  let sClosed1 := callSyscall6 { sBase with fs := fsFd1Closed } SYS_PPOLL ufds 3#64 tsp 0#64 8#64 0#64
  let sClosed3 := callSyscall6 { sBase with fs := fsAllClosed } SYS_PPOLL ufds 3#64 tsp 0#64 8#64 0#64
  let sZeroN   := callSyscall6 sBase SYS_PPOLL 0#64 0#64 tsp 0#64 8#64 0#64
  POLLNVAL == 0x0020#16 &&
  sOpen8.status == .Running && sOpen8.pc == 0x1004#64 && sOpen8.readReg64 .x0 == 0#64 &&
  sOpen8.mem.read16 (ufds + 6#64) == 0#16 &&
  sOpen8.mem.read16 (ufds + 14#64) == 0#16 &&
  sOpen8.mem.read16 (ufds + 22#64) == 0#16 &&
  sOpen0.status == .Running && sOpen0.pc == 0x1004#64 && sOpen0.readReg64 .x0 == 0#64 &&
  sOpen0.mem.read16 (ufds + 6#64) == 0#16 &&
  sOpen0.mem.read16 (ufds + 14#64) == 0#16 &&
  sOpen0.mem.read16 (ufds + 22#64) == 0#16 &&
  sBundle.status == .Running && sBundle.pc == 0x1004#64 && sBundle.readReg64 .x0 == 0#64 &&
  sClosed1.status == .Running && sClosed1.pc == 0x1004#64 && sClosed1.readReg64 .x0 == 1#64 &&
  sClosed1.mem.read16 (ufds + 6#64) == 0#16 &&
  sClosed1.mem.read16 (ufds + 14#64) == POLLNVAL &&
  sClosed1.mem.read16 (ufds + 22#64) == 0#16 &&
  sClosed3.status == .Running && sClosed3.pc == 0x1004#64 && sClosed3.readReg64 .x0 == 3#64 &&
  sClosed3.mem.read16 (ufds + 6#64) == POLLNVAL &&
  sClosed3.mem.read16 (ufds + 14#64) == POLLNVAL &&
  sClosed3.mem.read16 (ufds + 22#64) == POLLNVAL &&
  sZeroN.status == .Running && sZeroN.pc == 0x1004#64 && sZeroN.readReg64 .x0 == 0#64

theorem ppoll_valid_probes_ok : checkPpollValidProbes = true := by
  decide +kernel

/-- Negative errno and fail-closed `.Exception` checks for `ppoll`. -/
def checkPpollErrorsAndTraps : Bool :=
  let ufds := 0x20000#64
  let tsp  := 0x20040#64
  let fsOpen := ({} : FsState).setFd 0#64 (some (stdioDesc .rdonly))
  let fsCustom := ({} : FsState).setFd 0#64
    (some { path := "", accMode := .rdwr, kind := .custom 0 })
  let mkState (fd : BitVec 32) (ev : BitVec 16) (uPerm : Perm)
      (sec nsec : BitVec 64) (fs : FsState := fsOpen) : State :=
    { pc := 0x1000#64
      fs := fs
      mem := memOfRegions
        [{ start := ufds, perm := uPerm, bytes := pollfdBytes fd ev 0#16 },
         { start := tsp,  perm := .rw,   bytes := timespecBytes sec nsec }] }
  let sValid := mkState 0#32 0#16 .rw 0#64 0#64
  let sNfdsBig  := callSyscall6 sValid SYS_PPOLL ufds 1025#64 tsp 0#64 8#64 0#64
  let sBadTsp   := callSyscall6 sValid SYS_PPOLL ufds 1#64 0x90000#64 0#64 8#64 0#64
  let sNegSec   := callSyscall6 (mkState 0#32 0#16 .rw (-1#64) 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sNegNsec  := callSyscall6 (mkState 0#32 0#16 .rw 0#64 (-1#64)) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sBigNsec  := callSyscall6 (mkState 0#32 0#16 .rw 0#64 1000000000#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sBadSigSz := callSyscall6 sValid SYS_PPOLL ufds 1#64 tsp 0x20000#64 16#64 0#64
  let sBadUfds  := callSyscall6 sValid SYS_PPOLL 0x90000#64 1#64 tsp 0#64 8#64 0#64
  let sRoUfds   := callSyscall6 (mkState 0#32 0#16 .ro 0#64 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sNullTsp   := callSyscall6 sValid SYS_PPOLL ufds 1#64 0#64 0#64 8#64 0#64
  let sPosSec    := callSyscall6 (mkState 0#32 0#16 .rw 1#64 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sPosNsec   := callSyscall6 (mkState 0#32 0#16 .rw 0#64 1#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sNonNullSm := callSyscall6 sValid SYS_PPOLL ufds 1#64 tsp 0x20000#64 8#64 0#64
  let sFd3       := callSyscall6 (mkState 3#32 0#16 .rw 0#64 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sFdNeg1    := callSyscall6 (mkState (-1#32) 0#16 .rw 0#64 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sEventsNz  := callSyscall6 (mkState 0#32 1#16 .rw 0#64 0#64) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  let sCustomFd  := callSyscall6 (mkState 0#32 0#16 .rw 0#64 0#64 fsCustom) SYS_PPOLL ufds 1#64 tsp 0#64 8#64 0#64
  sNfdsBig.status == .Running && sNfdsBig.pc == 0x1004#64 && sNfdsBig.readReg64 .x0 == -EINVAL &&
  sBadTsp.status == .Running && sBadTsp.pc == 0x1004#64 && sBadTsp.readReg64 .x0 == EFAULT_RET &&
  sNegSec.status == .Running && sNegSec.pc == 0x1004#64 && sNegSec.readReg64 .x0 == -EINVAL &&
  sNegNsec.status == .Running && sNegNsec.pc == 0x1004#64 && sNegNsec.readReg64 .x0 == -EINVAL &&
  sBigNsec.status == .Running && sBigNsec.pc == 0x1004#64 && sBigNsec.readReg64 .x0 == -EINVAL &&
  sBadSigSz.status == .Running && sBadSigSz.pc == 0x1004#64 && sBadSigSz.readReg64 .x0 == -EINVAL &&
  sBadUfds.status == .Running && sBadUfds.pc == 0x1004#64 && sBadUfds.readReg64 .x0 == EFAULT_RET &&
  sRoUfds.status == .Running && sRoUfds.pc == 0x1004#64 && sRoUfds.readReg64 .x0 == EFAULT_RET &&
  isExceptionStatus sNullTsp.status &&
  isExceptionStatus sPosSec.status &&
  isExceptionStatus sPosNsec.status &&
  isExceptionStatus sNonNullSm.status &&
  isExceptionStatus sFd3.status &&
  isExceptionStatus sFdNeg1.status &&
  isExceptionStatus sEventsNz.status &&
  isExceptionStatus sCustomFd.status

theorem ppoll_errors_and_traps_ok : checkPpollErrorsAndTraps = true := by
  decide +kernel

/-! ## Sanitized `mmap` (`SYS_MMAP = 222`) -/

/-- Invoke anonymous private `PROT_READ | PROT_WRITE` `mmap(0, len, 3, 0x22, -1, 0)`. -/
def callAnonRwMmap (s : State) (len : BitVec 64) : State :=
  callSyscall6 s SYS_MMAP 0#64 len MMAP_PROT_RW MMAP_FLAGS_PRIVATE_ANON (-1#64) 0#64

/-- Valid `oracle.mmap` placement, `Process.defaultOracle` 256 KiB overlap fallback to `0x10000`,
    sanitization of `0` / misaligned / `>= 2^48` candidates (and sequential advance to `0x11000`),
    and `.OutOfMemory` on VA-space exhaustion (`len = 2^48`) or `physMemAvail` exhaustion. -/
def checkSanitizedMmap : Bool :=
  let sDefault0 : State :=
    { pc := 0x1000#64, physMemAvail := 0x10000, oracle := Process.defaultOracle, oracleIdx := 0 }
  let sDirect := callAnonRwMmap sDefault0 0x1000#64
  -- 256 KiB (`0x40000`) mapped at `0x600000000000` (`oracleIdx = 0`), then 4 KiB (`0x1000`) at
  -- `oracleIdx = 1` (`defaultOracle.mmap 1 = 0x600000010000`, inside `[0x600000000000, +0x40000)`):
  -- falls back to `0x10000` (`MMAP_MIN_ADDR`).
  let s256k : State :=
    { pc := 0x1004#64
      mem := Memory.empty.mapZero 0x600000000000#64 0x40000
      physMemAvail := 0x10000
      oracle := Process.defaultOracle
      oracleIdx := 1 }
  let sColl := callAnonRwMmap s256k 0x1000#64
  let sZero1 := callAnonRwMmap
    { pc := 0x1000#64, physMemAvail := 0x10000, oracle := { mmap := fun _ => 0#64 } } 0x1000#64
  let sZero2 := callAnonRwMmap sZero1 0x1000#64
  let sMisal := callAnonRwMmap
    { pc := 0x1000#64, physMemAvail := 0x10000, oracle := { mmap := fun _ => 0x10001#64 } } 0x1000#64
  let sPastVa := callAnonRwMmap
    { pc := 0x1000#64, physMemAvail := 0x10000, oracle := { mmap := fun _ => 0x0001000000000000#64 } } 0x1000#64
  let sOom := callAnonRwMmap sDefault0 0x0001000000000000#64
  BitVec.ofNat 64 MMAP_MIN_ADDR == 0x10000#64 &&
  Process.defaultOracle.mmap 0 == 0x600000000000#64 &&
  Process.defaultOracle.mmap 1 == 0x600000010000#64 &&
  sDirect.status == .Running && sDirect.pc == 0x1004#64 && sDirect.oracleIdx == 1 &&
  sDirect.readReg64 .x0 == 0x600000000000#64 &&
  sDirect.mem.perm 0x600000000000#64 == some Perm.rw &&
  sDirect.mem.perm 0x600000000fff#64 == some Perm.rw &&
  sDirect.mem.perm 0x600000001000#64 == none &&
  sDirect.mem.read64 0x600000000000#64 == 0#64 &&
  sColl.status == .Running && sColl.pc == 0x1008#64 && sColl.oracleIdx == 2 &&
  sColl.readReg64 .x0 == 0x10000#64 &&
  sColl.mem.perm 0x10000#64 == some Perm.rw &&
  sColl.mem.perm 0x10fff#64 == some Perm.rw &&
  sColl.mem.perm 0x11000#64 == none &&
  sColl.mem.perm 0x600000000000#64 == some Perm.rw &&
  sColl.mem.perm 0x600000010000#64 == some Perm.rw &&
  sColl.mem.perm 0x60000003ffff#64 == some Perm.rw &&
  sColl.mem.perm 0x600000040000#64 == none &&
  sColl.mem.read64 0x10000#64 == 0#64 &&
  sColl.mem.read64 0x10ff8#64 == 0#64 &&
  sZero1.status == .Running && sZero1.oracleIdx == 1 && sZero1.readReg64 .x0 == 0x10000#64 &&
  sZero2.status == .Running && sZero2.oracleIdx == 2 && sZero2.readReg64 .x0 == 0x11000#64 &&
  sZero2.mem.perm 0x11000#64 == some Perm.rw &&
  sZero2.mem.perm 0x11fff#64 == some Perm.rw &&
  sZero2.mem.read64 0x11000#64 == 0#64 &&
  sMisal.status == .Running && sMisal.oracleIdx == 1 && sMisal.readReg64 .x0 == 0x10000#64 &&
  sPastVa.status == .Running && sPastVa.oracleIdx == 1 && sPastVa.readReg64 .x0 == 0x10000#64 &&
  sOom.status == .OutOfMemory

theorem sanitized_mmap_ok : checkSanitizedMmap = true := by
  decide +kernel

/-! ## `mremap` (`SYS_MREMAP = 216`) -/

/-- Invoke `mremap(oldAddr, oldLen, newLen, flags)` via `execSyscall`. -/
def callMremap (s : State) (oldAddr oldLen newLen flags : BitVec 64) : State :=
  callSyscall6 s SYS_MREMAP oldAddr oldLen newLen flags 0#64 0#64

/-- Relocating growth (`MREMAP_MAYMOVE`, 4 KiB -> 8 KiB) to a valid oracle address and to a
    sanitized fallback address (`0x10000`) when `oracle.mmap = 0`. -/
def checkMremapRelocateGrowth : Bool :=
  let oldAddr := 0x20000#64
  let mem4k := patternedRwMem 0x20000 0x20fff
  let sReloc := callMremap
    { pc := 0x1000#64, mem := mem4k, physMemAvail := 0x1000, oracle := { mmap := fun _ => 0x600000000000#64 } }
    oldAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sSan := callMremap
    { pc := 0x1000#64, mem := mem4k, physMemAvail := 0x1000, oracle := { mmap := fun _ => 0#64 } }
    oldAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  sReloc.status == .Running && sReloc.pc == 0x1004#64 && sReloc.oracleIdx == 1 &&
  sReloc.readReg64 .x0 == 0x600000000000#64 &&
  sReloc.mem.read8 0x600000000000#64 == 0xa5#8 &&
  sReloc.mem.read8 0x600000000fff#64 == 0x5a#8 &&
  sReloc.mem.read64 0x600000001000#64 == 0#64 &&
  sReloc.mem.read64 0x600000001ff8#64 == 0#64 &&
  sReloc.mem.perm 0x600000000000#64 == some Perm.rw &&
  sReloc.mem.perm 0x600000001fff#64 == some Perm.rw &&
  sReloc.mem.perm oldAddr == none &&
  sReloc.mem.perm (oldAddr + 0xfff#64) == none &&
  sSan.status == .Running && sSan.pc == 0x1004#64 && sSan.oracleIdx == 1 &&
  sSan.readReg64 .x0 == 0x10000#64 &&
  sSan.mem.read8 0x10000#64 == 0xa5#8 &&
  sSan.mem.read8 0x10fff#64 == 0x5a#8 &&
  sSan.mem.read64 0x11000#64 == 0#64 &&
  sSan.mem.read64 0x11ff8#64 == 0#64 &&
  sSan.mem.perm 0x10000#64 == some Perm.rw &&
  sSan.mem.perm 0x11fff#64 == some Perm.rw &&
  sSan.mem.perm oldAddr == none &&
  sSan.mem.perm (oldAddr + 0xfff#64) == none

theorem mremap_relocate_growth_ok : checkMremapRelocateGrowth = true := by
  decide +kernel

/-- In-place growth (`4 KiB -> 8 KiB`), in-place shrink (`8 KiB -> 4 KiB`), `mremapFail` refusal,
    and VA-exhaustion (`newLen = 2^48`) `-ENOMEM` refusal preserving the original mapping. -/
def checkMremapInPlaceAndRefusal : Bool :=
  let oldAddr := 0x20000#64
  let mem4k := patternedRwMem 0x20000 0x20fff
  let mem8k := patternedRwMem 0x20000 0x21fff
  let sGrowInPlace := callMremap
    { pc := 0x1000#64, mem := mem4k, physMemAvail := 0x1000, oracle := { mmap := fun _ => oldAddr } }
    oldAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sShrinkInPlace := callMremap
    { pc := 0x1000#64, mem := mem8k, oracle := { mmap := fun _ => oldAddr } }
    oldAddr 0x2000#64 0x1000#64 MREMAP_MAYMOVE
  let sRefuse := callMremap
    { pc := 0x1000#64
      mem := mem4k
      oracle := { mmap := fun _ => 0x600000000000#64, mremapFail := fun _ => true } }
    oldAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sVaFull := callMremap
    { pc := 0x1000#64, mem := mem4k, oracle := { mmap := fun _ => 0x600000000000#64 } }
    oldAddr 0x1000#64 0x0001000000000000#64 MREMAP_MAYMOVE
  (-ENOMEM) == (-12#64) &&
  sGrowInPlace.status == .Running && sGrowInPlace.pc == 0x1004#64 && sGrowInPlace.oracleIdx == 1 &&
  sGrowInPlace.readReg64 .x0 == oldAddr &&
  sGrowInPlace.mem.read8 oldAddr == 0xa5#8 &&
  sGrowInPlace.mem.read8 (oldAddr + 0xfff#64) == 0x5a#8 &&
  sGrowInPlace.mem.read64 (oldAddr + 0x1000#64) == 0#64 &&
  sGrowInPlace.mem.read64 (oldAddr + 0x1ff8#64) == 0#64 &&
  sGrowInPlace.mem.perm (oldAddr + 0x1000#64) == some Perm.rw &&
  sGrowInPlace.mem.perm (oldAddr + 0x1fff#64) == some Perm.rw &&
  sShrinkInPlace.status == .Running && sShrinkInPlace.pc == 0x1004#64 &&
  sShrinkInPlace.oracleIdx == 1 && sShrinkInPlace.readReg64 .x0 == oldAddr &&
  sShrinkInPlace.mem.read8 oldAddr == 0xa5#8 &&
  sShrinkInPlace.mem.read8 (oldAddr + 0xfff#64) == 0x5a#8 &&
  sShrinkInPlace.mem.perm oldAddr == some Perm.rw &&
  sShrinkInPlace.mem.perm (oldAddr + 0xfff#64) == some Perm.rw &&
  sShrinkInPlace.mem.perm (oldAddr + 0x1000#64) == none &&
  sShrinkInPlace.mem.perm (oldAddr + 0x1fff#64) == none &&
  sRefuse.status == .Running && sRefuse.pc == 0x1004#64 && sRefuse.oracleIdx == 1 &&
  sRefuse.readReg64 .x0 == -ENOMEM &&
  sRefuse.mem.read8 oldAddr == 0xa5#8 &&
  sRefuse.mem.read8 (oldAddr + 0xfff#64) == 0x5a#8 &&
  sRefuse.mem.perm oldAddr == some Perm.rw &&
  sRefuse.mem.perm (oldAddr + 0xfff#64) == some Perm.rw &&
  sRefuse.mem.perm 0x600000000000#64 == none &&
  sVaFull.status == .Running && sVaFull.pc == 0x1004#64 && sVaFull.oracleIdx == 1 &&
  sVaFull.readReg64 .x0 == -ENOMEM &&
  sVaFull.mem.read8 oldAddr == 0xa5#8 &&
  sVaFull.mem.read8 (oldAddr + 0xfff#64) == 0x5a#8 &&
  sVaFull.mem.perm oldAddr == some Perm.rw &&
  sVaFull.mem.perm (oldAddr + 0xfff#64) == some Perm.rw

theorem mremap_inplace_and_refusal_ok : checkMremapInPlaceAndRefusal = true := by
  decide +kernel

/-- Errno validation and fail-closed `.Exception` checks for `mremap`. -/
def checkMremapErrorsAndTraps : Bool :=
  let rwAddr   := 0x20000#64
  let roAddr   := 0x30000#64
  let rxAddr   := 0x31000#64
  let noneAddr := 0x32000#64
  let mkPage (lo hi : Nat) (p : Perm) : State :=
    { pc := 0x1000#64
      mem := ⟨fun a =>
        let n := a.toNat
        cond (Nat.ble lo n && Nat.ble n hi) (some (some p, 0#8)) none⟩ }
  let sRw      := mkPage 0x20000 0x20fff .rw
  let sEmpty   : State := { pc := 0x1000#64, mem := Memory.empty }
  let sPartMem := mkPage 0x20000 0x20000 .rw
  let sMisal    := callMremap sRw 0x20001#64 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sNewZero  := callMremap sRw rwAddr 0x1000#64 0#64 MREMAP_MAYMOVE
  let sNewOvfl  := callMremap sRw rwAddr 0x1000#64 0xfffffffffffff001#64 MREMAP_MAYMOVE
  let sOldPast  := callMremap sRw 0x0000fffffffff000#64 0x2000#64 0x3000#64 MREMAP_MAYMOVE
  let sUnmapped := callMremap sEmpty 0x50000#64 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sFlags0   := callMremap sRw rwAddr 0x1000#64 0x2000#64 0#64
  let sFlags3   := callMremap sRw rwAddr 0x1000#64 0x2000#64 3#64
  let sOldZero  := callMremap sRw rwAddr 0#64 0x1000#64 MREMAP_MAYMOVE
  let sFrozenRo := callMremap (mkPage 0x30000 0x30fff .ro) roAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sFrozenRx := callMremap (mkPage 0x31000 0x31fff .rx) rxAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sProtNone := callMremap (mkPage 0x32000 0x32fff .protNone) noneAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  let sPartial  := callMremap sPartMem rwAddr 0x1000#64 0x2000#64 MREMAP_MAYMOVE
  sMisal.status == .Running && sMisal.pc == 0x1004#64 && sMisal.oracleIdx == 0 &&
  sMisal.readReg64 .x0 == -EINVAL &&
  sNewZero.status == .Running && sNewZero.pc == 0x1004#64 && sNewZero.oracleIdx == 0 &&
  sNewZero.readReg64 .x0 == -EINVAL &&
  sNewOvfl.status == .Running && sNewOvfl.pc == 0x1004#64 && sNewOvfl.oracleIdx == 0 &&
  sNewOvfl.readReg64 .x0 == -EINVAL &&
  sOldPast.status == .Running && sOldPast.pc == 0x1004#64 && sOldPast.oracleIdx == 0 &&
  sOldPast.readReg64 .x0 == -EINVAL &&
  sUnmapped.status == .Running && sUnmapped.pc == 0x1004#64 && sUnmapped.oracleIdx == 0 &&
  sUnmapped.readReg64 .x0 == EFAULT_RET &&
  isExceptionStatus sFlags0.status &&
  isExceptionStatus sFlags3.status &&
  isExceptionStatus sOldZero.status &&
  isExceptionStatus sFrozenRo.status &&
  isExceptionStatus sFrozenRx.status &&
  isExceptionStatus sProtNone.status &&
  isExceptionStatus sPartial.status

theorem mremap_errors_and_traps_ok : checkMremapErrorsAndTraps = true := by
  decide +kernel

/-! ## Per-Signal `rt_sigaction` (`134`), `tkill` (`130`), and `tgkill` (`131`) -/

/-- Invoke `rt_sigaction(signum, act, oldact, sigsetsize)` via `execSyscall`. -/
def callRtSigaction (s : State) (signum act oldact sigsetsize : BitVec 64) : State :=
  callSyscall6 s SYS_RT_SIGACTION signum act oldact sigsetsize 0#64 0#64

/-- Per-signal `rt_sigaction` installation, `UAPI_SA_FLAGS` and `SIG_UNBLOCKABLE_MASK` stripping, non-aliasing,
    `SIGKILL`/`SIGSTOP` semantics, validation errors/traps, and `SIGABRT` `tkill`/`tgkill`
    disposition interaction. -/
def checkRtSigactionAndTkill : Bool :=
  let actIgn  := 0x40000#64
  let actDfl  := 0x40020#64
  let actCust := 0x40040#64
  let oldBuf1 := 0x40060#64
  let oldBuf2 := 0x40080#64
  let oldBuf3 := 0x400a0#64
  let oldRo   := 0x41000#64
  let mem0 := memOfRegions
    [{ start := actIgn
       perm := .rw
       bytes := SigAction.toBytes
         { handler := SIG_IGN, flags := 0xffffffffffffffff#64, restorer := 0x400800#64, mask := 0xffffffffffffffff#64 } },
     { start := actDfl,  perm := .rw, bytes := SigAction.toBytes {} },
     { start := actCust, perm := .rw, bytes := SigAction.toBytes { handler := 0x400500#64 } },
     -- Non-zero initial bytes in `oldBuf1` so overwriting with 32 zero bytes (`SIG_DFL`) is verified.
     { start := oldBuf1, perm := .rw, bytes := List.replicate 32 0xff#8 },
     { start := oldBuf2, perm := .rw, bytes := List.replicate 32 0#8 },
     { start := oldBuf3, perm := .rw, bytes := List.replicate 32 0xff#8 },
     { start := oldRo,   perm := .ro, bytes := List.replicate 32 0#8 }]
  let s0 : State := { pc := 0x1000#64, mem := mem0 }
  let sPipeIgn   := callRtSigaction s0 13#64 actIgn oldBuf1 8#64
  let sPipeQuery := callRtSigaction sPipeIgn 13#64 0#64 oldBuf2 8#64
  let sIntQuery  := callRtSigaction sPipeIgn 2#64 0#64 oldBuf3 8#64
  let sKillSet   := callRtSigaction s0 9#64  actIgn 0#64    8#64
  let sStopSet   := callRtSigaction s0 19#64 actIgn 0#64    8#64
  let sKillQuery := callRtSigaction s0 9#64  0#64   oldBuf2 8#64
  let sStopQuery := callRtSigaction s0 19#64 0#64   oldBuf2 8#64
  let sSig0      := callRtSigaction s0 0#64      actIgn     0#64      8#64
  let sSigNeg1   := callRtSigaction s0 (-1#64)   actIgn     0#64      8#64
  let sSig65     := callRtSigaction s0 65#64     actIgn     0#64      8#64
  let sBadSetSz  := callRtSigaction s0 13#64     actIgn     0#64      16#64
  let sBadAct    := callRtSigaction s0 13#64     0x90000#64 0#64      8#64
  let sBadOldUnm := callRtSigaction s0 13#64     0#64       0x90000#64 8#64
  let sBadOldRo  := callRtSigaction s0 13#64     actIgn     oldRo     8#64
  let sCustomH   := callRtSigaction s0 13#64     actCust    0#64      8#64
  let sCustomAbrt := callRtSigaction s0 6#64     actCust    0#64      8#64
  -- Custom `sa_handler` is accepted only for `SIGSEGV` (`11`) and `SIGBUS` (`7`);
  -- `tkill`/`tgkill` on `SIGSEGV`/`SIGBUS` still fail closed at `.Exception`.
  let sSegvSet   := callRtSigaction s0 11#64     actCust    oldBuf1   8#64
  let sSegvQuery := callRtSigaction sSegvSet 11#64 0#64     oldBuf2   8#64
  let sBusSet    := callRtSigaction sSegvSet 7#64  actCust  0#64      8#64
  let sTkillSegv := callSyscall6 sSegvSet SYS_TKILL  1#64 11#64 0#64 0#64 0#64 0#64
  let sTgkillBus := callSyscall6 sBusSet  SYS_TGKILL 1#64 1#64  7#64 0#64 0#64 0#64
  let sAbrtIgn    := callRtSigaction s0 6#64 actIgn 0#64 8#64
  let sTkillIgn   := callSyscall6 sAbrtIgn  SYS_TKILL  1#64 6#64 0#64 0#64 0#64 0#64
  let sTgkillIgn  := callSyscall6 sTkillIgn SYS_TGKILL 1#64 1#64 6#64 0#64 0#64 0#64
  let sAbrtDfl    := callRtSigaction sTgkillIgn 6#64 actDfl oldBuf2 8#64
  let sTkillTerm  := callSyscall6 sAbrtDfl SYS_TKILL  1#64 6#64 0#64 0#64 0#64 0#64
  let sTgkillTerm := callSyscall6 sAbrtDfl SYS_TGKILL 1#64 1#64 6#64 0#64 0#64 0#64
  sPipeIgn.status == .Running && sPipeIgn.pc == 0x1004#64 && sPipeIgn.readReg64 .x0 == 0#64 &&
  sPipeIgn.mem.readBytes oldBuf1 32 == List.replicate 32 0#8 &&
  sPipeQuery.status == .Running && sPipeQuery.pc == 0x1008#64 && sPipeQuery.readReg64 .x0 == 0#64 &&
  sPipeQuery.mem.read64 (oldBuf2 + 0#64)  == 1#64 &&
  -- `sa_flags &= UAPI_SA_FLAGS` (arm64: `0xdc000807`, `kernel/signal.c:4401-4404`)
  sPipeQuery.mem.read64 (oldBuf2 + 8#64)  == 0xdc000807#64 &&
  sPipeQuery.mem.read64 (oldBuf2 + 16#64) == 0x400800#64 &&
  sPipeQuery.mem.read64 (oldBuf2 + 24#64) == 0xfffffffffffbfeff#64 &&
  sIntQuery.status == .Running && sIntQuery.readReg64 .x0 == 0#64 &&
  sIntQuery.mem.readBytes oldBuf3 32 == List.replicate 32 0#8 &&
  (sIntQuery.getSigAction 13#32).handler == SIG_IGN &&
  (sIntQuery.getSigAction 2#32).handler == SIG_DFL &&
  sKillSet.status == .Running && sKillSet.readReg64 .x0 == -EINVAL &&
  sStopSet.status == .Running && sStopSet.readReg64 .x0 == -EINVAL &&
  sKillQuery.status == .Running && sKillQuery.readReg64 .x0 == 0#64 &&
  sStopQuery.status == .Running && sStopQuery.readReg64 .x0 == 0#64 &&
  sSig0.status == .Running && sSig0.readReg64 .x0 == -EINVAL &&
  sSigNeg1.status == .Running && sSigNeg1.readReg64 .x0 == -EINVAL &&
  sSig65.status == .Running && sSig65.readReg64 .x0 == -EINVAL &&
  sBadSetSz.status == .Running && sBadSetSz.readReg64 .x0 == -EINVAL &&
  sBadAct.status == .Running && sBadAct.readReg64 .x0 == EFAULT_RET &&
  sBadOldUnm.status == .Running && sBadOldUnm.readReg64 .x0 == EFAULT_RET &&
  sBadOldRo.status == .Running && sBadOldRo.readReg64 .x0 == EFAULT_RET &&
  isExceptionStatus sCustomH.status &&
  isExceptionStatus sCustomAbrt.status &&
  sSegvSet.status == .Running && sSegvSet.readReg64 .x0 == 0#64 &&
  sSegvSet.mem.readBytes oldBuf1 32 == List.replicate 32 0#8 &&
  (sSegvSet.getSigAction 11#32).handler == 0x400500#64 &&
  sSegvQuery.status == .Running && sSegvQuery.readReg64 .x0 == 0#64 &&
  sSegvQuery.mem.read64 oldBuf2 == 0x400500#64 &&
  sBusSet.status == .Running && sBusSet.readReg64 .x0 == 0#64 &&
  (sBusSet.getSigAction 7#32).handler == 0x400500#64 &&
  isExceptionStatus sTkillSegv.status &&
  isExceptionStatus sTgkillBus.status &&
  sAbrtIgn.status == .Running && sAbrtIgn.readReg64 .x0 == 0#64 &&
  sTkillIgn.status == .Running && sTkillIgn.pc == 0x1008#64 && sTkillIgn.readReg64 .x0 == 0#64 &&
  sTgkillIgn.status == .Running && sTgkillIgn.pc == 0x100c#64 && sTgkillIgn.readReg64 .x0 == 0#64 &&
  sAbrtDfl.status == .Running && sAbrtDfl.readReg64 .x0 == 0#64 &&
  sAbrtDfl.mem.read64 oldBuf2 == SIG_IGN &&
  sTkillTerm.status == .Signaled 6#7 &&
  sTgkillTerm.status == .Signaled 6#7

theorem rt_sigaction_and_tkill_ok : checkRtSigactionAndTkill = true := by
  decide +kernel

/-! ## VFS Directory Descriptors (`FdKind.localDir`), `openatPure`, and `MAX_LFS_FILESIZE` -/

/-- Directory descriptor (`FdKind.localDir`) lifecycle (`openat` `O_RDONLY` / `O_DIRECTORY`, `fstat`,
    `fcntl` `F_GETFD`/`F_SETFD` vs unsupported `cmd` -> `.Exception`, `read` -> `-EISDIR`,
    `write` -> `-EBADF`, `pread64`/`lseek` -> `.Exception`, `close` -> `0`),
    `checkOpenFlags`-before-`readCString` ordering, `openatPure` / `applyOpenVerdict` agreement,
    and `MAX_LFS_FILESIZE` (`2^63 - 1`) `-EINVAL` (`rw_verify_area`) enforcement on `write`. -/
def checkVfsLocalDirOpenatPureAndLfs : Bool :=
  let pathSubAddr := 0x50000#64
  let pathDotAddr := 0x50020#64
  let rwBufAddr   := 0x50040#64
  let statBufAddr := 0x50100#64
  let unmappedPtr := 0x90000#64
  let mem0 := memOfRegions
    [{ start := pathSubAddr, perm := .rw, bytes := [0x73#8, 0x75#8, 0x62#8, 0x00#8] },
     { start := pathDotAddr, perm := .rw, bytes := [0x2e#8, 0x00#8] },
     { start := rwBufAddr,   perm := .rw, bytes := List.replicate 16 0x41#8 },
     { start := statBufAddr, perm := .rw, bytes := List.replicate 128 0xff#8 }]
  let fs0 := (({} : FsState).setEntry ["sub"] (some .dir))
    |>.setFile "big.bin" (some (.file [0x11#8]))
    |>.setFd 0#64 (some (stdioDesc .rdonly))
    |>.setFd 1#64 (some (stdioDesc .wronly))
    |>.setFd 2#64 (some (stdioDesc .wronly))
  let s0 : State := { pc := 0x1000#64, mem := mem0, fs := fs0 }
  let atFdcwd64 : BitVec 64 := 0xffffffffffffff9c#64
  let flagsDirCloexec : BitVec 64 := (O_DIRECTORY_W32 ||| O_CLOEXEC_W32).zeroExtend 64
  let sOpenSub := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr flagsDirCloexec 0#64 0#64 0#64
  let sOpenDot := callSyscall6 sOpenSub SYS_OPENAT atFdcwd64 pathDotAddr 0#64 0#64 0#64 0#64
  let sOpenDirWr    := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr 1#64 0#64 0#64 0#64
  let sOpenDirRdwr  := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr 2#64 0#64 0#64 0#64
  let sOpenDirCreat := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr (O_CREAT_W32.zeroExtend 64) 0#64 0#64 0#64
  let sOpenDirTrunc := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr (O_TRUNC_W32.zeroExtend 64) 0#64 0#64 0#64
  let sOpenDirExcl  := callSyscall6 s0 SYS_OPENAT atFdcwd64 pathSubAddr
    ((O_CREAT_W32 ||| O_EXCL_W32).zeroExtend 64) 0#64 0#64 0#64
  let sFstatDir      := callSyscall6 sOpenSub SYS_FSTAT   3#64 statBufAddr 0#64 0#64 0#64 0#64
  let sFcntlSubGet0  := callSyscall6 sOpenSub SYS_FCNTL   3#64 1#64        0#64 0#64 0#64 0#64
  let sFcntlSubSet0  := callSyscall6 sOpenSub SYS_FCNTL   3#64 2#64        0#64 0#64 0#64 0#64
  let sFcntlSubGet1  := callSyscall6 sFcntlSubSet0 SYS_FCNTL 3#64 1#64     0#64 0#64 0#64 0#64
  let sFcntlDotGet0  := callSyscall6 sOpenDot SYS_FCNTL   4#64 1#64        0#64 0#64 0#64 0#64
  let sFcntlDotSet1  := callSyscall6 sOpenDot SYS_FCNTL   4#64 2#64        1#64 0#64 0#64 0#64
  let sFcntlDotGet1  := callSyscall6 sFcntlDotSet1 SYS_FCNTL 4#64 1#64     0#64 0#64 0#64 0#64
  let sFcntlDirDupfd := callSyscall6 sOpenSub SYS_FCNTL   3#64 0#64        0#64 0#64 0#64 0#64
  let sFcntlDirGetfl := callSyscall6 sOpenSub SYS_FCNTL   3#64 3#64        0#64 0#64 0#64 0#64
  let sReadDir       := callSyscall6 sOpenSub SYS_READ    3#64 rwBufAddr   4#64 0#64 0#64 0#64
  let sReadDirUnm    := callSyscall6 sOpenSub SYS_READ    3#64 unmappedPtr 4#64 0#64 0#64 0#64
  let sReadDir0      := callSyscall6 sOpenSub SYS_READ    3#64 unmappedPtr 0#64 0#64 0#64 0#64
  let sReadDirEfault := callSyscall6 sOpenSub SYS_READ    3#64 rwBufAddr   0x8000000000000000#64 0#64 0#64 0#64
  let sWriteDir      := callSyscall6 sOpenSub SYS_WRITE   3#64 rwBufAddr   4#64 0#64 0#64 0#64
  let sPreadDir      := callSyscall6 sOpenSub SYS_PREAD64 3#64 rwBufAddr   4#64 0#64 0#64 0#64
  let sLseekDir      := callSyscall6 sOpenSub SYS_LSEEK   3#64 0#64        0#64 0#64 0#64 0#64
  let sCloseDir      := callSyscall6 sOpenSub SYS_CLOSE   3#64 0#64        0#64 0#64 0#64 0#64
  -- `checkOpenFlags` runs before `readCString` even when the path pointer is unmapped (`0x90000#64`).
  let sCreatDirUnmapped := callSyscall6 s0 SYS_OPENAT atFdcwd64 unmappedPtr
    ((O_CREAT_W32 ||| O_DIRECTORY_W32).zeroExtend 64) 0#64 0#64 0#64
  let sBadFlagsUnmapped := callSyscall6 s0 SYS_OPENAT atFdcwd64 unmappedPtr 4#64 0#64 0#64 0#64
  let isOpenTrap : OpenVerdict → Bool
    | .trap _ => true
    | _       => false
  let sSetupSub := (((s0.writeReg64 .x0 atFdcwd64).writeReg64 .x1 pathSubAddr).writeReg64 .x2 flagsDirCloexec)
  let vSub := openatPure s0.fs AT_FDCWD_W32 "sub" (O_DIRECTORY_W32 ||| O_CLOEXEC_W32)
  let sViaPure := applyOpenVerdict sSetupSub vSub
  let fsBigAtMax := fs0.setFd 5#64
    (some { path := "big.bin", accMode := .wronly, offset := MAX_LFS_FILESIZE, kind := .localFile })
  let fsAppendAtMax := fs0.setFd 5#64
    (some { path := "big.bin", accMode := .wronly, append := true, offset := MAX_LFS_FILESIZE, kind := .localFile })
  let fsBigNearMax := fs0.setFd 5#64
    (some { path := "big.bin", accMode := .wronly, offset := MAX_LFS_FILESIZE - 2, kind := .localFile })
  let fsSmall := fs0.setFd 5#64
    (some { path := "big.bin", accMode := .wronly, offset := 2, kind := .localFile })
  let sBigAtMax    : State := { s0 with fs := fsBigAtMax }
  let sAppendAtMax : State := { s0 with fs := fsAppendAtMax }
  let sBigNearMax  : State := { s0 with fs := fsBigNearMax }
  let sSmall       : State := { s0 with fs := fsSmall }
  let sWriteMaxZero      := callSyscall6 sBigAtMax    SYS_WRITE 5#64 rwBufAddr   0#64 0#64 0#64 0#64
  let sWriteMaxOne       := callSyscall6 sBigAtMax    SYS_WRITE 5#64 rwBufAddr   1#64 0#64 0#64 0#64
  let sWriteMaxOneUnm    := callSyscall6 sBigAtMax    SYS_WRITE 5#64 unmappedPtr 1#64 0#64 0#64 0#64
  let sWriteMaxEfault    := callSyscall6 sBigAtMax    SYS_WRITE 5#64 rwBufAddr   0x8000000000000000#64 0#64 0#64 0#64
  let sWriteAppendMaxOne := callSyscall6 sAppendAtMax SYS_WRITE 5#64 rwBufAddr   1#64 0#64 0#64 0#64
  let sWriteNear3        := callSyscall6 sBigNearMax  SYS_WRITE 5#64 rwBufAddr   3#64 0#64 0#64 0#64
  let sWriteSmall2       := callSyscall6 sSmall       SYS_WRITE 5#64 rwBufAddr   2#64 0#64 0#64 0#64
  let sRd4 : State := { sWriteSmall2 with
    fs := sWriteSmall2.fs.setFd 6#64 (some { path := "big.bin", accMode := .rdonly, offset := 0, kind := .localFile }) }
  let sRdEof : State := { sRd4 with
    fs := sRd4.fs.setFd 6#64 (some { path := "big.bin", accMode := .rdonly, offset := 4, kind := .localFile }) }
  let sWrExt4Edge : State := { sWriteSmall2 with
    fs := sWriteSmall2.fs.setFd 5#64 (some { path := "big.bin", accMode := .wronly, offset := FS_SAFE_MAX_FILESIZE - 1, kind := .localFile }) }
  let maxLfsBv   : BitVec 64 := 0x7fffffffffffffff#64
  let kaddrBv    : BitVec 64 := 0x8000000000000000#64
  let vaLimitBv  : BitVec 64 := 0x0001000000000000#64
  let overMaxRw  : BitVec 64 := 0x80000000#64
  let ext4MaxBv  : BitVec 64 := BitVec.ofNat 64 FS_SAFE_MAX_FILESIZE
  let ext4NearBv : BitVec 64 := BitVec.ofNat 64 (FS_SAFE_MAX_FILESIZE - 1)
  let sRdAtMax : State := { sRd4 with
    fs := sRd4.fs.setFd 6#64 (some { path := "big.bin", accMode := .rdonly, offset := MAX_LFS_FILESIZE, kind := .localFile }) }
  let sReadMaxZero     := callSyscall6 sRdAtMax    SYS_READ    6#64 rwBufAddr           0#64      0#64     0#64 0#64
  let sReadMaxOne      := callSyscall6 sRdAtMax    SYS_READ    6#64 rwBufAddr           1#64      0#64     0#64 0#64
  let sReadMaxOneUnm   := callSyscall6 sRdAtMax    SYS_READ    6#64 unmappedPtr         1#64      0#64     0#64 0#64
  let sReadZeroKaddr   := callSyscall6 sRd4        SYS_READ    6#64 kaddrBv             0#64      0#64     0#64 0#64
  let sPreadZeroKaddr  := callSyscall6 sRd4        SYS_PREAD64 6#64 kaddrBv             0#64      0#64     0#64 0#64
  let sPreadVaOverLfs  := callSyscall6 sRd4        SYS_PREAD64 6#64 vaLimitBv           0x1000#64 maxLfsBv 0#64 0#64
  let sWriteOutZeroKa  := callSyscall6 sRd4        SYS_WRITE   1#64 kaddrBv             0#64      0#64     0#64 0#64
  let sWriteFileZeroK  := callSyscall6 sSmall      SYS_WRITE   5#64 kaddrBv             0#64      0#64     0#64 0#64
  let sPreadMaxZero    := callSyscall6 sRd4        SYS_PREAD64 6#64 rwBufAddr           0#64      maxLfsBv 0#64 0#64
  let sPreadMaxOne     := callSyscall6 sRd4        SYS_PREAD64 6#64 rwBufAddr           1#64      maxLfsBv 0#64 0#64
  let sPreadMaxOneUnm  := callSyscall6 sRd4        SYS_PREAD64 6#64 unmappedPtr         1#64      maxLfsBv 0#64 0#64
  let sPreadMaxOverRw  := callSyscall6 sRd4        SYS_PREAD64 6#64 rwBufAddr           overMaxRw maxLfsBv 0#64 0#64
  let sReadOverMaxRw   := callSyscall6 sRd4        SYS_READ    6#64 rwBufAddr           overMaxRw 0#64     0#64 0#64
  let sPreadOverMaxRw  := callSyscall6 sRd4        SYS_PREAD64 6#64 rwBufAddr           overMaxRw 0#64     0#64 0#64
  let sWriteOutOverRw  := callSyscall6 sRd4        SYS_WRITE   1#64 rwBufAddr           overMaxRw 0#64     0#64 0#64
  let sWriteFileOverRw := callSyscall6 sSmall      SYS_WRITE   5#64 rwBufAddr           overMaxRw 0#64     0#64 0#64
  let sReadEofNull     := callSyscall6 sRdEof      SYS_READ    6#64 0#64                16#64     0#64     0#64 0#64
  let sReadShortOk     := callSyscall6 sRd4        SYS_READ    6#64 (rwBufAddr + 12#64) 16#64     0#64     0#64 0#64
  let sReadPartFault   := callSyscall6 sRd4        SYS_READ    6#64 (rwBufAddr + 14#64) 16#64     0#64     0#64 0#64
  let sWriteOutPartFlt := callSyscall6 sRd4        SYS_WRITE   1#64 (rwBufAddr + 14#64) 4#64      0#64     0#64 0#64
  let sWriteFilPartFlt := callSyscall6 sSmall      SYS_WRITE   5#64 (rwBufAddr + 14#64) 4#64      0#64     0#64 0#64
  let sLseekExt4Ok     := callSyscall6 sRd4        SYS_LSEEK   6#64 ext4NearBv          0#64      0#64     0#64 0#64
  let sLseekExt4Trap   := callSyscall6 sRd4        SYS_LSEEK   6#64 ext4MaxBv           0#64      0#64     0#64 0#64
  let sWriteExt4Trap   := callSyscall6 sWrExt4Edge SYS_WRITE   5#64 rwBufAddr           2#64      0#64     0#64 0#64
  let sSeekData2       := callSyscall6 sRd4        SYS_LSEEK   6#64 2#64                3#64      0#64     0#64 0#64
  let sSeekHole1       := callSyscall6 sRd4        SYS_LSEEK   6#64 1#64                4#64      0#64     0#64 0#64
  let sSeekDataEof     := callSyscall6 sRd4        SYS_LSEEK   6#64 4#64                3#64      0#64     0#64 0#64
  let sSeekHoleEof     := callSyscall6 sRd4        SYS_LSEEK   6#64 4#64                4#64      0#64     0#64 0#64
  let sSeekDataNeg     := callSyscall6 sRd4        SYS_LSEEK   6#64 (-1#64)             3#64      0#64     0#64 0#64
  let sSeekHoleNeg     := callSyscall6 sRd4        SYS_LSEEK   6#64 (-1#64)             4#64      0#64     0#64 0#64
  let sSeekWhence5     := callSyscall6 sRd4        SYS_LSEEK   6#64 0#64                5#64      0#64     0#64 0#64
  MAX_LFS_FILESIZE == 2 ^ 63 - 1 &&
  MAX_RW_COUNT == 0x7ffff000 &&
  FS_SAFE_MAX_FILESIZE == 0xffffffff &&
  sOpenSub.status == .Running && sOpenSub.readReg64 .x0 == 3#64 &&
  sOpenSub.fs.fds 3#64 == some
    { path := "sub", accMode := .rdonly, append := false, cloexec := true, offset := 0, kind := .localDir } &&
  sOpenDot.status == .Running && sOpenDot.readReg64 .x0 == 4#64 &&
  sOpenDot.fs.fds 4#64 == some
    { path := ".", accMode := .rdonly, append := false, cloexec := false, offset := 0, kind := .localDir } &&
  sOpenDirWr.status == .Running && sOpenDirWr.readReg64 .x0 == -EISDIR &&
  sOpenDirRdwr.status == .Running && sOpenDirRdwr.readReg64 .x0 == -EISDIR &&
  sOpenDirCreat.status == .Running && sOpenDirCreat.readReg64 .x0 == -EISDIR &&
  sOpenDirTrunc.status == .Running && sOpenDirTrunc.readReg64 .x0 == -EISDIR &&
  sOpenDirExcl.status == .Running && sOpenDirExcl.readReg64 .x0 == -EEXIST &&
  sFstatDir.status == .Running && sFstatDir.readReg64 .x0 == 0#64 &&
  sFstatDir.mem.read32 (statBufAddr + 16#64) == 0x41ed#32 &&
  sFstatDir.mem.read64 (statBufAddr + 48#64) == 0#64 &&
  sFcntlSubGet0.status == .Running && sFcntlSubGet0.readReg64 .x0 == 1#64 &&
  sFcntlSubSet0.status == .Running && sFcntlSubSet0.readReg64 .x0 == 0#64 &&
  sFcntlSubGet1.status == .Running && sFcntlSubGet1.readReg64 .x0 == 0#64 &&
  sFcntlDotGet0.status == .Running && sFcntlDotGet0.readReg64 .x0 == 0#64 &&
  sFcntlDotSet1.status == .Running && sFcntlDotSet1.readReg64 .x0 == 0#64 &&
  sFcntlDotGet1.status == .Running && sFcntlDotGet1.readReg64 .x0 == 1#64 &&
  isExceptionStatus sFcntlDirDupfd.status &&
  isExceptionStatus sFcntlDirGetfl.status &&
  sReadDir.status == .Running && sReadDir.readReg64 .x0 == -EISDIR &&
  sReadDir.trace == sOpenSub.trace &&
  sReadDirUnm.status == .Running && sReadDirUnm.readReg64 .x0 == -EISDIR &&
  sReadDir0.status == .Running && sReadDir0.readReg64 .x0 == -EISDIR &&
  sReadDirEfault.status == .Running && sReadDirEfault.readReg64 .x0 == EFAULT_RET &&
  sWriteDir.status == .Running && sWriteDir.readReg64 .x0 == -EBADF &&
  isExceptionStatus sPreadDir.status &&
  isExceptionStatus sLseekDir.status &&
  sCloseDir.status == .Running && sCloseDir.readReg64 .x0 == 0#64 &&
  sCloseDir.fs.fds 3#64 == none &&
  sCreatDirUnmapped.status == .Running && sCreatDirUnmapped.readReg64 .x0 == -EINVAL &&
  isExceptionStatus sBadFlagsUnmapped.status &&
  !isOpenTrap vSub &&
  (checkOpenFlags 4#32).map isOpenTrap == some true &&
  sViaPure.readReg64 .x0 == 3#64 &&
  sViaPure.fs.fds 3#64 == sOpenSub.fs.fds 3#64 &&
  sWriteMaxZero.status == .Running && sWriteMaxZero.readReg64 .x0 == 0#64 &&
  sWriteMaxOne.status == .Running && sWriteMaxOne.readReg64 .x0 == -EINVAL &&
  sWriteMaxOne.trace == sBigAtMax.trace &&
  sWriteMaxOneUnm.status == .Running && sWriteMaxOneUnm.readReg64 .x0 == -EINVAL &&
  sWriteMaxEfault.status == .Running && sWriteMaxEfault.readReg64 .x0 == EFAULT_RET &&
  sWriteAppendMaxOne.status == .Running && sWriteAppendMaxOne.readReg64 .x0 == -EINVAL &&
  sWriteAppendMaxOne.fs.files "big.bin" == some (.file [0x11#8]) &&
  sWriteNear3.status == .Running && sWriteNear3.readReg64 .x0 == -EINVAL &&
  sWriteSmall2.status == .Running && sWriteSmall2.readReg64 .x0 == 2#64 &&
  (sWriteSmall2.fs.fds 5#64).map FdEntry.offset == some 4 &&
  sWriteSmall2.fs.files "big.bin" == some (.file [0x11#8, 0x00#8, 0x41#8, 0x41#8]) &&
  sReadMaxZero.status == .Running && sReadMaxZero.readReg64 .x0 == 0#64 &&
  sReadMaxOne.status == .Running && sReadMaxOne.readReg64 .x0 == -EINVAL &&
  sReadMaxOneUnm.status == .Running && sReadMaxOneUnm.readReg64 .x0 == -EINVAL &&
  sReadZeroKaddr.status == .Running && sReadZeroKaddr.readReg64 .x0 == EFAULT_RET &&
  sPreadZeroKaddr.status == .Running && sPreadZeroKaddr.readReg64 .x0 == EFAULT_RET &&
  sPreadVaOverLfs.status == .Running && sPreadVaOverLfs.readReg64 .x0 == EFAULT_RET &&
  sWriteOutZeroKa.status == .Running && sWriteOutZeroKa.readReg64 .x0 == EFAULT_RET &&
  sWriteFileZeroK.status == .Running && sWriteFileZeroK.readReg64 .x0 == EFAULT_RET &&
  sPreadMaxZero.status == .Running && sPreadMaxZero.readReg64 .x0 == 0#64 &&
  sPreadMaxOne.status == .Running && sPreadMaxOne.readReg64 .x0 == -EINVAL &&
  sPreadMaxOneUnm.status == .Running && sPreadMaxOneUnm.readReg64 .x0 == -EINVAL &&
  sPreadMaxOverRw.status == .Running && sPreadMaxOverRw.readReg64 .x0 == -EINVAL &&
  sReadOverMaxRw.status == .Running && sReadOverMaxRw.readReg64 .x0 == 4#64 &&
  sPreadOverMaxRw.status == .Running && sPreadOverMaxRw.readReg64 .x0 == 4#64 &&
  sWriteOutOverRw.status == .Exception "unmodeled partial-fault short write" &&
  sWriteFileOverRw.status == .Exception "unmodeled partial-fault short write" &&
  sReadEofNull.status == .Running && sReadEofNull.readReg64 .x0 == 0#64 &&
  sReadShortOk.status == .Running && sReadShortOk.readReg64 .x0 == 4#64 &&
  sReadPartFault.status == .Exception "unmodeled partial-fault short read" &&
  sWriteOutPartFlt.status == .Exception "unmodeled partial-fault short write" &&
  sWriteFilPartFlt.status == .Exception "unmodeled partial-fault short write" &&
  sLseekExt4Ok.status == .Running && sLseekExt4Ok.readReg64 .x0 == ext4NearBv &&
  sLseekExt4Trap.status == .Exception "unmodeled lseek offset >= FS_SAFE_MAX_FILESIZE" &&
  sWriteExt4Trap.status == .Exception "unmodeled file write past FS_SAFE_MAX_FILESIZE" &&
  sSeekData2.status == .Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset" &&
  sSeekHole1.status == .Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset" &&
  sSeekDataEof.status == .Running && sSeekDataEof.readReg64 .x0 == -ENXIO &&
  sSeekHoleEof.status == .Running && sSeekHoleEof.readReg64 .x0 == -ENXIO &&
  sSeekDataNeg.status == .Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset" &&
  sSeekHoleNeg.status == .Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset" &&
  sSeekWhence5.status == .Running && sSeekWhence5.readReg64 .x0 == -EINVAL

theorem vfs_localdir_openatpure_and_lfs_ok : checkVfsLocalDirOpenatPureAndLfs = true := by
  decide +kernel

/-! ## `sigaltstack` (`SYS_SIGALTSTACK = 132`) and `MAP_STACK` (`0x20022`) -/

/-- Serialize a 24-byte LP64 `stack_t` with explicit 4-byte caller padding at `+12..+15`. -/
def stackTBytesWithPad (sp : BitVec 64) (flags pad : BitVec 32) (size : BitVec 64) : List (BitVec 8) :=
  leBytes64 sp ++ leBytes32 flags ++ leBytes32 pad ++ leBytes64 size

/-- Invoke `sigaltstack(uss, uoss)` via `execSyscall`. -/
def callSigaltstack (s : State) (uss uoss : BitVec 64) : State :=
  callSyscall6 s SYS_SIGALTSTACK uss uoss 0#64 0#64 0#64 0#64

/-- Conformance and boundary checks for `execSigaltstack` (`MINSIGSTKSZ`, `(sp, sp + size]`
    `onSigStack` endpoints, `SS_AUTODISARM`, `SS_DISABLE`, `-EFAULT` ordering, and unchanged-settings
    early return) and `MMAP_FLAGS_PRIVATE_ANON_STACK` (`0x20022` vs `MAP_FIXED | MAP_STACK`). -/
def checkSigaltstackAndMapStack : Bool :=
  let ussTooSmall   := 0x60000#64
  let ussMinOk      := 0x60020#64
  let ussInstall8k  := 0x60040#64
  let ussAuto8k     := 0x60060#64
  let ussDisableNz  := 0x60080#64
  let ussAutoDisNz  := 0x600a0#64
  let ussBadFlags4  := 0x600c0#64
  let ussBadFlags3  := 0x600e0#64
  let ussZero       := 0x60140#64
  let uossBuf1      := 0x60100#64
  let uossBuf2      := 0x60120#64
  let uossRo        := 0x61000#64
  let altSp         := 0x80000#64
  let altSz         := 0x2000#64
  let mem0 := memOfRegions
    [{ start := ussTooSmall,  perm := .rw, bytes := stackTBytesWithPad altSp 0#32 0#32 5119#64 },
     { start := ussMinOk,     perm := .rw, bytes := stackTBytesWithPad altSp 0#32 0xdeadbeef#32 5120#64 },
     { start := ussInstall8k, perm := .rw, bytes := stackTBytesWithPad altSp SS_ONSTACK 0xcafebabe#32 altSz },
     { start := ussAuto8k,    perm := .rw, bytes := stackTBytesWithPad altSp SS_AUTODISARM 0#32 altSz },
     { start := ussDisableNz, perm := .rw, bytes := stackTBytesWithPad altSp SS_DISABLE 0x12345678#32 0x41000#64 },
     { start := ussAutoDisNz, perm := .rw, bytes := stackTBytesWithPad altSp (SS_AUTODISARM ||| SS_DISABLE) 0#32 16#64 },
     { start := ussBadFlags4, perm := .rw, bytes := stackTBytesWithPad altSp 4#32 0#32 altSz },
     { start := ussBadFlags3, perm := .rw, bytes := stackTBytesWithPad altSp 3#32 0#32 altSz },
     { start := ussZero,      perm := .rw, bytes := stackTBytesWithPad 0#64 0#32 0#32 0#64 },
     { start := uossBuf1,     perm := .rw, bytes := List.replicate 24 0xff#8 },
     { start := uossBuf2,     perm := .rw, bytes := List.replicate 24 0xff#8 },
     { start := uossRo,       perm := .ro, bytes := List.replicate 24 0#8 }]
  let s0 : State := { pc := 0x1000#64, sp := 0x70000#64, mem := mem0, physMemAvail := 0x10000 }
  let sMmapStackRw   := callSyscall6 s0 SYS_MMAP 0#64 0x1000#64 3#64 MMAP_FLAGS_PRIVATE_ANON_STACK (-1#64) 0#64
  let sMmapStackNone := callSyscall6 s0 SYS_MMAP 0#64 0x1000#64 0#64 MMAP_FLAGS_PRIVATE_ANON_STACK (-1#64) 0#64
  let sMmapFixedStk  := callSyscall6 s0 SYS_MMAP 0x10000#64 0x1000#64 3#64 0x20032#64 (-1#64) 0#64
  let sInitQ := callSigaltstack s0 0#64 uossBuf1
  let s5119  := callSigaltstack s0 ussTooSmall uossBuf2
  let s5120  := callSigaltstack s0 ussMinOk uossBuf1
  let sInst8k := callSigaltstack s0 ussInstall8k uossBuf1
  let sAtLo   := callSigaltstack { sInst8k with sp := altSp }                ussMinOk uossBuf2
  let sAtLo1  := callSigaltstack { sInst8k with sp := altSp + 1#64 }         ussMinOk uossBuf2
  let sAtHi   := callSigaltstack { sInst8k with sp := altSp + altSz }        ussMinOk uossBuf2
  let sAtHi1  := callSigaltstack { sInst8k with sp := altSp + altSz + 1#64 } ussMinOk uossBuf2
  let sOnStkQ := callSigaltstack { sInst8k with sp := altSp + altSz }        0#64     uossBuf2
  let sAutoInst := callSigaltstack s0 ussAuto8k 0#64
  let sAutoOnQ  := callSigaltstack { sAutoInst with sp := altSp + 0x1000#64 } 0#64 uossBuf1
  let sAutoDis  := callSigaltstack sAutoInst ussAutoDisNz uossBuf2
  let sAutoDisQ := callSigaltstack sAutoDis 0#64 uossBuf1
  let sDropH    := callSigaltstack sInst8k ussDisableNz uossBuf2
  let sBad4     := callSigaltstack s0 ussBadFlags4 0#64
  let sBad3     := callSigaltstack s0 ussBadFlags3 0#64
  let sUssEf    := callSigaltstack s0 0x90000#64 uossBuf2
  let sUossEf   := callSigaltstack s0 ussMinOk uossRo
  -- Unchanged-settings early return (`kernel/signal.c:4486-4493`).
  let sZeroInit := callSigaltstack s0 ussZero uossBuf2
  let sZeroDis  := callSigaltstack sDropH ussZero 0#64
  (-EPERM) == (-1#64) &&
  sMmapStackRw.status == .Running && sMmapStackRw.readReg64 .x0 == 0x10000#64 &&
  sMmapStackRw.mem.perm 0x10000#64 == some Perm.rw &&
  sMmapStackNone.status == .Running && sMmapStackNone.readReg64 .x0 == 0x10000#64 &&
  sMmapStackNone.mem.perm 0x10000#64 == some Perm.protNone &&
  isExceptionStatus sMmapFixedStk.status &&
  sInitQ.status == .Running && sInitQ.readReg64 .x0 == 0#64 &&
  sInitQ.mem.read64 uossBuf1 == 0#64 &&
  sInitQ.mem.read32 (uossBuf1 + 8#64) == SS_DISABLE &&
  sInitQ.mem.read32 (uossBuf1 + 12#64) == 0#32 &&
  sInitQ.mem.read64 (uossBuf1 + 16#64) == 0#64 &&
  s5119.status == .Running && s5119.readReg64 .x0 == -ENOMEM &&
  s5119.sigAltStack == {} &&
  s5119.mem.readBytes uossBuf2 24 == List.replicate 24 0xff#8 &&
  s5120.status == .Running && s5120.readReg64 .x0 == 0#64 &&
  s5120.sigAltStack == { sp := altSp, size := 5120#64, ssFlags := 0#32 } &&
  sInst8k.status == .Running && sInst8k.readReg64 .x0 == 0#64 &&
  sAtLo.readReg64 .x0 == 0#64 &&
  sAtLo1.readReg64 .x0 == -EPERM &&
  sAtHi.readReg64 .x0 == -EPERM &&
  sAtHi1.readReg64 .x0 == 0#64 &&
  sOnStkQ.readReg64 .x0 == 0#64 &&
  sOnStkQ.mem.read32 (uossBuf2 + 8#64) == SS_ONSTACK &&
  sOnStkQ.mem.read32 (uossBuf2 + 12#64) == 0#32 &&
  -- `on_sig_stack` returns `false` under `SS_AUTODISARM` (`signal.h:596`), so `flags = SS_AUTODISARM`.
  sAutoInst.sigAltStack == { sp := altSp, size := altSz, ssFlags := SS_AUTODISARM } &&
  sAutoOnQ.mem.read32 (uossBuf1 + 8#64) == SS_AUTODISARM &&
  sAutoDis.readReg64 .x0 == 0#64 &&
  sAutoDis.sigAltStack == { sp := 0#64, size := 0#64, ssFlags := SS_AUTODISARM ||| SS_DISABLE } &&
  sAutoDisQ.mem.read32 (uossBuf1 + 8#64) == (SS_AUTODISARM ||| SS_DISABLE) &&
  sDropH.readReg64 .x0 == 0#64 &&
  sDropH.sigAltStack == { ssFlags := SS_DISABLE } &&
  sDropH.mem.read64 uossBuf2 == altSp &&
  sDropH.mem.read32 (uossBuf2 + 8#64) == 0#32 &&
  sDropH.mem.read32 (uossBuf2 + 12#64) == 0#32 &&
  sDropH.mem.read64 (uossBuf2 + 16#64) == altSz &&
  sBad4.readReg64 .x0 == -EINVAL &&
  sBad3.readReg64 .x0 == -EINVAL &&
  sUssEf.readReg64 .x0 == EFAULT_RET &&
  sUossEf.readReg64 .x0 == EFAULT_RET &&
  sUossEf.sigAltStack == { sp := altSp, size := 5120#64, ssFlags := 0#32 } &&
  sZeroInit.status == .Running && sZeroInit.readReg64 .x0 == 0#64 &&
  sZeroInit.sigAltStack == {} &&
  sZeroInit.mem.read32 (uossBuf2 + 8#64) == SS_DISABLE &&
  sZeroDis.status == .Running && sZeroDis.readReg64 .x0 == -ENOMEM &&
  sZeroDis.sigAltStack == { ssFlags := SS_DISABLE }

theorem sigaltstack_and_map_stack_ok : checkSigaltstackAndMapStack = true := by
  decide +kernel

end Arm64.Testing.Regression.StdSyscalls
