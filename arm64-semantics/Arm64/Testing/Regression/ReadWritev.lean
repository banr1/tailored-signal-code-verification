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
# Linux AArch64 `readv` and `writev` Regression Tests

Conformance tests comparing `execReadv` (`SYS_READV = 65`) and `execWritev` (`SYS_WRITEV = 66`)
against sequential single-buffer `read` and `write` calls, plus error-handling and fail-closed
descriptor cases.
-/

@[expose] public section

namespace Arm64.Testing.Regression.ReadWritev

open Arm64

/-- Dispatch a 3-argument Linux AArch64 supervisor call through `execSyscall`. -/
def call3 (s : State) (nr x0 x1 x2 : BitVec 64) : State :=
  execSyscall ((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2)

def isExceptionStatus : ExecStatus → Bool
  | .Exception _ => true
  | _            => false

/-- Serialize one little-endian 16-byte `struct iovec { void *iov_base; size_t iov_len; }`. -/
def iovecBytes (base len : BitVec 64) : List (BitVec 8) :=
  leBytes64 base ++ leBytes64 len

def memOfRegions (regions : List Snapshot.Region) : Memory :=
  ⟨Snapshot.cellAt regions⟩

def stdioDesc (mode : FdAccessMode) : FdEntry :=
  { path := "", accMode := mode, kind := .stdio }

def bufA : BitVec 64 := 0x50000#64
def bufB : BitVec 64 := 0x50010#64
def rbuf : BitVec 64 := 0x50200#64
def wvec : BitVec 64 := 0x50100#64
def rvec : BitVec 64 := 0x50300#64
def negVec : BitVec 64 := 0x50400#64
def unmapped : BitVec 64 := 0x90000#64

def s0 : State :=
  let mem := memOfRegions
    [{ start := bufA, perm := .rw, bytes := [0x68#8, 0x65#8, 0x6c#8, 0x6c#8, 0x6f#8] },
     { start := bufB, perm := .rw, bytes := [0x20#8, 0x77#8, 0x6f#8, 0x72#8, 0x6c#8, 0x64#8] },
     { start := wvec, perm := .rw, bytes := iovecBytes bufA 5#64 ++ iovecBytes bufB 6#64 },
     { start := rbuf, perm := .rw, bytes := List.replicate 16 0#8 },
     { start := rvec, perm := .rw,
       bytes := iovecBytes rbuf 3#64 ++ iovecBytes (rbuf + 8#64) 4#64 },
     { start := negVec, perm := .rw, bytes := iovecBytes bufA 0x8000000000000000#64 }]
  let fs := ({ stdin := [0x01#8, 0x02#8, 0x03#8, 0x04#8, 0x05#8] } : FsState)
    |>.setEntry ["sub"] (some .dir)
    |>.setFile "out.bin" (some (.file []))
    |>.setFile "in.bin" (some (.file ((List.range 9).map fun i => BitVec.ofNat 8 (0x11 + i))))
    |>.setFd 0#64 (some (stdioDesc .rdonly))
    |>.setFd 1#64 (some (stdioDesc .wronly))
    |>.setFd 2#64 (some (stdioDesc .wronly))
    |>.setFd 3#64 (some { path := "sub", accMode := .rdonly, kind := .localDir })
    |>.setFd 5#64 (some { path := "out.bin", accMode := .wronly })
    |>.setFd 6#64 (some { path := "in.bin", accMode := .rdonly })
  { pc := 0x1000#64, mem := mem, fs := fs }

def checkWritevMatchesWrites : Bool :=
  let sv  := call3 s0 SYS_WRITEV 1#64 wvec 2#64
  let s1  := call3 s0 SYS_WRITE 1#64 bufA 5#64
  let s2  := call3 s1 SYS_WRITE 1#64 bufB 6#64
  let fv  := call3 s0 SYS_WRITEV 5#64 wvec 2#64
  let f1  := call3 s0 SYS_WRITE 5#64 bufA 5#64
  let f2  := call3 f1 SYS_WRITE 5#64 bufB 6#64
  sv.status == .Running && s2.status == .Running &&
  sv.readReg64 .x0 == 11#64 && sv.trace == s2.trace && sv.trace.length == 11 &&
  sv.readReg64 .x1 == wvec && sv.readReg64 .x2 == 2#64 && sv.pc == s0.pc + 4#64 &&
  fv.status == .Running && f2.status == .Running &&
  fv.readReg64 .x0 == 11#64 &&
  fv.fs.fileBytes "out.bin" == f2.fs.fileBytes "out.bin" &&
  (fv.fs.fileBytes "out.bin").length == 11 &&
  fv.fs.fds 5#64 == f2.fs.fds 5#64 && fv.trace == f2.trace

theorem writev_matches_writes_ok : checkWritevMatchesWrites = true := by
  decide +kernel

def checkReadvMatchesReads : Bool :=
  -- `stdin` holds 5 bytes, so segments (3, 4) transfer 3 + 2 = 5.
  let sv := call3 s0 SYS_READV 0#64 rvec 2#64
  let s1 := call3 s0 SYS_READ 0#64 rbuf 3#64
  let s2 := call3 s1 SYS_READ 0#64 (rbuf + 8#64) 4#64
  let fv := call3 s0 SYS_READV 6#64 rvec 2#64
  let f1 := call3 s0 SYS_READ 6#64 rbuf 3#64
  let f2 := call3 f1 SYS_READ 6#64 (rbuf + 8#64) 4#64
  sv.status == .Running && s2.status == .Running &&
  sv.readReg64 .x0 == 5#64 &&
  sv.mem.readBytes rbuf 16 == s2.mem.readBytes rbuf 16 &&
  sv.fs.fds 0#64 == s2.fs.fds 0#64 &&
  sv.readReg64 .x1 == rvec && sv.readReg64 .x2 == 2#64 && sv.pc == s0.pc + 4#64 &&
  fv.status == .Running && f2.status == .Running &&
  fv.readReg64 .x0 == 7#64 &&
  fv.mem.readBytes rbuf 16 == f2.mem.readBytes rbuf 16 &&
  fv.mem.readBytes rbuf 16 ==
    [0x11#8, 0x12#8, 0x13#8, 0#8, 0#8, 0#8, 0#8, 0#8,
     0x14#8, 0x15#8, 0x16#8, 0x17#8, 0#8, 0#8, 0#8, 0#8] &&
  fv.fs.fds 6#64 == f2.fs.fds 6#64

theorem readv_matches_reads_ok : checkReadvMatchesReads = true := by
  decide +kernel

def checkRwvErrors : Bool :=
  let wv0       := call3 s0 SYS_WRITEV 1#64 unmapped 0#64
  let rv0       := call3 s0 SYS_READV 6#64 unmapped 0#64
  let wvMax     := call3 s0 SYS_WRITEV 1#64 wvec 1025#64
  let rvMax     := call3 s0 SYS_READV 6#64 rvec 1025#64
  let wvBadFd   := call3 s0 SYS_WRITEV 9#64 wvec 2#64
  let rvBadFd   := call3 s0 SYS_READV 9#64 rvec 2#64
  let wvBadMax  := call3 s0 SYS_WRITEV 9#64 wvec 1025#64
  let wvNegFd   := call3 s0 SYS_WRITEV 0xffffffff#64 wvec 2#64
  let rvWrOnly  := call3 s0 SYS_READV 5#64 rvec 2#64
  let wvRdOnly  := call3 s0 SYS_WRITEV 6#64 wvec 2#64
  let wvFault   := call3 s0 SYS_WRITEV 1#64 unmapped 2#64
  let rvFault   := call3 s0 SYS_READV 6#64 unmapped 2#64
  let wvNegLen  := call3 s0 SYS_WRITEV 1#64 negVec 1#64
  let rvDir     := call3 s0 SYS_READV 3#64 rvec 2#64
  let wvDir     := call3 s0 SYS_WRITEV 3#64 wvec 2#64
  let wvTrunc   := call3 s0 SYS_WRITEV 1#64 wvec 0x100000002#64
  let wvStdin   := call3 s0 SYS_WRITEV 0#64 wvec 2#64
  wv0.status == .Running && wv0.readReg64 .x0 == 0#64 && wv0.trace == s0.trace &&
  rv0.status == .Running && rv0.readReg64 .x0 == 0#64 &&
  wvMax.status == .Running && wvMax.readReg64 .x0 == -EINVAL &&
  rvMax.status == .Running && rvMax.readReg64 .x0 == -EINVAL &&
  wvBadFd.status == .Running && wvBadFd.readReg64 .x0 == -EBADF &&
  rvBadFd.status == .Running && rvBadFd.readReg64 .x0 == -EBADF &&
  wvBadMax.status == .Running && wvBadMax.readReg64 .x0 == -EBADF &&
  wvNegFd.status == .Running && wvNegFd.readReg64 .x0 == -EBADF &&
  rvWrOnly.status == .Running && rvWrOnly.readReg64 .x0 == -EBADF &&
  wvRdOnly.status == .Running && wvRdOnly.readReg64 .x0 == -EBADF &&
  wvFault.status == .Running && wvFault.readReg64 .x0 == EFAULT_RET &&
  rvFault.status == .Running && rvFault.readReg64 .x0 == EFAULT_RET &&
  wvNegLen.status == .Running && wvNegLen.readReg64 .x0 == -EINVAL &&
  wvNegLen.trace == s0.trace &&
  rvDir.status == .Running && rvDir.readReg64 .x0 == -EISDIR &&
  wvDir.status == .Running && wvDir.readReg64 .x0 == -EBADF &&
  wvTrunc.status == .Running && wvTrunc.readReg64 .x0 == 11#64 &&
  isExceptionStatus wvStdin.status

theorem rwv_errors_ok : checkRwvErrors = true := by
  decide +kernel

theorem writev_ne_single_write :
    ((call3 s0 SYS_WRITEV 1#64 wvec 2#64).trace ==
      (call3 s0 SYS_WRITE 1#64 bufA 5#64).trace) = false := by
  decide +kernel

end Arm64.Testing.Regression.ReadWritev
