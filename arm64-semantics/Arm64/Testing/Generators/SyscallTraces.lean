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
# Linux VFS Syscall Differential Trace Generators

Defines `dumpFsDiffTrace`, `dumpMmapDiffTrace`, and `dumpSigaltstackDiffTrace`, which execute
Linux AArch64 VFS, memory-mapping, and signal-stack syscall traces directly via `Arm64.execSyscall`
and print comma-separated outcomes for differential comparison against the host Linux kernel in
`tools/run-trusted-tests/src/fs_linux_diff_tests.rs`.
-/

@[expose] public section

namespace Testing.Generators

open Arm64

/-- Execute the CWD-relative FS syscall trace directly via `execSyscall` and emit comma-separated
    results (`ioctl`, `clock_gettime`, `openat`, `fstat`, `pread64`, `read`, `lseek` across
    `SEEK_SET`/`SEEK_CUR`/`SEEK_END`, `close`, `write`, `fcntl` `F_GETFD`/`F_SETFD`) for
    differential testing against the host Linux kernel in
    `tools/run-trusted-tests/src/fs_linux_diff_tests.rs`. -/
def dumpFsDiffTrace : IO Unit := do
  let cstr (str : String) : List (BitVec 8) :=
    (str.toList.map fun c => BitVec.ofNat 8 c.toNat) ++ [0#8]
  let s0 :=
    let mem := (Memory.empty.mapZero 0x2000#64 0x1000)
      |>.writeBytes 0x2000#64 (cstr "a")
      |>.writeBytes 0x2010#64 (cstr "b")
      |>.writeBytes 0x2020#64 (cstr "d")
      |>.writeBytes 0x2030#64 (cstr "missing/x")
      |>.writeBytes 0x2050#64 (cstr "a/x")
      |>.writeBytes 0x2070#64 (cstr "d/sub")
      |>.writeBytes 0x2090#64 (cstr ".//d//sub")
      |>.writeBytes 0x20b0#64 (cstr "<stdin>")
      |>.writeBytes 0x20c0#64 (cstr "<stdout>")
      |>.writeBytes 0x20d0#64 (cstr "<stderr>")
      |>.writeBytes 0x2180#64 [0x78#8, 0x79#8, 0x7a#8, 0x21#8]  -- "xyz!"
    let fs := Process.initFsState
      { stdin := [0x41#8]
        dirs  := ["d"]
        files := [("a", [65#8, 66#8, 67#8, 68#8, 69#8, 70#8, 71#8])] }
    { ({} : State) with mem, fs }
  let step (s : State) (nr x0 x1 x2 x3 : BitVec 64) : State :=
    execSyscall (((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64 .x3 x3)
  -- Directory lifecycle via `openat("d", O_RDONLY)` & `openat("d", O_RDONLY|O_CLOEXEC)` -> `fstat` -> `read` (-EISDIR, in-range unmapped -> -EISDIR, count=2^63 -> -EFAULT) -> `write` (-EBADF) -> `fcntl` (`F_GETFD`/`F_SETFD`) -> `close`
  let sDirOpen       := step s0       SYS_OPENAT (-100#64) 0x2020#64  0#64                 0#64 -- open dir "d" -> 3
  let sDirStat       := step sDirOpen SYS_FSTAT  3#64      0x2400#64  0#64                 0#64 -- stat dir "d" -> 0
  let dirMode        := sDirStat.mem.read32 0x2410#64
  let dirNlink       := sDirStat.mem.read32 0x2414#64
  let dirBlksize     := sDirStat.mem.read32 0x2438#64
  let sDirRead       := step sDirStat SYS_READ   3#64      0x2100#64  1#64                 0#64 -- read dir fd -> -21 (-EISDIR)
  let sDirReadUnm    := step sDirRead SYS_READ   3#64      0x90000#64 4#64                 0#64 -- read dir fd (in-range unmapped) -> -21 (-EISDIR)
  let sDirReadEfault := step sDirReadUnm SYS_READ 3#64     0x2100#64  0x8000000000000000#64 0#64 -- read dir fd (count = 2^63) -> -14 (-EFAULT)
  let sDirWrite      := step sDirReadEfault SYS_WRITE 3#64 0x2180#64  1#64                 0#64 -- write dir fd -> -9 (-EBADF)
  let sDirGetFd0     := step sDirWrite   SYS_FCNTL  3#64      1#64      0#64       0#64 -- F_GETFD on dir fd (O_RDONLY) -> 0
  let sDirSetFd1     := step sDirGetFd0  SYS_FCNTL  3#64      2#64      1#64       0#64 -- F_SETFD(FD_CLOEXEC) on dir fd -> 0
  let sDirGetFd1     := step sDirSetFd1  SYS_FCNTL  3#64      1#64      0#64       0#64 -- F_GETFD after F_SETFD(1) -> 1
  let sDirSetFd0     := step sDirGetFd1  SYS_FCNTL  3#64      2#64      0#64       0#64 -- F_SETFD(0) on dir fd -> 0
  let sDirGetFd2     := step sDirSetFd0  SYS_FCNTL  3#64      1#64      0#64       0#64 -- F_GETFD after F_SETFD(0) -> 0
  let sDirClose      := step sDirGetFd2  SYS_CLOSE  3#64      0#64      0#64       0#64 -- close dir fd -> 0
  let sDirCloOpen    := step sDirClose   SYS_OPENAT (-100#64) 0x2020#64 0x80000#64 0#64 -- open dir "d" (O_RDONLY|O_CLOEXEC) -> 3
  let sDirCloGetFd0  := step sDirCloOpen SYS_FCNTL  3#64      1#64      0#64       0#64 -- F_GETFD after O_CLOEXEC dir open -> 1
  let sDirCloSetFd0  := step sDirCloGetFd0 SYS_FCNTL 3#64     2#64      0#64       0#64 -- F_SETFD(0) on O_CLOEXEC dir fd -> 0
  let sDirCloGetFd1  := step sDirCloSetFd0 SYS_FCNTL 3#64     1#64      0#64       0#64 -- F_GETFD after F_SETFD(0) -> 0
  let sDirCloSetFd1  := step sDirCloGetFd1 SYS_FCNTL 3#64     2#64      1#64       0#64 -- F_SETFD(FD_CLOEXEC) on dir fd -> 0
  let sDirCloGetFd2  := step sDirCloSetFd1 SYS_FCNTL 3#64     1#64      0#64       0#64 -- F_GETFD after F_SETFD(1) -> 1
  let sDirCloClose   := step sDirCloGetFd2 SYS_CLOSE 3#64     0#64      0#64       0#64 -- close O_CLOEXEC dir fd -> 0
  let sDirCloClosedGet := step sDirCloClose SYS_FCNTL 3#64    1#64      0#64       0#64 -- F_GETFD on closed dir fd -> -9 (-EBADF)
  let mkDirDesc (clo : Bool) : FdEntry :=
    { path := "d", accMode := .rdonly, append := false, cloexec := clo, offset := 0, kind := .localDir }
  let dirStateParityOk : Bool :=
    [sDirOpen, sDirGetFd0, sDirSetFd1, sDirGetFd1, sDirSetFd0, sDirGetFd2, sDirClose,
     sDirCloOpen, sDirCloGetFd0, sDirCloSetFd0, sDirCloGetFd1, sDirCloSetFd1, sDirCloGetFd2,
     sDirCloClose, sDirCloClosedGet].all (fun s => s.status == .Running) &&
    sDirOpen.fs.fds 3#64 == some (mkDirDesc false) &&
    sDirSetFd1.fs.fds 3#64 == some (mkDirDesc true) &&
    sDirSetFd0.fs.fds 3#64 == some (mkDirDesc false) &&
    sDirClose.fs.fds 3#64 == none &&
    sDirCloOpen.fs.fds 3#64 == some (mkDirDesc true) &&
    sDirCloSetFd0.fs.fds 3#64 == some (mkDirDesc false) &&
    sDirCloSetFd1.fs.fds 3#64 == some (mkDirDesc true) &&
    sDirCloClose.fs.fds 3#64 == none
  unless dirStateParityOk do
    throw (IO.userError "dumpFsDiffTrace: directory fcntl status/fd parity check failed")
  -- Standard-stream out-of-band check: `openat` on `"<stdin>"` / `"<stdout>"` / `"<stderr>"` returns `-ENOENT`
  let sOpenStdin  := step sDirCloClosedGet SYS_OPENAT (-100#64) 0x20b0#64 0#64   0#64 -- "<stdin>" -> -2 (-ENOENT)
  let sOpenStdout := step sDirCloClosedGet SYS_OPENAT (-100#64) 0x20c0#64 0#64   0#64 -- "<stdout>" -> -2 (-ENOENT)
  let sOpenStderr := step sDirCloClosedGet SYS_OPENAT (-100#64) 0x20d0#64 0#64   0#64 -- "<stderr>" -> -2 (-ENOENT)
  let s1  := step sDirCloClosedGet SYS_IOCTL 3#64    0x5401#64 0x2100#64 0#64 -- closed fd -> -9
  let s2  := step s1  SYS_CLOCK_GETTIME 1#64      0x2280#64 0#64      0#64 -- 0
  let s3  := step s2  SYS_OPENAT        (-100#64) 0x2010#64 0#64      0#64 -- missing "b" -> -2
  let s4  := step s3  SYS_OPENAT        (-100#64) 0x2000#64 0#64      0#64 -- "a" -> fd 3
  let s5  := step s4  SYS_IOCTL         3#64      0x5401#64 0x2100#64 0#64 -- open regular fd 3 -> -25
  let s6  := step s5  SYS_FSTAT         3#64      0x2200#64 0#64      0#64 -- stat fd 3
  let fstatMode := s6.mem.read32 0x2210#64
  let fstatNlink := s6.mem.read32 0x2214#64
  let fstatSize := s6.mem.read64 0x2230#64
  let fstatBlksize := s6.mem.read32 0x2238#64
  let fstatBlocks := s6.mem.read64 0x2240#64
  let s7  := step s6  SYS_PREAD64       3#64      0x2100#64 4#64      2#64 -- "CDEF" (4)
  let s8  := step s7  SYS_READ          3#64      0x2110#64 5#64      0#64 -- "ABCDE" (5)
  let s9  := step s8  SYS_READ          3#64      0x2120#64 5#64      0#64 -- "FG" (2)
  let s10 := step s9  SYS_READ          3#64      0x2130#64 5#64      0#64 -- "" (0)
  let s11 := step s10 SYS_LSEEK         3#64      (-2#64)   2#64      0#64 -- SEEK_END - 2 -> 5
  let s12 := step s11 SYS_LSEEK         3#64      (-1#64)   1#64      0#64 -- SEEK_CUR - 1 -> 4
  let s13 := step s12 SYS_LSEEK         3#64      2#64      0#64      0#64 -- SEEK_SET 2 -> 2
  let s14 := step s13 SYS_CLOSE         3#64      0#64      0#64      0#64 -- 0
  let s15 := step s14 SYS_READ          3#64      0x2100#64 1#64      0#64 -- -9
  let s16 := step s15 SYS_OPENAT        (-100#64) 0x2010#64 0x241#64  0x1a4#64 -- O_WRONLY|O_CREAT|O_TRUNC 0644 -> 3
  let s17 := step s16 SYS_WRITE         3#64      0x2180#64 4#64      0#64 -- "xyz!" -> 4
  let s18 := step s17 SYS_OPENAT        (-100#64) 0x2010#64 0xc1#64   0x1a4#64 -- O_WRONLY|O_CREAT|O_EXCL 0644 -> -17
  let s19 := step s18 SYS_FSTAT         3#64      0x2300#64 0#64      0#64 -- fstat fd 3 ("b") -> size 4
  let s20 := step s19 SYS_FCNTL         3#64      1#64      0#64      0#64 -- F_GETFD before F_SETFD -> 0
  let s21 := step s20 SYS_FCNTL         3#64      2#64      1#64      0#64 -- F_SETFD (FD_CLOEXEC) on open fd 3 -> 0
  let s21b := step s21 SYS_FCNTL        3#64      1#64      0#64      0#64 -- F_GETFD after F_SETFD(1) -> 1
  let s22 := step s21b SYS_FCNTL        9#64      2#64      1#64      0#64 -- closed fd 9 -> -9 (-EBADF)
  let s23 := step s22 SYS_OPENAT        (-100#64) 0x2030#64 0x241#64  0x1a4#64 -- "missing/x" O_CREAT 0644 -> -2 (-ENOENT)
  let s24 := step s23 SYS_OPENAT        (-100#64) 0x2050#64 0x241#64  0x1a4#64 -- "a/x" O_CREAT 0644 -> -20 (-ENOTDIR)
  let s25 := step s24 SYS_OPENAT        (-100#64) 0x2070#64 0x241#64  0x1a4#64 -- "d/sub" O_CREAT 0644 -> 4
  let s26 := step s25 SYS_OPENAT        (-100#64) 0x2090#64 0x80000#64 0#64 -- ".//d//sub" O_RDONLY|O_CLOEXEC -> 5
  -- A 0-byte write at an offset past the end leaves the file unchanged (no zero padding), and
  -- `O_TRUNC` on an existing non-empty file ("b", "xyz!") empties it.
  let s27 := step s26 SYS_LSEEK         4#64      10#64     0#64      0#64 -- SEEK_SET 10 on empty "d/sub" -> 10
  let s28 := step s27 SYS_WRITE         4#64      0x2180#64 0#64      0#64 -- write 0 bytes -> 0
  let s29 := step s28 SYS_FSTAT         4#64      0x2600#64 0#64      0#64 -- stat "d/sub" -> size 0
  let s30 := step s29 SYS_OPENAT        (-100#64) 0x2010#64 0x201#64  0#64 -- O_WRONLY|O_TRUNC "b" -> 6
  let s31 := step s30 SYS_FSTAT         6#64      0x2680#64 0#64      0#64 -- stat "b" -> size 0
  let s32 := step s31 SYS_FCNTL         5#64      1#64      0#64      0#64 -- F_GETFD after O_CLOEXEC open -> 1
  -- `FS_SAFE_MAX_FILESIZE` (`0xffffffff`) boundary: `lseek` to `FS_SAFE_MAX_FILESIZE - 1` is
  -- modeled exactly, `write` 0 bytes there (mapped and unmapped in-range) -> `0`, and `lseek` to
  -- `FS_SAFE_MAX_FILESIZE` fails closed in the model (the host kernel's answer depends on the
  -- filesystem's `s_maxbytes`, so it is not compared). `O_APPEND` + `lseek(FS_SAFE_MAX_FILESIZE - 1)`
  -- + 1-byte `write` on the empty "b" writes at EOF (`0`) and returns `1`.
  let s33 := step s32 SYS_LSEEK         4#64      0xfffffffe#64         0#64    0#64
  let s34 := step s33 SYS_WRITE         4#64      0x2180#64             0#64    0#64
  let s34u := step s34 SYS_WRITE        4#64      0x90000#64            0#64    0#64
  let s35 := step s34u SYS_LSEEK        4#64      0xffffffff#64         0#64    0#64
  unless s35.status matches .Exception _ do
    throw (IO.userError "dumpFsDiffTrace: lseek to FS_SAFE_MAX_FILESIZE must fail closed")
  let s36 := step s34u SYS_OPENAT       (-100#64) 0x2010#64             0x401#64 0#64 -- "b" O_WRONLY|O_APPEND -> 7
  let s37 := step s36 SYS_LSEEK         7#64      0xfffffffe#64         0#64    0#64
  let s38 := step s37 SYS_WRITE         7#64      0x2180#64             1#64    0#64
  let vals : List Int := [
    (s1.readReg64 .x0).toInt,  -- ioctl closed (-9)
    (s2.readReg64 .x0).toInt,  -- clock_gettime (0)
    (s3.readReg64 .x0).toInt,  -- openat missing (-2)
    (s4.readReg64 .x0).toInt,  -- openat a (3)
    (s5.readReg64 .x0).toInt,  -- ioctl regular (-25)
    (s6.readReg64 .x0).toInt,  -- fstat ret (0)
    Int.ofNat fstatMode.toNat,           -- st_mode (0x81a4 = 33188)
    Int.ofNat fstatNlink.toNat,          -- st_nlink (1)
    Int.ofNat fstatSize.toNat,           -- st_size (7)
    Int.ofNat fstatBlksize.toNat,        -- st_blksize (4096)
    Int.ofNat fstatBlocks.toNat,         -- st_blocks (1)
    (s7.readReg64 .x0).toInt,  -- pread64 (4)
    (s8.readReg64 .x0).toInt,  -- read1 (5)
    (s9.readReg64 .x0).toInt,  -- read2 (2)
    (s10.readReg64 .x0).toInt, -- read3 (0)
    (s11.readReg64 .x0).toInt, -- lseek SEEK_END - 2 (5)
    (s12.readReg64 .x0).toInt, -- lseek SEEK_CUR - 1 (4)
    (s13.readReg64 .x0).toInt, -- lseek SEEK_SET 2 (2)
    (s14.readReg64 .x0).toInt, -- close (0)
    (s15.readReg64 .x0).toInt, -- read closed (-9)
    (s16.readReg64 .x0).toInt, -- openat create (3)
    (s17.readReg64 .x0).toInt, -- write (4)
    (s18.readReg64 .x0).toInt, -- openat excl (-17)
    (s19.readReg64 .x0).toInt, -- fstat fd 3 (0)
    Int.ofNat (s19.mem.read64 0x2330#64).toNat, -- fstat fd 3 size (4)
    (s20.readReg64 .x0).toInt, -- fcntl F_GETFD before F_SETFD (0)
    (s21.readReg64 .x0).toInt, -- fcntl F_SETFD (0)
    (s21b.readReg64 .x0).toInt, -- fcntl F_GETFD after F_SETFD (1)
    (s22.readReg64 .x0).toInt, -- fcntl closed fd (-9)
    (s23.readReg64 .x0).toInt, -- openat missing/x O_CREAT (-2)
    (s24.readReg64 .x0).toInt, -- openat a/x O_CREAT (-20)
    (s25.readReg64 .x0).toInt, -- openat d/sub O_CREAT (4)
    (s26.readReg64 .x0).toInt, -- openat .//d//sub O_RDONLY|O_CLOEXEC (5)
    (s27.readReg64 .x0).toInt, -- lseek past end (10)
    (s28.readReg64 .x0).toInt, -- write 0 bytes (0)
    (s29.readReg64 .x0).toInt, -- fstat d/sub (0)
    Int.ofNat (s29.mem.read64 0x2630#64).toNat, -- fstat d/sub size (0: no zero padding)
    (s30.readReg64 .x0).toInt, -- openat O_TRUNC existing b (6)
    (s31.readReg64 .x0).toInt, -- fstat b (0)
    Int.ofNat (s31.mem.read64 0x26b0#64).toNat, -- fstat b size (0: truncated)
    (s32.readReg64 .x0).toInt, -- fcntl F_GETFD after O_CLOEXEC open (1)
    (sDirOpen.readReg64 .x0).toInt,  -- openat dir "d" (3)
    (sDirStat.readReg64 .x0).toInt,  -- fstat dir "d" ret (0)
    Int.ofNat dirMode.toNat,         -- dir st_mode (0x41ed = 16877)
    Int.ofNat dirNlink.toNat,        -- dir st_nlink (2)
    Int.ofNat dirBlksize.toNat,      -- dir st_blksize (4096)
    (sDirRead.readReg64 .x0).toInt,       -- read dir fd (-21 = -EISDIR)
    (sDirReadUnm.readReg64 .x0).toInt,    -- read dir fd unmapped in-range (-21 = -EISDIR)
    (sDirReadEfault.readReg64 .x0).toInt, -- read dir fd count=2^63 (-14 = -EFAULT)
    (sDirWrite.readReg64 .x0).toInt,      -- write dir fd (-9 = -EBADF)
    (sDirGetFd0.readReg64 .x0).toInt,     -- fcntl F_GETFD on O_RDONLY dir fd (0)
    (sDirSetFd1.readReg64 .x0).toInt,     -- fcntl F_SETFD(FD_CLOEXEC) on dir fd (0)
    (sDirGetFd1.readReg64 .x0).toInt,     -- fcntl F_GETFD after F_SETFD(1) on dir fd (1)
    (sDirSetFd0.readReg64 .x0).toInt,     -- fcntl F_SETFD(0) on dir fd (0)
    (sDirGetFd2.readReg64 .x0).toInt,     -- fcntl F_GETFD after F_SETFD(0) on dir fd (0)
    (sDirClose.readReg64 .x0).toInt,      -- close dir fd (0)
    (sDirCloOpen.readReg64 .x0).toInt,    -- openat dir "d" O_RDONLY|O_CLOEXEC (3)
    (sDirCloGetFd0.readReg64 .x0).toInt,  -- fcntl F_GETFD after O_CLOEXEC dir open (1)
    (sDirCloSetFd0.readReg64 .x0).toInt,  -- fcntl F_SETFD(0) on O_CLOEXEC dir fd (0)
    (sDirCloGetFd1.readReg64 .x0).toInt,  -- fcntl F_GETFD after F_SETFD(0) (0)
    (sDirCloSetFd1.readReg64 .x0).toInt,  -- fcntl F_SETFD(FD_CLOEXEC) on dir fd (0)
    (sDirCloGetFd2.readReg64 .x0).toInt,  -- fcntl F_GETFD after F_SETFD(1) (1)
    (sDirCloClose.readReg64 .x0).toInt,   -- close O_CLOEXEC dir fd (0)
    (sDirCloClosedGet.readReg64 .x0).toInt, -- fcntl F_GETFD on closed dir fd (-9 = -EBADF)
    (sOpenStdin.readReg64 .x0).toInt,     -- openat "<stdin>" (-2 = -ENOENT)
    (sOpenStdout.readReg64 .x0).toInt,    -- openat "<stdout>" (-2 = -ENOENT)
    (sOpenStderr.readReg64 .x0).toInt,    -- openat "<stderr>" (-2 = -ENOENT)
    (s33.readReg64 .x0).toInt,  -- lseek FS_SAFE_MAX_FILESIZE - 1 (0xfffffffe)
    (s34.readReg64 .x0).toInt,  -- write 0 bytes at FS_SAFE_MAX_FILESIZE - 1 (0)
    (s34u.readReg64 .x0).toInt, -- write 0 bytes (unmapped in-range buf) at FS_SAFE_MAX_FILESIZE - 1 (0)
    (s36.readReg64 .x0).toInt,  -- openat "b" O_WRONLY|O_APPEND (7)
    (s37.readReg64 .x0).toInt,  -- lseek O_APPEND fd to FS_SAFE_MAX_FILESIZE - 1 (0xfffffffe)
    (s38.readReg64 .x0).toInt   -- write 1 byte on O_APPEND fd: writes at EOF (1)
  ]
  IO.println (String.intercalate "," (vals.map toString))

/-- Execute an 11-step guard-page memory syscall trace directly via `execSyscall` and emit 11
    comma-separated results for differential testing against the host Linux kernel in
    `tools/run-trusted-tests/src/fs_linux_diff_tests.rs` (`mmap_guard_trace_matches_linux_kernel`).
    Addresses are reported relative to the base `B` of a three-page read/write mapping so the
    model (`B = 0x50000`) and the host (`B` chosen by the kernel) can be compared:
    1. pages `B`, `B + 0x1000`, `B + 0x2000` are mapped read/write and hold `0x41`, `0x42`, `0x43`;
    2. `mmap(B + 0x1000, 0x1000, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0)` -> `0x1000`
       (relative);
    3. `write(fd, B + 0x1000, 1)` from the `PROT_NONE` page to a regular file -> `-EFAULT` (`-14`);
    4. `mprotect(B + 0x1000, 0x1000, PROT_READ|PROT_WRITE)` -> `0`, then the page reads `0` (the
       fixed mapping replaced it with zero-filled memory) and its neighbors still read `0x41`,
       `0x43`;
    5. after storing `0x55` at `B + 0x1000`, a second `MAP_FIXED` `PROT_NONE` mapping -> `0x1000`,
       then `mprotect` RW -> `0` and the page reads `0` again;
    6. `mmap(..., len = 0, ..., MAP_FIXED, ...)` -> `-EINVAL` (`-22`), `munmap(B, 0x3000)` -> `0`. -/
def dumpMmapDiffTrace : IO Unit := do
  let base : BitVec 64 := 0x50000#64
  let mem := ((((Memory.empty.mapZero base 0x3000).write8 base 0x41#8).write8 (base + 0x1000#64) 0x42#8).write8
    (base + 0x2000#64) 0x43#8)
  let fs := (({} : FsState).setFile "/out" (some (.file [])))
    |>.setFd 3#64 (some { path := "/out", accMode := .wronly })
  let s0 : State := { ({} : State) with mem, fs }
  let step (s : State) (nr x0 x1 x2 x3 : BitVec 64) : State :=
    execSyscall ((((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64
      .x3 x3).writeReg64 .x4 (-1#64) |>.writeReg64 .x5 0#64)
  let s1 := step s0 SYS_MMAP (base + 0x1000#64) 0x1000#64 0#64 0x32#64     -- MAP_FIXED PROT_NONE -> B + 0x1000
  let s2 := step s1 SYS_WRITE 3#64 (base + 0x1000#64) 1#64 0#64            -- write from PROT_NONE -> -14
  let s3 := step s2 SYS_MPROTECT (base + 0x1000#64) 0x1000#64 3#64 0#64    -- RW -> 0
  let s4 := { s3 with mem := s3.mem.write8 (base + 0x1000#64) 0x55#8 }
  let s5 := step s4 SYS_MMAP (base + 0x1000#64) 0x1000#64 0#64 0x32#64     -- MAP_FIXED again -> B + 0x1000
  let s6 := step s5 SYS_MPROTECT (base + 0x1000#64) 0x1000#64 3#64 0#64    -- RW -> 0
  let s7 := step s6 SYS_MMAP (base + 0x1000#64) 0#64 0#64 0x32#64          -- len 0 -> -22
  let s8 := step s7 SYS_MUNMAP base 0x3000#64 0#64 0#64                    -- 0
  let rel (v : BitVec 64) : Int := (v - base).toInt
  let vals : List Int := [
    rel (s1.readReg64 .x0),                          -- mmap fixed (0x1000 = 4096)
    (s2.readReg64 .x0).toInt,                        -- write from PROT_NONE (-14)
    (s3.readReg64 .x0).toInt,                        -- mprotect RW (0)
    (s3.mem.read8 (base + 0x1000#64)).toNat,         -- guard page byte after mprotect (0)
    (s3.mem.read8 base).toNat,                       -- lower neighbour (0x41 = 65)
    (s3.mem.read8 (base + 0x2000#64)).toNat,         -- upper neighbour (0x43 = 67)
    rel (s5.readReg64 .x0),                          -- second mmap fixed (4096)
    (s6.readReg64 .x0).toInt,                        -- mprotect RW (0)
    (s6.mem.read8 (base + 0x1000#64)).toNat,         -- replaced page byte (0)
    (s7.readReg64 .x0).toInt,                        -- mmap len 0 (-22)
    (s8.readReg64 .x0).toInt                         -- munmap (0)
  ]
  IO.println (String.intercalate "," (vals.map toString))

/-- Execute `MAP_STACK` `mmap` and `sigaltstack` (`SYS_SIGALTSTACK = 132`) edge cases through
    `Arm64.execSyscall` and print comma-separated `Int` outcomes for differential comparison
    against the host Linux kernel (`fs_linux_diff_tests::sigaltstack_and_map_stack_trace_matches_linux_kernel`). -/
def dumpSigaltstackDiffTrace : IO Unit := do
  let sInit : State := { ({} : State) with sp := 0x7fff_0000#64, physMemAvail := 2 ^ 30 }
  let call6 (s : State) (nr x0 x1 x2 x3 x4 x5 : BitVec 64) : State :=
    execSyscall (((((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64
      .x3 x3).writeReg64 .x4 x4).writeReg64 .x5 x5)
  let sMap := call6 sInit SYS_MMAP 0#64 0x4000#64 3#64 MMAP_FLAGS_PRIVATE_ANON_STACK (-1#64) 0#64
  let base := sMap.readReg64 .x0
  let guardVa := base + 0x1000#64
  let altSp := base + 0x2000#64
  let uss := base
  let uoss := base + 0x40#64
  let writeStackT (m : Memory) (addr sp : BitVec 64) (fl pad : BitVec 32) (sz : BitVec 64) : Memory :=
    m.writeBytes addr (leBytes64 sp ++ leBytes32 fl ++ leBytes32 pad ++ leBytes64 sz)
  let fillFF (m : Memory) (addr : BitVec 64) : Memory :=
    m.writeBytes addr (List.replicate 24 0xff#8)
  -- 1. Convert `guardVa` page to `PROT_NONE` for deterministic `-EFAULT` checks
  let sProt := call6 sMap SYS_MPROTECT guardVa 0x1000#64 0#64 0#64 0#64 0#64
  -- 2. Initial disabled query (`uss = 0, uoss != 0`)
  let sQ0 := call6 { sProt with mem := fillFF sProt.mem uoss } SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 3. `ss_size = 1024 < MINSIGSTKSZ` -> `-ENOMEM` (`uoss` untouched)
  let mSmall := fillFF (writeStackT sQ0.mem uss altSp 0#32 0#32 1024#64) uoss
  let sSmall := call6 { sQ0 with mem := mSmall } SYS_SIGALTSTACK uss uoss 0#64 0#64 0#64 0#64
  -- 4. Install `{ sp := altSp, flags := 0, pad := 0xdeadbeef, size := 0x2000 }`
  let mInst := fillFF (writeStackT sSmall.mem uss altSp 0#32 0xdeadbeef#32 0x2000#64) uoss
  let sInst := call6 { sSmall with mem := mInst } SYS_SIGALTSTACK uss uoss 0#64 0#64 0#64 0#64
  -- 5. Query active (`uss = 0`)
  let sQAct := call6 { sInst with mem := fillFF sInst.mem uoss } SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 6. Install `SS_AUTODISARM` (`0x80000000`) + query
  let sAuto := call6 { sQAct with mem := writeStackT sQAct.mem uss altSp SS_AUTODISARM 0#32 0x2000#64 }
    SYS_SIGALTSTACK uss 0#64 0#64 0#64 0#64 0#64
  let sQAuto := call6 sAuto SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 7. Disable with `SS_AUTODISARM | SS_DISABLE` and non-zero `size = 16` + query
  let sAutoDis := call6 { sQAuto with mem := writeStackT sQAuto.mem uss altSp (SS_AUTODISARM ||| SS_DISABLE) 0#32 16#64 }
    SYS_SIGALTSTACK uss 0#64 0#64 0#64 0#64 0#64
  let sQAutoDis := call6 sAutoDis SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 8. Disable with `SS_DISABLE` and non-zero `size = 0x41000` + query
  let sDis := call6 { sQAutoDis with mem := writeStackT sQAutoDis.mem uss altSp SS_DISABLE 0#32 0x41000#64 }
    SYS_SIGALTSTACK uss 0#64 0#64 0#64 0#64 0#64
  let sQDis := call6 sDis SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 9. Invalid flags (`4` and `3 = SS_ONSTACK | SS_DISABLE`)
  let sBad4 := call6 { sQDis with mem := writeStackT sQDis.mem uss altSp 4#32 0#32 0x2000#64 }
    SYS_SIGALTSTACK uss 0#64 0#64 0#64 0#64 0#64
  let sBad3 := call6 { sQDis with mem := writeStackT sQDis.mem uss altSp 3#32 0#32 0x2000#64 }
    SYS_SIGALTSTACK uss 0#64 0#64 0#64 0#64 0#64
  -- 10. `PROT_NONE` `uss = guardVa` -> `-EFAULT`
  let sEfUss := call6 sQDis SYS_SIGALTSTACK guardVa 0#64 0#64 0#64 0#64 0#64
  -- 11. Post-commit `uoss = guardVa` (`PROT_NONE`) `-EFAULT` ordering check + query
  let sEfUoss := call6 { sQDis with mem := writeStackT sQDis.mem uss altSp 0#32 0#32 0x2000#64 }
    SYS_SIGALTSTACK uss guardVa 0#64 0#64 0#64 0#64
  let sQAfterEf := call6 sEfUoss SYS_SIGALTSTACK 0#64 uoss 0#64 0#64 0#64 0#64
  -- 12. `munmap(base, 0x4000)` -> `0`
  let sUnmap := call6 sQAfterEf SYS_MUNMAP base 0x4000#64 0#64 0#64 0#64 0#64
  let rel (v : BitVec 64) : Int := (v - base).toInt
  let u (n : Nat) : Int := Int.ofNat n
  let vals : List Int := [
    (sProt.readReg64 .x0).toInt,
    (sQ0.readReg64 .x0).toInt,
    u (sQ0.mem.read64 uoss).toNat,
    u (sQ0.mem.read32 (uoss + 8#64)).toNat,
    u (sQ0.mem.read32 (uoss + 12#64)).toNat,
    u (sQ0.mem.read64 (uoss + 16#64)).toNat,
    (sSmall.readReg64 .x0).toInt,
    u (sSmall.mem.read8 uoss).toNat,
    (sInst.readReg64 .x0).toInt,
    u (sInst.mem.read32 (uoss + 8#64)).toNat,
    u (sInst.mem.read32 (uoss + 12#64)).toNat,
    (sQAct.readReg64 .x0).toInt,
    rel (sQAct.mem.read64 uoss),
    u (sQAct.mem.read32 (uoss + 8#64)).toNat,
    u (sQAct.mem.read32 (uoss + 12#64)).toNat,
    u (sQAct.mem.read64 (uoss + 16#64)).toNat,
    (sAuto.readReg64 .x0).toInt,
    (sQAuto.readReg64 .x0).toInt,
    u (sQAuto.mem.read32 (uoss + 8#64)).toNat,
    (sAutoDis.readReg64 .x0).toInt,
    (sQAutoDis.readReg64 .x0).toInt,
    u (sQAutoDis.mem.read64 uoss).toNat,
    u (sQAutoDis.mem.read32 (uoss + 8#64)).toNat,
    u (sQAutoDis.mem.read64 (uoss + 16#64)).toNat,
    (sDis.readReg64 .x0).toInt,
    u (sQDis.mem.read64 uoss).toNat,
    u (sQDis.mem.read32 (uoss + 8#64)).toNat,
    u (sQDis.mem.read64 (uoss + 16#64)).toNat,
    (sBad4.readReg64 .x0).toInt,
    (sBad3.readReg64 .x0).toInt,
    (sEfUss.readReg64 .x0).toInt,
    (sEfUoss.readReg64 .x0).toInt,
    rel (sQAfterEf.mem.read64 uoss),
    u (sQAfterEf.mem.read32 (uoss + 8#64)).toNat,
    u (sQAfterEf.mem.read64 (uoss + 16#64)).toNat,
    (sUnmap.readReg64 .x0).toInt
  ]
  IO.println (String.intercalate "," (vals.map toString))

end Testing.Generators
