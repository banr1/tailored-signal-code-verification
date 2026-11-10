/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public meta import ProofLib.Process
public import Std.Data.HashMap
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Harness.ElfRun
meta import ProofLib.TestFiles

/-!
# Static ELF64 Process Semantics and Syscall Conformance Tests

Kernel-checked conformance theorems for Linux AArch64 syscalls, fail-closed static ELF64 loading,
initial stack/`auxv` layout, and `ModeledSyscall` exhaustiveness, together with differential
runner checks on `echo_stdin.elf` and `abort_status.elf`.
-/

@[expose] public section

namespace Testing.Process

open Arm64 Arm64.Process ProofLib

set_option maxRecDepth 100000

/-! ## Syscall and Path-Resolution Conformance -/

/-- Conformance checks for `execFcntl` (`F_GETFD`/`F_SETFD` `cloexec` tracking on `.localFile`
    and `.localDir`, `-EBADF`, and unmodeled `cmd`/stdio traps), `execOpenat` (`O_CREAT` parent
    checks, trailing-slash/`O_DIRECTORY` errnos, and directory opens), and `resolveCwdPath`. -/
def checkProcessModelGapsConformance : Bool :=
  let writeCStr (m : Memory) (addr : BitVec 64) (s : String) : Memory :=
    m.writeBytes addr (bytesOfString s ++ [0#8])
  let mem0 := (Memory.empty.mapZero 0x40000#64 0x1000)
    |> (writeCStr · 0x40000#64 "missing/new")
    |> (writeCStr · 0x40040#64 "dir/new")
    |> (writeCStr · 0x40080#64 "reg/child")
    |> (writeCStr · 0x400c0#64 "./dir//sub/../escape")
    |> (writeCStr · 0x40100#64 ".//dir/./new")
    |> (writeCStr · 0x40140#64 "reg/")
    |> (writeCStr · 0x40180#64 "newslash/")
    |> (writeCStr · 0x401c0#64 "reg/sub/deep")
    |> (writeCStr · 0x40200#64 "reg/.")
    |> (writeCStr · 0x40240#64 "dir/missing/.")
    |> (writeCStr · 0x40280#64 "dir/")
    |> (writeCStr · 0x402c0#64 "./")
    |> (writeCStr · 0x40300#64 "reg")
  let fs0 := (({} : FsState).setFile "dir" (some .dir))
    |>.setFile "reg" (some (.file [0x41#8]))
    |>.setFd 3#64 (some { path := "reg", accMode := .rdonly })
    |>.setFd 4#64 (some { path := "reg", accMode := .rdonly })
  let s0 : State := { mem := mem0, fs := fs0 }
  let callSys (s : State) (nr x0 x1 x2 : BitVec 64) (x3 : BitVec 64 := 0#64) : State :=
    execSyscall (((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64 .x3 x3)
  -- fcntl: F_GETFD (1) -> 0 initially, F_SETFD (2, FD_CLOEXEC) -> 0, F_GETFD after F_SETFD -> 1,
  -- F_GETFD after O_CLOEXEC open -> 1, closed fd -> -EBADF, negative fd -> -EBADF,
  -- unmodeled stdio -> trap, other cmd (F_GETFL = 3) -> trap
  let sSetFd   := callSys s0 SYS_FCNTL 3#64 2#64 1#64
  let sGetFd   := callSys s0 SYS_FCNTL 3#64 1#64 0#64
  let sGetSet  := callSys sSetFd SYS_FCNTL 3#64 1#64 0#64
  let sOpenClo := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40300#64 0x80000#64 -- "reg" O_RDONLY|O_CLOEXEC -> fd 5
  let sGetClo  := callSys sOpenClo SYS_FCNTL 5#64 1#64 0#64                 -- F_GETFD after O_CLOEXEC open -> 1
  let sBadFd   := callSys s0 SYS_FCNTL 9#64 2#64 1#64
  let sNegFd   := callSys s0 SYS_FCNTL 0xffffffff#64 99#64 0#64
  let sStdio   := callSys s0 SYS_FCNTL 0#64 2#64 1#64
  let sBadCmd  := callSys s0 SYS_FCNTL 3#64 3#64 0#64 -- F_GETFL (3) traps
  -- openat(O_WRONLY | O_CREAT | O_TRUNC = 0x241, 0644):
  -- missing parent -> -ENOENT (-2), regular-file parent -> -ENOTDIR (-20), existing parent -> fd 5
  let sMissPar := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40000#64 0x241#64 0x1a4#64
  let sRegPar  := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40080#64 0x241#64 0x1a4#64
  let sOkCreat := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40040#64 0x241#64 0x1a4#64
  -- read via normalized "./dir/./new" after creation
  let sDotRead := callSys sOkCreat SYS_OPENAT 0xffffff9c#64 0x40100#64 0#64
  -- directory read open allocates a `.localDir` descriptor (`fd = 5`), supporting `F_GETFD`/`F_SETFD`
  let sDirOpen    := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40280#64 0#64
  let sDirGet0    := callSys sDirOpen SYS_FCNTL 5#64 1#64 0#64
  let sDirSet1    := callSys sDirOpen SYS_FCNTL 5#64 2#64 1#64
  let sDirGet1    := callSys sDirSet1 SYS_FCNTL 5#64 1#64 0#64
  let sDirSet0    := callSys sDirSet1 SYS_FCNTL 5#64 2#64 0#64
  let sDirBadCmd  := callSys sDirOpen SYS_FCNTL 5#64 3#64 0#64
  -- trailing slash / dot-component / deep regular-file ancestor edge cases matching fs/namei.c
  let sRegSlRd   := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40140#64 0#64
  let sRegSlCr   := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40140#64 0x241#64 0x1a4#64
  let sNewSlCr   := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40180#64 0x241#64 0x1a4#64
  let sDeepReg   := callSys s0 SYS_OPENAT 0xffffff9c#64 0x401c0#64 0x241#64 0x1a4#64 -- "reg/sub/deep" -> -ENOTDIR (-20)
  let sRegDotCr  := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40200#64 0x241#64 0x1a4#64 -- "reg/." -> -ENOTDIR (-20)
  let sMissDotCr := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40240#64 0x241#64 0x1a4#64 -- "dir/missing/." -> -ENOENT (-2)
  let sDirSlExcl := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40280#64 0xc1#64  0x1a4#64 -- "dir/" O_CREAT|O_EXCL -> -EISDIR (-21)
  let sDotSlExcl := callSys s0 SYS_OPENAT 0xffffff9c#64 0x402c0#64 0xc1#64  0x1a4#64 -- "./" O_CREAT|O_EXCL -> -EEXIST (-17)
  let sCreatDir  := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40040#64 0x4040#64 0x1a4#64 -- "dir/new" O_CREAT|O_DIRECTORY -> -EINVAL (-22)
  -- NAME_MAX vs trailing '/' + O_CREAT (`fs/namei.c:4707` checks EISDIR before final-segment NAME_MAX)
  let long256 := String.ofList (List.replicate 256 'n')
  let rLongSlCr := match openatPure fs0 AT_FDCWD_W32 (long256 ++ "/") 0x41#32 0x1a4#32 with
    | .errno e => e == EISDIR | _ => false
  let rLongSlRd := match openatPure fs0 AT_FDCWD_W32 (long256 ++ "/") 0#32 0#32 with
    | .errno e => e == ENAMETOOLONG | _ => false
  let rLongDotCr := match openatPure fs0 AT_FDCWD_W32 (long256 ++ "/.") 0x41#32 0x1a4#32 with
    | .errno e => e == ENAMETOOLONG | _ => false
  -- O_CREAT missing-file mode guard: creating without 0600 traps fail-closed; opening existing file with mode 0 succeeds
  let sModeZeroCr    := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40040#64 0x41#64  0#64
  let sModeRoCr      := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40040#64 0x41#64  0x124#64
  let sModeZeroExist := callSys s0 SYS_OPENAT 0xffffff9c#64 0x40300#64 0x241#64 0#64
  -- ".." path component fails closed with .Exception
  let sDotDot  := callSys s0 SYS_OPENAT 0xffffff9c#64 0x400c0#64 0#64
  -- resolveCwdPath direct unit checks
  let rOk1 := match resolveCwdPath AT_FDCWD_W32 "./coins" with | .ok p => p == ["coins"] | _ => false
  let rOk2 := match resolveCwdPath AT_FDCWD_W32 ".//signed-pre-keys/./1" with
    | .ok p => p == ["signed-pre-keys", "1"] | _ => false
  let rOk3 := match resolveCwdPath AT_FDCWD_W32 "///a//./b/" with
    | .trap m => m == "unmodeled absolute path" | _ => false
  let rOk4 := match resolveCwdPath AT_FDCWD_W32 "./" with | .ok p => p == [] | _ => false
  let rOk5 := match resolveCwdPath AT_FDCWD_W32 "///" with
    | .trap m => m == "unmodeled absolute path" | _ => false
  let rOk6 := match resolveCwdPath 4#32 "./sub//x" with
    | .trap m => m == "unmodeled non-AT_FDCWD dirfd" | _ => false
  let rOk7 := match resolveCwdPath 4#32 "." with
    | .trap m => m == "unmodeled non-AT_FDCWD dirfd" | _ => false
  let rEmp := match resolveCwdPath AT_FDCWD_W32 "" with | .errno e => e == ENOENT | _ => false
  let rDD  := match resolveCwdPath AT_FDCWD_W32 "dir/../secret" with | .trap _ => true | _ => false
  sSetFd.status == .Running && sSetFd.readReg64 .x0 == 0#64 &&
  sGetFd.status == .Running && sGetFd.readReg64 .x0 == 0#64 &&
  sGetSet.status == .Running && sGetSet.readReg64 .x0 == 1#64 &&
  sOpenClo.status == .Running && sOpenClo.readReg64 .x0 == 5#64 &&
  sGetClo.status == .Running && sGetClo.readReg64 .x0 == 1#64 &&
  sDirOpen.status == .Running && sDirOpen.readReg64 .x0 == 5#64 &&
  sDirOpen.fs.fds 5#64 == some { path := "dir/", accMode := .rdonly, kind := .localDir } &&
  sDirGet0.status == .Running && sDirGet0.readReg64 .x0 == 0#64 &&
  sDirSet1.status == .Running && sDirSet1.readReg64 .x0 == 0#64 &&
  sDirSet1.fs.fds 5#64 == some { path := "dir/", accMode := .rdonly, cloexec := true, kind := .localDir } &&
  sDirGet1.status == .Running && sDirGet1.readReg64 .x0 == 1#64 &&
  sDirSet0.status == .Running && sDirSet0.readReg64 .x0 == 0#64 &&
  sDirSet0.fs.fds 5#64 == some { path := "dir/", accMode := .rdonly, cloexec := false, kind := .localDir } &&
  sDirBadCmd.status == .Exception "unmodeled fcntl cmd" &&
  sBadFd.status == .Running && sBadFd.readReg64 .x0 == -9#64 &&
  sNegFd.status == .Running && sNegFd.readReg64 .x0 == -9#64 &&
  sStdio.status == .Exception "unmodeled stdio fd" &&
  sBadCmd.status == .Exception "unmodeled fcntl cmd" &&
  sMissPar.status == .Running && sMissPar.readReg64 .x0 == -2#64 &&
  (sMissPar.fs.files "missing/new").isNone &&
  sRegPar.status == .Running && sRegPar.readReg64 .x0 == -20#64 &&
  sOkCreat.status == .Running && sOkCreat.readReg64 .x0 == 5#64 &&
  (sOkCreat.fs.files "dir/new").isSome &&
  sDotRead.status == .Running && sDotRead.readReg64 .x0 == 6#64 &&
  sRegSlRd.status == .Running && sRegSlRd.readReg64 .x0 == -20#64 &&
  sRegSlCr.status == .Running && sRegSlCr.readReg64 .x0 == -21#64 &&
  sNewSlCr.status == .Running && sNewSlCr.readReg64 .x0 == -21#64 &&
  sDeepReg.status == .Running && sDeepReg.readReg64 .x0 == -20#64 &&
  sRegDotCr.status == .Running && sRegDotCr.readReg64 .x0 == -20#64 &&
  sMissDotCr.status == .Running && sMissDotCr.readReg64 .x0 == -2#64 &&
  sDirSlExcl.status == .Running && sDirSlExcl.readReg64 .x0 == -21#64 &&
  sDotSlExcl.status == .Running && sDotSlExcl.readReg64 .x0 == -17#64 &&
  sCreatDir.status == .Running && sCreatDir.readReg64 .x0 == -22#64 &&
  rLongSlCr && rLongSlRd && rLongDotCr &&
  sModeZeroCr.status == .Exception "unmodeled non-owner-rw O_CREAT mode" &&
  sModeRoCr.status == .Exception "unmodeled non-owner-rw O_CREAT mode" &&
  sModeZeroExist.status == .Running && sModeZeroExist.readReg64 .x0 == 5#64 &&
  sDotDot.status == .Exception "unmodeled '..' path component" &&
  rOk1 && rOk2 && rOk3 && rOk4 && rOk5 && rOk6 && rOk7 && rEmp && rDD

theorem process_model_gaps_conformance : checkProcessModelGapsConformance = true := by
  decide +kernel

theorem set_tid_address_and_sched_getaffinity_conformance :
    let mem0 := Memory.empty.mapZero 0x50000#64 0x1000
    let s0 : State := { mem := mem0 }
    let sTid := execSetTidAddress (s0.writeReg64 .x0 0#64)
    let sAff0 := execSchedGetaffinity
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 128#64).writeReg64 .x2 0x50000#64)
    let sAff1 := execSchedGetaffinity
      (((s0.writeReg64 .x0 1#64).writeReg64 .x1 8#64).writeReg64 .x2 0x50100#64)
    let sAffSmall := execSchedGetaffinity
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 4#64).writeReg64 .x2 0x50000#64)
    let sAffUnaligned := execSchedGetaffinity
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 12#64).writeReg64 .x2 0x50000#64)
    let sAffLen32Wrap := execSchedGetaffinity
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 0x1_0000_0000#64).writeReg64 .x2 0x50000#64)
    let sAffNegPid := execSchedGetaffinity
      (((s0.writeReg64 .x0 0xffffffff#64).writeReg64 .x1 8#64).writeReg64 .x2 0x50000#64)
    let sAffEfault := execSchedGetaffinity
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 8#64).writeReg64 .x2 0x90000#64)
    let sAffOtherPid := execSchedGetaffinity
      (((s0.writeReg64 .x0 2#64).writeReg64 .x1 8#64).writeReg64 .x2 0x50000#64)
    sTid.status = .Running ∧
    sTid.readReg64 .x0 = 1#64 ∧
    sAff0.status = .Running ∧
    sAff0.readReg64 .x0 = 8#64 ∧
    sAff0.mem.read64 0x50000#64 = 1#64 ∧
    sAff1.status = .Running ∧
    sAff1.readReg64 .x0 = 8#64 ∧
    sAff1.mem.read64 0x50100#64 = 1#64 ∧
    sAffSmall.readReg64 .x0 = -22#64 ∧
    sAffUnaligned.readReg64 .x0 = -22#64 ∧
    sAffLen32Wrap.readReg64 .x0 = -22#64 ∧
    sAffNegPid.readReg64 .x0 = -3#64 ∧
    sAffEfault.readReg64 .x0 = -14#64 ∧
    sAffOtherPid.status = .Exception "unmodeled sched_getaffinity pid" := by
  decide +kernel

/-- Kernel-checked conformance theorem for `getpid` (`172`), `gettid` (`178`),
    `rt_sigprocmask` (`135`), `rt_sigaction` (`134`), `tkill` (`130`), `tgkill` (`131`), and
    `ProcessOutcome.ofSignal` vs `ProcessOutcome.ofState`. -/
theorem abort_and_signal_syscalls_conformance :
    let mem0 := (((Memory.empty.mapZero 0x50000#64 0x1000).write64 0x50000#64 0xdeadbeefcafebabe#64
      ).write64 0x50400#64 0x40100#64
      ).write64 0x50408#64 0x200#64
    let memIgn := mem0.write64 0x50200#64 1#64
    let memCustom := mem0.write64 0x50300#64 0x4000#64
    let s0 : State := { mem := mem0 }
    let sPid := execSyscall (s0.writeReg64 .x8 SYS_GETPID)
    let sTid := execSyscall (s0.writeReg64 .x8 SYS_GETTID)
    -- rt_sigprocmask: empty / SIGKILL|SIGSTOP sets and SIG_UNBLOCK succeed & zero-fill oldset;
    -- non-zero blockable SIG_BLOCK / SIG_SETMASK fail closed with .Exception
    let sMaskOk := execRtSigprocmask
      ((((s0.writeReg64 .x0 0#64).writeReg64 .x1 0x50100#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sMaskKillStop := execRtSigprocmask
      ((((s0.writeReg64 .x0 0#64).writeReg64 .x1 0x50400#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sMaskUnblock := execRtSigprocmask
      ((((s0.writeReg64 .x0 1#64).writeReg64 .x1 0x50408#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sMaskBlockNonZero := execRtSigprocmask
      ((((s0.writeReg64 .x0 0#64).writeReg64 .x1 0x50408#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sMaskSetNonZero := execRtSigprocmask
      ((((s0.writeReg64 .x0 2#64).writeReg64 .x1 0x50408#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sMaskBadSz := execRtSigprocmask (s0.writeReg64 .x3 4#64)
    let sMaskBadHow := execRtSigprocmask
      (((s0.writeReg64 .x0 9#64).writeReg64 .x1 0x50408#64).writeReg64 .x3 8#64)
    let sMaskEfaultSet := execRtSigprocmask
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 0x90000#64).writeReg64 .x3 8#64)
    let sMaskWrapSet := execRtSigprocmask
      (((s0.writeReg64 .x0 0#64).writeReg64 .x1 0xfffffffffffffffc#64).writeReg64 .x3 8#64)
    let sMaskEfaultOld := execRtSigprocmask
      ((((s0.writeReg64 .x0 0#64).writeReg64 .x1 0#64).writeReg64 .x2 0x90000#64).writeReg64
        .x3 8#64)
    let sMaskWrapOld := execRtSigprocmask
      ((((s0.writeReg64 .x0 0#64).writeReg64 .x1 0#64).writeReg64 .x2 0xfffffffffffffffc#64).writeReg64
        .x3 8#64)
    -- rt_sigaction: SIG_DFL (0), SIG_IGN (1), NULL-act queries, and SIGSEGV/SIGBUS custom handlers succeed;
    -- custom handlers on other signals fail closed
    let sActOk := execRtSigaction
      ((((s0.writeReg64 .x0 6#64).writeReg64 .x1 0x50100#64).writeReg64 .x2 0x50000#64).writeReg64
        .x3 8#64)
    let sActOtherSig := execRtSigaction
      (((s0.writeReg64 .x0 11#64).writeReg64 .x1 0#64).writeReg64 .x3 8#64)
    let sActIgn := execRtSigaction
      ((((({ mem := memIgn } : State).writeReg64 .x0 13#64).writeReg64 .x1 0x50200#64).writeReg64
        .x2 0#64).writeReg64 .x3 8#64)
    let sActCustomSegv := execRtSigaction
      ((((({ mem := memCustom } : State).writeReg64 .x0 11#64).writeReg64 .x1 0x50300#64).writeReg64
        .x2 0#64).writeReg64 .x3 8#64)
    let sActCustomBus := execRtSigaction
      ((((({ mem := memCustom } : State).writeReg64 .x0 7#64).writeReg64 .x1 0x50300#64).writeReg64
        .x2 0#64).writeReg64 .x3 8#64)
    let sActCustomHandler := execRtSigaction
      ((((({ mem := memCustom } : State).writeReg64 .x0 15#64).writeReg64 .x1 0x50300#64).writeReg64
        .x2 0#64).writeReg64 .x3 8#64)
    -- tkill / tgkill: (1, 6) / (1, 1, 6) -> .Signaled 6#7; invalid -> -EINVAL; other -> .Exception
    let sTkillOk := execTkill ((s0.writeReg64 .x0 1#64).writeReg64 .x1 6#64)
    let sTgkillOk := execTgkill
      (((s0.writeReg64 .x0 1#64).writeReg64 .x1 1#64).writeReg64 .x2 6#64)
    let sTkillEinval := execTkill ((s0.writeReg64 .x0 0#64).writeReg64 .x1 6#64)
    let sTkillOtherTid := execTkill ((s0.writeReg64 .x0 2#64).writeReg64 .x1 6#64)
    let sTkillOtherSig := execTkill ((s0.writeReg64 .x0 1#64).writeReg64 .x1 9#64)
    let sTgkillOther := execTgkill
      (((s0.writeReg64 .x0 1#64).writeReg64 .x1 2#64).writeReg64 .x2 6#64)
    let outAbort := ProcessOutcome.ofTerminated? sTkillOk
    let outExit134 := ProcessOutcome.ofTerminated? (s0.setStatus (.Exited 134#64))
    sPid.readReg64 .x0 = 1#64 ∧
    sTid.readReg64 .x0 = 1#64 ∧
    sMaskOk.readReg64 .x0 = 0#64 ∧
    sMaskOk.mem.read64 0x50000#64 = 0#64 ∧
    sMaskKillStop.readReg64 .x0 = 0#64 ∧
    sMaskKillStop.mem.read64 0x50000#64 = 0#64 ∧
    sMaskUnblock.readReg64 .x0 = 0#64 ∧
    sMaskUnblock.mem.read64 0x50000#64 = 0#64 ∧
    sMaskBlockNonZero.status = .Exception "unmodeled non-zero signal mask in rt_sigprocmask" ∧
    sMaskSetNonZero.status = .Exception "unmodeled non-zero signal mask in rt_sigprocmask" ∧
    sMaskBadSz.readReg64 .x0 = -22#64 ∧
    sMaskBadHow.readReg64 .x0 = -22#64 ∧
    sMaskEfaultSet.readReg64 .x0 = -14#64 ∧
    sMaskWrapSet.readReg64 .x0 = -14#64 ∧
    sMaskEfaultOld.readReg64 .x0 = -14#64 ∧
    sMaskWrapOld.readReg64 .x0 = -14#64 ∧
    sActOk.readReg64 .x0 = 0#64 ∧
    sActOk.mem.read64 0x50000#64 = 0#64 ∧
    sActOtherSig.readReg64 .x0 = 0#64 ∧
    sActIgn.readReg64 .x0 = 0#64 ∧
    (sActIgn.getSigAction 13#32).handler = 1#64 ∧
    sActCustomSegv.readReg64 .x0 = 0#64 ∧
    (sActCustomSegv.getSigAction 11#32).handler = 0x4000#64 ∧
    sActCustomBus.readReg64 .x0 = 0#64 ∧
    (sActCustomBus.getSigAction 7#32).handler = 0x4000#64 ∧
    sActCustomHandler.status = .Exception "unmodeled rt_sigaction" ∧
    sTkillOk.status = .Signaled 6#7 ∧
    sTgkillOk.status = .Signaled 6#7 ∧
    sTkillEinval.readReg64 .x0 = -22#64 ∧
    sTkillOtherTid.status = .Exception "unmodeled tkill" ∧
    sTkillOtherSig.status = .Exception "unmodeled tkill" ∧
    sTgkillOther.status = .Exception "unmodeled tgkill" ∧
    ((match outAbort, outExit134 with
      | some oa, some oe =>
        oa.exitCode == 134#64 && oa.signal == some 6 &&
        oe.exitCode == 134#64 && oe.signal == none
      | _, _ => false) = true) := by
  decide +kernel

/-! ## Fail-Closed ELF64 Parser Negative Tests -/

def putU16LE (bs : ByteArray) (off : Nat) (v : Nat) : ByteArray :=
  let b0 := UInt8.ofNat (v % 256)
  let b1 := UInt8.ofNat ((v / 256) % 256)
  (bs.set! off b0).set! (off + 1) b1

def putU32LE (bs : ByteArray) (off : Nat) (v : Nat) : ByteArray :=
  let b0 := UInt8.ofNat (v % 256)
  let b1 := UInt8.ofNat ((v / 256) % 256)
  let b2 := UInt8.ofNat ((v / 65536) % 256)
  let b3 := UInt8.ofNat ((v / 16777216) % 256)
  (((bs.set! off b0).set! (off + 1) b1).set! (off + 2) b2).set! (off + 3) b3

def putU64LE (bs : ByteArray) (off : Nat) (v : Nat) : ByteArray :=
  let lo := putU32LE bs off (v % 4294967296)
  putU32LE lo (off + 4) (v / 4294967296)

/-- Minimal synthetic ELF64 `ET_EXEC` AArch64 image (`320` bytes, with `p_filesz = p_memsz = 256`
    and 64 trailing file bytes `[256, 320)` in the same page) used to mutate header fields for
    fail-closed negative tests and non-bss page-tail mapping tests. -/
def minimalValidElf : ByteArray :=
  let bs := ByteArray.mk (Array.replicate 320 0)
  -- ELF magic + ELFCLASS64 (2) + ELFDATA2LSB (1) + EV_CURRENT (1)
  let bs := ((((bs.set! 0 0x7f).set! 1 0x45).set! 2 0x4c).set! 3 0x46)
  let bs := ((bs.set! 4 2).set! 5 1).set! 6 1
  -- e_type = ET_EXEC (2), e_machine = EM_AARCH64 (183), e_version = 1
  let bs := putU16LE bs 16 2
  let bs := putU16LE bs 18 183
  let bs := putU32LE bs 20 1
  -- e_entry = 0x400080, e_phoff = 64, e_ehsize = 64, e_phentsize = 56, e_phnum = 1
  let bs := putU64LE bs 24 0x400080
  let bs := putU64LE bs 32 64
  let bs := putU16LE bs 52 64
  let bs := putU16LE bs 54 56
  let bs := putU16LE bs 56 1
  -- Program header 0 at offset 64: PT_LOAD (1), PF_R | PF_X (5), offset 0, vaddr 0x400000, filesz 256, memsz 256
  let bs := putU32LE bs 64 1
  let bs := putU32LE bs 68 5
  let bs := putU64LE bs 72 0
  let bs := putU64LE bs 80 0x400000
  let bs := putU64LE bs 96 256
  let bs := putU64LE bs 104 256
  bs

/-- Verify that `ElfImage.parseByteArray` accepts `minimalValidElf` and rejects malformed or
    unsupported ELF variants fail-closed. -/
def checkElfParserFailClosed : Bool :=
  let baseOk := (ElfImage.parseByteArray minimalValidElf).isOk
  let shortBad := !(ElfImage.parseByteArray (minimalValidElf.extract 0 32)).isOk
  let magicBad := !(ElfImage.parseByteArray (minimalValidElf.set! 0 0x00)).isOk
  let relBad := !(ElfImage.parseByteArray (putU16LE minimalValidElf 16 1)).isOk
  let pieBad := !(ElfImage.parseByteArray (putU16LE minimalValidElf 16 3)).isOk
  let archBad := !(ElfImage.parseByteArray (putU16LE minimalValidElf 18 62)).isOk
  let dynBad := !(ElfImage.parseByteArray (putU32LE minimalValidElf 64 2)).isOk
  let interpBad := !(ElfImage.parseByteArray (putU32LE minimalValidElf 64 3)).isOk
  let wxBad := !(ElfImage.parseByteArray (putU32LE minimalValidElf 68 7)).isOk
  let execStackElf := putU32LE (putU32LE minimalValidElf 64 0x6474e551) 68 7
  let execStackBad := !(ElfImage.parseByteArray execStackElf).isOk
  let roBssElf := putU64LE minimalValidElf 104 512
  let roBssBad := !(ElfImage.parseByteArray roBssElf).isOk
  -- Non-bss PT_LOAD (p_filesz == p_memsz = 256) maps trailing file bytes in the last page
  let nonBssTailElf := minimalValidElf.set! 300 0xab
  let nonBssTailOk :=
    match ElfImage.parseByteArray nonBssTailElf with
    | .ok img =>
      match img.segments with
      | [reg] => reg.bytes[300]? == some 0xab#8
      | _ => false
    | .error _ => false
  baseOk && shortBad && magicBad && relBad && pieBad && archBad && dynBad && interpBad &&
    wxBad && execStackBad && roBssBad && nonBssTailOk

theorem elf_parser_fail_closed_ok : checkElfParserFailClosed = true := by
  decide +kernel

/-! ## Static `echo_stdin.elf` and `abort_status.elf` Process Tests -/

requires_test_files ["fixtures/echo_stdin.elf"]

/-- Embedded `echo_stdin.elf` image (stock `zig cc -target aarch64-linux-musl -static`). -/
def echoStdinImg : ElfImage :=
  elf_image% "fixtures/echo_stdin.elf"

/-- Verify Linux AArch64 initial stack, `argv`, `envp`, `auxv`, and `fd 0/1/2` setup on
    `echo_stdin.elf`. -/
def checkInitialStackAndAuxv : Bool :=
  let inputs : ProcessInputs :=
    { argv  := [bytesOfString "echo_stdin", bytesOfString "-v"]
      envp  := [bytesOfString "LANG=C"]
      stdin := bytesOfString "abc" }
  match echoStdinImg.loadState inputs with
  | .error _ => false
  | .ok s0 =>
    let sp := s0.sp
    let argc := s0.mem.read64 sp
    let argv0Ptr := s0.mem.read64 (sp + 8#64)
    let argv1Ptr := s0.mem.read64 (sp + 16#64)
    let argvNull := s0.mem.read64 (sp + 24#64)
    let envp0Ptr := s0.mem.read64 (sp + 32#64)
    let envpNull := s0.mem.read64 (sp + 40#64)
    let aux0Tag  := s0.mem.read64 (sp + 48#64)
    let aux0Val  := s0.mem.read64 (sp + 56#64)
    s0.status == .Running &&
    s0.pc == echoStdinImg.entry &&
    sp.toNat % 16 == 0 &&
    s0.readReg64 .x0 == 0#64 &&
    s0.readReg64 .x29 == 0#64 &&
    s0.readReg64 .x30 == 0#64 &&
    argc == 2#64 &&
    s0.mem.readBytes argv0Ptr 11 == bytesOfString "echo_stdin" ++ [0#8] &&
    s0.mem.readBytes argv1Ptr 3 == bytesOfString "-v" ++ [0#8] &&
    argvNull == 0#64 &&
    s0.mem.readBytes envp0Ptr 7 == bytesOfString "LANG=C" ++ [0#8] &&
    envpNull == 0#64 &&
    aux0Tag == AuxvTag.phdr &&
    aux0Val == echoStdinImg.phdrVaddr &&
    s0.brkStart == echoStdinImg.brkStart &&
    s0.brk == echoStdinImg.brkStart

theorem initial_stack_and_auxv_ok : checkInitialStackAndAuxv = true := by
  decide +kernel

end_requires_test_files

/-- Convert each region's `List (BitVec 8)` to an `Array (BitVec 8)` once before constructing the
    memory lookup closure so LCNF does not re-materialize the `Array` on every byte read. -/
def mkRegionArrays (regions : List Snapshot.Region) :
    Array (BitVec 64 × Perm × Nat × Array (BitVec 8)) :=
  (regions.map fun r => (r.start, r.perm, r.nonAnonLen, r.bytes.toArray)).toArray

/-- `O(1)` array-backed version of `Snapshot.loadCellAt` over pre-materialized `mkRegionArrays`. -/
def fastCellAt (arrs : Array (BitVec 64 × Perm × Nat × Array (BitVec 8))) (a : BitVec 64) :
    Option (Option Perm × BitVec 8) :=
  arrs.findSome? fun (start, perm, nonAnonLen, bs) =>
    let i := (a - start).toNat
    if h : i < bs.size then
      let p := { perm with lazyFree := false, anon := if i < nonAnonLen then false else perm.anon }
      some (some p, bs[i])
    else none

/-- `fastCellAt (mkRegionArrays regions)` is extensionally equal to `Snapshot.loadCellAt regions`. -/
theorem fastCellAt_mkRegionArrays_eq (regions : List Snapshot.Region) :
    fastCellAt (mkRegionArrays regions) = Snapshot.loadCellAt regions := by
  funext a
  rw [fastCellAt, mkRegionArrays, List.findSome?_toArray, List.findSome?_map, Snapshot.loadCellAt]
  congr 1

/-- `ElfImage.loadState` using `fastWellFormed` and pre-materialized `Array`-backed initial segment
    lookup (`loadStateArrayBacked_eq`), avoiding repeated `List.length` / `List` indexing on large
    static ELF segments while producing the exact same `State` (`=`) as `img.loadState inputs`. -/
def loadStateArrayBacked (img : ElfImage) (inputs : ProcessInputs := {}) : Except String State := do
  if !fastWellFormed img then
    .error "ElfImage.loadState: image is not WellFormed"
  if inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) then
    .error "ElfImage.loadState: inputs.dirs paths must be relative without '..'"
  if inputs.files.any (fun (p, bs) => hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ Arm64.MAX_LFS_FILESIZE)) then
    .error "ElfImage.loadState: inputs.files paths must be relative without '..' and size <= MAX_LFS_FILESIZE"
  let (sp, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let regArrs := mkRegionArrays (img.segments ++ [stackRegion])
  let baseMem : Memory := ⟨fastCellAt regArrs⟩
  let mem := baseMem.mapZero stackBase inputs.init.stackSize
  let symtab : String → String → Option (BitVec 64) :=
    fun _ name => (img.symbols.find? (·.1 == name)).map (·.2)
  pure {
    regs         := RegFile.empty
    vregs        := VRegFile.empty
    sp           := sp
    pc           := img.entry
    pstate       := PState.zero
    mem          := mem
    tpidrEl0     := 0#64
    brkStart     := img.brkStart
    brk          := img.brkStart
    physMemAvail := inputs.init.physMemAvail
    fs           := initFsState inputs
    oracle       := inputs.init.oracle
    oracleIdx    := 0
    exclFails    := inputs.init.oracle.exclFails
    trace        := []
    status       := .Running
    symtab       := symtab }

theorem loadStateArrayBacked_eq (img : ElfImage) (inputs : ProcessInputs) :
    loadStateArrayBacked img inputs = img.loadState inputs := by
  dsimp only [loadStateArrayBacked, ElfImage.loadState]
  rw [fastWellFormed_eq]
  simp only [fastCellAt_mkRegionArrays_eq]

/-- Unaccelerated `runStepsPure` reference runner initialized from `loadStateArrayBacked`,
    kernel-proved equal to `runElfImage fuel img inputs Program.pureMem`. -/
def runElfImageRefArrayBacked (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs := {}) :
    Except String (State × Option ProcessOutcome) := do
  let s0 ← loadStateArrayBacked img inputs
  let sf := runStepsPure fuel s0
  pure (sf, ProcessOutcome.ofTerminated? sf)

theorem runElfImageRefArrayBacked_eq (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs) :
    runElfImageRefArrayBacked fuel img inputs = runElfImage fuel img inputs Program.pureMem := by
  rw [← runElfImagePure_eq, runElfImageRefArrayBacked, runElfImagePure, loadStateArrayBacked_eq]

/-- All Linux AArch64 syscalls handled by `Arm64.execSyscall` (`Arm64/Trusted/Syscalls.lean`). -/
inductive ModeledSyscall where
  | fcntl | ioctl | openat | close | lseek
  | read | write | readv | writev | pread64 | ppoll | fstat
  | exit | exitGroup | setTidAddress
  | getpid | gettid | sigaltstack | rtSigprocmask | rtSigaction | tkill | tgkill
  | clockGettime | schedGetaffinity
  | brk | munmap | mremap | mmap | mprotect | madvise | getrandom
  deriving DecidableEq, Repr

/-- Decode a 64-bit Linux AArch64 syscall number `nr` into `ModeledSyscall` if handled by
    `Arm64.execSyscall`. -/
def ModeledSyscall.ofNr? (nr : BitVec 64) : Option ModeledSyscall :=
  if nr == SYS_FCNTL then some .fcntl
  else if nr == SYS_IOCTL then some .ioctl
  else if nr == SYS_OPENAT then some .openat
  else if nr == SYS_CLOSE then some .close
  else if nr == SYS_LSEEK then some .lseek
  else if nr == SYS_READ then some .read
  else if nr == SYS_WRITE then some .write
  else if nr == SYS_READV then some .readv
  else if nr == SYS_WRITEV then some .writev
  else if nr == SYS_PREAD64 then some .pread64
  else if nr == SYS_PPOLL then some .ppoll
  else if nr == SYS_FSTAT then some .fstat
  else if nr == SYS_EXIT then some .exit
  else if nr == SYS_EXIT_GROUP then some .exitGroup
  else if nr == SYS_SET_TID_ADDRESS then some .setTidAddress
  else if nr == SYS_GETPID then some .getpid
  else if nr == SYS_GETTID then some .gettid
  else if nr == SYS_SIGALTSTACK then some .sigaltstack
  else if nr == SYS_RT_SIGPROCMASK then some .rtSigprocmask
  else if nr == SYS_RT_SIGACTION then some .rtSigaction
  else if nr == SYS_TKILL then some .tkill
  else if nr == SYS_TGKILL then some .tgkill
  else if nr == SYS_CLOCK_GETTIME then some .clockGettime
  else if nr == SYS_SCHED_GETAFFINITY then some .schedGetaffinity
  else if nr == SYS_BRK then some .brk
  else if nr == SYS_MUNMAP then some .munmap
  else if nr == SYS_MREMAP then some .mremap
  else if nr == SYS_MMAP then some .mmap
  else if nr == SYS_MPROTECT then some .mprotect
  else if nr == SYS_MADVISE then some .madvise
  else if nr == SYS_GETRANDOM then some .getrandom
  else none

/-- Verify that every syscall number `nr < 512` dispatched by `Arm64.execSyscall` is decoded by
    `ModeledSyscall.ofNr?`, so adding a new syscall to `execSyscall` without adding a constructor to
    `ModeledSyscall` (and handling it in the wildcard-free `syscallWriteRanges` match) causes a
    compile-time failure here. -/
def checkKnownSyscallsExhaustive : Bool :=
  (List.range 512).all fun n =>
    let nr := BitVec.ofNat 64 n
    let st := (execSyscall (({} : State).writeReg64 .x8 nr)).status
    (st != .Exception "unmodeled syscall (svc)") == (ModeledSyscall.ofNr? nr).isSome

theorem known_syscalls_exhaustive : checkKnownSyscallsExhaustive = true := by
  decide +kernel

/-- `(base, len)` of the first `n` iovecs (16-byte `{iov_base, iov_len}` records) at `vec` in `m`,
    with lengths clipped so that they sum to at most `budget` bytes (the bytes a vectored read
    filled, in segment order). -/
def iovFilledRanges (m : Memory) (vec : BitVec 64) : Nat → Nat → List (BitVec 64 × Nat)
  | 0, _ => []
  | _, 0 => []
  | n + 1, budget + 1 =>
    let len := min (m.read64 (vec + 8#64)).toNat (budget + 1)
    (m.read64 vec, len) :: iovFilledRanges m (vec + 16#64) n (budget + 1 - len)

/-- Return the `(base, len)` address ranges that `execSyscall s = s'` may have modified in
    `s'.mem` when `s'.status == .Running`.

    This match over `ModeledSyscall` has no wildcard catch-all, so adding a new constructor to
    `ModeledSyscall` fails to compile until its memory-write behavior is classified here. -/
def syscallWriteRanges (sc : ModeledSyscall) (s s' : State) : List (BitVec 64 × Nat) :=
  let ret := s'.readReg64 .x0
  match sc with
  | .read | .pread64 =>
    if ret.slt 0#64 || ret == 0#64 then [] else [(s.readReg64 .x1, ret.toNat)]
  | .readv =>
    if ret.slt 0#64 || ret == 0#64 then []
    else iovFilledRanges s.mem (s.readReg64 .x1) (s.readReg32 .x2).toNat ret.toNat
  | .ppoll =>
    if ret.slt 0#64 then [] else [(s.readReg64 .x0, (s.readReg32 .x1).toNat * 8)]
  | .fstat =>
    if ret.slt 0#64 then [] else [(s.readReg64 .x1, 128)]
  | .schedGetaffinity =>
    if ret.slt 0#64 then [] else [(s.readReg64 .x2, 8)]
  | .sigaltstack =>
    if ret.slt 0#64 || s.readReg64 .x1 == 0#64 then [] else [(s.readReg64 .x1, 24)]
  | .rtSigprocmask =>
    if ret.slt 0#64 || s.readReg64 .x2 == 0#64 then [] else [(s.readReg64 .x2, 8)]
  | .rtSigaction =>
    if ret.slt 0#64 || s.readReg64 .x2 == 0#64 then [] else [(s.readReg64 .x2, 32)]
  | .clockGettime =>
    if ret.slt 0#64 then [] else [(s.readReg64 .x1, 16)]
  | .getrandom =>
    if ret.slt 0#64 || ret == 0#64 then [] else [(s.readReg64 .x0, ret.toNat)]
  | .brk =>
    if s'.brk == s.brk then []
    else
      let oldPage := Arm64.pageAlignUp s.brk.toNat
      let newPage := Arm64.pageAlignUp s'.brk.toNat
      if oldPage < newPage then
        [(BitVec.ofNat 64 oldPage, newPage - oldPage)]
      else if newPage < oldPage then
        [(BitVec.ofNat 64 newPage, oldPage - newPage)]
      else []
  | .mmap =>
    if ret.slt 0#64 then [] else [(ret, Arm64.pageAlignUp (s.readReg64 .x1).toNat)]
  | .mremap =>
    if ret.slt 0#64 then []
    else [(s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat),
          (ret, Arm64.pageAlignUp (s.readReg64 .x2).toNat)]
  | .munmap | .mprotect | .madvise =>
    if ret.slt 0#64 then [] else [(s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat)]
  | .ioctl =>
    if ret.slt 0#64 || s.readReg32 .x1 != FIONREAD_W32 then [] else [(s.readReg64 .x2, 4)]
  | .fcntl | .openat | .close | .lseek | .write | .writev | .exit | .exitGroup
  | .setTidAddress
  | .getpid | .gettid | .tkill | .tgkill =>
    []

/-- Return the `(base, len)` address ranges that `execInst inst s = s'` may have modified in
    `s'.mem` when `s'.status == .Running`.

    This match is intentionally exhaustive over every `Instr` constructor (no wildcard catch-all)
    so adding a new instruction constructor to `Arm64.Instr` fails to compile until its memory
    write behavior is classified here. -/
def instWriteRanges (inst : Instr) (s s' : State) : List (BitVec 64 × Nat) :=
  match inst with
  | .str msz _ dst =>
    let (ea, _) := evalAddrMode s dst
    [(ea, msz.bytes)]
  | .stp w _ _ dst =>
    let (ea, _) := evalAddrMode s dst
    [(ea, 2 * (w : MemWidth).bytes)]
  | .strSimd sz _ addr =>
    let (ea, _) := evalAddrMode s addr
    [(ea, sz.bytes)]
  | .stpSimd sz _ _ addr =>
    let (ea, _) := evalAddrMode s addr
    [(ea, 2 * sz.bytes)]
  | .stnp sz rn _ _ offset =>
    [(s.readReg64 rn + offset, 2 * sz.bytes)]
  | .stnpSimd sz _ _ rn offset =>
    [(s.readReg64 rn + offset, 2 * sz.bytes)]
  | .st1SinglePost _ _ opcode _ size rn _ =>
    let opcHi := opcode.extractLsb' 1 2
    let nbytes : Nat :=
      if opcHi == 0#2 then 1 else if opcHi == 1#2 then 2
      else if (size.extractLsb' 0 1) == 0#1 then 4 else 8
    [(s.readReg64 rn, nbytes)]
  | .simdLdSt1Single isLoad _ _ _ opcode _ size rn _ =>
    if isLoad then [] else
      let opcHi := opcode.extractLsb' 1 2
      let nbytes : Nat :=
        if opcHi == 0#2 then 1 else if opcHi == 1#2 then 2
        else if (size.extractLsb' 0 1) == 0#1 then 4 else 8
      [(s.readReg64 rn, nbytes)]
  | .simdLdSt1Multi isLoad q _ nregs rn _ _ _ =>
    if isLoad then [] else [(s.readReg64 rn, nregs * (SimdMemSize.ofQ q).bytes)]
  | .simdLdStMulti isLoad q _ selem rn _ _ _ =>
    if isLoad then [] else [(s.readReg64 rn, selem * (SimdMemSize.ofQ q).bytes)]
  | .dcZva rt =>
    [(s.readReg64 rt &&& ~~~63#64, 64)]
  | .ldarStlr sz isLoad rn _ =>
    if isLoad then [] else [(s.readReg64 rn, sz.bytes)]
  | .stxr sz _ _ rn _
  | .cas sz _ _ _ rn _
  | .atomicRmw _ sz _ _ _ rn _ =>
    [(s.readReg64 rn, sz.bytes)]
  | .stxp sz _ _ rn _ _
  | .casp sz _ _ _ _ rn _ _ =>
    [(s.readReg64 rn, 2 * sz.bytes)]
  | .ldapurStlur sz opc rn _ offset =>
    if opc == 0#2 then [(s.readReg64 rn + offset, sz.bytes)] else []
  | .system isHalt imm =>
    if isHalt || imm != 0#16 then
      []
    else
      match ModeledSyscall.ofNr? (s.readReg64 .x8) with
      | some sc => syscallWriteRanges sc s s'
      | none    => []
  -- Non-memory-writing instructions (explicitly enumerated with no wildcard):
  | .ldr _ _ _ _ _ | .ldrLit _ _ _ _ | .ldp _ _ _ _ _
  | .addSubImm _ _ _ _ _ _ | .addSubShift _ _ _ _ _ _ _ | .addSubExt _ _ _ _ _ _ _
  | .addSubCarry _ _ _ _ _ | .dataProc1 _ _ _ _ | .dataProc2 _ _ _ _ _ | .dataProc3 _ _ _ _ _ _
  | .logicalImm _ _ _ _ _ | .logicalShift _ _ _ _ _ _ _ | .moveWide _ _ _ _ _
  | .bitfield _ _ _ _ _ _ | .extr _ _ _ _ _
  | .condSelect _ _ _ _ _ _ | .condCompareReg _ _ _ _ _ _ | .condCompareImm _ _ _ _ _ _
  | .adr _ _ _ | .b _ | .bl _ | .bCond _ _ | .br _ | .blr _ | .ret _
  | .cbz _ _ _ _ | .tbz _ _ _ _ _ | .nop
  | .ldxr _ _ _ _ | .sysReg _ _ _ | .barrier _ _
  | .ldpSimd _ _ _ _ | .ldrSimd _ _ _
  | .aes _ _ _ | .fmovGprVec _ _ _ _ _ _
  | .simdImmShift _ _ _ _ _ _ _ | .simdInsDup _ _ _ _ _ _
  | .simdThreeSame _ _ _ _ _ _ _ | .simdTwoRegMisc _ _ _ _ _ _
  | .simdAcrossLanes _ _ _ _ _ _ | .simdPermute _ _ _ _ _ _
  | .simdExt _ _ _ _ _
  | .fpDataProc1 _ _ _ _ | .fpDataProc2 _ _ _ _ _
  | .fpCompare _ _ _ _ _ | .fpImm _ _ _
  | .fpCondCompare _ _ _ _ _ _ | .fpCondSelect _ _ _ _ _
  | .fpDataProc3 _ _ _ _ _ _ _ | .fpFixedConv _ _ _ _ _ _ _
  | .ldxp _ _ _ _ _ | .ldapr _ _ _
  | .hint _ | .prfm _ _ | .prfmLit _ _
  | .ldrSimdLit _ _ _ | .ldnp _ _ _ _ _ | .ldnpSimd _ _ _ _ _
  | .crc32 _ _ _ _ _ | .simdTbl _ _ _ _ _ _ | .simdAddpScalar _ _
  | .simdLd1r _ _ _ _ _ _ | .udf _ | .simdPmull _ _ _ _ _
  | .simdDupScalar _ _ _ | .simdThreeDiff _ _ _ _ _ _ _
  | .cryptoSha2Reg _ _ _ | .cryptoSha3Reg _ _ _ _
  | .cryptoSha512Reg2 _ _ | .cryptoSha512Reg3 _ _ _ _
  | .cryptoSha3FourReg _ _ _ _ _ | .cryptoXar _ _ _ _ => []

/-- Compact `s.regs` and `s.vregs` into flat 32-element `Array`s so register-update closure
    chains stay bounded. -/
def compactRegs (s : State) : State :=
  let gprs : Array (BitVec 64) := Array.ofFn fun (i : Fin 32) => s.regs.regs (BitVec.ofNat 5 i.val)
  let vecs : Array (BitVec 128) := Array.ofFn fun (i : Fin 32) => s.vregs.regs (BitVec.ofNat 5 i.val)
  { s with
    regs  := ⟨fun i => gprs[i.toNat]'(by rw [Array.size_ofFn]; exact i.isLt)⟩
    vregs := ⟨fun i => vecs[i.toNat]'(by rw [Array.size_ofFn]; exact i.isLt)⟩ }

/-- Construct a flat-array-backed `Memory` over `[rwBase, rwCapEnd)` (`rwArr`) and
    `[stackBase, stackTop)` (`stkArr`), falling back to `baseMem` outside those ranges. -/
def mkFastMem (baseMem : Memory) (rwBase rwCapEnd stackBase stackTop : BitVec 64)
    (rwArr stkArr : Array (Option (Option Perm × BitVec 8))) : Memory :=
  ⟨fun a =>
    if rwBase ≤ a && a < rwCapEnd then
      let i := (a - rwBase).toNat
      if h : i < rwArr.size then rwArr[i] else baseMem.cells a
    else if stackBase ≤ a && a < stackTop then
      let i := (a - stackBase).toNat
      if h : i < stkArr.size then stkArr[i] else baseMem.cells a
    else
      baseMem.cells a⟩

/-- Execute one instruction from `s`. If `s.pc` cannot be fetched, transitions `s` to `.Halted`
    (matching `ProofLib.stepState Program.pureMem` and `Step.halt_unmapped`). If the instruction
    modified `s.mem` and remains `.Running`, extract the updated `(ea, cells)` slices and replace
    `s'.mem` with `Memory.empty` before returning so that the caller's `rwArr` and `stkArr`
    references are unique (`RC = 1`) for in-place `Array.set!`. -/
@[noinline] def stepAndExtractPatches (s : State) :
    State × List (BitVec 64 × Array (Option (Option Perm × BitVec 8))) :=
  match Program.pureMem.fetchMem s.mem s.pc with
  | none => ({ s with status := .Halted }, [])
  | some inst =>
    let s' := execInst inst s
    if s'.status != .Running then
      (s', [])
    else
      let ranges := instWriteRanges inst s s'
      if ranges.isEmpty then
        (s', [])
      else
        let patches := ranges.map fun (ea, len) =>
          (ea, Array.ofFn fun (i : Fin len) => s'.mem.cells (ea + BitVec.ofNat 64 i.val))
        ({ s' with mem := Memory.empty }, patches)

/-- Apply extracted byte patches in-place to `(rwArr, stkArr, baseMem)`. -/
def applyMemPatches (rwBase rwCapEnd stackBase stackTop : BitVec 64)
    (rwArr stkArr : Array (Option (Option Perm × BitVec 8))) (baseMem : Memory)
    (patches : List (BitVec 64 × Array (Option (Option Perm × BitVec 8)))) :
    Array (Option (Option Perm × BitVec 8)) × Array (Option (Option Perm × BitVec 8)) × Memory :=
  Id.run do
    let mut rw := rwArr
    let mut stk := stkArr
    let mut bm := baseMem
    for (ea, cells) in patches do
      for j in [0:cells.size] do
        let a := ea + BitVec.ofNat 64 j
        let c := cells[j]!
        if rwBase ≤ a && a < rwCapEnd then
          rw := rw.set! (a - rwBase).toNat c
        else if stackBase ≤ a && a < stackTop then
          stk := stk.set! (a - stackBase).toNat c
        else
          let prev := bm
          bm := ⟨fun q => if q == a then c else prev.cells q⟩
    return (rw, stk, bm)

/-- Run `img` with incremental array-backed memory and periodic register compaction for large
    binaries. -/
def runElfImageFast (chunks chunkSteps : Nat) (img : ElfImage) (inputs : ProcessInputs := {})
    (extraRwBytes : Nat := 512 * 1024) :
    Except String (State × Option ProcessOutcome) := do
  let s0 ← loadStateArrayBacked img inputs
  let (_, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let stackTop := inputs.init.stackTop
  let regArrs := mkRegionArrays (img.segments ++ [stackRegion])
  let rawBaseMem : Memory := ⟨fastCellAt regArrs⟩
  let s0Mem := rawBaseMem.mapZero stackBase inputs.init.stackSize
  let rwBase :=
    match img.segments.find? (fun seg => seg.perm == Perm.rw) with
    | some seg => seg.start
    | none     => img.brkStart
  let initRwLen :=
    let brkPage := Arm64.pageAlignUp img.brkStart.toNat
    if brkPage > rwBase.toNat then brkPage - rwBase.toNat else 0
  let rwCapLen := initRwLen + extraRwBytes
  let rwCapEnd := rwBase + BitVec.ofNat 64 rwCapLen
  let rwArrInit : Array (Option (Option Perm × BitVec 8)) :=
    Array.ofFn fun (i : Fin rwCapLen) =>
      if i.val < initRwLen || rwCapEnd > stackBase then
        s0Mem.cells (rwBase + BitVec.ofNat 64 i.val)
      else
        none
  -- Materialize only the active top-of-stack window `[stkFastBase, stackTop)` in `stkArr`; lower
  -- stack pages in `[stackBase, stkFastBase)` remain lazily backed by `s0Mem` / `baseMem` so
  -- initialization and array updates do not scale with the 8 MiB `defaultStackSize`.
  let stkFrameLen := inputs.init.stackTop.toNat - s0.sp.toNat
  let stkLen := Nat.min inputs.init.stackSize
    (Nat.max (64 * 1024) (Arm64.pageAlignUp (stkFrameLen + 32 * 1024)))
  let stkFastBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - stkLen)
  let stkArrInit : Array (Option (Option Perm × BitVec 8)) :=
    Array.ofFn fun (i : Fin stkLen) => s0Mem.cells (stkFastBase + BitVec.ofNat 64 i.val)
  let memInit := mkFastMem s0Mem rwBase rwCapEnd stkFastBase stackTop rwArrInit stkArrInit
  let sInit := compactRegs { s0 with mem := memInit }
  let totalSteps := chunks * chunkSteps
  let rec loop (fuel : Nat) (s : State)
      (rwArr stkArr : Array (Option (Option Perm × BitVec 8))) (baseMem : Memory) : State :=
    match fuel with
    | 0 => s
    | k + 1 =>
      if s.status != .Running then
        s
      else
        let s1 := if k % 64 == 0 then compactRegs s else s
        let (s2, patches) := stepAndExtractPatches s1
        if patches.isEmpty then
          loop k s2 rwArr stkArr baseMem
        else
          let (rwArr', stkArr', baseMem') :=
            applyMemPatches rwBase rwCapEnd stkFastBase stackTop rwArr stkArr baseMem patches
          let mem' := mkFastMem baseMem' rwBase rwCapEnd stkFastBase stackTop rwArr' stkArr'
          loop k { s2 with mem := mem' } rwArr' stkArr' baseMem'
  let sf := loop totalSteps sInit rwArrInit stkArrInit s0Mem
  pure (sf, ProcessOutcome.ofTerminated? sf)

/-- Flat-array + `Std.HashMap` memory representation so loads/stores across `.data`/`.bss`/`brk`,
    the initial user stack, and anonymous `SYS_mmap` / `SYS_munmap` / `SYS_mremap` pages all run in
    `O(1)` without nested function-closure chains. -/
def mkFastMemMmap (baseMem : Memory) (rwBase rwCapEnd stackBase stackTop : BitVec 64)
    (rwArr stkArr : Array (Option (Option Perm × BitVec 8)))
    (extraMap : Std.HashMap UInt64 (Option (Option Perm × BitVec 8))) : Memory :=
  ⟨fun a =>
    if rwBase ≤ a && a < rwCapEnd then
      let i := (a - rwBase).toNat
      if h : i < rwArr.size then rwArr[i] else baseMem.cells a
    else if stackBase ≤ a && a < stackTop then
      let i := (a - stackBase).toNat
      if h : i < stkArr.size then stkArr[i] else baseMem.cells a
    else
      match extraMap[a.toNat.toUInt64]? with
      | some cell => cell
      | none      => baseMem.cells a⟩

def applyMemPatchesMmap (rwBase rwCapEnd stackBase stackTop : BitVec 64)
    (rwArr stkArr : Array (Option (Option Perm × BitVec 8)))
    (extraMap : Std.HashMap UInt64 (Option (Option Perm × BitVec 8)))
    (patches : List (BitVec 64 × Array (Option (Option Perm × BitVec 8)))) :
    Array (Option (Option Perm × BitVec 8)) ×
      Array (Option (Option Perm × BitVec 8)) ×
      Std.HashMap UInt64 (Option (Option Perm × BitVec 8)) :=
  Id.run do
    let mut rw := rwArr
    let mut stk := stkArr
    let mut extra := extraMap
    for (ea, cells) in patches do
      for j in [0:cells.size] do
        let a := ea + BitVec.ofNat 64 j
        let c := cells[j]!
        if rwBase ≤ a && a < rwCapEnd then
          rw := rw.set! (a - rwBase).toNat c
        else if stackBase ≤ a && a < stackTop then
          stk := stk.set! (a - stackBase).toNat c
        else
          extra := extra.insert a.toNat.toUInt64 c
    return (rw, stk, extra)

/-- Execute `img` up to `maxSteps` instructions using flat arrays for `brk`/stack and a
    `Std.HashMap` for anonymous `SYS_mmap` / `SYS_munmap` / `SYS_mremap` regions. -/
def runElfImageFastMmap (maxSteps : Nat) (img : ElfImage) (inputs : ProcessInputs := {}) :
    Except String (State × Option ProcessOutcome) := do
  let s0 ← loadStateArrayBacked img inputs
  let (_, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let stackTop := inputs.init.stackTop
  let regArrs := mkRegionArrays (img.segments ++ [stackRegion])
  let rawBaseMem : Memory := ⟨fastCellAt regArrs⟩
  let s0Mem := rawBaseMem.mapZero stackBase inputs.init.stackSize
  let rwBase :=
    match img.segments.find? (fun seg => seg.perm == Perm.rw) with
    | some seg => seg.start
    | none     => img.brkStart
  let initRwLen :=
    let brkPage := Arm64.pageAlignUp img.brkStart.toNat
    if brkPage > rwBase.toNat then brkPage - rwBase.toNat else 0
  let rwCapLen := initRwLen + 1024 * 1024
  let rwCapEnd := rwBase + BitVec.ofNat 64 rwCapLen
  let rwArrInit : Array (Option (Option Perm × BitVec 8)) :=
    Array.ofFn fun (i : Fin rwCapLen) =>
      if i.val < initRwLen || rwCapEnd > stackBase then
        s0Mem.cells (rwBase + BitVec.ofNat 64 i.val)
      else
        none
  let stkFrameLen := inputs.init.stackTop.toNat - s0.sp.toNat
  let stkLen := Nat.min inputs.init.stackSize
    (Nat.max (64 * 1024) (Arm64.pageAlignUp (stkFrameLen + 32 * 1024)))
  let stkFastBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - stkLen)
  let stkArrInit : Array (Option (Option Perm × BitVec 8)) :=
    Array.ofFn fun (i : Fin stkLen) => s0Mem.cells (stkFastBase + BitVec.ofNat 64 i.val)
  let extraInit : Std.HashMap UInt64 (Option (Option Perm × BitVec 8)) := {}
  let memInit := mkFastMemMmap s0Mem rwBase rwCapEnd stkFastBase stackTop rwArrInit stkArrInit extraInit
  let sInit := compactRegs { s0 with mem := memInit }
  let rec loop (fuel : Nat) (s : State)
      (rwArr stkArr : Array (Option (Option Perm × BitVec 8)))
      (extraMap : Std.HashMap UInt64 (Option (Option Perm × BitVec 8))) : State :=
    match fuel with
    | 0 => s
    | k + 1 =>
      if s.status != .Running then
        s
      else
        let s1 := if k % 64 == 0 then compactRegs s else s
        let (s2, patches) := stepAndExtractPatches s1
        if patches.isEmpty then
          loop k s2 rwArr stkArr extraMap
        else
          let (rwArr', stkArr', extraMap') :=
            applyMemPatchesMmap rwBase rwCapEnd stkFastBase stackTop rwArr stkArr extraMap patches
          let mem' :=
            mkFastMemMmap s0Mem rwBase rwCapEnd stkFastBase stackTop rwArr' stkArr' extraMap'
          loop k { s2 with mem := mem' } rwArr' stkArr' extraMap'
  let sf := loop maxSteps sInit rwArrInit stkArrInit extraInit
  pure (sf, ProcessOutcome.ofTerminated? sf)

/-- Check whether `m1.cells` and `m2.cells` agree on every byte in `[base, base + len)`. -/
def memRangeCellsEq (m1 m2 : Memory) (base : BitVec 64) (len : Nat) : Bool :=
  (List.range len).all fun i =>
    let a := base + BitVec.ofNat 64 i
    m1.cells a == m2.cells a

requires_test_files ["fixtures/echo_stdin.elf"]

set_option compiler.extract_closed false in
/-- Execute `echo_stdin.elf` end-to-end from `crt1.o` `_start` through `__libc_start_main` and
    `main` to `SYS_exit_group(0)` across multiple `stdin` payloads. -/
def checkEchoStdinProcess (_ : Unit := ()) : Bool :=
  let payloads : List (List (BitVec 8)) :=
    [ [],
      bytesOfString "hello stock musl process!\n",
      [0x00#8, 0x01#8, 0x7f#8, 0x80#8, 0xff#8, 0x42#8] ]
  payloads.all fun msg =>
    match runElfImageFast 20 256 echoStdinImg { stdin := msg } with
    | .ok (_, some out) => out.exitCode == 0#64 && out.stdout == msg && out.stderr == []
    | _ => false

set_option compiler.extract_closed false in
/-- Cross-check `runElfImageFast` against the reference `runElfImage` (`runSteps Program.pureMem`)
    on `echo_stdin.elf`: verify that final `ProcessOutcome`, `status`, `pc`, `sp`, `pstate`,
    `tpidrEl0`, `brkStart`, `brk`, `fds`, `fs`, `oracleIdx`, all 32 GPRs, all 32 SIMD/FP VRegs,
    and all memory cells across every loaded ELF segment, `[brkStart, pageAlignUp brk)`, and the
    stack `[stackBase, stackTop)` are identical, and that an unmapped instruction fetch transitions
    both runners to `.Halted` (`Step.halt_unmapped`). -/
def checkEchoStdinFastVsRef (_ : Unit := ()) : Bool :=
  let msg := bytesOfString "hello stock musl process!\n"
  let inputs : ProcessInputs :=
    { argv  := [bytesOfString "echo_stdin"]
      envp  := [bytesOfString "LANG=C"]
      stdin := msg
      init  := { stackSize := 8192 } }
  let haltEntry :=
    match echoStdinImg.segments.find? (fun seg => seg.perm.x) with
    | some seg => seg.start + BitVec.ofNat 64 (seg.bytes.length - 4)
    | none     => echoStdinImg.entry
  let haltImg := { echoStdinImg with entry := haltEntry }
  let unmappedHaltEq :=
    match runElfImageFast 1 16 haltImg inputs, runElfImagePure 16 haltImg inputs with
    | .ok (sFastH, none), .ok (sRefH, none) =>
      sFastH.status == .Halted &&
      sRefH.status == .Halted &&
      sFastH.pc == sRefH.pc &&
      sFastH.sp == sRefH.sp
    | _, _ => false
  match runElfImageFast 20 256 echoStdinImg inputs, runElfImagePure 5000 echoStdinImg inputs with
  | .ok (sFast, some outFast), .ok (sRef, some outRef) =>
    let gprsEq := (List.range 32).all fun i =>
      sFast.regs.regs (BitVec.ofNat 5 i) == sRef.regs.regs (BitVec.ofNat 5 i)
    let vregsEq := (List.range 32).all fun i =>
      sFast.vregs.regs (BitVec.ofNat 5 i) == sRef.vregs.regs (BitVec.ofNat 5 i)
    let segsEq := echoStdinImg.segments.all fun seg =>
      memRangeCellsEq sFast.mem sRef.mem seg.start seg.bytes.length
    let brkEndNat := Arm64.pageAlignUp sRef.brk.toNat
    let brkLen := if brkEndNat > echoStdinImg.brkStart.toNat then
      brkEndNat - echoStdinImg.brkStart.toNat else 0
    let brkEq := memRangeCellsEq sFast.mem sRef.mem echoStdinImg.brkStart brkLen
    let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
    let stackEq := memRangeCellsEq sFast.mem sRef.mem stackBase inputs.init.stackSize
    let fdsEq := (List.range 16).all fun fd =>
      sFast.fs.fds (BitVec.ofNat 64 fd) == sRef.fs.fds (BitVec.ofNat 64 fd)
    -- Also run with the default 8 MiB stack (`defaultStackSize`) so the below-window
    -- (`[stackBase, stkFastBase)`) fallback in `mkFastMem` and `applyMemPatches` is diffed
    -- against `runElfImagePure` across both untouched zero pages and below-window stores/loads.
    let defInputs : ProcessInputs :=
      { argv  := [bytesOfString "echo_stdin"]
        envp  := [bytesOfString "LANG=C"]
        stdin := msg }
    let defStackEq :=
      match runElfImageFast 20 256 echoStdinImg defInputs,
            runElfImagePure 5000 echoStdinImg defInputs with
      | .ok (sFastD, some outFastD), .ok (sRefD, some outRefD) =>
        let defStackBase := BitVec.ofNat 64 (defInputs.init.stackTop.toNat - defInputs.init.stackSize)
        let stkFrameLen := defInputs.init.stackTop.toNat - sRefD.sp.toNat
        let stkLen := Nat.min defInputs.init.stackSize
          (Nat.max (64 * 1024) (Arm64.pageAlignUp (stkFrameLen + 32 * 1024)))
        let stkFastBase := BitVec.ofNat 64 (defInputs.init.stackTop.toNat - stkLen)
        outFastD.exitCode == outRefD.exitCode &&
        outFastD.stdout == outRefD.stdout &&
        outFastD.stderr == outRefD.stderr &&
        outFastD.exitCode == 0#64 &&
        outFastD.stdout == msg &&
        sFastD.status == sRefD.status &&
        sFastD.pc == sRefD.pc &&
        sFastD.sp == sRefD.sp &&
        -- Active top-of-stack window, `stkFastBase` boundary, bottom page of 8 MiB stack, and guard:
        memRangeCellsEq sFastD.mem sRefD.mem (defInputs.init.stackTop - 8192#64) 8192 &&
        memRangeCellsEq sFastD.mem sRefD.mem (stkFastBase - 256#64) 512 &&
        memRangeCellsEq sFastD.mem sRefD.mem defStackBase 512 &&
        memRangeCellsEq sFastD.mem sRefD.mem (defStackBase - 16#64) 16
      | _, _ => false
    -- Below-window store/load test at `sp - 0x20000` (128 KiB below `sp`, below the 64 KiB
    -- `stkFastBase` window on the default 8 MiB stack):
    --   sub x9, sp, #0x20, lsl #12  (0xd14083e9)
    --   movz x10, #0xbeef           (0xd297ddea)
    --   str x10, [x9]               (0xf900012a)
    --   ldr x0, [x9]                (0xf9400120)
    let belowWinCode : List (BitVec 8) :=
      [ 0xe9#8, 0x83#8, 0x40#8, 0xd1#8
      , 0xea#8, 0xdd#8, 0x97#8, 0xd2#8
      , 0x2a#8, 0x01#8, 0x00#8, 0xf9#8
      , 0x20#8, 0x01#8, 0x40#8, 0xf9#8 ]
    let belowWinImg : ElfImage :=
      { echoStdinImg with
        segments := echoStdinImg.segments.map fun seg =>
          if seg.perm.x then
            let off := (echoStdinImg.entry - seg.start).toNat
            { seg with bytes := seg.bytes.take off ++ belowWinCode ++ seg.bytes.drop (off + 16) }
          else seg }
    let belowWinStoreEq :=
      match runElfImageFast 1 4 belowWinImg defInputs,
            runElfImagePure 4 belowWinImg defInputs with
      | .ok (sFastB, none), .ok (sRefB, none) =>
        let targetAddr := sRefB.sp - 0x20000#64
        sFastB.status == .Running &&
        sRefB.status == .Running &&
        sFastB.pc == sRefB.pc &&
        sFastB.readReg64 .x0 == 0xbeef#64 &&
        sRefB.readReg64 .x0 == 0xbeef#64 &&
        memRangeCellsEq sFastB.mem sRefB.mem (targetAddr - 16#64) 64
      | _, _ => false
    unmappedHaltEq &&
    defStackEq &&
    belowWinStoreEq &&
    outFast.exitCode == outRef.exitCode &&
    outFast.stdout == outRef.stdout &&
    outFast.stderr == outRef.stderr &&
    outFast.exitCode == 0#64 &&
    outFast.stdout == msg &&
    outFast.stderr == [] &&
    sFast.status == sRef.status &&
    sFast.pc == sRef.pc &&
    sFast.sp == sRef.sp &&
    sFast.pstate == sRef.pstate &&
    sFast.tpidrEl0 == sRef.tpidrEl0 &&
    sFast.brkStart == sRef.brkStart &&
    sFast.brk == sRef.brk &&
    sFast.trace == sRef.trace &&
    sFast.oracleIdx == sRef.oracleIdx &&
    fdsEq && gprsEq && vregsEq && segsEq && brkEq && stackEq
  | _, _ => false

end_requires_test_files

requires_test_files ["fixtures/abort_status.elf"]

set_option maxRecDepth 2000000 in
noncomputable def abortStatusBytes : List (BitVec 8) :=
  file_bytes% "fixtures/abort_status.elf"
    sha256 "b526fc816c410668c8a389cd73c32ae38e9b85d166bdb51ed7dabfa5bd9e023b"

/-- Embedded `abort_status.elf` image (stock `zig cc -target aarch64-linux-musl -static`). -/
def abortStatusImg : ElfImage :=
  elf_image% "fixtures/abort_status.elf"

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 2000000 in
theorem abortStatus_parse : ElfImage.parse abortStatusBytes = .ok abortStatusImg := by
  exact ElfImage.parse_of_fastParse rfl

set_option compiler.extract_closed false in
/-- Cross-check `runElfImageFast` against the reference `runElfImage` (`runSteps Program.pureMem`)
    on `abort_status.elf` for both stock musl `abort()` (`argc = 1`, failing closed in
    `rt_sigprocmask` on `__block_all_sigs`) and normal `exit(134)` (`argc = 2`,
    `exitCode = 134#64`, `signal = none`). -/
def checkAbortStatusProcess (_ : Unit := ()) : Bool :=
  let abortInputs : ProcessInputs :=
    { argv := [bytesOfString "abort_status"]
      init := { stackSize := 8192 } }
  let exitInputs : ProcessInputs :=
    { argv := [bytesOfString "abort_status", bytesOfString "exit134"]
      init := { stackSize := 8192 } }
  let abortOk :=
    match runElfImageFast 20 256 abortStatusImg abortInputs,
          runElfImagePure 5000 abortStatusImg abortInputs with
    | .ok (sFast, none), .ok (sRef, none) =>
      let gprsEq := (List.range 32).all fun i =>
        sFast.regs.regs (BitVec.ofNat 5 i) == sRef.regs.regs (BitVec.ofNat 5 i)
      let vregsEq := (List.range 32).all fun i =>
        sFast.vregs.regs (BitVec.ofNat 5 i) == sRef.vregs.regs (BitVec.ofNat 5 i)
      let stackBase := BitVec.ofNat 64 (abortInputs.init.stackTop.toNat - abortInputs.init.stackSize)
      let stackEq := memRangeCellsEq sFast.mem sRef.mem stackBase abortInputs.init.stackSize
      sFast.status == .Exception "unmodeled non-zero signal mask in rt_sigprocmask" &&
      sFast.status == sRef.status &&
      sFast.pc == sRef.pc &&
      sFast.sp == sRef.sp &&
      sFast.trace == sRef.trace &&
      gprsEq && vregsEq && stackEq
    | _, _ => false
  let exitOk :=
    match runElfImageFast 20 256 abortStatusImg exitInputs,
          runElfImagePure 5000 abortStatusImg exitInputs with
    | .ok (sFast, some outFast), .ok (sRef, some outRef) =>
      outFast.exitCode == 134#64 &&
      outFast.signal == none &&
      outRef.exitCode == 134#64 &&
      outRef.signal == none &&
      sFast.status == .Exited 134#64 &&
      sFast.status == sRef.status
    | _, _ => false
  abortOk && exitOk

end_requires_test_files

def closeInheritedFdsCmd : String :=
  "for fd in /proc/self/fd/*; do f=\"${fd##*/}\"; case \"$f\" in 0|1|2) ;; *) eval \"exec ${f}>&-\" 2>/dev/null || true ;; esac; done"

/-- Run a static AArch64 ELF under `qemu-aarch64` via `bash` and return the POSIX wait status `$?`
    (`128 + sig` for fatal signal deaths such as `134` on `SIGABRT = 6`). -/
def runQemuShellExitStatus (elfPath : String) (extraArgs : List String := []) : IO (Option Nat) := do
  let absElf ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath elfPath)
  let absFetchQemu ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath "scripts/fetch-qemu-aarch64")
  let quotedArgs := String.intercalate " " ((absElf.toString :: extraArgs).map fun s => "\"" ++ s ++ "\"")
  let script :=
    s!"ulimit -c 0 && {closeInheritedFdsCmd} && QEMU=\"$(command -v qemu-aarch64 || \"{absFetchQemu}\")\" && " ++
    s!"\"$QEMU\" {quotedArgs} >/dev/null 2>&1; printf '%u' \"$?\""
  let res ← IO.Process.output { cmd := "bash", args := #["-c", script] }
  return res.stdout.trimAscii.toString.toNat?

/-- Differential conformance test comparing stock static musl `abort()` (`abort_status.elf`) under
    `qemu-aarch64` (`134`) against `runElfByteArray` (`runSteps Program.pureMem`, failing closed on
    `rt_sigprocmask` non-zero signal mask in `__block_all_sigs`) and `exit(134)` (`134`,
    `signal = none`). -/
def checkAbortStatusVsQemuIO : IO Bool := do
  let elfPath ← Testing.Harness.resolveRepoFilePath "Arm64/Testing/Regression/fixtures/abort_status.elf"
  let elfBytes ← IO.FS.readBinFile elfPath
  let qemuAbort? ← runQemuShellExitStatus elfPath.toString
  let qemuExit?  ← runQemuShellExitStatus elfPath.toString ["exit134"]
  let simAbort := runElfByteArrayPure 5000 elfBytes { argv := [bytesOfString "abort_status"] }
  let simExit  := runElfByteArrayPure 5000 elfBytes
    { argv := [bytesOfString "abort_status", bytesOfString "exit134"] }
  match qemuAbort?, qemuExit?, simAbort, simExit with
  | some qAbort, some qExit, .ok (sAbort, none), .ok (_, some oExit) =>
    return (
      qAbort == 134 &&
      sAbort.status == .Exception "unmodeled non-zero signal mask in rt_sigprocmask" &&
      qExit == 134 &&
      oExit.exitCode == BitVec.ofNat 64 qExit &&
      oExit.signal == none)
  | _, _, _, _ =>
    return false

end Testing.Process
