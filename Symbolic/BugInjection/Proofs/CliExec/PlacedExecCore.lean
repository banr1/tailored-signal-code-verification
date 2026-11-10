/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar
public import Symbolic.BugInjection.Proofs.CliExec.FastEval

/-!
# Placed `FastState` Executor

Executable `FastState` runner for relocatable CLI binaries without fixed base-address assumptions.
Defines `FastProgPlaced` and `PrebuiltElfPlaced` (depth-62 radix-tree hook lookup and cache-line
instruction decoding across the 64-bit address space), `fastExecSyscallPlaced` and
`fastEvalInstPlaced` for Linux syscalls, exclusives, and barriers, fuel-bounded and `2 ^ k`-step
cached chunk runners, and per-call `FastState` initialization and outcome checkers.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore

open Arm64 Arm64.Memory Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.SignalSession (CliHooks Inputs Outcome OutcomeMatchesProcess
  cliProcessInputs filesOf sigAbrt)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced

/-- Update `fs.brk` after forcing `newBrk` via `withForcedBV`. -/
def fastSetBrk (fs : FastState) (newBrk : BitVec 64) : FastState :=
  withForcedBV newBrk fun bk' =>
    fs.withFields fun rg sp pc ps m ivs tp fp bs _ ph ffs orcl oi ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk', ph, ffs, orcl, oi, ex, tr, st, sg⟩

theorem fastSetBrk_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (newBrk : BitVec 64) :
    (fastSetBrk fs newBrk).Agrees (s.setBrk newBrk) := by
  simp only [fastSetBrk, withForcedBV_eq, FastState.withFields_eq, State.setBrk]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, rfl, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

/-- Update `fs.physMemAvail` after forcing `newPhys` via `withForcedNat`. -/
def fastSetPhysMemAvail (fs : FastState) (newPhys : Nat) : FastState :=
  RadixMemAux.withForcedNat newPhys fun ph' =>
    fs.withFields fun rg sp pc ps m ivs tp fp bs bk _ ffs orcl oi ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph', ffs, orcl, oi, ex, tr, st, sg⟩

theorem fastSetPhysMemAvail_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (newPhys : Nat) :
    (fastSetPhysMemAvail fs newPhys).Agrees (s.setPhysMemAvail newPhys) := by
  simp only [fastSetPhysMemAvail, RadixMemAux.withForcedNat_eq, FastState.withFields_eq,
    State.setPhysMemAvail]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, rfl, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

/-- Increment `fs.oracleIdx` with forced `Nat` evaluation, as in `State.nextOracle`. -/
def fastNextOracle (fs : FastState) : FastState :=
  RadixMemAux.withForcedNat (fs.oracleIdx + 1) fun oi' =>
    fs.withFields fun rg sp pc ps m ivs tp fp bs bk ph ffs orcl _ ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi', ex, tr, st, sg⟩

theorem fastNextOracle_agrees {fs : FastState} {s : State} (h : fs.Agrees s) :
    (fastNextOracle fs).Agrees s.nextOracle := by
  simp only [fastNextOracle, RadixMemAux.withForcedNat_eq, FastState.withFields_eq,
    State.nextOracle, ← h.oracleIdx]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, rfl, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

/-- Drop the head of `fs.exclFails`, as in `State.stepExclOracle`. -/
def fastStepExclOracle (fs : FastState) : FastState :=
  fs.withFields fun rg sp pc ps m ivs tp fp bs bk ph ffs orcl oi ex tr st sg =>
    ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex.tail, tr, st, sg⟩

theorem fastStepExclOracle_agrees {fs : FastState} {s : State} (h : fs.Agrees s) :
    (fastStepExclOracle fs).Agrees s.stepExclOracle := by
  simp only [fastStepExclOracle, FastState.withFields_eq, State.stepExclOracle, h.exclFails]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, rfl,
    h.trace, h.status, h.sigAltStack⟩

def fastFdBytes (ffs : FastFs) (desc : FdEntry) : List (BitVec 8) :=
  match desc.kind with
  | .stdio => ffs.stdin
  | .localFile => match ffs.files desc.path with | some (.file bs) => bs | _ => []
  | .localDir | .custom _ => []

theorem fastFdBytes_eq {ffs : FastFs} {sfs : FsState} (h : ffs.Agrees sfs) (desc : FdEntry) :
    fastFdBytes ffs desc = sfs.fdBytes desc := by
  unfold fastFdBytes FsState.fdBytes
  cases desc.kind with
  | stdio => exact h.2.1
  | localFile =>
    dsimp
    rw [FastFs.files_eq h desc.path]
    cases sfs.files desc.path with
    | none => rfl
    | some e => cases e <;> rfl
  | localDir => rfl
  | custom _ => rfl

/-- Lowest unused file descriptor in `[3, FsState.maxOpenFds)`. -/
def fastAllocFd (ffs : FastFs) : Option (BitVec 64) :=
  ((List.range (FsState.maxOpenFds - 3)).find? fun i =>
    ffs.getFd (BitVec.ofNat 64 (i + 3)) == none).map fun i => BitVec.ofNat 64 (i + 3)

theorem fastAllocFd_eq {ffs : FastFs} {sfs : FsState} (h : ffs.Agrees sfs) :
    fastAllocFd ffs = sfs.allocFd := by
  unfold fastAllocFd FsState.allocFd
  have hfn : (fun i => ffs.getFd (BitVec.ofNat 64 (i + 3)) == none) =
      (fun i => sfs.fds (BitVec.ofNat 64 (i + 3)) == none) := by
    funext i
    rw [FastFs.getFd_eq h]
  rw [hfn]

/-- `FastFs` counterpart of `Arm64.ancestorWalkErrno?`. -/
def fastAncestorWalkErrno? (ffs : FastFs) (rawPath : String) : Option (BitVec 64) :=
  let segs := (splitSlash rawPath).filter (!·.isEmpty)
  let rec walk (cur : FsPath) : List String → Option (BitVec 64)
    | [] => none
    | seg :: rest =>
      if seg.length > NAME_MAX then some ENAMETOOLONG
      else
        let cur' := if seg == "." then cur else cur ++ [seg]
        match ffs.getEntry cur' with
        | some .dir      => walk cur' rest
        | some (.file _) => some ENOTDIR
        | none           => some ENOENT
  match walk [] segs.dropLast with
  | some err => some err
  | none => if segs.getLast?.any (·.length > NAME_MAX) then some ENAMETOOLONG else none

/-- `FastFs` counterpart of `Arm64.strictAncestorWalkErrno?` over `segs.dropLast`. -/
def fastStrictAncestorWalkErrno? (ffs : FastFs) (rawPath : String) : Option (BitVec 64) :=
  fastAncestorWalkErrno?.walk ffs [] ((splitSlash rawPath).filter (!·.isEmpty)).dropLast

private theorem fastAncestorWalk_eq {ffs : FastFs} {sfs : FsState} (h : ffs.Agrees sfs)
    (cur : FsPath) (segs : List String) :
    fastAncestorWalkErrno?.walk ffs cur segs = ancestorWalkErrno?.walk sfs cur segs := by
  induction segs generalizing cur with
  | nil => rfl
  | cons seg rest ih =>
    unfold fastAncestorWalkErrno?.walk ancestorWalkErrno?.walk
    dsimp only
    split
    · rfl
    · rw [FastFs.getEntry_eq h]
      cases sfs.getEntry (if seg == "." then cur else cur ++ [seg]) with
      | none => rfl
      | some e =>
        cases e with
        | dir => exact ih _
        | file _ => rfl

theorem fastStrictAncestorWalkErrno?_eq {ffs : FastFs} {sfs : FsState} (h : ffs.Agrees sfs)
    (rawPath : String) :
    fastStrictAncestorWalkErrno? ffs rawPath = strictAncestorWalkErrno? sfs rawPath :=
  fastAncestorWalk_eq h [] _

theorem fastAncestorWalkErrno?_eq {ffs : FastFs} {sfs : FsState} (h : ffs.Agrees sfs)
    (rawPath : String) :
    fastAncestorWalkErrno? ffs rawPath = ancestorWalkErrno? sfs rawPath := by
  unfold fastAncestorWalkErrno? ancestorWalkErrno?
  dsimp only
  rw [fastAncestorWalk_eq h [] _]
  cases ancestorWalkErrno?.walk sfs [] ((splitSlash rawPath).filter (!·.isEmpty)).dropLast <;> rfl

/-- Closure-free counterpart of `Arm64.OpenVerdict` over `FastFs`. -/
inductive FastOpenVerdict where
  | opened (fd : BitVec 64) (ffs' : FastFs) (changedPath? : Option String)
  | errno  (err : BitVec 64)
  | trap   (msg : String)

def fastCheckOpenFlags (flags : BitVec 32) : Option FastOpenVerdict :=
  if (flags &&& ~~~OPENAT_KNOWN_MASK) != 0#32 || (flags &&& 3#32) == 3#32 then
    some (.trap "unmodeled openat flags")
  else if (flags &&& O_CREAT_W32) != 0#32 && (flags &&& O_DIRECTORY_W32) != 0#32 then
    some (.errno EINVAL)
  else
    none

/-- Working-directory `openat` decision tree over `FastFs`, corresponding to `Arm64.openatPure`. -/
def fastOpenatPure (ffs : FastFs) (dfd : BitVec 32) (rawPath : String) (flags : BitVec 32)
    (mode : BitVec 32 := 0o666#32) : FastOpenVerdict :=
  match fastCheckOpenFlags flags with
  | some v => v
  | none =>
    let acc : FdAccessMode :=
      if (flags &&& 3#32) == 0#32 then .rdonly
      else if (flags &&& 3#32) == 1#32 then .wronly
      else .rdwr
    let hasCreat   := (flags &&& O_CREAT_W32) != 0#32
    let hasExcl    := (flags &&& O_EXCL_W32) != 0#32
    let hasTrunc   := (flags &&& O_TRUNC_W32) != 0#32
    let hasAppend  := (flags &&& O_APPEND_W32) != 0#32
    let hasDir     := (flags &&& O_DIRECTORY_W32) != 0#32
    let hasCloexec := (flags &&& O_CLOEXEC_W32) != 0#32
    match resolveCwdPath dfd rawPath with
    | .trap msg => .trap msg
    | .errno err => .errno err
    | .ok segs =>
      match fastStrictAncestorWalkErrno? ffs rawPath with
      | some err => .errno err
      | none =>
        let isTrailDir := trailingDir rawPath
        let isTrailNormSlash := trailingNormSlash rawPath
        if hasCreat && isTrailNormSlash then .errno EISDIR
        else if ((splitSlash rawPath).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX) then
          .errno ENAMETOOLONG
        else
          match ffs.getEntry segs with
          | some .dir =>
            if hasCreat && hasExcl && !isTrailNormSlash then .errno EEXIST
            else if acc != .rdonly || hasTrunc || hasCreat then .errno EISDIR
            else match fastAllocFd ffs with
              | none => .errno EMFILE
              | some fd =>
                let ffs' := ffs.setFd fd
                  (some { path := rawPath, accMode := .rdonly, append := hasAppend,
                          cloexec := hasCloexec, offset := 0, kind := .localDir })
                .opened fd ffs' none
          | some (.file oldBytes) =>
            if isTrailDir || hasDir then .errno ENOTDIR
            else if hasCreat && hasExcl then .errno EEXIST
            else match fastAllocFd ffs with
              | none => .errno EMFILE
              | some fd =>
                let bs' := if hasTrunc then [] else oldBytes
                let ffs' := (ffs.setEntry segs (some (.file bs'))).setFd fd
                  (some { path := rawPath, accMode := acc, append := hasAppend,
                          cloexec := hasCloexec, offset := 0 })
                .opened fd ffs' (if hasTrunc then some segs.toPathString else none)
          | none =>
            if !hasCreat then .errno ENOENT
            else match fastAllocFd ffs with
              | none => .errno EMFILE
              | some fd =>
                if (mode &&& O_CREAT_OWNER_RW_MASK) != O_CREAT_OWNER_RW_MASK then
                  .trap "unmodeled non-owner-rw O_CREAT mode"
                else
                  let ffs' := (ffs.setEntry segs (some (.file []))).setFd fd
                    (some { path := rawPath, accMode := acc, append := hasAppend,
                            cloexec := hasCloexec, offset := 0 })
                  .opened fd ffs' (some segs.toPathString)

def fastApplyOpenVerdict (fs : FastState) : FastOpenVerdict → Option FastState
  | .opened fd ffs' none     => some (((fs.setFs ffs').writeReg64 Reg.x0 fd).advancePC)
  | .opened fd ffs' (some p) =>
    some ((((fs.setFs ffs').appendTrace [.fileChanged p]).writeReg64 Reg.x0 fd).advancePC)
  | .errno err               => some ((fs.writeReg64 Reg.x0 (-err)).advancePC)
  | .trap _                  => none

/-- `SYS_FCNTL` (`25`) evaluator on `FastState`. -/
def fastExecFcntl (fs : FastState) : Option FastState :=
  let rawFd := fs.readReg32 Reg.x0
  let cmd   := fs.readReg32 Reg.x1
  let arg   := fs.readReg64 Reg.x2
  if rawFd.slt 0#32 then
    some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
  else
    let fd := rawFd.zeroExtend 64
    match fs.fs.getFd fd with
    | none =>
      if fd < 3#64 then none
      else some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
    | some desc =>
      if !(desc.kind == .localFile || desc.kind == .localDir) then none
      else if cmd == F_GETFD_W32 then
        some ((fs.writeReg64 Reg.x0 (if desc.cloexec then 1#64 else 0#64)).advancePC)
      else if cmd == F_SETFD_W32 then
        let ffs' := fs.fs.setFd fd (some { desc with cloexec := (arg &&& 1#64) != 0#64 })
        some (((fs.setFs ffs').writeReg64 Reg.x0 0#64).advancePC)
      else none

/-- `SYS_OPENAT` (`56`) evaluator on `FastState`. -/
def fastExecOpenat (fs : FastState) : Option FastState :=
  let dfd   := fs.readReg32 Reg.x0
  let fname := fs.readReg64 Reg.x1
  let flags := fs.readReg32 Reg.x2
  let mode  := fs.readReg32 Reg.x3
  match fastCheckOpenFlags flags with
  | some v => fastApplyOpenVerdict fs v
  | none =>
    match readCStringFast fs.mem fname with
    | .trap _ => none
    | .errno err => some ((fs.writeReg64 Reg.x0 (-err)).advancePC)
    | .ok rawPath => fastApplyOpenVerdict fs (fastOpenatPure fs.fs dfd rawPath flags mode)

/-- `SYS_CLOSE` (`57`) evaluator on `FastState`. -/
def fastExecClose (fs : FastState) : Option FastState :=
  let rawFd := fs.readReg32 Reg.x0
  if rawFd.slt 0#32 then
    some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
  else
    let fd := rawFd.zeroExtend 64
    match fs.fs.getFd fd with
    | none =>
      if fd < 3#64 then none
      else some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
    | some desc =>
      if desc.kind != .localFile && desc.kind != .localDir then none
      else some (((fs.setFs (fs.fs.setFd fd none)).writeReg64 Reg.x0 0#64).advancePC)

/-- `SYS_READ` (`63`) evaluator on `FastState`. -/
def fastExecRead (fs : FastState) : Option FastState :=
  let rawFd := fs.readReg32 Reg.x0
  let buf   := fs.readReg64 Reg.x1
  let count := fs.readReg64 Reg.x2
  if rawFd.slt 0#32 then
    some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
  else
    let fd := rawFd.zeroExtend 64
    match fs.fs.getFd fd with
    | none =>
      if fd < 3#64 then none
      else some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
    | some desc =>
      if desc.kind == .localDir then
        if !desc.accMode.canRead then
          some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
        else if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
          some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
        else
          some ((fs.writeReg64 Reg.x0 (-EISDIR)).advancePC)
      else if !(desc.kind == .localFile || desc.kind == .stdio) then
        none
      else if !desc.accMode.canRead then
        some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
      else if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
        some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
      else
        let pos := desc.offset
        if desc.kind == .localFile && decide (pos + count.toNat > MAX_LFS_FILESIZE) then
          some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
        else
          let count' := min count.toNat MAX_RW_COUNT
          let fileBytes := fastFdBytes fs.fs desc
          let chunk := (fileBytes.drop pos).take count'
          if fs.mem.canWrite buf chunk.length then
            let fs1 := fs.setMem (fs.mem.writeBytes buf chunk)
            let fs2 := fs1.setFs (fs1.fs.setFd fd (some { desc with offset := pos + chunk.length }))
            some ((fs2.writeReg64 Reg.x0 (BitVec.ofNat 64 chunk.length)).advancePC)
          else if !fs.mem.canWrite buf 1 then
            some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
          else
            none

/-- `SYS_FSTAT` (`80`) evaluator on `FastState`. -/
def fastExecFstat (fs : FastState) : Option FastState :=
  let rawFd   := fs.readReg32 Reg.x0
  let statbuf := fs.readReg64 Reg.x1
  if rawFd.slt 0#32 then
    some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
  else
    let fd := rawFd.zeroExtend 64
    match fs.fs.getFd fd with
    | none =>
      if fd < 3#64 then none
      else some ((fs.writeReg64 Reg.x0 (-EBADF)).advancePC)
    | some desc =>
      if desc.kind != .localFile && desc.kind != .localDir then
        none
      else
        let entry := (fs.fs.files desc.path).getD (.file [])
        if !fs.mem.canWrite statbuf 128 then
          some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
        else
          some (((fs.setMem (fs.mem.writeBytes statbuf (encodeLinuxStat entry))).writeReg64
            Reg.x0 0#64).advancePC)

/-- `SYS_BRK` (`214`) evaluator on `FastState`. -/
def fastExecBrk (fs : FastState) : Option FastState :=
  let addr := fs.readReg64 Reg.x0
  if addr == 0#64 || addr.ult fs.brkStart then
    some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
  else
    let oldPage := Arm64.pageAlignUp fs.brk.toNat
    let newPage := Arm64.pageAlignUp addr.toNat
    if decide (newPage ≤ oldPage) then
      let shrinkBytes := oldPage - newPage
      if !fs.mem.allPerm (·.mapped) (BitVec.ofNat 64 newPage) shrinkBytes then
        some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
      else if !decide (oldPage ≤ USER_VA_LIMIT) then
        none
      else
        let reclaimed := fs.mem.countRw (BitVec.ofNat 64 newPage) shrinkBytes
        let mem := fs.mem.unmapWritable (BitVec.ofNat 64 newPage) shrinkBytes
        some (((((fastSetBrk fs addr).setMem mem |>
          fun st => fastSetPhysMemAvail st (fs.physMemAvail + reclaimed)).writeReg64
            Reg.x0 addr)).advancePC)
    else
      let growBytes := newPage - oldPage
      if !decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) ||
          !fs.mem.canMap (BitVec.ofNat 64 oldPage) (growBytes + BRK_GUARD_GAP) then
        some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
      else if !decide (growBytes ≤ fs.physMemAvail) then
        some (fs.setStatus .OutOfMemory)
      else
        let mem := fs.mem.mapZero (BitVec.ofNat 64 oldPage) growBytes
        some (((((fastSetBrk fs addr).setMem mem |>
          fun st => fastSetPhysMemAvail st (fs.physMemAvail - growBytes)).writeReg64
            Reg.x0 addr)).advancePC)

/-- `SYS_MUNMAP` (`215`) evaluator on `FastState`. -/
def fastExecMunmap (fs : FastState) : Option FastState :=
  let addr := fs.readReg64 Reg.x0
  let len := (fs.readReg64 Reg.x1).toNat
  let size := Arm64.pageAlignUp len
  if addr.toNat % PAGE_SIZE != 0 || len == 0 || !decide (addr.toNat + size ≤ 2 ^ 48) then
    some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
  else if !fs.mem.allPerm (fun p => !p.frozen) addr size then
    none
  else
    let reclaimed := fs.mem.countRw addr size
    some (((fastSetPhysMemAvail (fs.setMem (fs.mem.unmapNonFrozen addr size))
      (fs.physMemAvail + reclaimed)).writeReg64 Reg.x0 0#64).advancePC)

/-- `SYS_MREMAP` (`216`) evaluator on `FastState`. -/
def fastExecMremap (fs : FastState) : Option FastState :=
  let oldAddr := fs.readReg64 Reg.x0
  let oldLen := (fs.readReg64 Reg.x1).toNat
  let newLen := (fs.readReg64 Reg.x2).toNat
  let flags := fs.readReg64 Reg.x3
  if flags != MREMAP_MAYMOVE then
    none
  else if oldAddr.toNat % PAGE_SIZE != 0 || newLen == 0 ||
      !decide (newLen ≤ 2 ^ 64 - PAGE_SIZE) then
    some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
  else if oldLen == 0 then
    none
  else
    let oldAligned := Arm64.pageAlignUp oldLen
    let newAligned := Arm64.pageAlignUp newLen
    if !decide (oldAddr.toNat + oldAligned ≤ USER_VA_LIMIT) then
      some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
    else if !fs.mem.allPerm (fun p => !p.frozen) oldAddr oldAligned then
      none
    else if fs.mem.canMap oldAddr oldAligned then
      some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
    else if !fs.mem.allPerm (· == some Perm.rw) oldAddr oldAligned then
      none
    else if !fs.mem.allAnon oldAddr oldAligned then
      none
    else if fs.oracle.mremapFail fs.oracleIdx then
      some (((fastNextOracle fs).writeReg64 Reg.x0 (-ENOMEM)).advancePC)
    else
      let fmUnmapped := fs.mem.unmapNonFrozen oldAddr oldAligned
      match sanitizeMmapAddrFast fmUnmapped (fs.oracle.mmap fs.oracleIdx) newAligned with
      | none =>
        some (((fastNextOracle fs).writeReg64 Reg.x0 (-ENOMEM)).advancePC)
      | some newBase =>
        if !decide (newAligned ≤ fs.physMemAvail + oldAligned) then
          some (fs.setStatus .OutOfMemory)
        else
          let fm' := fs.mem.remapRw oldAddr oldAligned newBase newAligned
          let st1 := fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail + oldAligned - newAligned)
          some (((fastNextOracle st1).writeReg64 Reg.x0 newBase).advancePC)

/-- `SYS_MMAP` (`222`) evaluator on `FastState`. -/
def fastExecMmap (fs : FastState) : Option FastState :=
  let len := (fs.readReg64 Reg.x1).toNat
  let prot := fs.readReg64 Reg.x2
  let flags := fs.readReg64 Reg.x3
  if (prot != MMAP_PROT_RW && prot != MMAP_PROT_NONE) ||
      (flags != MMAP_FLAGS_PRIVATE_ANON && flags != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        flags != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      fs.readReg64 Reg.x5 != 0#64 then
    none
  else if len == 0 then
    some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
  else if flags == MMAP_FLAGS_PRIVATE_ANON_FIXED then
    let addr := fs.readReg64 Reg.x0
    let size := Arm64.pageAlignUp len
    if addr.toNat % PAGE_SIZE != 0 || addr.toNat < MMAP_MIN_ADDR ||
        !decide (addr.toNat + size ≤ 2 ^ 48) then
      none
    else if !fs.mem.allPerm (fun p => !p.frozen) addr size then
      none
    else
      let reclaimed := fs.mem.countRw addr size
      if prot == MMAP_PROT_NONE then
        let fm' := ((fs.mem.unmapNonFrozen addr size).mapZero addr size).setPermNonFrozen
          addr size Perm.protNone
        some (((fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail + reclaimed)).writeReg64
          Reg.x0 addr).advancePC)
      else if !decide (size ≤ fs.physMemAvail + reclaimed) then
        some (fs.setStatus .OutOfMemory)
      else
        let fm' := (fs.mem.unmapNonFrozen addr size).mapZero addr size
        some (((fastSetPhysMemAvail (fs.setMem fm')
          (fs.physMemAvail + reclaimed - size)).writeReg64 Reg.x0 addr).advancePC)
  else
    let size := Arm64.pageAlignUp len
    match sanitizeMmapAddrFast fs.mem (fs.oracle.mmap fs.oracleIdx) size with
    | some base =>
      if prot == MMAP_PROT_NONE then
        let fm' := (fs.mem.mapZero base size).setPermNonFrozen base size Perm.protNone
        some (((fastNextOracle (fs.setMem fm')).writeReg64 Reg.x0 base).advancePC)
      else if !decide (size ≤ fs.physMemAvail) then
        some (fs.setStatus .OutOfMemory)
      else
        let fm' := fs.mem.mapZero base size
        let st1 := fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail - size)
        some (((fastNextOracle st1).writeReg64 Reg.x0 base).advancePC)
    | none =>
      some (fs.setStatus .OutOfMemory)

/-- `SYS_MPROTECT` (`226`) evaluator on `FastState`. -/
def fastExecMprotect (fs : FastState) : Option FastState :=
  let addr := fs.readReg64 Reg.x0
  let len := (fs.readReg64 Reg.x1).toNat
  let prot := fs.readReg64 Reg.x2
  let size := Arm64.pageAlignUp len
  if prot != MMAP_PROT_NONE && prot != MMAP_PROT_RW then
    none
  else if addr.toNat % PAGE_SIZE != 0 then
    some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
  else if !decide (addr.toNat + size ≤ 2 ^ 48) then
    none
  else if len == 0 then
    some ((fs.writeReg64 Reg.x0 0#64).advancePC)
  else if !fs.mem.allPerm (fun p => !p.frozen) addr size then
    none
  else if !fs.mem.allPerm (·.mapped) addr size then
    if fs.mem.canMap addr size then
      some ((fs.writeReg64 Reg.x0 (-ENOMEM)).advancePC)
    else
      none
  else if prot == MMAP_PROT_NONE then
    some (((fs.setMem (fs.mem.setPermNonFrozen addr size Perm.protNone)).writeReg64
      Reg.x0 0#64).advancePC)
  else
    let oldRw := fs.mem.countRw addr size
    let needed := size - oldRw
    if !decide (needed ≤ fs.physMemAvail) then
      some (fs.setStatus .OutOfMemory)
    else
      let fm' := fs.mem.setPermNonFrozen addr size Perm.rw
      some (((fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail - needed)).writeReg64
        Reg.x0 0#64).advancePC)

/-- Dispatch `SVC #0` on `FastState` under `Arm64.Syscall.standard`. -/
def fastExecSyscallPlaced (fs : FastState) : Option FastState :=
  let nr := fs.readReg64 Reg.x8
  if nr == 25#64 then fastExecFcntl fs
  else if nr == 56#64 then fastExecOpenat fs
  else if nr == 57#64 then fastExecClose fs
  else if nr == 63#64 then fastExecRead fs
  else if nr == 80#64 then fastExecFstat fs
  else if nr == 93#64 || nr == 94#64 then some (fs.setStatus (.Exited (fs.readReg64 Reg.x0)))
  else if nr == 96#64 then some ((fs.writeReg64 Reg.x0 SIM_TID).advancePC)
  else if nr == 214#64 then fastExecBrk fs
  else if nr == 215#64 then fastExecMunmap fs
  else if nr == 216#64 then fastExecMremap fs
  else if nr == 222#64 then fastExecMmap fs
  else if nr == 226#64 then fastExecMprotect fs
  else none

/-- Evaluator for `Instr.stxr` (`STXR*`/`STLXR*`) on `FastState`, corresponding to `execInstWithSvc`. -/
def fastExecStxr (sz : MemWidth) (rs rn rt : Reg) (fs : FastState) : Option FastState :=
  if !FastEvalScalar.fastCheckRegSPAligned fs rn then
    none
  else
    let ea := fs.readReg64 rn
    if !sz.isAligned ea then
      none
    else if !fs.mem.canWrite ea sz.bytes then
      none
    else
      let val := fs.readReg64 rt
      let fs1 := fastStepExclOracle fs
      if fs.exclFails.headD false then
        some ((fs1.writeReg .W32 rs 1#64).advancePC)
      else
        some (((fs1.setMem (fs.mem.writeSized sz ea val)).writeReg .W32 rs 0#64).advancePC)

theorem fastExecLdxr_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : MemWidth} {acq : Bool} {rn rt : Reg}
    (heval : FastEvalScalar.fastExecLdarStlr sz true rn rt fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.ldxr sz acq rn rt) s) := by
  have h1 := FastEvalScalar.fastExecLdarStlr_sound h svc heval
  simpa only [execInstWithSvc, ↓reduceIte] using h1

theorem fastExecStxr_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : MemWidth} {rel : Bool} {rs rn rt : Reg}
    (heval : fastExecStxr sz rs rn rt fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.stxr sz rel rs rn rt) s) := by
  unfold fastExecStxr at heval
  rw [FastEvalScalar.fastCheckRegSPAligned_eq h, FastState.readReg64_eq h rn] at heval
  simp only [execInstWithSvc]
  cases hsp : checkRegSPAligned s rn
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    cases hal : sz.isAligned (s.readReg64 rn)
    · simp [hal] at heval
    · simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      rw [FastMem.canWrite_eq h.mem] at heval
      cases hcw : s.mem.canWrite (s.readReg64 rn) sz.bytes
      · simp [hcw] at heval
      · simp only [hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        rw [h.exclFails, FastState.readReg64_eq h rt] at heval
        have hstep := fastStepExclOracle_agrees h
        have hmem_eq : (fastStepExclOracle fs).mem = fs.mem := by
          simp [fastStepExclOracle]
        have hs_mem : s.stepExclOracle.mem = s.mem := rfl
        cases hex : s.exclFails.headD false
        · have hwf : s.exclWillFail = false := hex
          simp only [hex, hwf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
          subst heval
          rw [← hmem_eq, ← hs_mem]
          exact FastState.advancePC_agrees
            (FastState.writeReg_agrees
              (FastEvalScalar.writeSized_setMem_agrees hstep sz _ _) .W32 rs 0#64)
        · have hwf : s.exclWillFail = true := hex
          simp only [hex, hwf, ↓reduceIte, Option.some.injEq] at heval ⊢
          subst heval
          exact FastState.advancePC_agrees
            (FastState.writeReg_agrees hstep .W32 rs 1#64)

theorem fastExecBarrier_sound {fs : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) (crm : BitVec 4) (op2 : BitVec 3) :
    fs.advancePC.Agrees (execInstWithSvc svc (.barrier crm op2) s) := by
  simp only [execInstWithSvc]
  exact FastState.advancePC_agrees h

def fastEvalInstPlaced (inst : Arm64.Instr) (fs : FastState) : Option FastState :=
  match inst with
  | .system false 0#16 => fastExecSyscallPlaced fs
  | .ldxr sz _acq rn rt => FastEvalScalar.fastExecLdarStlr sz true rn rt fs
  | .stxr sz _rel rs rn rt => fastExecStxr sz rs rn rt fs
  | .barrier _ _ => some fs.advancePC
  | _ => FastEval.fastEvalInst inst fs

/-- Radix-tree depth covering `2 ^ 62` 32-bit instruction words (`2 ^ 64` bytes). -/
def progPlacedDepth : Nat := 62

def progPlacedWordBound : Nat := 2 ^ progPlacedDepth

/-- Pre-decoded action at word index `idx = pc.toNat / 4 < 2 ^ 62`. -/
inductive StepEntryPlaced where
  | instr (i : Arm64.Instr)
  | hook (name : String)
  | unmapped
  deriving Repr

/-- Relocatable program bundle: `addrs` for `mallocng` subroutines, `hooks` stub tree at depth 62,
and `rxLines` sharing `baseLines` for on-demand cache-line decoding. -/
structure FastProgPlaced where
  addrs   : MallocngCallAddrs := {}
  hooks   : BinTree String := .empty
  rxLines : BinTree Line64 := .empty
  deriving Repr

/-- Prebuilt ELF memory lines and program table shared across invocations of a placed binary. -/
structure PrebuiltElfPlaced where
  baseLines : BinTree Line64
  prog      : FastProgPlaced

/-- Decode word `w < 16` (`4 * w .. 4 * w + 3`) of a 64-byte cache line `line`; returns `.instr`
only when all four bytes are executable and non-writable (`x && !w`, hence `Frozen`). -/
def decodeStepFromLinePlaced (line : Line64) (w : Nat) : StepEntryPlaced :=
  match btGet 6 line (4 * w), btGet 6 line (4 * w + 1),
        btGet 6 line (4 * w + 2), btGet 6 line (4 * w + 3) with
  | some (some p0, b0), some (some p1, b1), some (some p2, b2), some (some p3, b3) =>
    if p0.x && !p0.w && p1.x && !p1.w && p2.x && !p2.w && p3.x && !p3.w then
      match Arm64.decode (b3 ++ b2 ++ b1 ++ b0) with
      | some inst => .instr inst
      | none => .unmapped
    else .unmapped
  | _, _, _, _ => .unmapped

def withForcedUInt8ListPlaced {α : Type} : List UInt8 → (List UInt8 → α) → α
  | [], k => k []
  | b :: bs, k => withForcedUInt8ListPlaced bs fun bs' => k (b :: bs')

@[simp] theorem withForcedUInt8ListPlaced_eq {α : Type} (bs : List UInt8)
    (k : List UInt8 → α) : withForcedUInt8ListPlaced bs k = k bs := by
  induction bs generalizing k with
  | nil => rfl
  | cons b bs ih => exact ih (fun bs' => k (b :: bs'))

def withForcedNameTablePlaced {α : Type} : List (List UInt8) → (List (List UInt8) → α) → α
  | [], k => k []
  | nm :: nms, k =>
    withForcedUInt8ListPlaced nm fun nm' =>
    withForcedNameTablePlaced nms fun nms' =>
      k (nm' :: nms')

@[simp] theorem withForcedNameTablePlaced_eq {α : Type} (nms : List (List UInt8))
    (k : List (List UInt8) → α) : withForcedNameTablePlaced nms k = k nms := by
  induction nms generalizing k with
  | nil => rfl
  | cons nm nms ih =>
    simp only [withForcedNameTablePlaced, withForcedUInt8ListPlaced_eq]
    exact ih (fun nms' => k (nm :: nms'))

def hookPlacedExactNamesBs (W : CliHooks) : List (List UInt8) :=
  panicPlacedExactNamesBs ++
    ((fastHookTablePlaced (fun _ => none) {} W).map Prod.fst).map strUtf8Bytes

def hasHookPlacedBs (pfx : List UInt8) (tbl : List (List UInt8)) (bs : List UInt8) : Bool :=
  listUInt8IsPrefix pfx bs || tbl.any (fun p => listUInt8Eq bs p)

def overlayHooksPlacedAux (pfx : List UInt8) (tbl : List (List UInt8)) :
    List (String × Nat) → BinTree String → BinTree String
  | [], tr => tr
  | (name, vaddr) :: rest, tr =>
    withForcedBinTree (overlayHooksPlacedAux pfx tbl rest tr) fun tr' =>
      if Nat.beq (Nat.mod vaddr 4) 0 && Nat.blt (Nat.div vaddr 4) progPlacedWordBound &&
          hasHookPlacedBs pfx tbl (strUtf8Bytes name) then
        btSet progPlacedDepth tr' (Nat.div vaddr 4) name
      else
        tr'

/-- Overlay hooked `(symbolName, absoluteVaddr)` entries into a depth-62 `BinTree String` in reverse
list order so the first hooked stub at `vaddr` wins. -/
def overlayHooksPlaced (W : CliHooks) (stubs : List (String × Nat)) (tr : BinTree String) :
    BinTree String :=
  withForcedUInt8ListPlaced panicPrefixBs fun pfx =>
  withForcedNameTablePlaced (hookPlacedExactNamesBs W) fun tbl =>
    overlayHooksPlacedAux pfx tbl stubs tr

def overlayHooksPlacedBv (W : CliHooks) (stubs : List (String × BitVec 64)) (tr : BinTree String) :
    BinTree String :=
  overlayHooksPlaced W (stubs.map fun (nm, va) => (nm, va.toNat)) tr

/-- Resolve word index `idx = pc.toNat / 4 < 2 ^ 62`, giving `fp.hooks` priority over `fp.rxLines`. -/
def lookupStepEntryPlaced (fp : FastProgPlaced) (idx : Nat) : StepEntryPlaced :=
  match btGet progPlacedDepth fp.hooks idx with
  | some name => .hook name
  | none =>
    match btGet 58 fp.rxLines (Nat.div idx 16) with
    | some line => decodeStepFromLinePlaced line (Nat.mod idx 16)
    | none => .unmapped

/-- Direct memory-fetching single-step runner for hook-free `mallocng` subroutines. -/
def fastStepMemPlaced (evalF : Arm64.Instr → FastState → Option FastState) (fs : FastState) :
    Option FastState :=
  match fs.status with
  | .Running =>
    if fs.pc.toNat % 4 == 0 && fs.mem.canExec fs.pc 4 then
      match Arm64.decode (fs.mem.read32 fs.pc) with
      | some inst => evalF inst fs
      | none => none
    else none
  | _ => none

abbrev fastStepPlacedSub : FastState → Option FastState :=
  fastStepMemPlaced fastEvalInstPlaced

/-- Execute one step of `fp` from `fs` under extern hooks `W`, instruction evaluator `evalF`, and
subroutine stepper `subStep`. -/
def fastStepPlacedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced) (fs : FastState) :
    Option FastState :=
  match fs.status with
  | .Running =>
    let va := fs.pc.toNat
    if Nat.beq (Nat.mod va 4) 0 && Nat.blt (Nat.div va 4) progPlacedWordBound then
      match lookupStepEntryPlaced fp (Nat.div va 4) with
      | .instr inst => evalF inst fs
      | .hook name => fastExecExternPlaced subStep fp.addrs W name fs
      | .unmapped => none
    else
      none
  | _ => none

abbrev fastStepPlacedW (W : CliHooks) : FastProgPlaced → FastState → Option FastState :=
  fastStepPlacedCoreW W fastEvalInstPlaced fastStepPlacedSub

abbrev fastStepPlaced : FastProgPlaced → FastState → Option FastState :=
  fastStepPlacedW compHooks0

/-- Run up to `fuel` steps of `fastStepPlacedCoreW`, returning early once `fs.status ≠ .Running`. -/
def fastRunStepsPlacedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) :
    Nat → FastProgPlaced → FastState → Option FastState
  | 0, _, fs => some fs
  | fuel + 1, fp, fs =>
    match fs.status with
    | .Running =>
      match fastStepPlacedCoreW W evalF subStep fp fs with
      | some fs' => fastRunStepsPlacedCoreW W evalF subStep fuel fp fs'
      | none => none
    | _ => some fs

abbrev fastRunStepsPlacedW (W : CliHooks) : Nat → FastProgPlaced → FastState → Option FastState :=
  fastRunStepsPlacedCoreW W fastEvalInstPlaced fastStepPlacedSub

abbrev fastRunStepsPlaced : Nat → FastProgPlaced → FastState → Option FastState :=
  fastRunStepsPlacedW compHooks0

/-- Execute up to `2 ^ k` steps of `fastStepPlacedCoreW` by recursive doubling. -/
def fastRunPow2PlacedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced) :
    Nat → FastState → Option FastState
  | 0, fs =>
    match fs.status with
    | .Running => fastStepPlacedCoreW W evalF subStep fp fs
    | _ => some fs
  | k + 1, fs =>
    match fs.status with
    | .Running =>
      match fastRunPow2PlacedCoreW W evalF subStep fp k fs with
      | some fs' => fastRunPow2PlacedCoreW W evalF subStep fp k fs'
      | none => none
    | _ => some fs

abbrev fastRunPow2PlacedW (W : CliHooks) : FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunPow2PlacedCoreW W fastEvalInstPlaced fastStepPlacedSub

abbrev fastRunPow2Placed : FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunPow2PlacedW compHooks0

/-- Reflexive-transitive reachability relation generated by fuel-bounded and `2 ^ k`-step chunks. -/
inductive FastReachablePlacedCoreW (W : CliHooks)
    (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced) :
    FastState → FastState → Prop where
  | refl (fs : FastState) : FastReachablePlacedCoreW W evalF subStep fp fs fs
  | chunk {fs1 fs2 : FastState} (fuel : Nat)
      (h : fastRunStepsPlacedCoreW W evalF subStep fuel fp fs1 = some fs2) :
      FastReachablePlacedCoreW W evalF subStep fp fs1 fs2
  | pow2 {fs1 fs2 : FastState} (k : Nat)
      (h : fastRunPow2PlacedCoreW W evalF subStep fp k fs1 = some fs2) :
      FastReachablePlacedCoreW W evalF subStep fp fs1 fs2
  | trans {fs1 fs2 fs3 : FastState}
      (h1 : FastReachablePlacedCoreW W evalF subStep fp fs1 fs2)
      (h2 : FastReachablePlacedCoreW W evalF subStep fp fs2 fs3) :
      FastReachablePlacedCoreW W evalF subStep fp fs1 fs3

abbrev FastReachablePlacedW (W : CliHooks) : FastProgPlaced → FastState → FastState → Prop :=
  FastReachablePlacedCoreW W fastEvalInstPlaced fastStepPlacedSub

abbrev FastReachablePlaced : FastProgPlaced → FastState → FastState → Prop :=
  FastReachablePlacedW compHooks0

/-- Insert `e : StepEntryPlaced` into `ic` after forcing `e` to constructor WHNF. -/
def btSetStepPlaced (ic : BinTree StepEntryPlaced) (idx : Nat) (e : StepEntryPlaced) :
    BinTree StepEntryPlaced :=
  match e with
  | .instr i => btSet progPlacedDepth ic idx (.instr i)
  | .hook nm => btSet progPlacedDepth ic idx (.hook nm)
  | .unmapped => btSet progPlacedDepth ic idx .unmapped

private theorem btSetStepPlaced_eq (ic : BinTree StepEntryPlaced) (idx : Nat)
    (e : StepEntryPlaced) :
    btSetStepPlaced ic idx e = btSet progPlacedDepth ic idx e := by
  cases e <;> rfl

/-- Every populated entry in the depth-62 instruction cache `ic` agrees with
`lookupStepEntryPlaced fp`. -/
def ICachePlacedSound (fp : FastProgPlaced) (ic : BinTree StepEntryPlaced) : Prop :=
  ∀ idx < progPlacedWordBound, ∀ e,
    btGet progPlacedDepth ic idx = some e → lookupStepEntryPlaced fp idx = e

theorem icachePlacedSound_empty (fp : FastProgPlaced) : ICachePlacedSound fp .empty := by
  intro _ _ _ h
  rw [btGet_empty] at h
  nomatch h

/-- Single-step runner that consults and populates `ic : BinTree StepEntryPlaced` on demand. -/
def fastStepCachedPlacedCoreW (W : CliHooks) (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced)
    (ic : BinTree StepEntryPlaced) (fs : FastState) :
    Option (BinTree StepEntryPlaced × FastState) :=
  match fs.status with
  | .Running =>
    let va := fs.pc.toNat
    if Nat.beq (Nat.mod va 4) 0 && Nat.blt (Nat.div va 4) progPlacedWordBound then
      let idx := Nat.div va 4
      match btGet progPlacedDepth ic idx with
      | some (.instr inst) =>
        match evalF inst fs with
        | some fs' => some (ic, fs')
        | none => none
      | some (.hook name) =>
        match fastExecExternPlaced subStep fp.addrs W name fs with
        | some fs' => some (ic, fs')
        | none => none
      | some .unmapped => none
      | none =>
        let e := lookupStepEntryPlaced fp idx
        withForcedBinTree (btSetStepPlaced ic idx e) fun ic' =>
          match e with
          | .instr inst =>
            match evalF inst fs with
            | some fs' => some (ic', fs')
            | none => none
          | .hook name =>
            match fastExecExternPlaced subStep fp.addrs W name fs with
            | some fs' => some (ic', fs')
            | none => none
          | .unmapped => none
    else
      none
  | _ => none

theorem fastStepCachedPlacedCoreW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {subStep : FastState → Option FastState}
    {fp : FastProgPlaced} {ic ic' : BinTree StepEntryPlaced} {fs fs' : FastState}
    (hic : ICachePlacedSound fp ic)
    (h : fastStepCachedPlacedCoreW W evalF subStep fp ic fs = some (ic', fs')) :
    ICachePlacedSound fp ic' ∧ fastStepPlacedCoreW W evalF subStep fp fs = some fs' := by
  unfold fastStepCachedPlacedCoreW at h
  unfold fastStepPlacedCoreW
  revert h; cases fs.status <;> intro h
  · dsimp only at h ⊢
    split at h; swap; · nomatch h
    rename_i hcond
    simp only [hcond, ↓reduceIte]
    have hlt : Nat.div fs.pc.toNat 4 < progPlacedWordBound := by
      simp only [Bool.and_eq_true, Nat.blt_eq] at hcond; exact hcond.2
    cases hget : btGet progPlacedDepth ic (Nat.div fs.pc.toNat 4) with
    | some e =>
      rw [hget] at h
      rw [hic _ hlt e hget]
      cases e with
      | instr inst =>
        dsimp only at h ⊢
        cases hev : evalF inst fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
      | hook name =>
        dsimp only at h ⊢
        cases hev : fastExecExternPlaced subStep fp.addrs W name fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
      | unmapped => nomatch h
    | none =>
      rw [hget] at h
      simp only [withForcedBinTree_eq] at h
      have hic_new : ICachePlacedSound fp (btSetStepPlaced ic (Nat.div fs.pc.toNat 4)
          (lookupStepEntryPlaced fp (Nat.div fs.pc.toNat 4))) := by
        intro j hj e' hgj
        rw [btSetStepPlaced_eq] at hgj
        by_cases hjeq : Nat.div fs.pc.toNat 4 = j
        · subst hjeq
          rw [btGet_btSet_same'] at hgj
          injection hgj
        · rw [btGet_btSet_ne progPlacedDepth _ j ic _ hlt hj hjeq] at hgj
          exact hic j hj e' hgj
      cases he : lookupStepEntryPlaced fp (Nat.div fs.pc.toNat 4) with
      | instr inst =>
        rw [he] at h hic_new
        dsimp only at h ⊢
        cases hev : evalF inst fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic_new, rfl⟩
      | hook name =>
        rw [he] at h hic_new
        dsimp only at h ⊢
        cases hev : fastExecExternPlaced subStep fp.addrs W name fs <;> rw [hev] at h
        · nomatch h
        · injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic_new, rfl⟩
      | unmapped =>
        rw [he] at h; nomatch h
  all_goals nomatch h

def fastRunPow2CachedPlacedCoreW (W : CliHooks)
    (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced) :
    Nat → BinTree StepEntryPlaced → FastState → Option (BinTree StepEntryPlaced × FastState)
  | 0, ic, fs =>
    match fs.status with
    | .Running => fastStepCachedPlacedCoreW W evalF subStep fp ic fs
    | _ => some (ic, fs)
  | k + 1, ic, fs =>
    match fs.status with
    | .Running =>
      match fastRunPow2CachedPlacedCoreW W evalF subStep fp k ic fs with
      | some (ic1, fs1) => fastRunPow2CachedPlacedCoreW W evalF subStep fp k ic1 fs1
      | none => none
    | _ => some (ic, fs)

theorem fastRunPow2CachedPlacedCoreW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {subStep : FastState → Option FastState}
    {fp : FastProgPlaced} {k : Nat} {ic ic' : BinTree StepEntryPlaced} {fs fsf : FastState}
    (hic : ICachePlacedSound fp ic)
    (h : fastRunPow2CachedPlacedCoreW W evalF subStep fp k ic fs = some (ic', fsf)) :
    ICachePlacedSound fp ic' ∧ fastRunPow2PlacedCoreW W evalF subStep fp k fs = some fsf := by
  induction k generalizing ic ic' fs fsf with
  | zero =>
    unfold fastRunPow2CachedPlacedCoreW at h
    unfold fastRunPow2PlacedCoreW
    revert h; cases fs.status <;> intro h
    · exact fastStepCachedPlacedCoreW_eq hic h
    all_goals
      dsimp only at h ⊢
      injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩
  | succ n ih =>
    unfold fastRunPow2CachedPlacedCoreW at h
    unfold fastRunPow2PlacedCoreW
    revert h; cases fs.status <;> intro h
    · dsimp only at h ⊢
      cases hmid : fastRunPow2CachedPlacedCoreW W evalF subStep fp n ic fs with
      | none => rw [hmid] at h; nomatch h
      | some p =>
        rcases p with ⟨ic1, fs1⟩
        rw [hmid] at h
        obtain ⟨hic1, hr1⟩ := ih hic hmid
        obtain ⟨hic2, hr2⟩ := ih hic1 h
        rw [hr1]; exact ⟨hic2, hr2⟩
    all_goals
      dsimp only at h ⊢
      injection h with hp; injection hp with h1 h2; subst h1 h2; exact ⟨hic, rfl⟩

/-- Execute one `2 ^ k`-step chunk with a fresh `.empty` instruction cache. -/
def fastRunChunkCachedPlacedCoreW (W : CliHooks)
    (evalF : Arm64.Instr → FastState → Option FastState)
    (subStep : FastState → Option FastState) (fp : FastProgPlaced) (k : Nat) (fs : FastState) :
    Option FastState :=
  match fastRunPow2CachedPlacedCoreW W evalF subStep fp k .empty fs with
  | some (_, fs') => some fs'
  | none => none

theorem fastRunChunkCachedPlacedCoreW_eq
    {W : CliHooks} {evalF : Arm64.Instr → FastState → Option FastState}
    {subStep : FastState → Option FastState}
    {fp : FastProgPlaced} {k : Nat} {fs fsf : FastState}
    (h : fastRunChunkCachedPlacedCoreW W evalF subStep fp k fs = some fsf) :
    fastRunPow2PlacedCoreW W evalF subStep fp k fs = some fsf := by
  unfold fastRunChunkCachedPlacedCoreW at h
  cases hm : fastRunPow2CachedPlacedCoreW W evalF subStep fp k .empty fs with
  | none => rw [hm] at h; nomatch h
  | some p =>
    rcases p with ⟨ic', fs'⟩
    rw [hm] at h; injection h with heq; subst heq
    exact (fastRunPow2CachedPlacedCoreW_eq (icachePlacedSound_empty fp) hm).2

abbrev fastRunChunkCachedPlacedW (W : CliHooks) : FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunChunkCachedPlacedCoreW W fastEvalInstPlaced fastStepPlacedSub

abbrev fastRunChunkCachedPlaced : FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunChunkCachedPlacedW compHooks0

theorem fastRunChunkCachedPlaced_eq {fp : FastProgPlaced} {k : Nat} {fs fsf : FastState}
    (h : fastRunChunkCachedPlaced fp k fs = some fsf) :
    fastRunPow2Placed fp k fs = some fsf :=
  fastRunChunkCachedPlacedCoreW_eq h

/-- Validate `elf` (`WellFormed`, non-wrapping `brkStart`, and placed token-patch bounds). -/
def checkElfPrebuildOkPlaced (elf : ElfImage) (regsWithLen : List (Snapshot.Region × Nat))
    (tokStorageAddr tokOnceAddr : BitVec 64) : Bool :=
  !elf.segments.isEmpty &&
  elf.phent == 56 &&
  fastRegionsDisjointAndAligned regsWithLen &&
  fastEntryInExecRegion elf.entry regsWithLen &&
  elf.brkStart.toNat % Obj.pageSize == 0 &&
  regsWithLen.all (fun (r, len) => r.start.toNat + len ≤ elf.brkStart.toNat) &&
  elf.brkStart.toNat ≤ 2 ^ 48 &&
  tokStorageAddr.toNat + 1 ≤ elf.brkStart.toNat &&
  tokOnceAddr.toNat + 12 ≤ elf.brkStart.toNat

/-- Build the initial `FastState` for `pinputs` by overlaying the initial stack region onto
`pb.baseLines`. -/
def initFastStateFromBasePlacedProcess (elf : ElfImage) (pb : PrebuiltElfPlaced)
    (pinputs : ProcessInputs) : Option FastState :=
  if pinputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) then
    none
  else if pinputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) then
    none
  else
    match buildInitialStack elf pinputs with
    | .error _ => none
    | .ok (sp, stackRegion) =>
      let top := pinputs.init.stackTop.toNat
      let sz := pinputs.init.stackSize
      RadixMemAux.withForcedNat stackRegion.bytes.length fun stackLen =>
        if sz ≤ top then
          let sb := top - sz
          if elf.brkStart.toNat ≤ sb &&
              sb ≤ stackRegion.start.toNat &&
              stackRegion.start.toNat + stackLen ≤ top &&
              top ≤ 2 ^ 60 then
            let stackCells :=
              regionToCells stackRegion.perm stackRegion.nonAnonLen 0 stackRegion.bytes
            withForcedBinTree (setCellsAt pb.baseLines stackRegion.start.toNat stackCells)
              fun lines =>
                let fm : FastMem := { lines := lines, stackBase := sb, stackTop := top }
                some {
                  regs         := FastRegs.empty
                  sp           := sp
                  pc           := elf.entry
                  pstate       := PState.zero
                  mem          := fm
                  heapIvs      := []
                  tpidrEl0     := 0#64
                  fpsr         := 0#32
                  brkStart     := elf.brkStart
                  brk          := elf.brkStart
                  physMemAvail := pinputs.init.physMemAvail
                  fs           := initFastFs pinputs
                  oracle       := pinputs.init.oracle
                  oracleIdx    := 0
                  exclFails    := pinputs.init.oracle.exclFails
                  trace        := []
                  status       := .Running
                  sigAltStack  := {}
                }
          else none
        else none

def initFastStateFromBasePlaced (elf : ElfImage) (pb : PrebuiltElfPlaced) (inp : Inputs) :
    Option FastState :=
  initFastStateFromBasePlacedProcess elf pb (cliProcessInputs inp)

def isExitedWith (st : ExecStatus) (code : BitVec 64) : Bool :=
  match st with
  | .Exited c => c == code
  | _ => false

def isSignaledWith (st : ExecStatus) (sig : BitVec 7) : Bool :=
  match st with
  | .Signaled s => s == sig
  | _ => false

/-- Check `.Exited expectedCode` termination with expected `stdout` bytes and filesystem view. -/
def checkFastExited (fs : FastState) (expectedCode : BitVec 64)
    (expectedStdout : List (BitVec 8))
    (expectedFiles : List (String × List (BitVec 8))) : Bool :=
  isExitedWith fs.status expectedCode &&
  ProcessOutcome.traceStreamBytes .stdout fs.trace == expectedStdout &&
  fastFsMatchesFilesOf fs.fs expectedFiles

def checkFastExited0 (fs : FastState) (expectedStdout : List (BitVec 8))
    (expectedFiles : List (String × List (BitVec 8))) : Bool :=
  checkFastExited fs 0#64 expectedStdout expectedFiles

def checkFastAborted (fs : FastState) : Bool :=
  isSignaledWith fs.status sigAbrt

theorem checkFastExited_sound
    {fs : FastState} {sf : State} {code : BitVec 64}
    {expectedStdout : List (BitVec 8)} {expectedFiles : List (String × List (BitVec 8))}
    (hag : fs.Agrees sf)
    (hchk : checkFastExited fs code expectedStdout expectedFiles = true) :
    sf.status = .Exited code ∧
      OutcomeMatchesProcess
        (.exited (code.toNat % 256) expectedStdout (filesOf expectedFiles))
        (ProcessOutcome.ofState code sf) := by
  unfold checkFastExited at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hexit, hstdout⟩, hfiles⟩
  have hst : sf.status = .Exited code := by
    rw [← hag.status]
    cases h : fs.status <;> simp [isExitedWith, h] at hexit
    exact congrArg ExecStatus.Exited hexit
  have hout_eq : ProcessOutcome.traceStreamBytes .stdout sf.trace = expectedStdout := by
    rw [← hag.trace]
    exact eq_of_beq hstdout
  have hfs_eq : CryptoVerification.SignalSession.fsView sf.fs = filesOf expectedFiles :=
    fastFsMatchesFilesOf_sound hag.fs hfiles
  exact ⟨hst, rfl, rfl, hout_eq, hfs_eq⟩

theorem checkFastExited0_sound
    {fs : FastState} {sf : State}
    {expectedStdout : List (BitVec 8)} {expectedFiles : List (String × List (BitVec 8))}
    (hag : fs.Agrees sf)
    (hchk : checkFastExited0 fs expectedStdout expectedFiles = true) :
    sf.status = .Exited 0#64 ∧
      OutcomeMatchesProcess
        (.exited 0 expectedStdout (filesOf expectedFiles))
        (ProcessOutcome.ofState 0#64 sf) :=
  checkFastExited_sound hag hchk

theorem checkFastAborted_sound
    {fs : FastState} {sf : State}
    (hag : fs.Agrees sf)
    (hchk : checkFastAborted fs = true) :
    sf.status = .Signaled sigAbrt ∧
      OutcomeMatchesProcess .aborted (ProcessOutcome.ofSignal sigAbrt sf) := by
  unfold checkFastAborted at hchk
  have hst : sf.status = .Signaled sigAbrt := by
    rw [← hag.status]
    cases h : fs.status <;> simp [isSignaledWith, h] at hchk
    exact congrArg ExecStatus.Signaled hchk
  exact ⟨hst, rfl, rfl⟩

end Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
