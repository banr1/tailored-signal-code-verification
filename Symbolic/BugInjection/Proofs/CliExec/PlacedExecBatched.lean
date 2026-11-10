/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar
public import Symbolic.BugInjection.Proofs.CliExec.FastEval
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore

/-!
# Line-Batched Placed Executor

Defines cache-line-batched counterparts (`*B`) of the placed VM syscall evaluators, instruction
evaluator, single-stepper, and `2 ^ n`-step chunk runners from `PlacedExecCore` and
`ElfFullSpecPlacedCore`, and proves each equal (`=`) to its unbatched original via
`RadixMemPlacedBatched`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.PlacedExecBatched

open Arm64 Arm64.Memory
open CryptoVerification.SignalSession (CliHooks Inputs)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced (sanitizeMmapAddrFast)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched (sanitizeMmapAddrFastB
  sanitizeMmapAddrFast_eq_batched)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (FastProgPlaced PrebuiltElfPlaced
  fastSetBrk fastSetPhysMemAvail fastNextOracle fastExecFcntl fastExecOpenat
  fastExecClose fastExecRead fastExecFstat fastExecBrk fastExecMunmap fastExecMremap
  fastExecMmap fastExecMprotect fastExecSyscallPlaced fastExecStxr fastEvalInstPlaced
  fastStepMemPlaced fastStepPlacedSub fastRunChunkCachedPlacedCoreW fastRunChunkCachedPlaced
  initFastStateFromBasePlaced checkFastExited0 checkFastExited checkFastAborted)
open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (ElfFullSpecPlaced MkCkpt
  prebuiltOfFullPlaced headerElfOfFullPlaced runElfChunkPlacedLHS
  checkElfFinalChunkPlacedExited0 checkElfFinalChunkPlacedExited
  checkElfFinalChunkPlacedAborted)

/-- Cache-line-batched counterpart of `FastMem.remapRw`. -/
def remapRwB (fm : FastMem) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) : FastMem :=
  let fmUnmapped := fm.unmapNonFrozenB oldBase oldSize
  let cNewSize := min newSize (2 ^ 64)
  let copyLen := min cNewSize oldSize
  let fmCopied := FastMem.remapWriteLoop fm oldBase oldSize newBase fmUnmapped 0 copyLen
  if copyLen < cNewSize then
    let zeroBase := newBase + BitVec.ofNat 64 copyLen
    let zeroLen := cNewSize - copyLen
    if !(fm.allPermB (fun p => !p.frozen) zeroBase zeroLen) ||
        !(fmCopied.canMapB zeroBase zeroLen) then
      FastMem.remapWriteLoop fm oldBase oldSize newBase fmCopied copyLen zeroLen
    else
      fmCopied.mapZeroB zeroBase zeroLen
  else
    fmCopied

theorem remapRw_eq_batched (fm : FastMem) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) :
    fm.remapRw oldBase oldSize newBase newSize = remapRwB fm oldBase oldSize newBase newSize := by
  unfold FastMem.remapRw remapRwB
  simp only [FastMem.unmapNonFrozen_eq_batched, FastMem.allPerm_eq_batched,
    FastMem.canMap_eq_batched, FastMem.mapZero_eq_batched]

def fastExecBrkB (fs : FastState) : Option FastState :=
  let addr := fs.readReg64 Reg.x0
  if addr == 0#64 || addr.ult fs.brkStart then
    some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
  else
    let oldPage := Arm64.pageAlignUp fs.brk.toNat
    let newPage := Arm64.pageAlignUp addr.toNat
    if decide (newPage ≤ oldPage) then
      let shrinkBytes := oldPage - newPage
      if !fs.mem.allPermB (·.mapped) (BitVec.ofNat 64 newPage) shrinkBytes then
        some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
      else if !decide (oldPage ≤ USER_VA_LIMIT) then
        none
      else
        let reclaimed := fs.mem.countRwB (BitVec.ofNat 64 newPage) shrinkBytes
        let mem := fs.mem.unmapWritableB (BitVec.ofNat 64 newPage) shrinkBytes
        some (((((fastSetBrk fs addr).setMem mem |>
          fun st => fastSetPhysMemAvail st (fs.physMemAvail + reclaimed)).writeReg64
            Reg.x0 addr)).advancePC)
    else
      let growBytes := newPage - oldPage
      if !decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) ||
          !fs.mem.canMapB (BitVec.ofNat 64 oldPage) (growBytes + BRK_GUARD_GAP) then
        some ((fs.writeReg64 Reg.x0 fs.brk).advancePC)
      else if !decide (growBytes ≤ fs.physMemAvail) then
        some (fs.setStatus .OutOfMemory)
      else
        let mem := fs.mem.mapZeroB (BitVec.ofNat 64 oldPage) growBytes
        some (((((fastSetBrk fs addr).setMem mem |>
          fun st => fastSetPhysMemAvail st (fs.physMemAvail - growBytes)).writeReg64
            Reg.x0 addr)).advancePC)

theorem fastExecBrk_eq_batched (fs : FastState) :
    fastExecBrk fs = fastExecBrkB fs := by
  unfold fastExecBrk fastExecBrkB
  simp only [FastMem.allPerm_eq_batched, FastMem.countRw_eq_batched,
    FastMem.unmapWritable_eq_batched, FastMem.canMap_eq_batched, FastMem.mapZero_eq_batched]

def fastExecMunmapB (fs : FastState) : Option FastState :=
  let addr := fs.readReg64 Reg.x0
  let len := (fs.readReg64 Reg.x1).toNat
  let size := Arm64.pageAlignUp len
  if addr.toNat % PAGE_SIZE != 0 || len == 0 || !decide (addr.toNat + size ≤ 2 ^ 48) then
    some ((fs.writeReg64 Reg.x0 (-EINVAL)).advancePC)
  else if !fs.mem.allPermB (fun p => !p.frozen) addr size then
    none
  else
    let reclaimed := fs.mem.countRwB addr size
    some (((fastSetPhysMemAvail (fs.setMem (fs.mem.unmapNonFrozenB addr size))
      (fs.physMemAvail + reclaimed)).writeReg64 Reg.x0 0#64).advancePC)

theorem fastExecMunmap_eq_batched (fs : FastState) :
    fastExecMunmap fs = fastExecMunmapB fs := by
  unfold fastExecMunmap fastExecMunmapB
  simp only [FastMem.allPerm_eq_batched, FastMem.countRw_eq_batched,
    FastMem.unmapNonFrozen_eq_batched]

def fastExecMremapB (fs : FastState) : Option FastState :=
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
    else if !fs.mem.allPermB (fun p => !p.frozen) oldAddr oldAligned then
      none
    else if fs.mem.canMapB oldAddr oldAligned then
      some ((fs.writeReg64 Reg.x0 EFAULT_RET).advancePC)
    else if !fs.mem.allPermB (· == some Perm.rw) oldAddr oldAligned then
      none
    else if !fs.mem.allAnonB oldAddr oldAligned then
      none
    else if fs.oracle.mremapFail fs.oracleIdx then
      some (((fastNextOracle fs).writeReg64 Reg.x0 (-ENOMEM)).advancePC)
    else
      let fmUnmapped := fs.mem.unmapNonFrozenB oldAddr oldAligned
      match sanitizeMmapAddrFastB fmUnmapped (fs.oracle.mmap fs.oracleIdx) newAligned with
      | none =>
        some (((fastNextOracle fs).writeReg64 Reg.x0 (-ENOMEM)).advancePC)
      | some newBase =>
        if !decide (newAligned ≤ fs.physMemAvail + oldAligned) then
          some (fs.setStatus .OutOfMemory)
        else
          let fm' := remapRwB fs.mem oldAddr oldAligned newBase newAligned
          let st1 := fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail + oldAligned - newAligned)
          some (((fastNextOracle st1).writeReg64 Reg.x0 newBase).advancePC)

theorem fastExecMremap_eq_batched (fs : FastState) :
    fastExecMremap fs = fastExecMremapB fs := by
  unfold fastExecMremap fastExecMremapB
  simp only [FastMem.allPerm_eq_batched, FastMem.canMap_eq_batched, FastMem.allAnon_eq_batched,
    FastMem.unmapNonFrozen_eq_batched, sanitizeMmapAddrFast_eq_batched, remapRw_eq_batched]
  rfl

def fastExecMmapB (fs : FastState) : Option FastState :=
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
    else if !fs.mem.allPermB (fun p => !p.frozen) addr size then
      none
    else
      let reclaimed := fs.mem.countRwB addr size
      if prot == MMAP_PROT_NONE then
        let fm' := ((fs.mem.unmapNonFrozenB addr size).mapZeroB addr size).setPermNonFrozenB
          addr size Perm.protNone
        some (((fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail + reclaimed)).writeReg64
          Reg.x0 addr).advancePC)
      else if !decide (size ≤ fs.physMemAvail + reclaimed) then
        some (fs.setStatus .OutOfMemory)
      else
        let fm' := (fs.mem.unmapNonFrozenB addr size).mapZeroB addr size
        some (((fastSetPhysMemAvail (fs.setMem fm')
          (fs.physMemAvail + reclaimed - size)).writeReg64 Reg.x0 addr).advancePC)
  else
    let size := Arm64.pageAlignUp len
    match sanitizeMmapAddrFastB fs.mem (fs.oracle.mmap fs.oracleIdx) size with
    | some base =>
      if prot == MMAP_PROT_NONE then
        let fm' := (fs.mem.mapZeroB base size).setPermNonFrozenB base size Perm.protNone
        some (((fastNextOracle (fs.setMem fm')).writeReg64 Reg.x0 base).advancePC)
      else if !decide (size ≤ fs.physMemAvail) then
        some (fs.setStatus .OutOfMemory)
      else
        let fm' := fs.mem.mapZeroB base size
        let st1 := fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail - size)
        some (((fastNextOracle st1).writeReg64 Reg.x0 base).advancePC)
    | none =>
      some (fs.setStatus .OutOfMemory)

theorem fastExecMmap_eq_batched (fs : FastState) :
    fastExecMmap fs = fastExecMmapB fs := by
  unfold fastExecMmap fastExecMmapB
  simp only [FastMem.allPerm_eq_batched, FastMem.countRw_eq_batched,
    FastMem.unmapNonFrozen_eq_batched, FastMem.mapZero_eq_batched,
    FastMem.setPermNonFrozen_eq_batched, sanitizeMmapAddrFast_eq_batched]
  rfl

def fastExecMprotectB (fs : FastState) : Option FastState :=
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
  else if !fs.mem.allPermB (fun p => !p.frozen) addr size then
    none
  else if !fs.mem.allPermB (·.mapped) addr size then
    if fs.mem.canMapB addr size then
      some ((fs.writeReg64 Reg.x0 (-ENOMEM)).advancePC)
    else
      none
  else if prot == MMAP_PROT_NONE then
    some (((fs.setMem (fs.mem.setPermNonFrozenB addr size Perm.protNone)).writeReg64
      Reg.x0 0#64).advancePC)
  else
    let oldRw := fs.mem.countRwB addr size
    let needed := size - oldRw
    if !decide (needed ≤ fs.physMemAvail) then
      some (fs.setStatus .OutOfMemory)
    else
      let fm' := fs.mem.setPermNonFrozenB addr size Perm.rw
      some (((fastSetPhysMemAvail (fs.setMem fm') (fs.physMemAvail - needed)).writeReg64
        Reg.x0 0#64).advancePC)

theorem fastExecMprotect_eq_batched (fs : FastState) :
    fastExecMprotect fs = fastExecMprotectB fs := by
  unfold fastExecMprotect fastExecMprotectB
  simp only [FastMem.allPerm_eq_batched, FastMem.canMap_eq_batched,
    FastMem.setPermNonFrozen_eq_batched, FastMem.countRw_eq_batched]

def fastExecSyscallPlacedB (fs : FastState) : Option FastState :=
  let nr := fs.readReg64 Reg.x8
  if nr == 25#64 then fastExecFcntl fs
  else if nr == 56#64 then fastExecOpenat fs
  else if nr == 57#64 then fastExecClose fs
  else if nr == 63#64 then fastExecRead fs
  else if nr == 80#64 then fastExecFstat fs
  else if nr == 93#64 || nr == 94#64 then some (fs.setStatus (.Exited (fs.readReg64 Reg.x0)))
  else if nr == 96#64 then some ((fs.writeReg64 Reg.x0 SIM_TID).advancePC)
  else if nr == 214#64 then fastExecBrkB fs
  else if nr == 215#64 then fastExecMunmapB fs
  else if nr == 216#64 then fastExecMremapB fs
  else if nr == 222#64 then fastExecMmapB fs
  else if nr == 226#64 then fastExecMprotectB fs
  else none

theorem fastExecSyscallPlaced_eq_batched (fs : FastState) :
    fastExecSyscallPlaced fs = fastExecSyscallPlacedB fs := by
  unfold fastExecSyscallPlaced fastExecSyscallPlacedB
  simp only [fastExecBrk_eq_batched, fastExecMunmap_eq_batched, fastExecMremap_eq_batched,
    fastExecMmap_eq_batched, fastExecMprotect_eq_batched]

def fastEvalInstPlacedB (inst : Arm64.Instr) (fs : FastState) : Option FastState :=
  match inst with
  | .system false 0#16 => fastExecSyscallPlacedB fs
  | .ldxr sz _acq rn rt => FastEvalScalar.fastExecLdarStlr sz true rn rt fs
  | .stxr sz _rel rs rn rt => fastExecStxr sz rs rn rt fs
  | .barrier _ _ => some fs.advancePC
  | _ => FastEval.fastEvalInst inst fs

theorem fastEvalInstPlaced_eq_batched :
    fastEvalInstPlaced = fastEvalInstPlacedB := by
  funext inst fs
  cases inst with
  | system msr imm =>
    cases msr
    · by_cases h0 : imm = 0#16
      · subst h0
        exact fastExecSyscallPlaced_eq_batched fs
      · simp [fastEvalInstPlaced, fastEvalInstPlacedB, h0]
    · rfl
  | _ => rfl

abbrev fastStepPlacedSubB : FastState → Option FastState :=
  fastStepMemPlaced fastEvalInstPlacedB

theorem fastStepPlacedSub_eq_batched :
    fastStepPlacedSub = fastStepPlacedSubB := by
  unfold fastStepPlacedSub fastStepPlacedSubB
  rw [fastEvalInstPlaced_eq_batched]

abbrev fastRunChunkCachedPlacedWB (W : CliHooks) :
    FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunChunkCachedPlacedCoreW W fastEvalInstPlacedB fastStepPlacedSubB

abbrev fastRunChunkCachedPlacedB : FastProgPlaced → Nat → FastState → Option FastState :=
  fastRunChunkCachedPlacedWB compHooks0

theorem fastRunChunkCachedPlacedW_eq_batched (W : CliHooks) (fp : FastProgPlaced) (k : Nat)
    (fs : FastState) :
    PlacedExecCore.fastRunChunkCachedPlacedW W fp k fs =
      fastRunChunkCachedPlacedWB W fp k fs := by
  unfold PlacedExecCore.fastRunChunkCachedPlacedW fastRunChunkCachedPlacedWB
  rw [fastEvalInstPlaced_eq_batched, fastStepPlacedSub_eq_batched]

theorem fastRunChunkCachedPlaced_eq_batched (fp : FastProgPlaced) (k : Nat) (fs : FastState) :
    fastRunChunkCachedPlaced fp k fs = fastRunChunkCachedPlacedB fp k fs :=
  fastRunChunkCachedPlacedW_eq_batched compHooks0 fp k fs

/-- Cache-line-batched counterpart of `runElfChunkPlacedLHS`. -/
def runElfChunkPlacedLHSB (spec : ElfFullSpecPlaced) (inp : Inputs) (n : Nat) (ck : MkCkpt) :
    Option FastState :=
  let pb := prebuiltOfFullPlaced spec
  match initFastStateFromBasePlaced (headerElfOfFullPlaced spec) pb inp with
  | none => none
  | some fs0 => fastRunChunkCachedPlacedB pb.prog n (ck pb fs0)

theorem runElfChunkPlacedLHS_eq_batched (spec : ElfFullSpecPlaced) (inp : Inputs) (n : Nat)
    (ck : MkCkpt) :
    runElfChunkPlacedLHS spec inp n ck = runElfChunkPlacedLHSB spec inp n ck := by
  unfold runElfChunkPlacedLHS runElfChunkPlacedLHSB
  dsimp only
  cases initFastStateFromBasePlaced (headerElfOfFullPlaced spec) (prebuiltOfFullPlaced spec) inp with
  | none => rfl
  | some fs0 => exact fastRunChunkCachedPlaced_eq_batched _ n _

def checkElfFinalChunkPlacedExited0B (spec : ElfFullSpecPlaced) (inp : Inputs) (n : Nat)
    (ck : MkCkpt) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFullPlaced spec
  match initFastStateFromBasePlaced (headerElfOfFullPlaced spec) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlacedB pb.prog n (ck pb fs0) with
    | none => false
    | some fsf => checkFastExited0 fsf outStdout outFiles

theorem checkElfFinalChunkPlacedExited0_eq_batched (spec : ElfFullSpecPlaced) (inp : Inputs)
    (n : Nat) (ck : MkCkpt) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) :
    checkElfFinalChunkPlacedExited0 spec inp n ck outStdout outFiles =
      checkElfFinalChunkPlacedExited0B spec inp n ck outStdout outFiles := by
  unfold checkElfFinalChunkPlacedExited0 checkElfFinalChunkPlacedExited0B
  dsimp only
  cases initFastStateFromBasePlaced (headerElfOfFullPlaced spec) (prebuiltOfFullPlaced spec) inp with
  | none => rfl
  | some fs0 => dsimp only; rw [fastRunChunkCachedPlaced_eq_batched]; rfl

def checkElfFinalChunkPlacedExitedB (spec : ElfFullSpecPlaced) (inp : Inputs) (n : Nat)
    (ck : MkCkpt) (code : BitVec 64) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) : Bool :=
  let pb := prebuiltOfFullPlaced spec
  match initFastStateFromBasePlaced (headerElfOfFullPlaced spec) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlacedB pb.prog n (ck pb fs0) with
    | none => false
    | some fsf => checkFastExited fsf code outStdout outFiles

theorem checkElfFinalChunkPlacedExited_eq_batched (spec : ElfFullSpecPlaced) (inp : Inputs)
    (n : Nat) (ck : MkCkpt) (code : BitVec 64) (outStdout : List (BitVec 8))
    (outFiles : List (String × List (BitVec 8))) :
    checkElfFinalChunkPlacedExited spec inp n ck code outStdout outFiles =
      checkElfFinalChunkPlacedExitedB spec inp n ck code outStdout outFiles := by
  unfold checkElfFinalChunkPlacedExited checkElfFinalChunkPlacedExitedB
  dsimp only
  cases initFastStateFromBasePlaced (headerElfOfFullPlaced spec) (prebuiltOfFullPlaced spec) inp with
  | none => rfl
  | some fs0 => dsimp only; rw [fastRunChunkCachedPlaced_eq_batched]; rfl

def checkElfFinalChunkPlacedAbortedB (spec : ElfFullSpecPlaced) (inp : Inputs) (n : Nat)
    (ck : MkCkpt) : Bool :=
  let pb := prebuiltOfFullPlaced spec
  match initFastStateFromBasePlaced (headerElfOfFullPlaced spec) pb inp with
  | none => false
  | some fs0 =>
    match fastRunChunkCachedPlacedB pb.prog n (ck pb fs0) with
    | none => false
    | some fsf => checkFastAborted fsf

theorem checkElfFinalChunkPlacedAborted_eq_batched (spec : ElfFullSpecPlaced) (inp : Inputs)
    (n : Nat) (ck : MkCkpt) :
    checkElfFinalChunkPlacedAborted spec inp n ck =
      checkElfFinalChunkPlacedAbortedB spec inp n ck := by
  unfold checkElfFinalChunkPlacedAborted checkElfFinalChunkPlacedAbortedB
  dsimp only
  cases initFastStateFromBasePlaced (headerElfOfFullPlaced spec) (prebuiltOfFullPlaced spec) inp with
  | none => rfl
  | some fs0 => dsimp only; rw [fastRunChunkCachedPlaced_eq_batched]; rfl

end Symbolic.BugInjection.Proofs.CliExec.PlacedExecBatched
