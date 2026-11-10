/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.Semantics
import Std.Tactic.BVDecide.Normalize.Prop
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Instruction and Syscall Non-`.Panicked` Preservation

**Checked by Lean.**

Proves that `Arm64.execInstWithSvc` (under any `.Panicked`-avoiding supervisor handler) and
`Arm64.Program.evalInst` under `Syscall.standard` never transition a non-`.Panicked` state into
`.Panicked`.
-/

namespace Arm64

section NotPanicked

private theorem ite_status_ne_panicked {c : Prop} [Decidable c] {a b : State}
    (ha : a.status ≠ .Panicked) (hb : b.status ≠ .Panicked) :
    (if c then a else b).status ≠ .Panicked := by
  split
  · exact ha
  · exact hb

private theorem st_advancePC (s : State) : s.advancePC.status = s.status := rfl
private theorem st_setPC (s : State) (x : BitVec 64) : (s.setPC x).status = s.status := rfl
private theorem st_setPState (s : State) (x : PState) : (s.setPState x).status = s.status := rfl
private theorem st_setMem (s : State) (m : Memory) : (s.setMem m).status = s.status := rfl
private theorem st_setFpsr (s : State) (x : BitVec 32) : (s.setFpsr x).status = s.status := rfl
private theorem st_orFpsr (s : State) (x : BitVec 32) : (s.orFpsr x).status = s.status := rfl
private theorem st_setBrk (s : State) (x : BitVec 64) : (s.setBrk x).status = s.status := rfl
private theorem st_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).status = s.status := rfl
private theorem st_setFs (s : State) (x : FsState) : (s.setFs x).status = s.status := rfl
private theorem st_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).status = s.status := rfl
private theorem st_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).status = s.status := rfl
private theorem st_appendTrace (s : State) (x : List TraceEvent) :
    (s.appendTrace x).status = s.status := rfl
private theorem st_nextOracle (s : State) : s.nextOracle.status = s.status := rfl
private theorem st_stepExclOracle (s : State) : s.stepExclOracle.status = s.status := rfl
private theorem st_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).status = s.status := by unfold State.writeReg64; split <;> rfl
private theorem st_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).status = s.status := st_writeReg64 s r (BitVec.zeroExtend 64 v)
private theorem st_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).status = s.status := by
  cases w
  · exact st_writeReg32 s r (v.truncate 32)
  · exact st_writeReg64 s r v
private theorem st_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).status = s.status := rfl
private theorem st_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).status = s.status := rfl
private theorem st_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).status = s.status := rfl
private theorem st_setStatus (s : State) (x : ExecStatus) : (s.setStatus x).status = x := rfl

private theorem exception_ne_panicked (msg : String) : ExecStatus.Exception msg ≠ .Panicked := by
  intro h; cases h

private theorem halted_ne_panicked : ExecStatus.Halted ≠ .Panicked := by
  intro h; cases h

private theorem exited_ne_panicked (code : BitVec 64) : ExecStatus.Exited code ≠ .Panicked := by
  intro h; cases h

private theorem signaled_ne_panicked (sig : BitVec 7) : ExecStatus.Signaled sig ≠ .Panicked := by
  intro h; cases h

private theorem oom_ne_panicked : ExecStatus.OutOfMemory ≠ .Panicked := by
  intro h; cases h

private theorem advancePC_ne_panicked {s : State} (hs : s.status ≠ .Panicked) :
    s.advancePC.status ≠ .Panicked := hs
private theorem setPC_ne_panicked {s : State} {x : BitVec 64} (hs : s.status ≠ .Panicked) :
    (s.setPC x).status ≠ .Panicked := hs
private theorem setPState_ne_panicked {s : State} {x : PState} (hs : s.status ≠ .Panicked) :
    (s.setPState x).status ≠ .Panicked := hs
private theorem setMem_ne_panicked {s : State} {m : Memory} (hs : s.status ≠ .Panicked) :
    (s.setMem m).status ≠ .Panicked := hs
private theorem setFpsr_ne_panicked {s : State} {x : BitVec 32} (hs : s.status ≠ .Panicked) :
    (s.setFpsr x).status ≠ .Panicked := hs
private theorem orFpsr_ne_panicked {s : State} {x : BitVec 32} (hs : s.status ≠ .Panicked) :
    (s.orFpsr x).status ≠ .Panicked := hs
private theorem stepExclOracle_ne_panicked {s : State} (hs : s.status ≠ .Panicked) :
    s.stepExclOracle.status ≠ .Panicked := hs
private theorem writeReg64_ne_panicked {s : State} {r : Reg} {v : BitVec 64}
    (hs : s.status ≠ .Panicked) : (s.writeReg64 r v).status ≠ .Panicked := by
  rw [st_writeReg64]; exact hs
private theorem writeReg32_ne_panicked {s : State} {r : Reg} {v : BitVec 32}
    (hs : s.status ≠ .Panicked) : (s.writeReg32 r v).status ≠ .Panicked := by
  rw [st_writeReg32]; exact hs
private theorem writeReg_ne_panicked {s : State} {w : Width} {r : Reg} {v : BitVec 64}
    (hs : s.status ≠ .Panicked) : (s.writeReg w r v).status ≠ .Panicked := by
  rw [st_writeReg]; exact hs
private theorem writeVReg128_ne_panicked {s : State} {i : BitVec 5} {v : BitVec 128}
    (hs : s.status ≠ .Panicked) : (s.writeVReg128 i v).status ≠ .Panicked := hs
private theorem writeVReg64_ne_panicked {s : State} {i : BitVec 5} {v : BitVec 64}
    (hs : s.status ≠ .Panicked) : (s.writeVReg64 i v).status ≠ .Panicked := hs
private theorem writeVReg32_ne_panicked {s : State} {i : BitVec 5} {v : BitVec 32}
    (hs : s.status ≠ .Panicked) : (s.writeVReg32 i v).status ≠ .Panicked := hs
private theorem setStatus_exception_ne_panicked {s : State} {msg : String} :
    (s.setStatus (.Exception msg)).status ≠ .Panicked := exception_ne_panicked msg
private theorem setStatus_exited_ne_panicked {s : State} {code : BitVec 64} :
    (s.setStatus (.Exited code)).status ≠ .Panicked := exited_ne_panicked code
private theorem setStatus_halted_ne_panicked {s : State} :
    (s.setStatus .Halted).status ≠ .Panicked := halted_ne_panicked

set_option linter.unusedSimpArgs false

macro "status_norm" : tactic => `(tactic|
  simp only [st_advancePC, st_setPC, st_setPState, st_setMem, st_setFpsr, st_orFpsr,
    st_setBrk, st_setPhysMemAvail, st_setFs, st_setSigAction, st_setSigAltStack,
    st_nextOracle, st_stepExclOracle,
    st_appendTrace, st_writeReg64, st_writeReg32, st_writeReg, st_writeVReg128, st_writeVReg64,
    st_writeVReg32, st_setStatus])

macro "not_panicked_close" h:ident : tactic => `(tactic|
  (repeat' split
   repeat' split
   all_goals
     try dsimp (config := { zeta := true, zetaHave := true }) only
     try status_norm
     first
       | exact $h
       | exact exception_ne_panicked _
       | exact halted_ne_panicked
       | exact exited_ne_panicked _
       | exact signaled_ne_panicked _
       | exact oom_ne_panicked
       | (intro hpan; cases hpan)))

private theorem execAddSubImm_not_panicked (w : Width) (op : AddSubOp) (rd rn : Reg)
    (imm12 : BitVec 12) (shift12 : Bool) {s : State} (hs : s.status ≠ .Panicked) :
    (execAddSubImm w op rd rn imm12 shift12 s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execAddSubImm]; not_panicked_close hs

private theorem execAddSubExt_not_panicked (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (ext : ExtendType) (amt : Nat) {s : State} (hs : s.status ≠ .Panicked) :
    (execAddSubExt w op rd rn rm ext amt s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execAddSubExt]; not_panicked_close hs

private theorem execAddSubShift_not_panicked (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) {s : State} (hs : s.status ≠ .Panicked) :
    (execAddSubShift w op rd rn rm sh amt s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execAddSubShift]; not_panicked_close hs

private theorem execAddSubCarry_not_panicked (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execAddSubCarry w op rd rn rm s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execAddSubCarry]; not_panicked_close hs

private theorem execLogicalImm_not_panicked (w : Width) (op : LogicalOp) (rd rn : Reg)
    (imm : BitVec 64) {s : State} (hs : s.status ≠ .Panicked) :
    (execLogicalImm w op rd rn imm s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execLogicalImm]; not_panicked_close hs

private theorem execLogicalShift_not_panicked (w : Width) (op : LogicalOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) {s : State} (hs : s.status ≠ .Panicked) :
    (execLogicalShift w op rd rn rm sh amt s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execLogicalShift]; not_panicked_close hs

private theorem execMoveWide_not_panicked (w : Width) (op : MoveWideOp) (rd : Reg)
    (imm : BitVec 16) (hw : Nat) {s : State} (hs : s.status ≠ .Panicked) :
    (execMoveWide w op rd imm hw s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMoveWide]; not_panicked_close hs

private theorem execBitfield_not_panicked (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) {s : State} (hs : s.status ≠ .Panicked) :
    (execBitfield w op rd rn immr imms s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execBitfield]; not_panicked_close hs

private theorem execCondSelect_not_panicked (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) {s : State} (hs : s.status ≠ .Panicked) :
    (execCondSelect w op rd rn rm cond s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execCondSelect]; not_panicked_close hs

private theorem execCondCompare_not_panicked (w : Width) (isSub isImm : Bool) (rn : Reg)
    (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execCondCompare w isSub isImm rn rhs rm nzcv cond s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execCondCompare]; not_panicked_close hs

private theorem execDataProc1_not_panicked (w : Width) (op : DataProc1Op) (rd rn : Reg)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execDataProc1 w op rd rn s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execDataProc1]; not_panicked_close hs

private theorem execDataProc2_not_panicked (w : Width) (op : DataProc2Op) (rd rn rm : Reg)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execDataProc2 w op rd rn rm s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execDataProc2]; not_panicked_close hs

private theorem execDataProc3_not_panicked (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execDataProc3 w op rd rn rm ra s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execDataProc3]; not_panicked_close hs

private theorem execLdr_not_panicked (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (addr : AddrMode) {s : State} (hs : s.status ≠ .Panicked) :
    (execLdr w size signed rt addr s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execLdr]
  generalize evalAddrMode s addr = ea
  not_panicked_close hs

private theorem execLdrLit_not_panicked (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) {s : State} (hs : s.status ≠ .Panicked) :
    (execLdrLit w size signed rt offset s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execLdrLit]; not_panicked_close hs

private theorem execStr_not_panicked (size : MemWidth) (rt : Reg) (addr : AddrMode)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execStr size rt addr s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execStr]
  generalize evalAddrMode s addr = ea
  not_panicked_close hs

private theorem execLdp_not_panicked (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execLdp w signed rt1 rt2 addr s).status ≠ .Panicked := by
  unfold execLdp
  rcases evalAddrMode s addr with ⟨ea, wb⟩
  cases wb <;> dsimp (config := { zeta := true, zetaHave := true }) only <;> not_panicked_close hs

private theorem execStp_not_panicked (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execStp w rt1 rt2 addr s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execStp]
  generalize evalAddrMode s addr = ea
  not_panicked_close hs

private theorem applySimdResult_ne_panicked {rd : BitVec 5} {r : Except String (BitVec 128)}
    {s : State} (hs : s.status ≠ .Panicked) :
    (applySimdResult s rd r).status ≠ .Panicked := by
  cases r <;> not_panicked_close hs

private theorem applySimdSatResult_ne_panicked {rd : BitVec 5} {r : Except String (BitVec 128)}
    {satFlags : Option (BitVec 32)} {s : State} (hs : s.status ≠ .Panicked) :
    (applySimdSatResult s rd r satFlags).status ≠ .Panicked := by
  cases r <;> cases satFlags <;> not_panicked_close hs

private theorem simdLoadRegs_status (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m k vt ea s).status = s.status
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]
    rw [simdLoadRegs_status sz m k, st_writeVReg128]

private theorem simdLoadRegs_ne_panicked {sz : SimdMemSize} {m : Memory} {k : Nat}
    {vt : BitVec 5} {ea : BitVec 64} {s : State} (hs : s.status ≠ .Panicked) :
    (simdLoadRegs sz m k vt ea s).status ≠ .Panicked := by
  rw [simdLoadRegs_status]; exact hs

/-! ### System Calls -/

private theorem execReadCommon_not_panicked (isPread : Bool) {s : State} (hs : s.status ≠ .Panicked) :
    (execReadCommon s isPread).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]; not_panicked_close hs

private theorem execRead_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execRead s).status ≠ .Panicked :=
  execReadCommon_not_panicked false hs

private theorem execPread64_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execPread64 s).status ≠ .Panicked :=
  execReadCommon_not_panicked true hs

private theorem execWrite_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execWrite s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
    (dsimp only
     repeat' apply ite_status_ne_panicked
     repeat' apply ite_status_ne_panicked
     all_goals not_panicked_close hs)

private theorem execExit_not_panicked {s : State} (_hs : s.status ≠ .Panicked) :
    (execExit s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execExit]; not_panicked_close _hs

private theorem execFcntl_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execFcntl s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; not_panicked_close hs

private theorem execIoctl_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execIoctl s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; not_panicked_close hs

private theorem applyOpenVerdict_not_panicked {s : State} (v : OpenVerdict)
    (hs : s.status ≠ .Panicked) : (applyOpenVerdict s v).status ≠ .Panicked := by
  cases v with
  | opened _ _ chg => cases chg <;> not_panicked_close hs
  | errno _ => not_panicked_close hs
  | trap _ => not_panicked_close hs

private theorem execOpenat_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execOpenat s).status ≠ .Panicked := by
  unfold execOpenat; dsimp only
  split
  · exact applyOpenVerdict_not_panicked _ hs
  · split <;> first | exact applyOpenVerdict_not_panicked _ hs | not_panicked_close hs

private theorem execClose_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execClose s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execClose]; not_panicked_close hs

private theorem execLseek_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execLseek s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execLseek]; not_panicked_close hs

private theorem execFstat_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execFstat s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execFstat]; not_panicked_close hs

private theorem execPpoll_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execPpoll s).status ≠ .Panicked := by
  unfold execPpoll; dsimp only
  refine ite_status_ne_panicked setStatus_exception_ne_panicked ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked setStatus_exception_ne_panicked ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked setStatus_exception_ne_panicked ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked setStatus_exception_ne_panicked ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs)) ?_
  refine ite_status_ne_panicked setStatus_exception_ne_panicked ?_
  cases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
  | none => exact setStatus_exception_ne_panicked
  | some mc =>
    rcases mc with ⟨m', count⟩; dsimp only
    exact ite_status_ne_panicked (advancePC_ne_panicked (writeReg64_ne_panicked hs))
      (advancePC_ne_panicked (writeReg64_ne_panicked (setMem_ne_panicked hs)))

private theorem execBrk_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execBrk s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execBrk]; not_panicked_close hs

private theorem execMunmap_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execMunmap s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; not_panicked_close hs

private theorem execMremap_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execMremap s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMremap]; not_panicked_close hs

private theorem execMmap_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execMmap s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMmap]; not_panicked_close hs

private theorem execMprotect_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execMprotect s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; not_panicked_close hs

private theorem execMadvise_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execMadvise s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; not_panicked_close hs

private theorem execTkill_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execTkill s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execTkill]; not_panicked_close hs

private theorem execTgkill_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execTgkill s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; not_panicked_close hs

private theorem execSigaltstack_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execSigaltstack s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; not_panicked_close hs

private theorem execRtSigaction_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execRtSigaction s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; not_panicked_close hs

private theorem execRtSigprocmask_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execRtSigprocmask s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; not_panicked_close hs

private theorem execClockGettime_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execClockGettime s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; not_panicked_close hs

private theorem execGetrandom_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execGetrandom s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; not_panicked_close hs

private theorem execSetTidAddress_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execSetTidAddress s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execSetTidAddress]; not_panicked_close hs

private theorem execSchedGetaffinity_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execSchedGetaffinity s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; not_panicked_close hs

private theorem execGetpid_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (execGetpid s).status ≠ .Panicked := by
  dsimp (config := { zetaHave := true }) only [execGetpid]; not_panicked_close hs

private theorem standardEntry_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    ∀ p ∈ Syscall.standardTable, (p.2 s).status ≠ .Panicked := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact execRead_not_panicked hs
  · exact execWrite_not_panicked hs
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_status_ne_panicked
      (fun _ h => execRead_not_panicked h) hs
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_status_ne_panicked
      (fun _ h => execWrite_not_panicked h) hs
  · exact execExit_not_panicked hs
  · exact execExit_not_panicked hs
  · exact execFcntl_not_panicked hs
  · exact execIoctl_not_panicked hs
  · exact execOpenat_not_panicked hs
  · exact execClose_not_panicked hs
  · exact execLseek_not_panicked hs
  · exact execPread64_not_panicked hs
  · exact execFstat_not_panicked hs
  · exact execPpoll_not_panicked hs
  · exact execBrk_not_panicked hs
  · exact execMunmap_not_panicked hs
  · exact execMremap_not_panicked hs
  · exact execMmap_not_panicked hs
  · exact execMprotect_not_panicked hs
  · exact execMadvise_not_panicked hs
  · exact execTkill_not_panicked hs
  · exact execTgkill_not_panicked hs
  · exact execSigaltstack_not_panicked hs
  · exact execRtSigaction_not_panicked hs
  · exact execRtSigprocmask_not_panicked hs
  · exact execClockGettime_not_panicked hs
  · exact execGetrandom_not_panicked hs
  · exact execSetTidAddress_not_panicked hs
  · exact execSchedGetaffinity_not_panicked hs
  · exact execGetpid_not_panicked hs
  · exact execGetpid_not_panicked hs

private theorem syscallStandard_not_panicked {s : State} (hs : s.status ≠ .Panicked) :
    (Syscall.standard s).status ≠ .Panicked := by
  unfold Syscall.standard Syscall.dispatch
  split
  · rename_i nr fn hfind
    exact standardEntry_not_panicked hs (nr, fn) (List.mem_of_find?_eq_some hfind)
  · exact exception_ne_panicked _

private theorem evalSvc_status (svc : State → State) (s : State) :
    (evalSvc svc s).status = (svc s).status := rfl

/-! ### Instruction Dispatcher -/

private theorem exception_ne_panicked_imp {msg : String} :
    ExecStatus.Exception msg ≠ .Panicked := exception_ne_panicked msg

private theorem exited_ne_panicked_imp {code : BitVec 64} :
    ExecStatus.Exited code ≠ .Panicked := exited_ne_panicked code

macro "peel_step" h:ident hsvc_s:ident : tactic => `(tactic|
  repeat' (first
    | with_reducible exact $h
    | with_reducible exact $hsvc_s
    | with_reducible exact halted_ne_panicked
    | with_reducible apply exception_ne_panicked_imp
    | with_reducible apply exited_ne_panicked_imp
    | with_reducible apply ite_status_ne_panicked
    | with_reducible apply advancePC_ne_panicked
    | with_reducible apply setPC_ne_panicked
    | with_reducible apply setPState_ne_panicked
    | with_reducible apply setMem_ne_panicked
    | with_reducible apply setFpsr_ne_panicked
    | with_reducible apply orFpsr_ne_panicked
    | with_reducible apply stepExclOracle_ne_panicked
    | with_reducible apply writeReg64_ne_panicked
    | with_reducible apply writeReg32_ne_panicked
    | with_reducible apply writeReg_ne_panicked
    | with_reducible apply writeVReg128_ne_panicked
    | with_reducible apply writeVReg64_ne_panicked
    | with_reducible apply writeVReg32_ne_panicked
    | with_reducible apply simdLoadRegs_ne_panicked
    | with_reducible apply applySimdResult_ne_panicked
    | with_reducible apply applySimdSatResult_ne_panicked
    | with_reducible apply setStatus_exception_ne_panicked
    | with_reducible apply setStatus_exited_ne_panicked
    | with_reducible apply setStatus_halted_ne_panicked))

private theorem exec_ldrSimd_not_panicked {svc : State → State}
    {sz : SimdMemSize} {vt : VReg} {addr : AddrMode} {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.ldrSimd sz vt addr) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · exact setStatus_exception_ne_panicked
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_step hs hs)

private theorem exec_strSimd_not_panicked {svc : State → State}
    {sz : SimdMemSize} {vt : VReg} {addr : AddrMode} {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.strSimd sz vt addr) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · exact setStatus_exception_ne_panicked
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_step hs hs)

private theorem exec_ldpSimd_not_panicked {svc : State → State}
    {sz : SimdMemSize} {vt1 vt2 : VReg} {addr : AddrMode} {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.ldpSimd sz vt1 vt2 addr) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · exact setStatus_exception_ne_panicked
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_step hs hs)

private theorem exec_stpSimd_not_panicked {svc : State → State}
    {sz : SimdMemSize} {vt1 vt2 : VReg} {addr : AddrMode} {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.stpSimd sz vt1 vt2 addr) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · exact setStatus_exception_ne_panicked
  · cases addr <;>
      (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
       peel_step hs hs)

private theorem exec_st1SinglePost_not_panicked {svc : State → State}
    {q : Bool} {rm : VReg} {opcode : BitVec 3} {sBit : Bool} {size : BitVec 2}
    {rn : Reg} {vt : VReg} {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.st1SinglePost q rm opcode sBit size rn vt) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · exact exception_ne_panicked _
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    peel_step hs hs

private theorem exec_simdLdSt1Multi_not_panicked {svc : State → State}
    {isLoad q : Bool} {size : BitVec 2} {nregs : Nat} {rn : Reg} {postIdx : Bool} {rm vt : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdLdSt1Multi isLoad q size nregs rn postIdx rm vt) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdLd1r_not_panicked {svc : State → State}
    {q : Bool} {size : BitVec 2} {rn : Reg} {postIdx : Bool} {rm vt : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdLd1r q size rn postIdx rm vt) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_fmovGprVec_not_panicked {svc : State → State}
    {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.fmovGprVec sf ftype rmode opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_fpDataProc1_not_panicked {svc : State → State}
    {ftype : BitVec 2} {opcode : BitVec 6} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.fpDataProc1 ftype opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_fpFixedConv_not_panicked {svc : State → State}
    {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3} {scale : BitVec 6} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.fpFixedConv sf ftype rmode opcode scale rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdImmShift_not_panicked {svc : State → State}
    {q op : Bool} {immh : BitVec 4} {immb : BitVec 3} {opc : BitVec 5} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdImmShift q op immh immb opc rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdInsDup_not_panicked {svc : State → State}
    {q op : Bool} {imm5 : BitVec 5} {imm4 : BitVec 4} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdInsDup q op imm5 imm4 rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdThreeSame_not_panicked {svc : State → State}
    {q u : Bool} {size : BitVec 2} {rm : VReg} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdThreeSame q u size rm opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    split <;> peel_step hs hs
  · try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
    peel_step hs hs

private theorem exec_simdTwoRegMisc_not_panicked {svc : State → State}
    {q u : Bool} {size : BitVec 2} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdTwoRegMisc q u size opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdAcrossLanes_not_panicked {svc : State → State}
    {q u : Bool} {size : BitVec 2} {opcode : BitVec 5} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdAcrossLanes q u size opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdPermute_not_panicked {svc : State → State}
    {q : Bool} {size : BitVec 2} {rm : VReg} {opcode : BitVec 3} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdPermute q size rm opcode rn rd) s).status ≠ .Panicked := by
  apply ite_status_ne_panicked <;>
    (try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
     peel_step hs hs)

private theorem exec_simdTbl_not_panicked {svc : State → State}
    {q : Bool} {rm : VReg} {len : BitVec 2} {isTbx : Bool} {rn rd : VReg}
    {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc (.simdTbl q rm len isTbx rn rd) s).status ≠ .Panicked :=
  advancePC_ne_panicked (writeVReg128_ne_panicked hs)

theorem execInstWithSvc_status_ne_panicked {svc : State → State}
    (hsvc : ∀ {s : State}, s.status ≠ .Panicked → (svc s).status ≠ .Panicked)
    (inst : Instr) {s : State} (hs : s.status ≠ .Panicked) :
    (execInstWithSvc svc inst s).status ≠ .Panicked := by
  have hsvc_s : (svc s).status ≠ .Panicked := hsvc hs
  cases inst with
  | ldrSimd => exact exec_ldrSimd_not_panicked hs
  | strSimd => exact exec_strSimd_not_panicked hs
  | ldpSimd => exact exec_ldpSimd_not_panicked hs
  | stpSimd => exact exec_stpSimd_not_panicked hs
  | st1SinglePost => exact exec_st1SinglePost_not_panicked hs
  | simdLdSt1Multi => exact exec_simdLdSt1Multi_not_panicked hs
  | simdLd1r => exact exec_simdLd1r_not_panicked hs
  | fmovGprVec => exact exec_fmovGprVec_not_panicked hs
  | fpDataProc1 => exact exec_fpDataProc1_not_panicked hs
  | fpFixedConv => exact exec_fpFixedConv_not_panicked hs
  | simdImmShift => exact exec_simdImmShift_not_panicked hs
  | simdInsDup => exact exec_simdInsDup_not_panicked hs
  | simdThreeSame => exact exec_simdThreeSame_not_panicked hs
  | simdTwoRegMisc => exact exec_simdTwoRegMisc_not_panicked hs
  | simdAcrossLanes => exact exec_simdAcrossLanes_not_panicked hs
  | simdPermute => exact exec_simdPermute_not_panicked hs
  | simdTbl => exact exec_simdTbl_not_panicked hs
  | addSubImm => exact execAddSubImm_not_panicked _ _ _ _ _ _ hs
  | addSubShift => exact execAddSubShift_not_panicked _ _ _ _ _ _ _ hs
  | addSubExt => exact execAddSubExt_not_panicked _ _ _ _ _ _ _ hs
  | addSubCarry => exact execAddSubCarry_not_panicked _ _ _ _ _ hs
  | logicalImm => exact execLogicalImm_not_panicked _ _ _ _ _ hs
  | logicalShift => exact execLogicalShift_not_panicked _ _ _ _ _ _ _ hs
  | moveWide => exact execMoveWide_not_panicked _ _ _ _ _ hs
  | bitfield => exact execBitfield_not_panicked _ _ _ _ _ _ hs
  | condSelect => exact execCondSelect_not_panicked _ _ _ _ _ _ hs
  | condCompareReg => exact execCondCompare_not_panicked _ _ _ _ _ _ _ _ hs
  | condCompareImm => exact execCondCompare_not_panicked _ _ _ _ _ _ _ _ hs
  | dataProc1 => exact execDataProc1_not_panicked _ _ _ _ hs
  | dataProc2 => exact execDataProc2_not_panicked _ _ _ _ _ hs
  | dataProc3 => exact execDataProc3_not_panicked _ _ _ _ _ _ hs
  | ldr => exact execLdr_not_panicked _ _ _ _ _ hs
  | ldrLit => exact execLdrLit_not_panicked _ _ _ _ _ hs
  | str => exact execStr_not_panicked _ _ _ hs
  | ldp => exact execLdp_not_panicked _ _ _ _ _ hs
  | stp => exact execStp_not_panicked _ _ _ _ hs
  | ldnp => exact execLdp_not_panicked _ _ _ _ _ hs
  | stnp => exact execStp_not_panicked _ _ _ _ hs
  | cryptoSha2Reg => exact applySimdResult_ne_panicked hs
  | cryptoSha3Reg => exact applySimdResult_ne_panicked hs
  | udf => exact setStatus_exception_ne_panicked
  | _ =>
    first
      | apply ite_status_ne_panicked
      | apply advancePC_ne_panicked
      | apply setPC_ne_panicked
    all_goals
      try dsimp (config := { beta := true, iota := true, zeta := true, zetaHave := true }) only
      peel_step hs hsvc_s

theorem evalInst_standard_status_ne_panicked {prog : Program}
    (hsvc : prog.svc = Syscall.standard) (inst : Instr) {s : State}
    (hs : s.status ≠ .Panicked) :
    (prog.evalInst inst s).status ≠ .Panicked := by
  unfold Program.evalInst
  refine execInstWithSvc_status_ne_panicked (fun {s'} hs' => ?_) inst hs
  rw [evalSvc_status, hsvc]
  exact syscallStandard_not_panicked hs'

end NotPanicked

end Arm64
