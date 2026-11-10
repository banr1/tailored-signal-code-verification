/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.Hoare.LibcHooks
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux

/-!
# Closure-Free Machine State and PQXDH/SPQR Hook Soundness

Defines the closure-free machine state `FastState`, its extensional agreement relation
`FastState.Agrees` with `Arm64.State`, the `FastHookPost` postcondition, and computable
implementations with soundness proofs for the PQXDH and SPQR V1 extern hooks.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

set_option autoImplicit false

open Arm64 Arm64.Memory ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.LibsignalHmac (readShaState shaStateBytes compress256Hook)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchetRepr (errTag)
open CryptoVerification.LibsignalTripleRatchet (readVec32 diffieHellmanHook pubFromSecretHook
  zeroizeSecretHook)
open CryptoVerification.LibsignalSpqrV1 (MlKem
  mlkemFromSeedName mlkemPk1Name mlkemPk2Name mlkemEncaps1Name mlkemEncaps2Name
  mlkemDecapsName mlkemValidatePkName libcruxHmacName)
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux

abbrev NondetOracle := Arm64.Oracle

/-- Closure-free AArch64 + Linux process machine state backed by `FastRegs`, `FastMem`, `FastFs`,
and sorted disjoint heap intervals `heapIvs`. -/
structure FastState where
  regs         : FastRegs := FastRegs.empty
  sp           : BitVec 64 := 0#64
  pc           : BitVec 64 := 0#64
  pstate       : PState := PState.zero
  mem          : FastMem
  heapIvs      : List (Nat × Nat) := []
  tpidrEl0     : BitVec 64 := 0#64
  fpsr         : BitVec 32 := 0#32
  brkStart     : BitVec 64 := 0#64
  brk          : BitVec 64 := 0#64
  physMemAvail : Nat := 0
  fs           : FastFs := {}
  oracle       : NondetOracle := {}
  oracleIdx    : Nat := 0
  exclFails    : List Bool := []
  trace        : List TraceEvent := []
  status       : ExecStatus := .Running
  sigAltStack  : SigAltStack := {}

namespace FastState

/-- Extensional agreement between `FastState` and `Arm64.State`, including `HeapIntervalsAgree`. -/
structure Agrees (fst : FastState) (s : State) : Prop where
  regs         : fst.regs.Agrees s.regs s.vregs
  sp           : fst.sp = s.sp
  pc           : fst.pc = s.pc
  pstate       : fst.pstate = s.pstate
  mem          : fst.mem.Agrees s.mem
  heapIvs      : HeapIntervalsAgree fst.heapIvs s.mem
  tpidrEl0     : fst.tpidrEl0 = s.tpidrEl0
  fpsr         : fst.fpsr = s.fpsr
  brkStart     : fst.brkStart = s.brkStart
  brk          : fst.brk = s.brk
  physMemAvail : fst.physMemAvail = s.physMemAvail
  fs           : fst.fs.Agrees s.fs
  oracle       : fst.oracle = s.oracle
  oracleIdx    : fst.oracleIdx = s.oracleIdx
  exclFails    : fst.exclFails = s.exclFails
  trace        : fst.trace = s.trace
  status       : fst.status = s.status
  sigAltStack  : fst.sigAltStack = s.sigAltStack

def readReg64 (fs : FastState) (r : Reg) : BitVec 64 :=
  match r with
  | .gpr idx => if idx == 31#5 then 0#64 else fs.regs.readGpr idx
  | .sp      => fs.sp
  | .xzr     => 0#64

@[inline] def withFields {α : Type} (fs : FastState) (k : FastRegs → BitVec 64 → BitVec 64 → PState →
    FastMem → List (Nat × Nat) → BitVec 64 → BitVec 32 → BitVec 64 → BitVec 64 → Nat → FastFs →
    NondetOracle → Nat → List Bool → List TraceEvent → ExecStatus → SigAltStack → α) : α :=
  match fs with
  | ⟨r, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩ =>
    k r sp pc ps m ivs tp fp bs bk ph ffs orcl oi ex tr st sg

@[simp] theorem withFields_eq {α : Type} (fs : FastState) (k) :
    fs.withFields (α := α) k = k fs.regs fs.sp fs.pc fs.pstate fs.mem fs.heapIvs fs.tpidrEl0 fs.fpsr
      fs.brkStart fs.brk fs.physMemAvail fs.fs fs.oracle fs.oracleIdx fs.exclFails
      fs.trace fs.status fs.sigAltStack := by unfold withFields; cases fs; rfl

def writeReg64 (fs : FastState) (r : Reg) (val : BitVec 64) : FastState :=
  match r with
  | .gpr idx =>
    if idx == 31#5 then fs
    else match fs with
      | ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩ =>
        match rg.writeGpr idx val with
        | ⟨g', v'⟩ => ⟨⟨g', v'⟩, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  | .sp =>
    match fs with
    | ⟨rg, _, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩ =>
      match val.toNat with
      | 0 => ⟨rg, 0#64, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
      | k + 1 => ⟨rg, BitVec.ofNat 64 (Nat.succ k), pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  | .xzr => fs

def readReg32 (fs : FastState) (r : Reg) : BitVec 32 := (fs.readReg64 r).truncate 32
def writeReg32 (fs : FastState) (r : Reg) (val : BitVec 32) : FastState := fs.writeReg64 r (val.zeroExtend 64)

def readReg (fs : FastState) (w : Width) (r : Reg) : BitVec 64 :=
  match w with | .W32 => (fs.readReg32 r).zeroExtend 64 | .W64 => fs.readReg64 r

def writeReg (fs : FastState) (w : Width) (r : Reg) (val : BitVec 64) : FastState :=
  fs.writeReg64 r (match w with | .W32 => (val.truncate 32).zeroExtend 64 | .W64 => val)

def readVReg128 (fs : FastState) (idx : BitVec 5) : BitVec 128 := fs.regs.readVReg idx

def writeVReg128 (fs : FastState) (idx : BitVec 5) (val : BitVec 128) : FastState :=
  match fs with
  | ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩ =>
    match rg.writeVReg idx val with
    | ⟨g', v'⟩ => ⟨⟨g', v'⟩, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def readVReg64 (fs : FastState) (idx : BitVec 5) : BitVec 64 := (fs.readVReg128 idx).truncate 64
def writeVReg64 (fs : FastState) (idx : BitVec 5) (val : BitVec 64) : FastState := fs.writeVReg128 idx (val.zeroExtend 128)
def readVReg32 (fs : FastState) (idx : BitVec 5) : BitVec 32 := (fs.readVReg128 idx).truncate 32
def writeVReg32 (fs : FastState) (idx : BitVec 5) (val : BitVec 32) : FastState := fs.writeVReg128 idx (val.zeroExtend 128)

def setPC (fs : FastState) (newPC : BitVec 64) : FastState :=
  match fs with
  | ⟨rg, sp, _, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩ =>
    match newPC.toNat with
    | 0 => ⟨rg, sp, 0#64, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
    | k + 1 => ⟨rg, sp, BitVec.ofNat 64 (Nat.succ k), ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def advancePC (fs : FastState) : FastState := fs.setPC (fs.pc + 4#64)

def setPState (fs : FastState) (ps' : PState) : FastState :=
  match fs, canonPState ps' with
  | ⟨rg, sp, pc, _, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩, ⟨n, z, c, v⟩ =>
    ⟨rg, sp, pc, ⟨n, z, c, v⟩, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def setFpsr (fs : FastState) (fpsr : BitVec 32) : FastState :=
  withForcedBV fpsr fun f =>
    fs.withFields fun rg sp pc ps m ivs tp _ bs bk ph ffs orcl oi ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, f, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def orFpsr (fs : FastState) (flags : BitVec 32) : FastState := fs.setFpsr (fs.fpsr ||| flags)

def setMem (fs : FastState) (fm : FastMem) : FastState :=
  match fs, fm with
  | ⟨rg, sp, pc, ps, _, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩, ⟨lines, sb, top⟩ =>
    ⟨rg, sp, pc, ps, ⟨lines, sb, top⟩, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def setMemAndIvs (fs : FastState) (fm : FastMem) (ivs : List (Nat × Nat)) : FastState :=
  withForcedFastMem fm fun fm' =>
    withForcedIvList ivs fun ivs' =>
      fs.withFields fun rg sp pc ps _ _ tp fp bs bk ph ffs orcl oi ex tr st sg =>
        ⟨rg, sp, pc, ps, fm', ivs', tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

def setStatus (fs : FastState) (st' : ExecStatus) : FastState :=
  withForcedExecStatus st' fun st'' =>
    fs.withFields fun rg sp pc ps m ivs tp fp bs bk ph ffs orcl oi ex tr _ sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st'', sg⟩

def appendTrace (fs : FastState) (evs : List TraceEvent) : FastState :=
  fs.withFields fun rg sp pc ps m ivs tp fp bs bk ph ffs orcl oi ex tr st sg =>
    withForcedListSpine (tr ++ evs) fun tr' =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr', st, sg⟩

def setFs (fs : FastState) (newFs : FastFs) : FastState :=
  withForcedFastFs newFs fun ffs' =>
    fs.withFields fun rg sp pc ps m ivs tp fp bs bk ph _ orcl oi ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs', orcl, oi, ex, tr, st, sg⟩

def retToLr (fs : FastState) : FastState :=
  fs.setPC (fs.readReg64 .lr)

def abortOnPanic (fs : FastState) : FastState :=
  match fs.status with
  | .Panicked => fs.setStatus (.Signaled sigAbrt)
  | _ => fs

theorem readReg64_eq {fs : FastState} {s : State} (h : fs.Agrees s) (r : Reg) :
    fs.readReg64 r = s.readReg64 r := by
  cases r with
  | gpr idx =>
    simp only [readReg64, State.readReg64]
    by_cases h31 : idx == 31#5
    · simp [h31]
    · simp [h31, FastRegs.readGpr_eq h.regs idx]
  | sp => exact h.sp
  | xzr => rfl

theorem readReg32_eq {fs : FastState} {s : State} (h : fs.Agrees s) (r : Reg) :
    fs.readReg32 r = s.readReg32 r := by
  simp only [readReg32, State.readReg32, readReg64_eq h r]

theorem readReg_eq {fs : FastState} {s : State} (h : fs.Agrees s) (w : Width) (r : Reg) :
    fs.readReg w r = s.readReg w r := by
  cases w <;> simp [readReg, State.readReg, readReg32_eq h r, readReg64_eq h r]

theorem readVReg128_eq {fs : FastState} {s : State} (h : fs.Agrees s) (idx : BitVec 5) :
    fs.readVReg128 idx = s.readVReg128 idx :=
  FastRegs.readVReg_eq h.regs idx

private theorem cleanBV64_eq (v : BitVec 64) (k : Nat) (hn : v.toNat = k) : BitVec.ofNat 64 k = v := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← hn, Nat.mod_eq_of_lt v.isLt]

theorem writeReg64_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (r : Reg) (val : BitVec 64) :
    (fs.writeReg64 r val).Agrees (s.writeReg64 r val) := by
  rcases fs with ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  simp only [writeReg64, State.writeReg64]
  cases r with
  | gpr idx =>
    by_cases h31 : (idx == 31#5) = true
    · simp only [h31, ↓reduceIte]; exact h
    · simp only [h31, Bool.false_eq_true, ↓reduceIte]
      have hg := FastRegs.writeGpr_agrees h.regs idx val
      rcases hrg : rg.writeGpr idx val with ⟨g', v'⟩; rw [hrg] at hg
      exact ⟨hg, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr, h.brkStart, h.brk,
        h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩
  | sp =>
    cases hn : val.toNat with
    | zero => exact ⟨h.regs, cleanBV64_eq val 0 hn, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
        h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩
    | succ k => exact ⟨h.regs, cleanBV64_eq val (Nat.succ k) hn, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
        h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩
  | xzr => exact h

theorem writeReg32_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (r : Reg) (val : BitVec 32) :
    (fs.writeReg32 r val).Agrees (s.writeReg32 r val) := writeReg64_agrees h r (val.zeroExtend 64)

theorem writeReg_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (w : Width) (r : Reg) (val : BitVec 64) :
    (fs.writeReg w r val).Agrees (s.writeReg w r val) := writeReg64_agrees h r _

theorem writeVReg128_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (idx : BitVec 5) (val : BitVec 128) :
    (fs.writeVReg128 idx val).Agrees (s.writeVReg128 idx val) := by
  rcases fs with ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  have hv := FastRegs.writeVReg_agrees h.regs idx val
  dsimp only [writeVReg128]; rcases hrv : rg.writeVReg idx val with ⟨g', v'⟩; rw [hrv] at hv
  exact ⟨hv, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr, h.brkStart, h.brk,
    h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩

theorem setPC_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (newPC : BitVec 64) :
    (fs.setPC newPC).Agrees (s.setPC newPC) := by
  rcases fs with ⟨rg, sp, pc, ps, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  dsimp only [setPC, State.setPC]
  cases hn : newPC.toNat with
  | zero => exact ⟨h.regs, h.sp, cleanBV64_eq newPC 0 hn, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
      h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩
  | succ k => exact ⟨h.regs, h.sp, cleanBV64_eq newPC (Nat.succ k) hn, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
      h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩

theorem advancePC_agrees {fs : FastState} {s : State} (h : fs.Agrees s) :
    fs.advancePC.Agrees s.advancePC := by
  simp only [advancePC, State.advancePC, ← h.pc]
  exact setPC_agrees h (fs.pc + 4#64)

theorem setPState_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (ps : PState) :
    (fs.setPState ps).Agrees (s.setPState ps) := by
  rcases fs with ⟨rg, sp, pc, _, m, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  unfold setPState State.setPState; rw [canonPState_eq]; rcases ps with ⟨n, z, c, v⟩
  exact ⟨h.regs, h.sp, h.pc, rfl, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr, h.brkStart, h.brk,
    h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩

theorem setFpsr_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (fpsr : BitVec 32) :
    (fs.setFpsr fpsr).Agrees (s.setFpsr fpsr) := by
  simp only [setFpsr, withForcedBV_eq, withFields_eq, State.setFpsr]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, rfl,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

theorem orFpsr_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (flags : BitVec 32) :
    (fs.orFpsr flags).Agrees (s.orFpsr flags) := by
  simp only [orFpsr, State.orFpsr, ← h.fpsr]
  exact setFpsr_agrees h (fs.fpsr ||| flags)

theorem setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    {fm : FastMem} {m : Memory} (hm : fm.Agrees m) (hivs : HeapIntervalsAgree fs.heapIvs m) :
    (fs.setMem fm).Agrees (s.setMem m) := by
  rcases fs with ⟨rg, sp, pc, ps, _, ivs, tp, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩
  rcases fm with ⟨lines, sb, top⟩
  exact ⟨h.regs, h.sp, h.pc, h.pstate, hm, hivs, h.tpidrEl0, h.fpsr, h.brkStart, h.brk,
    h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails, h.trace, h.status, h.sigAltStack⟩

theorem setMemAndIvs_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    {fm : FastMem} {ivs : List (Nat × Nat)} {m : Memory}
    (hm : fm.Agrees m) (hivs : HeapIntervalsAgree ivs m) :
    (fs.setMemAndIvs fm ivs).Agrees (s.setMem m) := by
  simp only [setMemAndIvs, withForcedFastMem_eq, withForcedIvList_eq, withFields_eq]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, hm, hivs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

theorem setStatus_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (st : ExecStatus) :
    (fs.setStatus st).Agrees (s.setStatus st) := by
  simp only [setStatus, withForcedExecStatus_eq, withFields_eq]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, rfl, h.sigAltStack⟩

theorem appendTrace_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (evs : List TraceEvent) :
    (fs.appendTrace evs).Agrees (s.appendTrace evs) := by
  simp only [appendTrace, withFields_eq, withForcedListSpine_eq, State.appendTrace, ← h.trace]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    rfl, h.status, h.sigAltStack⟩

theorem setFs_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    {ffs : FastFs} {sfs : FsState} (hfs : ffs.Agrees sfs) :
    (fs.setFs ffs).Agrees (s.setFs sfs) := by
  simp only [setFs, withForcedFastFs_eq, withFields_eq]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, h.tpidrEl0, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, hfs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

theorem retToLr_agrees {fs : FastState} {s : State} (h : fs.Agrees s) :
    fs.retToLr.Agrees (returnToLinkRegister s) := by
  simp only [retToLr, returnToLinkRegister, readReg64_eq h .lr]
  exact setPC_agrees h (s.readReg64 .lr)

end FastState

private theorem readBytesCached_length (fm : FastMem) :
    ∀ (n : Nat) (curHi : Nat) (curLine : Option Line64) (base : BitVec 64),
      (FastMem.readBytesCached fm curHi curLine base n).length = n
  | 0, _, _, _ => rfl
  | n + 1, curHi, curLine, base => by
    simp only [FastMem.readBytesCached, FastMem.withForcedLineOpt_eq, withForcedBV_eq,
      List.length_cons, readBytesCached_length fm n]

theorem fastReadBytes_length (fm : FastMem) (base : BitVec 64) (n : Nat) :
    (fm.readBytes base n).length = n := by
  cases n with
  | zero => rfl
  | succ k =>
    simp only [FastMem.readBytes, FastMem.withForcedLineOpt_eq]
    exact readBytesCached_length fm (k + 1) _ _ base

def fastReadVecN (fm : FastMem) (a : BitVec 64) (n : Nat) : List.Vector (BitVec 8) n :=
  ⟨fm.readBytes a n, fastReadBytes_length fm a n⟩

theorem fastReadVecN_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) (n : Nat) :
    fastReadVecN fm a n = readVecN m a n :=
  Subtype.ext (FastMem.readBytes_eq h a n)

theorem fastReadVec32_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fastReadVecN fm a 32 = readVec32 m a :=
  Subtype.ext (FastMem.readBytes_eq h a 32)

private theorem allPerm_of_perm_eq {m1 m2 : Memory} (hp : ∀ a, m2.perm a = m1.perm a)
    (pred : Option Perm → Bool) :
    ∀ (n : Nat) (addr : BitVec 64), m2.allPerm pred addr n = m1.allPerm pred addr n
  | 0, _ => rfl
  | n + 1, addr => by
    simp only [Memory.allPerm, hp addr, allPerm_of_perm_eq hp pred n (addr + 1#64)]

theorem canWrite_of_perm_eq {m1 m2 : Memory} (hp : ∀ a, m2.perm a = m1.perm a)
    (addr : BitVec 64) (n : Nat) :
    m2.canWrite addr n = m1.canWrite addr n :=
  allPerm_of_perm_eq hp _ n addr

private theorem allPerm_add (m : Memory) (pred : Option Perm → Bool) :
    ∀ (a b : Nat) (addr : BitVec 64),
      m.allPerm pred addr (a + b) =
        (m.allPerm pred addr a && m.allPerm pred (addr + BitVec.ofNat 64 a) b)
  | 0, b, addr => by simp [Memory.allPerm]
  | a + 1, b, addr => by
    have hadd : addr + 1#64 + BitVec.ofNat 64 a = addr + BitVec.ofNat 64 (a + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [Nat.succ_add, Memory.allPerm, Memory.allPerm, allPerm_add m pred a b (addr + 1#64),
      hadd, Bool.and_assoc]

theorem canWrite_add (m : Memory) (addr : BitVec 64) (a b : Nat) :
    m.canWrite addr (a + b) = (m.canWrite addr a && m.canWrite (addr + BitVec.ofNat 64 a) b) :=
  allPerm_add m _ a b addr

theorem canWrite_split24 {m : Memory} {r : BitVec 64} (h24 : m.canWrite r 24 = true) :
    m.canWrite r 8 = true ∧ m.canWrite (r + 8#64) 8 = true ∧ m.canWrite (r + 16#64) 8 = true := by
  have h1 : m.canWrite r (8 + 16) = true := h24
  rw [canWrite_add] at h1
  simp only [Bool.and_eq_true] at h1
  have h2 : m.canWrite (r + 8#64) (8 + 8) = true := h1.2
  rw [canWrite_add] at h2
  simp only [Bool.and_eq_true] at h2
  have h16 : r + 8#64 + 8#64 = r + 16#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [h16] at h2
  exact ⟨h1.1, h2.1, h2.2⟩

theorem canWrite_mono_le {m : Memory} {addr : BitVec 64} {a b : Nat}
    (hab : a ≤ b) (h : m.canWrite addr b = true) :
    m.canWrite addr a = true := by
  have hsplit : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  rw [hsplit, canWrite_add, Bool.and_eq_true] at h
  exact h.1

/-- Postcondition relating a computable `FastState` output `fs'` to an `Arm64.State` hook `h`
at `s`: state agreement, frozen-memory preservation, and symbol-table preservation. -/
def FastHookPost (h : State → State) (s : State) (fs' : FastState) : Prop :=
  fs'.Agrees (h s) ∧ s.mem.KeepsFrozen (h s).mem ∧ (h s).symtab = s.symtab

theorem fastAbortOnPanic_post {h : State → State} {s : State} {fs' : FastState}
    (hp : FastHookPost h s fs') :
    FastHookPost (abortOnPanic h) s fs'.abortOnPanic := by
  rcases hp with ⟨hag, hkf, hsym⟩
  dsimp only [FastHookPost, abortOnPanic, FastState.abortOnPanic]
  rw [hag.status]
  cases (h s).status <;>
    exact ⟨by first | exact hag | exact FastState.setStatus_agrees hag (.Signaled sigAbrt),
      hkf, hsym⟩

/-- Write `bs` at `dst` when writable and branch to `lr`. -/
def fastWriteBytesRet (dst : BitVec 64) (bs : List (BitVec 8)) (fs : FastState) :
    Option FastState :=
  if fs.mem.canWrite dst bs.length then
    let lr := fs.readReg64 .lr
    some ((fs.setMem (fs.mem.writeBytes dst bs)).setPC lr)
  else
    none

theorem fastWriteBytesRet_returnToLr_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (dst : BitVec 64) (bs : List (BitVec 8))
    (hsome : fastWriteBytesRet dst bs fs = some fs') :
    FastHookPost (fun st => returnToLinkRegister (st.setMem (st.mem.writeBytes dst bs))) s fs' := by
  unfold fastWriteBytesRet at hsome
  by_cases hcw : fs.mem.canWrite dst bs.length = true
  · simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
    subst hsome
    have hcw_s : s.mem.canWrite dst bs.length = true := by
      rw [← FastMem.canWrite_eq hag.mem]; exact hcw
    have hm' := FastMem.writeBytes_agrees hag.mem dst bs
    have hivs' := HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_writeBytes_eq s.mem dst bs)
    have hag1 := FastState.setMem_agrees hag hm' hivs'
    rw [FastState.readReg64_eq hag .lr]
    exact ⟨FastState.setPC_agrees hag1 (s.readReg64 .lr),
      keepsFrozen_writeBytes bs hcw_s, rfl⟩
  · simp [hcw] at hsome

theorem fastWriteBytesRet_retHook_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (dst : BitVec 64) (bs : List (BitVec 8))
    (hsome : fastWriteBytesRet dst bs fs = some fs') :
    FastHookPost (retHook fun st => st.setMem (st.mem.writeBytes dst bs)) s fs' :=
  fastWriteBytesRet_returnToLr_post hag dst bs hsome

def fastWriteVecHeader (fm : FastMem) (v cap ptr len : BitVec 64) : FastMem :=
  ((fm.write64 v cap).write64 (v + 8#64) ptr).write64 (v + 16#64) len

theorem fastWriteVecHeader_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (v cap ptr len : BitVec 64) :
    (fastWriteVecHeader fm v cap ptr len).Agrees (writeVecHeader m v cap ptr len) := by
  unfold fastWriteVecHeader writeVecHeader
  exact FastMem.write64_agrees (FastMem.write64_agrees (FastMem.write64_agrees h v cap)
    (v + 8#64) ptr) (v + 16#64) len

theorem perm_writeVecHeader_eq (m : Memory) (v cap ptr len a : BitVec 64) :
    (writeVecHeader m v cap ptr len).perm a = m.perm a := by
  simp only [writeVecHeader, perm_write64_eq]

theorem keepsFrozen_writeVecHeader {m : Memory} {v : BitVec 64}
    (hcw : m.canWrite v 24 = true) (cap ptr len : BitVec 64) :
    m.KeepsFrozen (writeVecHeader m v cap ptr len) := by
  obtain ⟨h0, h8, h16⟩ := canWrite_split24 hcw
  have kf1 := keepsFrozen_write64 h0 cap
  have h8' : (m.write64 v cap).canWrite (v + 8#64) 8 = true := by
    rw [canWrite_of_perm_eq (perm_write64_eq m v cap)]; exact h8
  have kf2 := keepsFrozen_write64 h8' ptr
  have h16' : ((m.write64 v cap).write64 (v + 8#64) ptr).canWrite (v + 16#64) 8 = true := by
    rw [canWrite_of_perm_eq (perm_write64_eq _ (v + 8#64) ptr),
      canWrite_of_perm_eq (perm_write64_eq m v cap)]
    exact h16
  have kf3 := keepsFrozen_write64 h16' len
  exact KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3

def fastAllocFail (fs : FastState) : FastState :=
  let lr := fs.readReg64 .lr
  ((fs.appendTrace [allocFailedEvent]).writeReg64 .x0 0#64).setPC lr

theorem fastAllocFail_post {fs : FastState} {s : State} (hag : fs.Agrees s) :
    FastHookPost allocFail s (fastAllocFail fs) := by
  unfold fastAllocFail allocFail retHook
  rw [FastState.readReg64_eq hag .lr]
  refine ⟨FastState.setPC_agrees
    (FastState.writeReg64_agrees (FastState.appendTrace_agrees hag [allocFailedEvent]) .x0 0#64)
    (s.readReg64 .lr), KeepsFrozen.refl s.mem, rfl⟩

def fastAllocPanic (fs : FastState) : FastState :=
  (fs.appendTrace [allocFailedEvent]).setStatus .Panicked

theorem fastAllocPanic_post {fs : FastState} {s : State} (hag : fs.Agrees s) :
    FastHookPost allocPanicHook s (fastAllocPanic fs) :=
  ⟨FastState.setStatus_agrees (FastState.appendTrace_agrees hag [allocFailedEvent]) .Panicked,
    KeepsFrozen.refl s.mem, rfl⟩

/-- Bump-allocate `bs` on the heap, write a `Vec<u8>` header `(bs.length, p, outLen)` at `x8`, and
return to `lr` (or panic on allocation failure). -/
def fastReturnFreshVecU8Len (bs : List (BitVec 8)) (outLen : Nat) (fs : FastState) :
    Option FastState :=
  match fastBumpAlloc fs.heapIvs bs.length 1 with
  | some (p, ivs') =>
    let fm1 := fs.mem.mapFresh p bs.length Perm.rw
    let r := fs.readReg64 .x8
    if fm1.canWrite p bs.length && fm1.canWrite r 24 then
      let cap := BitVec.ofNat 64 bs.length
      let len := BitVec.ofNat 64 outLen
      let fm2 := fastWriteVecHeader (fm1.writeBytes p bs) r cap p len
      let lr := fs.readReg64 .lr
      some ((fs.setMemAndIvs fm2 ivs').setPC lr)
    else
      none
  | none => some (fastAllocPanic fs)

theorem fastReturnFreshVecU8Len_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (bs : List (BitVec 8)) (outLen : Nat)
    (hsome : fastReturnFreshVecU8Len bs outLen fs = some fs') :
    FastHookPost
      (bumpThen bs.length 1
        (fun s p =>
          retHook (fun s =>
            s.setMem (writeVecHeader (s.mem.writeBytes p bs) (s.readReg64 .x8)
              (BitVec.ofNat 64 bs.length) p (BitVec.ofNat 64 outLen))) s)
        allocPanicHook) s fs' := by
  unfold fastReturnFreshVecU8Len at hsome
  dsimp only [FastHookPost, bumpThen]
  cases hba : fastBumpAlloc fs.heapIvs bs.length 1 with
  | none =>
    rw [hba] at hsome
    injection hsome with hsome
    subst hsome
    rw [fastBumpAlloc_none_sound hag.heapIvs hba]
    exact fastAllocPanic_post hag
  | some pair =>
    rcases pair with ⟨p, ivs'⟩
    rw [hba] at hsome
    dsimp only at hsome
    obtain ⟨hbump, hivs1⟩ := fastBumpAlloc_some_sound hag.heapIvs hba
    rw [hbump]
    dsimp only
    set fm1 := fs.mem.mapFresh p bs.length Perm.rw
    set r := fs.readReg64 .x8
    by_cases hcw : (fm1.canWrite p bs.length && fm1.canWrite r 24) = true
    · simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      simp only [Bool.and_eq_true] at hcw
      have hm1 := FastMem.mapFresh_agrees hag.mem p bs.length Perm.rw
      have hcwp_s : (s.mem.mapFresh p bs.length Perm.rw).canWrite p bs.length = true := by
        rw [← FastMem.canWrite_eq hm1]; exact hcw.1
      have hcwr_s : (s.mem.mapFresh p bs.length Perm.rw).canWrite (s.readReg64 .x8) 24 = true := by
        rw [← FastState.readReg64_eq hag .x8, ← FastMem.canWrite_eq hm1]; exact hcw.2
      have hm2 := FastMem.writeBytes_agrees hm1 p bs
      set cap := BitVec.ofNat 64 bs.length
      set len := BitVec.ofNat 64 outLen
      have hr : r = s.readReg64 .x8 := FastState.readReg64_eq hag .x8
      rw [hr, FastState.readReg64_eq hag .lr]
      have hm3 := fastWriteVecHeader_agrees hm2 (s.readReg64 .x8) cap p len
      have hivs3 : HeapIntervalsAgree ivs'
          (writeVecHeader ((s.mem.mapFresh p bs.length Perm.rw).writeBytes p bs)
            (s.readReg64 .x8) cap p len) := by
        apply HeapIntervalsAgree.of_perm_eq hivs1
        intro a
        rw [perm_writeVecHeader_eq, perm_writeBytes_eq]
      have hag_ret : ((fs.setMemAndIvs (fastWriteVecHeader (fm1.writeBytes p bs)
          (s.readReg64 .x8) cap p len) ivs').setPC (s.readReg64 .lr)).Agrees
          (retHook (fun st =>
            st.setMem (writeVecHeader (st.mem.writeBytes p bs) (st.readReg64 .x8) cap p len))
            (s.setMem (s.mem.mapFresh p bs.length Perm.rw))) := by
        unfold retHook
        exact FastState.setPC_agrees (FastState.setMemAndIvs_agrees hag hm3 hivs3)
          (s.readReg64 .lr)
      have kf1 := keepsFrozen_mapFresh s.mem p bs.length Perm.rw
      have kf2 := keepsFrozen_writeBytes bs hcwp_s
      have hcwr2 : ((s.mem.mapFresh p bs.length Perm.rw).writeBytes p bs).canWrite
          (s.readReg64 .x8) 24 = true := by
        rw [canWrite_of_perm_eq (perm_writeBytes_eq _ p bs)]; exact hcwr_s
      have kf3 := keepsFrozen_writeVecHeader hcwr2 cap p len
      exact ⟨hag_ret, KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩
    · simp [hcw] at hsome

def fastReturnFreshVecU8 (bs : List (BitVec 8)) (fs : FastState) : Option FastState :=
  fastReturnFreshVecU8Len bs bs.length fs

theorem fastReturnFreshVecU8_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (bs : List (BitVec 8))
    (hsome : fastReturnFreshVecU8 bs fs = some fs') :
    FastHookPost (returnFreshVecU8 bs) s fs' :=
  fastReturnFreshVecU8Len_post hag bs bs.length hsome

def fastCompress512 (F512 : Sha512State → List (BitVec 8) → Sha512State) (fs : FastState) :
    Option FastState :=
  let x0 := fs.readReg64 .x0
  let st : Sha512State := List.Vector.ofFn fun i : Fin 8 =>
    fs.mem.read64 (x0 + BitVec.ofNat 64 (8 * i.val))
  let bs := fs.mem.readBytes (fs.readReg64 .x1) (128 * (fs.readReg64 .x2).toNat)
  fastWriteBytesRet x0 (sha512StateBytesLE ((chunks128 bs).foldl F512 st)) fs

theorem fastCompress512_post {F512 : Sha512State → List (BitVec 8) → Sha512State}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCompress512 F512 fs = some fs') :
    FastHookPost (compress512Hook F512) s fs' := by
  unfold fastCompress512 at hsome
  dsimp only at hsome
  have hst : (List.Vector.ofFn fun i : Fin 8 =>
      fs.mem.read64 (fs.readReg64 .x0 + BitVec.ofNat 64 (8 * i.val))) =
      readSha512State s.mem (s.readReg64 .x0) := by
    unfold readSha512State
    congr 1; funext i
    rw [FastState.readReg64_eq hag .x0, FastMem.read64_eq hag.mem]
  rw [hst, FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x2, FastMem.readBytes_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastToEdwards
    (montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160))
    (fs : FastState) : Option FastState :=
  let r := fs.readReg64 .x8
  match montToEd (fastReadVecN fs.mem (fs.readReg64 .x0) 32) (((fs.readReg64 .x1).setWidth 8) &&& 1#8) with
  | some p =>
    if fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) p.toList.length then
      some ((fs.setMem ((fs.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList)).retToLr)
    else none
  | none =>
    if fs.mem.canWrite r 8 then
      some ((fs.setMem (fs.mem.write64 r 0#64)).retToLr)
    else none

theorem fastToEdwards_post
    {montToEd : List.Vector (BitVec 8) 32 → BitVec 8 → Option (List.Vector (BitVec 8) 160)}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastToEdwards montToEd fs = some fs') :
    FastHookPost (toEdwardsHook montToEd) s fs' := by
  unfold fastToEdwards at hsome
  dsimp only [FastHookPost, toEdwardsHook]
  rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
    FastState.readReg64_eq hag .x8, fastReadVecN_eq hag.mem] at hsome
  set r := s.readReg64 .x8
  cases hme : montToEd (readVecN s.mem (s.readReg64 .x0) 32) (((s.readReg64 .x1).setWidth 8) &&& 1#8) with
  | some p =>
    rw [hme] at hsome
    dsimp only at hsome
    cases hcw : (fs.mem.canWrite r 8 && fs.mem.canWrite (r + 8#64) p.toList.length) with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
      have hm1 := FastMem.write64_agrees hag.mem r 1#64
      have hm2 := FastMem.writeBytes_agrees hm1 (r + 8#64) p.toList
      have hivs2 : HeapIntervalsAgree fs.heapIvs
          ((s.mem.write64 r 1#64).writeBytes (r + 8#64) p.toList) := by
        apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
        intro a; rw [perm_writeBytes_eq, perm_write64_eq]
      have kf1 := keepsFrozen_write64 hcw.1 1#64
      have hcw2 : (s.mem.write64 r 1#64).canWrite (r + 8#64) p.toList.length = true := by
        rw [canWrite_of_perm_eq (perm_write64_eq s.mem r 1#64)]; exact hcw.2
      have kf2 := keepsFrozen_writeBytes p.toList hcw2
      exact ⟨FastState.retToLr_agrees (FastState.setMem_agrees hag hm2 hivs2),
        KeepsFrozen.trans kf1 kf2, rfl⟩
  | none =>
    rw [hme] at hsome
    dsimp only at hsome
    cases hcw : fs.mem.canWrite r 8 with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      rw [FastMem.canWrite_eq hag.mem] at hcw
      have hm1 := FastMem.write64_agrees hag.mem r 0#64
      have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_write64_eq s.mem r 0#64)
      exact ⟨FastState.retToLr_agrees (FastState.setMem_agrees hag hm1 hivs1),
        keepsFrozen_write64 hcw 0#64, rfl⟩

def fastCompress (compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32)
    (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (compress (fastReadVecN fs.mem (fs.readReg64 .x0) 160)).toList fs

theorem fastCompress_post {compress : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 32}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastCompress compress fs = some fs') :
    FastHookPost (compressHook compress) s fs' := by
  unfold fastCompress at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastEdNeg (edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160)
    (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (edNeg (fastReadVecN fs.mem (fs.readReg64 .x0) 160)).toList fs

theorem fastEdNeg_post {edNeg : List.Vector (BitVec 8) 160 → List.Vector (BitVec 8) 160}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastEdNeg edNeg fs = some fs') :
    FastHookPost (edNegHook edNeg) s fs' := by
  unfold fastEdNeg at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastTorsionFree (isTorsionFree : List.Vector (BitVec 8) 160 → Bool) (fs : FastState) :
    Option FastState :=
  some ((fs.writeReg64 .x0
    (if isTorsionFree (fastReadVecN fs.mem (fs.readReg64 .x0) 160) then 1#64 else 0#64)).retToLr)

theorem fastTorsionFree_post {isTorsionFree : List.Vector (BitVec 8) 160 → Bool}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastTorsionFree isTorsionFree fs = some fs') :
    FastHookPost (torsionFreeHook isTorsionFree) s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, torsionFreeHook]
  rw [FastState.readReg64_eq hag .x0, fastReadVecN_eq hag.mem]
  exact ⟨FastState.retToLr_agrees (FastState.writeReg64_agrees hag .x0 _),
    KeepsFrozen.refl s.mem, rfl⟩

def fastDsmb (dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160) (fs : FastState) :
    Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (dsmb (fastReadVecN fs.mem (fs.readReg64 .x0) 32)
      (fastReadVecN fs.mem (fs.readReg64 .x1) 160)
      (fastReadVecN fs.mem (fs.readReg64 .x2) 32)).toList fs

theorem fastDsmb_post {dsmb : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160 →
    List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 160}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastDsmb dsmb fs = some fs') :
    FastHookPost (dsmbHook dsmb) s fs' := by
  unfold fastDsmb at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x2,
    fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastScalarMod (scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32)
    (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (scalarMod (fastReadVecN fs.mem (fs.readReg64 .x0) 32)).toList fs

theorem fastScalarMod_post {scalarMod : List.Vector (BitVec 8) 32 → List.Vector (BitVec 8) 32}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastScalarMod scalarMod fs = some fs') :
    FastHookPost (scalarModHook scalarMod) s fs' := by
  unfold fastScalarMod at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastScalarWide (scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32)
    (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (scalarWide (fastReadVecN fs.mem (fs.readReg64 .x0) 64)).toList fs

theorem fastScalarWide_post {scalarWide : List.Vector (BitVec 8) 64 → List.Vector (BitVec 8) 32}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastScalarWide scalarWide fs = some fs') :
    FastHookPost (scalarWideHook scalarWide) s fs' := by
  unfold fastScalarWide at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastKemEncaps (encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32) (fs : FastState) :
    Option FastState :=
  let r := fs.readReg64 .x8
  let o := encaps (fastReadVecN fs.mem (fs.readReg64 .x0) 1568)
    (fastReadVecN fs.mem (fs.readReg64 .x1) 32)
  if fs.mem.canWrite r o.1.toList.length && fs.mem.canWrite (r + 1568#64) o.2.toList.length then
    some ((fs.setMem ((fs.mem.writeBytes r o.1.toList).writeBytes (r + 1568#64) o.2.toList)).retToLr)
  else none

theorem fastKemEncaps_post {encaps : List.Vector (BitVec 8) 1568 → List.Vector (BitVec 8) 32 →
    List.Vector (BitVec 8) 1568 × List.Vector (BitVec 8) 32}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastKemEncaps encaps fs = some fs') :
    FastHookPost (kemEncapsHook encaps) s fs' := by
  unfold fastKemEncaps at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, kemEncapsHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem] at hsome
  set r := s.readReg64 .x8
  set o := encaps (readVecN s.mem (s.readReg64 .x0) 1568) (readVecN s.mem (s.readReg64 .x1) 32)
  cases hcw : (fs.mem.canWrite r o.1.toList.length &&
      fs.mem.canWrite (r + 1568#64) o.2.toList.length) with
  | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
  | true =>
    simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
    subst hsome
    simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
    have hm1 := FastMem.writeBytes_agrees hag.mem r o.1.toList
    have hm2 := FastMem.writeBytes_agrees hm1 (r + 1568#64) o.2.toList
    have hivs2 : HeapIntervalsAgree fs.heapIvs
        ((s.mem.writeBytes r o.1.toList).writeBytes (r + 1568#64) o.2.toList) := by
      apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
      intro a; rw [perm_writeBytes_eq, perm_writeBytes_eq]
    have kf1 := keepsFrozen_writeBytes o.1.toList hcw.1
    have hcw2 : (s.mem.writeBytes r o.1.toList).canWrite (r + 1568#64) o.2.toList.length = true := by
      rw [canWrite_of_perm_eq (perm_writeBytes_eq s.mem r o.1.toList)]; exact hcw.2
    have kf2 := keepsFrozen_writeBytes o.2.toList hcw2
    exact ⟨FastState.retToLr_agrees (FastState.setMem_agrees hag hm2 hivs2),
      KeepsFrozen.trans kf1 kf2, rfl⟩

def fastKemDecaps (decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (decaps (fastReadVecN fs.mem (fs.readReg64 .x0) 3168)
      (fastReadVecN fs.mem (fs.readReg64 .x1) 1568)).toList fs

theorem fastKemDecaps_post {decaps : List.Vector (BitVec 8) 3168 → List.Vector (BitVec 8) 1568 →
    List.Vector (BitVec 8) 32}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastKemDecaps decaps fs = some fs') :
    FastHookPost (kemDecapsHook decaps) s fs' := by
  unfold fastKemDecaps at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_returnToLr_post hag _ _ hsome

def fastMlkemFromSeed (K : MlKem) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (K.keyPair (fastReadVecN fs.mem (fs.readReg64 .x0) 64)).toList fs

theorem fastMlkemFromSeed_post {K : MlKem} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemFromSeed K fs = some fs') :
    FastHookPost (mlkemFromSeedHook K) s fs' := by
  unfold fastMlkemFromSeed at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    fastReadVecN_eq hag.mem, ← MlKem.fromSeed_dk] at hsome
  exact fastWriteBytesRet_retHook_post hag _ _ hsome

def fastMlkemPk1 (fs : FastState) : Option FastState :=
  let lr := fs.readReg64 .lr
  some ((fs.writeReg64 .x0 (fs.readReg64 .x0 + 2304#64)).setPC lr)

theorem fastMlkemPk1_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemPk1 fs = some fs') :
    FastHookPost mlkemPk1Hook s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, mlkemPk1Hook, retHook]
  rw [FastState.readReg64_eq hag .lr, FastState.readReg64_eq hag .x0]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastMlkemPk2 (fs : FastState) : Option FastState :=
  let lr := fs.readReg64 .lr
  some ((fs.writeReg64 .x0 (fs.readReg64 .x0 + 1152#64)).setPC lr)

theorem fastMlkemPk2_post {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemPk2 fs = some fs') :
    FastHookPost mlkemPk2Hook s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, mlkemPk2Hook, retHook]
  rw [FastState.readReg64_eq hag .lr, FastState.readReg64_eq hag .x0]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastMlkemEncaps1 (K : MlKem) (fs : FastState) : Option FastState :=
  let ret := fs.readReg64 .x8
  let lr := fs.readReg64 .lr
  if (fs.readReg64 .x4).toNat < 2080 || (fs.readReg64 .x6).toNat < 32 then
    if fs.mem.canWrite ret 2 then
      some ((fs.setMem (fs.mem.writeBytes ret [1#8, 1#8])).setPC lr)
    else none
  else
    let hdr := fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat
    let rand := fastReadVecN fs.mem (fs.readReg64 .x2) 32
    let esA := fs.readReg64 .x3
    let ssA := fs.readReg64 .x5
    match K.encaps1 hdr rand with
    | some (ct1, es, ss) =>
      let b0 := 0#8 :: ct1.toList
      if fs.mem.canWrite ret b0.length && fs.mem.canWrite esA es.toList.length &&
          fs.mem.canWrite ssA ss.toList.length then
        some ((fs.setMem (((fs.mem.writeBytes ret b0).writeBytes esA es.toList).writeBytes
          ssA ss.toList)).setPC lr)
      else none
    | none =>
      if fs.mem.canWrite ret 1 then
        some ((fs.setMem (fs.mem.writeBytes ret [1#8])).setPC lr)
      else none

theorem fastMlkemEncaps1_post {K : MlKem} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemEncaps1 K fs = some fs') :
    FastHookPost (mlkemEncaps1Hook K) s fs' := by
  unfold fastMlkemEncaps1 at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, mlkemEncaps1Hook, retHook]
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x4,
    FastState.readReg64_eq hag .x6, FastState.readReg64_eq hag .lr] at hsome
  set ret := s.readReg64 .x8
  cases hlen : (decide ((s.readReg64 .x4).toNat < 2080) || decide ((s.readReg64 .x6).toNat < 32)) with
  | true =>
    simp only [hlen, ↓reduceIte] at hsome ⊢
    cases hcw : fs.mem.canWrite ret 2 with
    | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
    | true =>
      simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
      subst hsome
      rw [FastMem.canWrite_eq hag.mem] at hcw
      have hm1 := FastMem.writeBytes_agrees hag.mem ret [1#8, 1#8]
      have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_writeBytes_eq s.mem ret [1#8, 1#8])
      exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
        keepsFrozen_writeBytes [1#8, 1#8] hcw, rfl⟩
  | false =>
    simp only [hlen, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x0, FastState.readReg64_eq hag .x1,
      FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x3,
      FastState.readReg64_eq hag .x5, FastMem.readBytes_eq hag.mem,
      fastReadVecN_eq hag.mem] at hsome
    set hdr := s.mem.readBytes (s.readReg64 .x0) (s.readReg64 .x1).toNat
    set rand := readVecN s.mem (s.readReg64 .x2) 32
    set esA := s.readReg64 .x3
    set ssA := s.readReg64 .x5
    cases henc : K.encaps1 hdr rand with
    | some tup =>
      rcases tup with ⟨ct1, es, ss⟩
      rw [henc] at hsome
      dsimp only at hsome
      set b0 := 0#8 :: ct1.toList
      cases hcw : (fs.mem.canWrite ret b0.length && fs.mem.canWrite esA es.toList.length &&
          fs.mem.canWrite ssA ss.toList.length) with
      | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
      | true =>
        simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
        subst hsome
        simp only [Bool.and_eq_true, FastMem.canWrite_eq hag.mem] at hcw
        rcases hcw with ⟨⟨hcw1, hcw2⟩, hcw3⟩
        have hm1 := FastMem.writeBytes_agrees hag.mem ret b0
        have hm2 := FastMem.writeBytes_agrees hm1 esA es.toList
        have hm3 := FastMem.writeBytes_agrees hm2 ssA ss.toList
        have hivs3 : HeapIntervalsAgree fs.heapIvs
            (((s.mem.writeBytes ret b0).writeBytes esA es.toList).writeBytes ssA ss.toList) := by
          apply HeapIntervalsAgree.of_perm_eq hag.heapIvs
          intro a; rw [perm_writeBytes_eq, perm_writeBytes_eq, perm_writeBytes_eq]
        have kf1 := keepsFrozen_writeBytes b0 hcw1
        have hcw2' : (s.mem.writeBytes ret b0).canWrite esA es.toList.length = true := by
          rw [canWrite_of_perm_eq (perm_writeBytes_eq s.mem ret b0)]; exact hcw2
        have kf2 := keepsFrozen_writeBytes es.toList hcw2'
        have hcw3' : ((s.mem.writeBytes ret b0).writeBytes esA es.toList).canWrite
            ssA ss.toList.length = true := by
          rw [canWrite_of_perm_eq (perm_writeBytes_eq _ esA es.toList),
            canWrite_of_perm_eq (perm_writeBytes_eq s.mem ret b0)]
          exact hcw3
        have kf3 := keepsFrozen_writeBytes ss.toList hcw3'
        exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm3 hivs3) (s.readReg64 .lr),
          KeepsFrozen.trans (KeepsFrozen.trans kf1 kf2) kf3, rfl⟩
    | none =>
      rw [henc] at hsome
      dsimp only at hsome
      cases hcw : fs.mem.canWrite ret 1 with
      | false => simp only [hcw, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hsome
      | true =>
        simp only [hcw, ↓reduceIte, Option.some.injEq] at hsome
        subst hsome
        rw [FastMem.canWrite_eq hag.mem] at hcw
        have hm1 := FastMem.writeBytes_agrees hag.mem ret [1#8]
        have hivs1 := HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_writeBytes_eq s.mem ret [1#8])
        exact ⟨FastState.setPC_agrees (FastState.setMem_agrees hag hm1 hivs1) (s.readReg64 .lr),
          keepsFrozen_writeBytes [1#8] hcw, rfl⟩

def fastMlkemEncaps2 (K : MlKem) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (K.encaps2 (fastReadVecN fs.mem (fs.readReg64 .x0) 2080)
      (fastReadVecN fs.mem (fs.readReg64 .x1) 1152)).toList fs

theorem fastMlkemEncaps2_post {K : MlKem} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemEncaps2 K fs = some fs') :
    FastHookPost (mlkemEncaps2Hook K) s fs' := by
  unfold fastMlkemEncaps2 at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_retHook_post hag _ _ hsome

def fastMlkemDecaps (K : MlKem) (fs : FastState) : Option FastState :=
  fastWriteBytesRet (fs.readReg64 .x8)
    (K.decaps (fastReadVecN fs.mem (fs.readReg64 .x0) 2400)
      (fastReadVecN fs.mem (fs.readReg64 .x1) 960)
      (fastReadVecN fs.mem (fs.readReg64 .x2) 128)).toList fs

theorem fastMlkemDecaps_post {K : MlKem} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemDecaps K fs = some fs') :
    FastHookPost (mlkemDecapsHook K) s fs' := by
  unfold fastMlkemDecaps at hsome
  rw [FastState.readReg64_eq hag .x8, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x2,
    fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem, fastReadVecN_eq hag.mem] at hsome
  exact fastWriteBytesRet_retHook_post hag _ _ hsome

def fastMlkemValidatePk (K : MlKem) (fs : FastState) : Option FastState :=
  let lr := fs.readReg64 .lr
  let hdr := fs.mem.readBytes (fs.readReg64 .x0) (fs.readReg64 .x1).toNat
  let ek := fs.mem.readBytes (fs.readReg64 .x2) (fs.readReg64 .x3).toNat
  some ((fs.writeReg64 .x0 (if K.validPkBytes hdr ek then 255#64 else 0#64)).setPC lr)

theorem fastMlkemValidatePk_post {K : MlKem} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (hsome : fastMlkemValidatePk K fs = some fs') :
    FastHookPost (mlkemValidatePkHook K) s fs' := by
  injection hsome with hsome
  subst hsome
  dsimp only [FastHookPost, mlkemValidatePkHook, retHook]
  rw [FastState.readReg64_eq hag .lr, FastState.readReg64_eq hag .x0,
    FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x2,
    FastState.readReg64_eq hag .x3, FastMem.readBytes_eq hag.mem, FastMem.readBytes_eq hag.mem]
  exact ⟨FastState.setPC_agrees (FastState.writeReg64_agrees hag .x0 _) (s.readReg64 .lr),
    KeepsFrozen.refl s.mem, rfl⟩

def fastLibcruxHmac (F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState)
    (fs : FastState) : Option FastState :=
  if (fs.readReg64 .x0).setWidth 32 != 0#32 then
    some (fs.setStatus (.Exception "libcrux_hmac::hmac: alg != Sha256"))
  else
    let keyLen := (fs.readReg64 .x2).toNat
    let dataLen := (fs.readReg64 .x4).toNat
    if keyLen < 2 ^ 32 ∧ dataLen < 2 ^ 32 then
      let key := fs.mem.readBytes (fs.readReg64 .x1) keyLen
      let data := fs.mem.readBytes (fs.readReg64 .x3) dataLen
      let tag := HMAC.hmacWith F key data
      let outLen :=
        if (fs.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32 then
          min (fs.readReg64 .x6).toNat tag.length
        else
          tag.length
      fastReturnFreshVecU8Len tag outLen fs
    else
      some (fs.setStatus .Panicked)

theorem fastLibcruxHmac_post {F : HMAC.ShaState → List (BitVec 8) → HMAC.ShaState}
    {fs fs' : FastState} {s : State} (hag : fs.Agrees s)
    (hsome : fastLibcruxHmac F fs = some fs') :
    FastHookPost (libcruxHmacHook F) s fs' := by
  unfold fastLibcruxHmac at hsome
  dsimp only at hsome
  dsimp only [FastHookPost, libcruxHmacHook]
  rw [FastState.readReg64_eq hag .x0] at hsome
  cases halg : ((s.readReg64 .x0).setWidth 32 != 0#32) with
  | true =>
    simp only [halg, ↓reduceIte, Option.some.injEq] at hsome ⊢
    subst hsome
    exact ⟨FastState.setStatus_agrees hag _, KeepsFrozen.refl s.mem, rfl⟩
  | false =>
    simp only [halg, Bool.false_eq_true, ↓reduceIte] at hsome ⊢
    rw [FastState.readReg64_eq hag .x2, FastState.readReg64_eq hag .x4] at hsome
    set keyLen := (s.readReg64 .x2).toNat
    set dataLen := (s.readReg64 .x4).toNat
    by_cases hlt : keyLen < 2 ^ 32 ∧ dataLen < 2 ^ 32
    · simp only [hlt] at hsome ⊢
      rw [FastState.readReg64_eq hag .x1, FastState.readReg64_eq hag .x3,
        FastState.readReg64_eq hag .x5, FastState.readReg64_eq hag .x6,
        FastMem.readBytes_eq hag.mem, FastMem.readBytes_eq hag.mem] at hsome
      exact fastReturnFreshVecU8Len_post hag _ _ hsome
    · simp only [hlt, ↓reduceIte, Option.some.injEq] at hsome ⊢
      subst hsome
      exact ⟨FastState.setStatus_agrees hag .Panicked, KeepsFrozen.refl s.mem, rfl⟩

end Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
