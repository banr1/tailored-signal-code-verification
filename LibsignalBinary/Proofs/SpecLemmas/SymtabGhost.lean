/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.LibcHooks
import LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Ghost-State Independence of `State.symtab`

**Checked by Lean.**

`Step` never modifies `State.symtab`, and instruction/syscall execution (`execInst`,
`execSyscall`) commutes with `State.withSymtab`. Consequently, for any program whose
extern hooks, override hooks, and `svc` handler commute with `State.withSymtab`
(`Program.HooksSymtabFree`), replacing `symtab` in both endpoints preserves `Steps`
(`symtabGhost_of_hooksSymtabFree`).
-/

namespace Arm64

/-- Replace the symbol table. Named so `simp`/`dsimp` rewrite it without touching every structure
update in the goal. -/
def State.withSymtab (s : State) (t : String → String → Option (BitVec 64)) : State :=
  { s with symtab := t }

/-- `f` neither reads nor writes `State.symtab`: it commutes with replacing it. -/
abbrev SymtabFree (f : State → State) : Prop :=
  ∀ (t : String → String → Option (BitVec 64)) (s : State),
    f (s.withSymtab t) = (f s).withSymtab t

/-- Every hook of the table `X` is `SymtabFree`. -/
def SymtabFreeHooks (X : String → Option (State → State)) : Prop :=
  ∀ n f, X n = some f → SymtabFree f

/-- Every extern hook, override hook, and supervisor-call handler of `P` is `SymtabFree`. -/
def Program.HooksSymtabFree (P : Program) : Prop :=
  SymtabFreeHooks P.externs ∧ SymtabFreeHooks P.overrides ∧ SymtabFree P.svc

/-- Replacing `symtab` in both start and end states preserves `Steps P`. -/
def SymtabGhost (P : Program) : Prop :=
  ∀ (t : String → String → Option (BitVec 64)) {s s' : State},
    Steps P s s' → Steps P { s with symtab := t } { s' with symtab := t }

namespace State

section WithSymtab

variable (s : State) (t : String → String → Option (BitVec 64))

theorem withSymtab_symtab : (s.withSymtab t).symtab = t := rfl
theorem withSymtab_self : s.withSymtab s.symtab = s := rfl
theorem withSymtab_withSymtab (t' : String → String → Option (BitVec 64)) :
    (s.withSymtab t).withSymtab t' = s.withSymtab t' := rfl

/-! ## Field Projections -/
theorem withSymtab_regs : (s.withSymtab t).regs = s.regs := rfl
theorem withSymtab_vregs : (s.withSymtab t).vregs = s.vregs := rfl
theorem withSymtab_sp : (s.withSymtab t).sp = s.sp := rfl
theorem withSymtab_pc : (s.withSymtab t).pc = s.pc := rfl
theorem withSymtab_pstate : (s.withSymtab t).pstate = s.pstate := rfl
theorem withSymtab_mem : (s.withSymtab t).mem = s.mem := rfl
theorem withSymtab_tpidrEl0 : (s.withSymtab t).tpidrEl0 = s.tpidrEl0 := rfl
theorem withSymtab_fpsr : (s.withSymtab t).fpsr = s.fpsr := rfl
theorem withSymtab_brkStart : (s.withSymtab t).brkStart = s.brkStart := rfl
theorem withSymtab_brk : (s.withSymtab t).brk = s.brk := rfl
theorem withSymtab_fs : (s.withSymtab t).fs = s.fs := rfl
theorem withSymtab_trace : (s.withSymtab t).trace = s.trace := rfl
theorem withSymtab_status : (s.withSymtab t).status = s.status := rfl
theorem withSymtab_sigActions : (s.withSymtab t).sigActions = s.sigActions := rfl
theorem withSymtab_sigAltStack : (s.withSymtab t).sigAltStack = s.sigAltStack := rfl
theorem withSymtab_physMemAvail : (s.withSymtab t).physMemAvail = s.physMemAvail := rfl
theorem withSymtab_getSigAction (sig : BitVec 32) :
    (s.withSymtab t).getSigAction sig = s.getSigAction sig := rfl
theorem withSymtab_readReg64 (r : Reg) : (s.withSymtab t).readReg64 r = s.readReg64 r := rfl
theorem withSymtab_readReg32 (r : Reg) : (s.withSymtab t).readReg32 r = s.readReg32 r := rfl
theorem withSymtab_readReg (w : Width) (r : Reg) :
    (s.withSymtab t).readReg w r = s.readReg w r := rfl
theorem withSymtab_readVReg128 (i : BitVec 5) :
    (s.withSymtab t).readVReg128 i = s.readVReg128 i := rfl
theorem withSymtab_readVReg64 (i : BitVec 5) :
    (s.withSymtab t).readVReg64 i = s.readVReg64 i := rfl
theorem withSymtab_readVReg32 (i : BitVec 5) :
    (s.withSymtab t).readVReg32 i = s.readVReg32 i := rfl
theorem withSymtab_spAligned : (s.withSymtab t).spAligned = s.spAligned := rfl
theorem withSymtab_checkRegSPAligned (r : Reg) :
    checkRegSPAligned (s.withSymtab t) r = checkRegSPAligned s r := rfl
theorem withSymtab_checkAddrSPAligned (a : AddrMode) :
    checkAddrSPAligned (s.withSymtab t) a = checkAddrSPAligned s a := rfl
theorem withSymtab_evalAddrMode (a : AddrMode) :
    evalAddrMode (s.withSymtab t) a = evalAddrMode s a := rfl

/-! ## State Updates -/
theorem withSymtab_setMem (m : Memory) : (s.withSymtab t).setMem m = (s.setMem m).withSymtab t :=
  rfl
theorem withSymtab_setStatus (x : ExecStatus) :
    (s.withSymtab t).setStatus x = (s.setStatus x).withSymtab t := rfl
theorem withSymtab_setPC (x : BitVec 64) : (s.withSymtab t).setPC x = (s.setPC x).withSymtab t :=
  rfl
theorem withSymtab_advancePC : (s.withSymtab t).advancePC = s.advancePC.withSymtab t := rfl
theorem withSymtab_setPState (x : PState) :
    (s.withSymtab t).setPState x = (s.setPState x).withSymtab t := rfl
theorem withSymtab_setFpsr (x : BitVec 32) :
    (s.withSymtab t).setFpsr x = (s.setFpsr x).withSymtab t := rfl
theorem withSymtab_orFpsr (x : BitVec 32) :
    (s.withSymtab t).orFpsr x = (s.orFpsr x).withSymtab t := rfl
theorem withSymtab_setBrk (x : BitVec 64) : (s.withSymtab t).setBrk x = (s.setBrk x).withSymtab t :=
  rfl
theorem withSymtab_setPhysMemAvail (x : Nat) :
    (s.withSymtab t).setPhysMemAvail x = (s.setPhysMemAvail x).withSymtab t := rfl
theorem withSymtab_setFs (x : FsState) : (s.withSymtab t).setFs x = (s.setFs x).withSymtab t := rfl
theorem withSymtab_setSigAction (sig : BitVec 32) (act : SigAction) :
    (s.withSymtab t).setSigAction sig act = (s.setSigAction sig act).withSymtab t := rfl
theorem withSymtab_setSigAltStack (sas : SigAltStack) :
    (s.withSymtab t).setSigAltStack sas = (s.setSigAltStack sas).withSymtab t := rfl
theorem withSymtab_appendTrace (x : List TraceEvent) :
    (s.withSymtab t).appendTrace x = (s.appendTrace x).withSymtab t := rfl
theorem withSymtab_writeReg64 (r : Reg) (v : BitVec 64) :
    (s.withSymtab t).writeReg64 r v = (s.writeReg64 r v).withSymtab t := rfl
theorem withSymtab_writeReg32 (r : Reg) (v : BitVec 32) :
    (s.withSymtab t).writeReg32 r v = (s.writeReg32 r v).withSymtab t := rfl
theorem withSymtab_writeReg (w : Width) (r : Reg) (v : BitVec 64) :
    (s.withSymtab t).writeReg w r v = (s.writeReg w r v).withSymtab t := rfl
theorem withSymtab_writeVReg128 (i : BitVec 5) (v : BitVec 128) :
    (s.withSymtab t).writeVReg128 i v = (s.writeVReg128 i v).withSymtab t := rfl
theorem withSymtab_writeVReg64 (i : BitVec 5) (v : BitVec 64) :
    (s.withSymtab t).writeVReg64 i v = (s.writeVReg64 i v).withSymtab t := rfl
theorem withSymtab_writeVReg32 (i : BitVec 5) (v : BitVec 32) :
    (s.withSymtab t).writeVReg32 i v = (s.writeVReg32 i v).withSymtab t := rfl

/-- A partially applied read (`simdStoreRegs` takes `s.readVReg128` as a function). -/
theorem withSymtab_readVReg128_fn : (s.withSymtab t).readVReg128 = s.readVReg128 := rfl

/-- Record-update normalizer pulling `withSymtab` outside `{ s with status := ... }`. -/
theorem status_withSymtab_symtab (status : ExecStatus) :
    ({ s with status := status, symtab := (s.withSymtab t).symtab } : State) =
      ({ s with status := status } : State).withSymtab t := rfl

theorem tpidrEl0_withSymtab_symtab (v : BitVec 64) :
    ({ s with tpidrEl0 := v, symtab := (s.withSymtab t).symtab } : State) =
      ({ s with tpidrEl0 := v } : State).withSymtab t := rfl

/-! ## Exclusive-Monitor Fields -/
theorem withSymtab_oracle : (s.withSymtab t).oracle = s.oracle := rfl
theorem withSymtab_oracleIdx : (s.withSymtab t).oracleIdx = s.oracleIdx := rfl
theorem withSymtab_exclFails : (s.withSymtab t).exclFails = s.exclFails := rfl
theorem withSymtab_exclWillFail : (s.withSymtab t).exclWillFail = s.exclWillFail := rfl
theorem withSymtab_nextOracle : (s.withSymtab t).nextOracle = s.nextOracle.withSymtab t := rfl
theorem withSymtab_stepExclOracle :
    (s.withSymtab t).stepExclOracle = s.stepExclOracle.withSymtab t := rfl

theorem ite_withSymtab {c : Prop} [Decidable c] (A B : State) :
    (if c then A.withSymtab t else B.withSymtab t) = (if c then A else B).withSymtab t := by
  split <;> rfl

/-- Case split on an `if` that appears on both sides, for terms too large for `split`
(its `simp` exceeds the step limit on the whole goal). -/
theorem ite_eq_withSymtab_of {c : Prop} [Decidable c] {A B A' B' : State}
    (hA : c → A = A'.withSymtab t) (hB : ¬c → B = B'.withSymtab t) :
    (if c then A else B) = (if c then A' else B').withSymtab t := by
  split
  · exact hA ‹c›
  · exact hB ‹¬c›

end WithSymtab

end State

/-- Normalise a `SymtabFree` goal: zeta-reduce, push `withSymtab` out of every read and write,
and decide each `if` whose condition a hypothesis decides. -/
macro "symtab_free_norm" : tactic => `(tactic|
  (try dsimp (config := { zetaHave := true, zeta := true, instances := true }) only [
     State.withSymtab_regs, State.withSymtab_vregs, State.withSymtab_sp,
     State.withSymtab_pc, State.withSymtab_pstate, State.withSymtab_mem,
     State.withSymtab_tpidrEl0, State.withSymtab_fpsr, State.withSymtab_brkStart,
     State.withSymtab_brk, State.withSymtab_fs, State.withSymtab_trace,
     State.withSymtab_status, State.withSymtab_sigActions, State.withSymtab_sigAltStack,
     State.withSymtab_physMemAvail,
     State.withSymtab_getSigAction,
     State.withSymtab_readReg64,
     State.withSymtab_readReg32, State.withSymtab_readReg, State.withSymtab_readVReg128,
     State.withSymtab_readVReg64, State.withSymtab_readVReg32, State.withSymtab_spAligned,
     State.withSymtab_checkRegSPAligned, State.withSymtab_checkAddrSPAligned,
     State.withSymtab_evalAddrMode, State.withSymtab_setMem,
     State.withSymtab_setStatus, State.withSymtab_setPC, State.withSymtab_advancePC,
     State.withSymtab_setPState, State.withSymtab_setFpsr, State.withSymtab_orFpsr,
     State.withSymtab_setBrk, State.withSymtab_setPhysMemAvail, State.withSymtab_setFs,
     State.withSymtab_setSigAction, State.withSymtab_setSigAltStack,
     State.withSymtab_appendTrace,
     State.withSymtab_writeReg64, State.withSymtab_writeReg32, State.withSymtab_writeReg,
     State.withSymtab_writeVReg128, State.withSymtab_writeVReg64, State.withSymtab_writeVReg32,
     State.withSymtab_readVReg128_fn,
     State.status_withSymtab_symtab, State.tpidrEl0_withSymtab_symtab,
     State.withSymtab_oracle, State.withSymtab_oracleIdx, State.withSymtab_exclFails,
     State.withSymtab_exclWillFail, State.withSymtab_nextOracle, State.withSymtab_stepExclOracle]
   try simp (config := { instances := true }) only [*, State.ite_withSymtab, Bool.false_eq_true,
     Bool.true_eq_false, Bool.not_true, Bool.not_false, ↓reduceIte, ↓reduceDIte]))

/-- Close `f (s.withSymtab t) = (f s).withSymtab t` once `f` is unfolded: normalise, split every
`if` and `match`, and close each leaf by `rfl`. Hypotheses of the form
`∀ s, g (s.withSymtab t) = (g s).withSymtab t` in the context are used for sub-functions `g`. -/
macro "symtab_free_close" : tactic => `(tactic|
  (symtab_free_norm
   repeat' (split <;> try symtab_free_norm)
   all_goals first | with_reducible rfl | rfl))

set_option linter.unusedSimpArgs false

/-! ## Instruction Execution Helpers -/

section ExecHelpers

variable (t : String → String → Option (BitVec 64)) (s : State)

theorem execAddSubImm_withSymtab (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (shift12 : Bool) :
    execAddSubImm w op rd rn imm12 shift12 (s.withSymtab t) =
      (execAddSubImm w op rd rn imm12 shift12 s).withSymtab t := by
  simp only [execAddSubImm]; symtab_free_close
theorem execAddSubExt_withSymtab (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amt : Nat) :
    execAddSubExt w op rd rn rm ext amt (s.withSymtab t) =
      (execAddSubExt w op rd rn rm ext amt s).withSymtab t := by
  simp only [execAddSubExt]; symtab_free_close
theorem execAddSubShift_withSymtab (w : Width) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) :
    execAddSubShift w op rd rn rm sh amt (s.withSymtab t) =
      (execAddSubShift w op rd rn rm sh amt s).withSymtab t := by
  simp only [execAddSubShift]; symtab_free_close
theorem execAddSubCarry_withSymtab (w : Width) (op : AddSubOp) (rd rn rm : Reg) :
    execAddSubCarry w op rd rn rm (s.withSymtab t) =
      (execAddSubCarry w op rd rn rm s).withSymtab t := by
  simp only [execAddSubCarry]; symtab_free_close
theorem execLogicalImm_withSymtab (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64) :
    execLogicalImm w op rd rn imm (s.withSymtab t) =
      (execLogicalImm w op rd rn imm s).withSymtab t := by
  simp only [execLogicalImm]; symtab_free_close
theorem execLogicalShift_withSymtab (w : Width) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) :
    execLogicalShift w op rd rn rm sh amt (s.withSymtab t) =
      (execLogicalShift w op rd rn rm sh amt s).withSymtab t := by
  simp only [execLogicalShift]; symtab_free_close
theorem execMoveWide_withSymtab (w : Width) (op : MoveWideOp) (rd : Reg) (imm : BitVec 16)
    (hw : Nat) :
    execMoveWide w op rd imm hw (s.withSymtab t) = (execMoveWide w op rd imm hw s).withSymtab t := by
  simp only [execMoveWide]; symtab_free_close
theorem execBitfield_withSymtab (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) :
    execBitfield w op rd rn immr imms (s.withSymtab t) =
      (execBitfield w op rd rn immr imms s).withSymtab t := by
  simp only [execBitfield]; symtab_free_close
theorem execCondSelect_withSymtab (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) :
    execCondSelect w op rd rn rm cond (s.withSymtab t) =
      (execCondSelect w op rd rn rm cond s).withSymtab t := by
  simp only [execCondSelect]; symtab_free_close
theorem execCondCompare_withSymtab (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64)
    (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) :
    execCondCompare w isSub isImm rn rhs rm nzcv cond (s.withSymtab t) =
      (execCondCompare w isSub isImm rn rhs rm nzcv cond s).withSymtab t := by
  simp only [execCondCompare]; symtab_free_close
theorem execDataProc1_withSymtab (w : Width) (op : DataProc1Op) (rd rn : Reg) :
    execDataProc1 w op rd rn (s.withSymtab t) = (execDataProc1 w op rd rn s).withSymtab t := by
  simp only [execDataProc1]; symtab_free_close
theorem execDataProc2_withSymtab (w : Width) (op : DataProc2Op) (rd rn rm : Reg) :
    execDataProc2 w op rd rn rm (s.withSymtab t) = (execDataProc2 w op rd rn rm s).withSymtab t := by
  simp only [execDataProc2]; symtab_free_close
theorem execDataProc3_withSymtab (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) :
    execDataProc3 w op rd rn rm ra (s.withSymtab t) =
      (execDataProc3 w op rd rn rm ra s).withSymtab t := by
  simp only [execDataProc3]; symtab_free_close
theorem execLdr_withSymtab (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (addr : AddrMode) :
    execLdr w size signed rt addr (s.withSymtab t) = (execLdr w size signed rt addr s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execLdr]
  symtab_free_norm; generalize evalAddrMode s addr = ea; symtab_free_close
theorem execLdrLit_withSymtab (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) :
    execLdrLit w size signed rt offset (s.withSymtab t) =
      (execLdrLit w size signed rt offset s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execLdrLit]; symtab_free_close
theorem execStr_withSymtab (size : MemWidth) (rt : Reg) (addr : AddrMode) :
    execStr size rt addr (s.withSymtab t) = (execStr size rt addr s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execStr]
  symtab_free_norm; generalize evalAddrMode s addr = ea; symtab_free_close
theorem execLdp_withSymtab (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) :
    execLdp w signed rt1 rt2 addr (s.withSymtab t) = (execLdp w signed rt1 rt2 addr s).withSymtab t := by
  unfold execLdp
  rw [State.withSymtab_checkAddrSPAligned, State.withSymtab_evalAddrMode, State.withSymtab_mem]
  rcases evalAddrMode s addr with ⟨ea, wb⟩
  cases wb <;>
    simp only [State.withSymtab_setStatus, State.withSymtab_writeReg64,
      State.withSymtab_writeReg, State.withSymtab_advancePC, State.ite_withSymtab]
theorem execStp_withSymtab (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) :
    execStp w rt1 rt2 addr (s.withSymtab t) = (execStp w rt1 rt2 addr s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execStp]
  symtab_free_norm; generalize evalAddrMode s addr = ea; symtab_free_close
theorem applySimdResult_withSymtab (rd : BitVec 5) (r : Except String (BitVec 128)) :
    applySimdResult (s.withSymtab t) rd r = (applySimdResult s rd r).withSymtab t := by
  cases r <;> rfl
theorem applySimdSatResult_withSymtab (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) :
    applySimdSatResult (s.withSymtab t) rd r satFlags =
      (applySimdSatResult s rd r satFlags).withSymtab t := by
  cases r <;> cases satFlags <;> rfl

end ExecHelpers

theorem simdLoadRegs_withSymtab (t : String → String → Option (BitVec 64)) (sz : SimdMemSize)
    (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      simdLoadRegs sz m k vt ea (s.withSymtab t) = (simdLoadRegs sz m k vt ea s).withSymtab t
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]
    rw [State.withSymtab_writeVReg128, simdLoadRegs_withSymtab t sz m k]

/-! ## System Calls -/

section Syscalls

variable (t : String → String → Option (BitVec 64)) (s : State)

theorem execIoctl_withSymtab : execIoctl (s.withSymtab t) = (execIoctl s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; symtab_free_close
theorem execFcntl_withSymtab : execFcntl (s.withSymtab t) = (execFcntl s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; symtab_free_close
private theorem applyOpenVerdict_withSymtab (v : OpenVerdict) :
    applyOpenVerdict (s.withSymtab t) v = (applyOpenVerdict s v).withSymtab t := by
  cases v <;> dsimp only [applyOpenVerdict] <;> symtab_free_close
theorem execOpenat_withSymtab : execOpenat (s.withSymtab t) = (execOpenat s).withSymtab t := by
  simp only [execOpenat, State.withSymtab_readReg32, State.withSymtab_readReg64,
    State.withSymtab_mem, State.withSymtab_fs]
  rcases checkOpenFlags (s.readReg32 Reg.x2) with _ | v
  · rcases readCString s.mem (s.readReg64 Reg.x1) with rawPath | _ | _ <;>
      simp only [applyOpenVerdict_withSymtab, State.withSymtab_setStatus,
        State.withSymtab_writeReg64, State.withSymtab_advancePC]
  · exact applyOpenVerdict_withSymtab t s v
theorem execClose_withSymtab : execClose (s.withSymtab t) = (execClose s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execClose]; symtab_free_close
theorem execLseek_withSymtab : execLseek (s.withSymtab t) = (execLseek s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execLseek]; symtab_free_close
theorem execReadCommon_withSymtab (b : Bool) :
    execReadCommon (s.withSymtab t) b = (execReadCommon s b).withSymtab t := by
  dsimp only [execReadCommon]
  rw [State.withSymtab_readReg32, State.withSymtab_readReg64, State.withSymtab_readReg64,
    State.withSymtab_readReg64, State.withSymtab_mem, State.withSymtab_fs]
  rcases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with _ | desc <;>
    simp only [State.withSymtab_writeReg64, State.withSymtab_advancePC,
      State.withSymtab_setStatus, State.withSymtab_setMem, State.withSymtab_setFs,
      State.withSymtab_fs, State.ite_withSymtab]
theorem execRead_withSymtab : execRead (s.withSymtab t) = (execRead s).withSymtab t :=
  execReadCommon_withSymtab t s false
theorem execPread64_withSymtab : execPread64 (s.withSymtab t) = (execPread64 s).withSymtab t :=
  execReadCommon_withSymtab t s true
theorem execWrite_withSymtab : execWrite (s.withSymtab t) = (execWrite s).withSymtab t := by
  dsimp only [execWrite]
  rw [State.withSymtab_readReg32, State.withSymtab_readReg64, State.withSymtab_readReg64,
    State.withSymtab_mem, State.withSymtab_fs]
  rcases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with _ | desc <;>
    simp only [State.withSymtab_writeReg64, State.withSymtab_advancePC,
      State.withSymtab_setStatus, State.withSymtab_appendTrace, State.withSymtab_setFs,
      State.ite_withSymtab]
theorem execExit_withSymtab : execExit (s.withSymtab t) = (execExit s).withSymtab t := rfl
theorem execFstat_withSymtab : execFstat (s.withSymtab t) = (execFstat s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execFstat]; symtab_free_close
theorem execPpoll_withSymtab : execPpoll (s.withSymtab t) = (execPpoll s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  symtab_free_norm
  rcases evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with _ | ⟨m', count⟩ <;>
    symtab_free_close
theorem execSetTidAddress_withSymtab :
    execSetTidAddress (s.withSymtab t) = (execSetTidAddress s).withSymtab t := rfl
theorem execGetpid_withSymtab :
    execGetpid (s.withSymtab t) = (execGetpid s).withSymtab t := rfl
theorem execSchedGetaffinity_withSymtab :
    execSchedGetaffinity (s.withSymtab t) = (execSchedGetaffinity s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; symtab_free_close
theorem execRtSigprocmask_withSymtab :
    execRtSigprocmask (s.withSymtab t) = (execRtSigprocmask s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; symtab_free_close
theorem execRtSigaction_withSymtab :
    execRtSigaction (s.withSymtab t) = (execRtSigaction s).withSymtab t := by
  unfold execRtSigaction
  by_cases hact : s.readReg64 Reg.x1 == 0#64 <;>
    (simp (config := { instances := true }) only [State.withSymtab_readReg32,
       State.withSymtab_readReg64, State.withSymtab_mem, State.withSymtab_getSigAction,
       State.withSymtab_setSigAction, State.withSymtab_setMem, State.withSymtab_writeReg64,
       State.withSymtab_advancePC, State.withSymtab_setStatus, State.ite_withSymtab,
       hact, ↓reduceIte, Bool.false_eq_true]
     rfl)
theorem execTkill_withSymtab :
    execTkill (s.withSymtab t) = (execTkill s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execTkill]; symtab_free_close
theorem execTgkill_withSymtab :
    execTgkill (s.withSymtab t) = (execTgkill s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; symtab_free_close
theorem execSigaltstack_withSymtab :
    execSigaltstack (s.withSymtab t) = (execSigaltstack s).withSymtab t := by
  unfold execSigaltstack
  by_cases huss : s.readReg64 Reg.x0 == 0#64 <;>
    by_cases hdis : s.mem.read32 (s.readReg64 Reg.x0 + 8#64) &&& ~~~SS_AUTODISARM == SS_DISABLE <;>
      (simp (config := { instances := true }) only [State.withSymtab_readReg64,
         State.withSymtab_mem, State.withSymtab_sp, State.withSymtab_sigAltStack,
         State.withSymtab_setSigAltStack, State.withSymtab_setMem, State.withSymtab_writeReg64,
         State.withSymtab_advancePC, State.withSymtab_setStatus, State.ite_withSymtab,
         huss, hdis, ↓reduceIte, Bool.false_eq_true]
       rfl)
theorem execClockGettime_withSymtab :
    execClockGettime (s.withSymtab t) = (execClockGettime s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; symtab_free_close
theorem execGetrandom_withSymtab :
    execGetrandom (s.withSymtab t) = (execGetrandom s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; symtab_free_close
theorem execMremap_withSymtab : execMremap (s.withSymtab t) = (execMremap s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execMremap]
  symtab_free_norm
  rcases sanitizeMmapAddr
      (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (pageAlignUp (s.readReg64 Reg.x1).toNat))
      (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 Reg.x2).toNat) with _ | newBase <;>
    symtab_free_close
theorem execMmap_withSymtab : execMmap (s.withSymtab t) = (execMmap s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execMmap]; symtab_free_close
theorem execBrk_withSymtab : execBrk (s.withSymtab t) = (execBrk s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execBrk]; symtab_free_close
theorem execMunmap_withSymtab : execMunmap (s.withSymtab t) = (execMunmap s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; symtab_free_close
theorem execMprotect_withSymtab : execMprotect (s.withSymtab t) = (execMprotect s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; symtab_free_close
theorem execMadvise_withSymtab : execMadvise (s.withSymtab t) = (execMadvise s).withSymtab t := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; symtab_free_close

theorem dispatch_withSymtab (table : List (BitVec 64 × (State → State)))
    (htab : ∀ p ∈ table, p.2 (s.withSymtab t) = (p.2 s).withSymtab t) :
    Syscall.dispatch table (s.withSymtab t) = (Syscall.dispatch table s).withSymtab t := by
  unfold Syscall.dispatch
  rw [State.withSymtab_readReg64]
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · rfl

private theorem standardEntry_withSymtab :
    ∀ p ∈ Syscall.standardTable, p.2 (s.withSymtab t) = (p.2 s).withSymtab t := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact execRead_withSymtab t s
  · exact execWrite_withSymtab t s
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execReadv_symtab_comm t
      (execRead_withSymtab t) s
  · exact LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev.execWritev_symtab_comm t
      (execWrite_withSymtab t) s
  · exact execExit_withSymtab t s
  · exact execExit_withSymtab t s
  · exact execFcntl_withSymtab t s
  · exact execIoctl_withSymtab t s
  · exact execOpenat_withSymtab t s
  · exact execClose_withSymtab t s
  · exact execLseek_withSymtab t s
  · exact execPread64_withSymtab t s
  · exact execFstat_withSymtab t s
  · exact execPpoll_withSymtab t s
  · exact execBrk_withSymtab t s
  · exact execMunmap_withSymtab t s
  · exact execMremap_withSymtab t s
  · exact execMmap_withSymtab t s
  · exact execMprotect_withSymtab t s
  · exact execMadvise_withSymtab t s
  · exact execTkill_withSymtab t s
  · exact execTgkill_withSymtab t s
  · exact execSigaltstack_withSymtab t s
  · exact execRtSigaction_withSymtab t s
  · exact execRtSigprocmask_withSymtab t s
  · exact execClockGettime_withSymtab t s
  · exact execGetrandom_withSymtab t s
  · exact execSetTidAddress_withSymtab t s
  · exact execSchedGetaffinity_withSymtab t s
  · exact execGetpid_withSymtab t s
  · exact execGetpid_withSymtab t s

theorem execSyscall_withSymtab : execSyscall (s.withSymtab t) = (execSyscall s).withSymtab t :=
  dispatch_withSymtab t s Syscall.standardTable (standardEntry_withSymtab t s)

end Syscalls

/-! ## Instructions -/

theorem execSyscall_symtabFree : SymtabFree execSyscall := execSyscall_withSymtab

theorem evalSvc_withSymtab {svc : State → State} (hsvc : SymtabFree svc)
    (t : String → String → Option (BitVec 64)) (s : State) :
    evalSvc svc (s.withSymtab t) = (evalSvc svc s).withSymtab t := by
  simp only [evalSvc, hsvc t s]
  rfl

set_option maxHeartbeats 1000000 in
theorem execInstWithSvc_withSymtab {svc : State → State} (hsvc : SymtabFree svc)
    (inst : Instr) (t : String → String → Option (BitVec 64)) (s : State) :
    execInstWithSvc svc inst (s.withSymtab t) = (execInstWithSvc svc inst s).withSymtab t := by
  have h1a := execAddSubImm_withSymtab t
  have h1b := execAddSubExt_withSymtab t
  have h2 := execAddSubShift_withSymtab t
  have h3 := execAddSubCarry_withSymtab t
  have h4 := execLogicalImm_withSymtab t
  have h5 := execLogicalShift_withSymtab t
  have h6 := execMoveWide_withSymtab t
  have h7 := execBitfield_withSymtab t
  have h8 := execCondSelect_withSymtab t
  have h9 := execCondCompare_withSymtab t
  have h10 := execDataProc1_withSymtab t
  have h11 := execDataProc2_withSymtab t
  have h12 := execDataProc3_withSymtab t
  have h13 := execLdr_withSymtab t
  have h14 := execLdrLit_withSymtab t
  have h15 := execStr_withSymtab t
  have h16 := execLdp_withSymtab t
  have h17 := execStp_withSymtab t
  have h18 := applySimdResult_withSymtab t
  have h18b := applySimdSatResult_withSymtab t
  have h19 := simdLoadRegs_withSymtab t
  have h20 : ∀ s, svc (s.withSymtab t) = (svc s).withSymtab t := hsvc t
  cases inst
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    dsimp only [execInstWithSvc]
    by_cases hbad : (size == 3#2 && !q || !(selem == 2 || selem == 3 || selem == 4)) = true
    · simp only [hbad, ↓reduceIte]; cases s; rfl
    · by_cases h3s : selem ≥ 3 <;> by_cases h4s : selem ≥ 4 <;>
        (simp only [hbad, h3s, h4s, Bool.false_eq_true, ↓reduceIte,
           State.withSymtab_readReg64, State.withSymtab_readVReg128_fn, State.withSymtab_mem,
           State.withSymtab_writeReg64, State.withSymtab_writeVReg128, State.withSymtab_advancePC,
           State.withSymtab_setMem, State.withSymtab_setStatus, State.withSymtab_checkRegSPAligned,
           State.ite_withSymtab]
         try symtab_free_close)
  all_goals (
    dsimp only [execInstWithSvc]
    first
      | with_reducible rfl
      | (symtab_free_norm
         repeat' (split <;> try symtab_free_norm)
         all_goals first
           | with_reducible rfl
           | (apply State.ite_eq_withSymtab_of
              all_goals intro _
              all_goals first
                | with_reducible rfl
                | (repeat' (split <;> try symtab_free_norm)
                   done))))

theorem execInst_withSymtab (inst : Instr) (t : String → String → Option (BitVec 64))
    (s : State) : execInst inst (s.withSymtab t) = (execInst inst s).withSymtab t :=
  execInstWithSvc_withSymtab execSyscall_symtabFree inst t s

theorem execInst_symtabFree (inst : Instr) : SymtabFree (execInst inst) :=
  execInst_withSymtab inst

theorem Program.evalInst_withSymtab {P : Program} (hsvc : SymtabFree P.svc)
    (inst : Instr) (t : String → String → Option (BitVec 64)) (s : State) :
    P.evalInst inst (s.withSymtab t) = (P.evalInst inst s).withSymtab t :=
  execInstWithSvc_withSymtab (evalSvc_withSymtab hsvc) inst t s

/-! ## Step and Multi-Step Runs -/

/-- A `SymtabFree` function keeps `symtab`. -/
theorem SymtabFree.symtab_eq {f : State → State} (hf : SymtabFree f) (s : State) :
    (f s).symtab = s.symtab :=
  (congrArg State.symtab (hf s.symtab s)).trans rfl

/-- The hook at any PC of a program whose hooks are `SymtabFree` is `SymtabFree`. -/
theorem Program.HooksSymtabFree.externAt {P : Program} (hP : P.HooksSymtabFree)
    {pc : BitVec 64} {f : State → State} (h : P.externAt? pc = some f) : SymtabFree f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hP.1 n f hno
    · cases hno
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hP.2.1 n f hno
    · cases hno

/-- One step with `symtab` replaced in both states is a step. -/
theorem Step.symtab_transport {P : Program} (hP : P.HooksSymtabFree)
    (t : String → String → Option (BitVec 64)) {s s' : State} (h : Step P s s') :
    Step P (s.withSymtab t) (s'.withSymtab t) := by
  cases h with
  | exec h_run h_fetch =>
    rw [← Program.evalInst_withSymtab hP.2.2]
    exact Step.exec (s := s.withSymtab t) h_run h_fetch
  | halt_unmapped h_run h_fetch h_ext =>
    exact Step.halt_unmapped (s := s.withSymtab t) h_run h_fetch h_ext
  | @extern f h_run h_ext h_keep _ =>
    have e := hP.externAt h_ext t s
    rw [← e]
    refine Step.extern (s := s.withSymtab t) (f := f) h_run h_ext ?_ ?_
    · rw [e]; exact h_keep
    · exact (congrArg State.symtab e).trans rfl
  | @extern_fault f h_run h_ext h_nkeep =>
    have hf := hP.externAt h_ext
    have hn : ¬ ((s.withSymtab t).mem.KeepsFrozen (f (s.withSymtab t)).mem ∧
        (f (s.withSymtab t)).symtab = (s.withSymtab t).symtab) := by
      rw [hf t s]
      exact fun ⟨hk, _⟩ => h_nkeep ⟨hk, hf.symtab_eq s⟩
    exact Step.extern_fault (s := s.withSymtab t) (f := f) h_run h_ext hn

/-- A run with `symtab` replaced in both end states is a run. -/
theorem Steps.symtab_transport {P : Program} (hP : P.HooksSymtabFree)
    (t : String → String → Option (BitVec 64)) {s s' : State} (h : Steps P s s') :
    Steps P (s.withSymtab t) (s'.withSymtab t) := by
  induction h with
  | refl _ => exact Steps.refl _
  | step h1 _ ih => exact Steps.step (h1.symtab_transport hP t) ih

/-- Proves `SymtabGhost P` when all hooks and `svc` of `P` satisfy `SymtabFree`. -/
theorem symtabGhost_of_hooksSymtabFree {P : Program} (hP : P.HooksSymtabFree) :
    SymtabGhost P :=
  fun t _ _ h => h.symtab_transport hP t

/-! ## Hook Tables and Programs -/

theorem symtabFreeHooks_none : SymtabFreeHooks fun _ => none := by
  intro _ _ h
  cases h

/-- A table given by a list of rows, each `SymtabFree`. -/
theorem symtabFreeHooks_lookup {L : List (String × (State → State))}
    (hL : ∀ p ∈ L, SymtabFree p.2) : SymtabFreeHooks fun n => L.lookup n := by
  intro n f h
  induction L with
  | nil => cases h
  | cons p L ih =>
    obtain ⟨m, g⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · cases h
      exact hL _ List.mem_cons_self
    · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h

theorem Program.HooksSymtabFree.of {P : Program} (hX : SymtabFreeHooks P.externs)
    (hO : SymtabFreeHooks P.overrides) (hS : SymtabFree P.svc := by exact execSyscall_symtabFree) :
    P.HooksSymtabFree :=
  ⟨hX, hO, hS⟩

theorem Program.hooksSymtabFree_ofImage {img : Obj.Image} {X O : String → Option (State → State)}
    (hX : SymtabFreeHooks X) (hO : SymtabFreeHooks O) :
    (Program.ofImage img X O).HooksSymtabFree :=
  ⟨hX, hO, execSyscall_symtabFree⟩

theorem Program.hooksSymtabFree_rebase {P : Program} {b : BitVec 64}
    {X O : String → Option (State → State)} (hX : SymtabFreeHooks X) (hO : SymtabFreeHooks O)
    (hS : SymtabFree P.svc := by exact execSyscall_symtabFree) :
    (P.rebase b X O).HooksSymtabFree :=
  ⟨hX, hO, hS⟩

theorem Rust.panicked_symtabFree : SymtabFree Rust.panicked := fun _ _ => rfl

theorem Rust.symtabFreeHooks_withPanics {X : String → Option (State → State)}
    (hX : SymtabFreeHooks X) : SymtabFreeHooks (Rust.withPanics X) := by
  intro n f h
  unfold Rust.withPanics at h
  split at h
  · cases h
    exact Rust.panicked_symtabFree
  · exact hX n f h

/-! ## Standard `ProofLib` Hooks -/

/-- `retHook f` (run `f`, then return to `lr`) is `SymtabFree` if `f` is. -/
theorem retHook_symtabFree {f : State → State} (hf : SymtabFree f) :
    SymtabFree (ProofLib.retHook f) := by
  intro t s
  simp only [ProofLib.retHook, hf t s]
  rfl

theorem hookNoop_symtabFree : SymtabFree ProofLib.hookNoop :=
  retHook_symtabFree fun _ _ => rfl

theorem hookReturnZero_symtabFree : SymtabFree ProofLib.hookReturnZero :=
  retHook_symtabFree fun _ _ => rfl

theorem hookMemset_symtabFree : SymtabFree ProofLib.hookMemset :=
  retHook_symtabFree fun _ _ => rfl

theorem hookMemcpy_symtabFree : SymtabFree ProofLib.hookMemcpy :=
  retHook_symtabFree fun _ _ => rfl

theorem hookMemmove_symtabFree : SymtabFree ProofLib.hookMemmove :=
  hookMemcpy_symtabFree

end Arm64
