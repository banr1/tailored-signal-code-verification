/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

/-!
# Closure-Free Scalar, Memory, System-Register, and Syscall Evaluator

Defines `fastEvalScalar`, a closure-free evaluator over `FastState` for scalar ALU, branch,
GPR and SIMD load/store, `dc zva`, system-register, and `SVC #0` instructions, and proves
agreement with `Arm64.Program.evalInst` under `Syscall.standard` (`fastEvalScalar_sound`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar

open Arm64 Arm64.Memory
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows

theorem readVReg64_eq {fs : FastState} {s : State} (h : fs.Agrees s) (idx : BitVec 5) :
    fs.readVReg64 idx = s.readVReg64 idx := by
  simp only [FastState.readVReg64, State.readVReg64, FastState.readVReg128_eq h idx]

theorem readVReg32_eq {fs : FastState} {s : State} (h : fs.Agrees s) (idx : BitVec 5) :
    fs.readVReg32 idx = s.readVReg32 idx := by
  simp only [FastState.readVReg32, State.readVReg32, FastState.readVReg128_eq h idx]

theorem writeVReg64_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (idx : BitVec 5) (val : BitVec 64) :
    (fs.writeVReg64 idx val).Agrees (s.writeVReg64 idx val) :=
  FastState.writeVReg128_agrees h idx (val.zeroExtend 128)

theorem writeVReg32_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (idx : BitVec 5) (val : BitVec 32) :
    (fs.writeVReg32 idx val).Agrees (s.writeVReg32 idx val) :=
  FastState.writeVReg128_agrees h idx (val.zeroExtend 128)

def setTpidrEl0 (fs : FastState) (v : BitVec 64) : FastState :=
  withForcedBV v fun tv =>
    fs.withFields fun rg sp pc ps m ivs _ fp bs bk ph ffs orcl oi ex tr st sg =>
      ⟨rg, sp, pc, ps, m, ivs, tv, fp, bs, bk, ph, ffs, orcl, oi, ex, tr, st, sg⟩

theorem setTpidrEl0_agrees {fs : FastState} {s : State} (h : fs.Agrees s) (v : BitVec 64) :
    (setTpidrEl0 fs v).Agrees { s with tpidrEl0 := v } := by
  simp only [setTpidrEl0, withForcedBV_eq, FastState.withFields_eq]
  exact ⟨h.regs, h.sp, h.pc, h.pstate, h.mem, h.heapIvs, rfl, h.fpsr,
    h.brkStart, h.brk, h.physMemAvail, h.fs, h.oracle, h.oracleIdx, h.exclFails,
    h.trace, h.status, h.sigAltStack⟩

@[inline] def fastSpAligned (fs : FastState) : Bool :=
  (fs.sp &&& 0b1111#64) == 0#64

@[inline] def fastCheckRegSPAligned (fs : FastState) (r : Reg) : Bool :=
  match r with
  | .sp => fastSpAligned fs
  | _ => true

@[inline] def fastCheckAddrSPAligned (fs : FastState) (addr : AddrMode) : Bool :=
  fastCheckRegSPAligned fs addr.baseReg

theorem fastSpAligned_eq {fs : FastState} {s : State} (h : fs.Agrees s) :
    fastSpAligned fs = s.spAligned := by
  simp only [fastSpAligned, State.spAligned, h.sp]

theorem fastCheckRegSPAligned_eq {fs : FastState} {s : State} (h : fs.Agrees s) (r : Reg) :
    fastCheckRegSPAligned fs r = checkRegSPAligned s r := by
  cases r <;> simp [fastCheckRegSPAligned, checkRegSPAligned, fastSpAligned_eq h]

theorem fastCheckAddrSPAligned_eq {fs : FastState} {s : State} (h : fs.Agrees s) (addr : AddrMode) :
    fastCheckAddrSPAligned fs addr = checkAddrSPAligned s addr :=
  fastCheckRegSPAligned_eq h addr.baseReg

def fastEvalAddrMode (fs : FastState) (addr : AddrMode) : BitVec 64 × Option (Reg × BitVec 64) :=
  match addr with
  | .Offset base off =>
    withForcedBV (fs.readReg64 base + off) fun ea => (ea, none)
  | .UnscaledOffset base off =>
    withForcedBV (fs.readReg64 base + off) fun ea => (ea, none)
  | .PreIndex base off =>
    withForcedBV (fs.readReg64 base + off) fun ea => (ea, some (base, ea))
  | .PostIndex base off =>
    withForcedBV (fs.readReg64 base) fun baseVal =>
      withForcedBV (baseVal + off) fun wbVal => (baseVal, some (base, wbVal))
  | .RegOffset base index ext amount =>
    withForcedBV (fs.readReg64 base + extendVal .W64 (fs.readReg64 index) ext amount) fun ea =>
      (ea, none)

theorem fastEvalAddrMode_eq {fs : FastState} {s : State} (h : fs.Agrees s) (addr : AddrMode) :
    fastEvalAddrMode fs addr = evalAddrMode s addr := by
  cases addr <;> simp [fastEvalAddrMode, evalAddrMode, FastState.readReg64_eq h]

@[inline] def applyOptPState (fs : FastState) (optPs : Option PState) : FastState :=
  match optPs with
  | some ps => fs.setPState ps
  | none => fs

theorem applyOptPState_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (optPs : Option PState) :
    (applyOptPState fs optPs).Agrees (match optPs with | some ps => s.setPState ps | none => s) := by
  cases optPs with
  | none => exact h
  | some ps => exact FastState.setPState_agrees h ps

@[inline] def applyWriteback (fs : FastState) (wb : Option (Reg × BitVec 64)) : FastState :=
  match wb with
  | some (base, newBase) => fs.writeReg64 base newBase
  | none => fs

theorem applyWriteback_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (wb : Option (Reg × BitVec 64)) :
    (applyWriteback fs wb).Agrees
      (match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s) := by
  cases wb with
  | none => exact h
  | some p => exact FastState.writeReg64_agrees h p.1 p.2

theorem perm_writeSized_eq (m : Memory) (sz : MemWidth) (addr : BitVec 64) (val : BitVec 64)
    (a : BitVec 64) :
    (m.writeSized sz addr val).perm a = m.perm a := by
  cases sz with
  | B8  => exact perm_write8_eq m addr _ a
  | H16 => exact perm_write16_eq m addr _ a
  | W32 => exact perm_write32_eq m addr _ a
  | X64 => exact perm_write64_eq m addr _ a

theorem perm_writeSimdSized_eq (m : Memory) (sz : SimdMemSize) (addr : BitVec 64) (val : BitVec 128)
    (a : BitVec 64) :
    (m.writeSimdSized sz addr val).perm a = m.perm a := by
  cases sz with
  | B8   => exact perm_write8_eq m addr _ a
  | H16  => exact perm_write16_eq m addr _ a
  | S32  => exact perm_write32_eq m addr _ a
  | D64  => exact perm_write64_eq m addr _ a
  | Q128 => exact perm_write128_eq m addr _ a

theorem writeSized_setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (sz : MemWidth) (addr : BitVec 64) (val : BitVec 64) :
    (fs.setMem (fs.mem.writeSized sz addr val)).Agrees
      (s.setMem (s.mem.writeSized sz addr val)) :=
  FastState.setMem_agrees h
    (FastMem.writeSized_agrees h.mem sz addr val)
    (HeapIntervalsAgree.of_perm_eq h.heapIvs (perm_writeSized_eq s.mem sz addr val))

theorem writeSized2_setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (sz : MemWidth) (a1 : BitVec 64) (v1 : BitVec 64) (a2 : BitVec 64) (v2 : BitVec 64) :
    (fs.setMem ((fs.mem.writeSized sz a1 v1).writeSized sz a2 v2)).Agrees
      (s.setMem ((s.mem.writeSized sz a1 v1).writeSized sz a2 v2)) :=
  FastState.setMem_agrees h
    (FastMem.writeSized_agrees (FastMem.writeSized_agrees h.mem sz a1 v1) sz a2 v2)
    (HeapIntervalsAgree.of_perm_eq
      (HeapIntervalsAgree.of_perm_eq h.heapIvs (perm_writeSized_eq s.mem sz a1 v1))
      (perm_writeSized_eq _ sz a2 v2))

theorem writeSimdSized_setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (sz : SimdMemSize) (addr : BitVec 64) (val : BitVec 128) :
    (fs.setMem (fs.mem.writeSimdSized sz addr val)).Agrees
      (s.setMem (s.mem.writeSimdSized sz addr val)) :=
  FastState.setMem_agrees h
    (FastMem.writeSimdSized_agrees h.mem sz addr val)
    (HeapIntervalsAgree.of_perm_eq h.heapIvs (perm_writeSimdSized_eq s.mem sz addr val))

theorem writeSimdSized2_setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (sz : SimdMemSize) (a1 : BitVec 64) (v1 : BitVec 128) (a2 : BitVec 64) (v2 : BitVec 128) :
    (fs.setMem ((fs.mem.writeSimdSized sz a1 v1).writeSimdSized sz a2 v2)).Agrees
      (s.setMem ((s.mem.writeSimdSized sz a1 v1).writeSimdSized sz a2 v2)) :=
  FastState.setMem_agrees h
    (FastMem.writeSimdSized_agrees (FastMem.writeSimdSized_agrees h.mem sz a1 v1) sz a2 v2)
    (HeapIntervalsAgree.of_perm_eq
      (HeapIntervalsAgree.of_perm_eq h.heapIvs (perm_writeSimdSized_eq s.mem sz a1 v1))
      (perm_writeSimdSized_eq _ sz a2 v2))

theorem writeSimdSized4_setMem_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (sz : SimdMemSize) (a1 : BitVec 64) (v1 : BitVec 128) (a2 : BitVec 64) (v2 : BitVec 128)
    (a3 : BitVec 64) (v3 : BitVec 128) (a4 : BitVec 64) (v4 : BitVec 128) :
    (fs.setMem ((((fs.mem.writeSimdSized sz a1 v1).writeSimdSized sz a2 v2).writeSimdSized
      sz a3 v3).writeSimdSized sz a4 v4)).Agrees
      (s.setMem ((((s.mem.writeSimdSized sz a1 v1).writeSimdSized sz a2 v2).writeSimdSized
        sz a3 v3).writeSimdSized sz a4 v4)) :=
  FastState.setMem_agrees h
    (FastMem.writeSimdSized_agrees (FastMem.writeSimdSized_agrees
      (FastMem.writeSimdSized_agrees (FastMem.writeSimdSized_agrees h.mem sz a1 v1) sz a2 v2) sz a3 v3) sz a4 v4)
    (HeapIntervalsAgree.of_perm_eq (HeapIntervalsAgree.of_perm_eq (HeapIntervalsAgree.of_perm_eq
      (HeapIntervalsAgree.of_perm_eq h.heapIvs (perm_writeSimdSized_eq s.mem sz a1 v1))
      (perm_writeSimdSized_eq _ sz a2 v2)) (perm_writeSimdSized_eq _ sz a3 v3)) (perm_writeSimdSized_eq _ sz a4 v4))

def fastExecAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg)
    (imm12 : BitVec 12) (shift12 : Bool) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let imm : BitVec 64 := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
  let (res, optPs) := evalAddSub w op x imm none
  (applyOptPState (fs.writeReg w rd res) optPs).advancePC

theorem fastExecAddSubImm_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool) :
    (fastExecAddSubImm w op rd rn imm12 shift12 fs).Agrees
      (execAddSubImm w op rd rn imm12 shift12 s) := by
  simp only [fastExecAddSubImm, execAddSubImm, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (applyOptPState_agrees (FastState.writeReg_agrees h w rd _) _)

def fastExecAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (ext : ExtendType) (amount : Nat) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let y := extendVal w (fs.readReg64 rm) ext amount
  let (res, optPs) := evalAddSub w op x y none
  (applyOptPState (fs.writeReg w rd res) optPs).advancePC

theorem fastExecAddSubExt_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat) :
    (fastExecAddSubExt w op rd rn rm ext amount fs).Agrees
      (execAddSubExt w op rd rn rm ext amount s) := by
  simp only [fastExecAddSubExt, execAddSubExt, FastState.readReg_eq h, FastState.readReg64_eq h]
  exact FastState.advancePC_agrees (applyOptPState_agrees (FastState.writeReg_agrees h w rd _) _)

def fastExecAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (shift : ShiftType) (amount : Nat) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let y := shiftVal w (fs.readReg w rm) shift amount
  let (res, optPs) := evalAddSub w op x y none
  (applyOptPState (fs.writeReg w rd res) optPs).advancePC

theorem fastExecAddSubShift_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) :
    (fastExecAddSubShift w op rd rn rm shift amount fs).Agrees
      (execAddSubShift w op rd rn rm shift amount s) := by
  simp only [fastExecAddSubShift, execAddSubShift, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (applyOptPState_agrees (FastState.writeReg_agrees h w rd _) _)

def fastExecLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg)
    (mask : BitVec 64) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let (res, optPs) := evalLogical w op x mask fs.pstate
  (applyOptPState (fs.writeReg w rd res) optPs).advancePC

theorem fastExecLogicalImm_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    (fastExecLogicalImm w op rd rn mask fs).Agrees
      (execLogicalImm w op rd rn mask s) := by
  simp only [fastExecLogicalImm, execLogicalImm, FastState.readReg_eq h, h.pstate]
  exact FastState.advancePC_agrees (applyOptPState_agrees (FastState.writeReg_agrees h w rd _) _)

def fastExecLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg)
    (shift : ShiftType) (amount : Nat) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let y := shiftVal w (fs.readReg w rm) shift amount
  let (res, optPs) := evalLogical w op x y fs.pstate
  (applyOptPState (fs.writeReg w rd res) optPs).advancePC

theorem fastExecLogicalShift_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat) :
    (fastExecLogicalShift w op rd rn rm shift amount fs).Agrees
      (execLogicalShift w op rd rn rm shift amount s) := by
  simp only [fastExecLogicalShift, execLogicalShift, FastState.readReg_eq h, h.pstate]
  exact FastState.advancePC_agrees (applyOptPState_agrees (FastState.writeReg_agrees h w rd _) _)

def fastExecMoveWide (w : Width) (op : MoveWideOp) (rd : Reg)
    (imm16 : BitVec 16) (hw : Nat) (fs : FastState) : FastState :=
  let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< hw
  let res : BitVec 64 :=
    match op with
    | .MOVZ => shifted
    | .MOVN => ~~~shifted
    | .MOVK =>
      let old := fs.readReg w rd
      let clearMask := ~~~(65535#64 <<< hw)
      (old &&& clearMask) ||| shifted
  (fs.writeReg w rd res).advancePC

theorem fastExecMoveWide_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat) :
    (fastExecMoveWide w op rd imm16 hw fs).Agrees
      (execMoveWide w op rd imm16 hw s) := by
  simp only [fastExecMoveWide, execMoveWide, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecBitfield (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) (fs : FastState) : FastState :=
  let dst := fs.readReg w rd
  let src := fs.readReg w rn
  let res := evalBitfield w op dst src immr imms
  (fs.writeReg w rd res).advancePC

theorem fastExecBitfield_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) :
    (fastExecBitfield w op rd rn immr imms fs).Agrees
      (execBitfield w op rd rn immr imms s) := by
  simp only [fastExecBitfield, execBitfield, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecExtr (w : Width) (rd rn rm : Reg) (lsb : Nat) (fs : FastState) : FastState :=
  let res : BitVec 64 :=
    match w with
    | .W32 =>
      let n32 := fs.readReg32 rn
      let m32 := fs.readReg32 rm
      let pair64 : BitVec 64 := n32 ++ m32
      ((pair64 >>> (lsb % 32)).truncate 32).zeroExtend 64
    | .W64 =>
      let n64 := fs.readReg64 rn
      let m64 := fs.readReg64 rm
      let pair128 : BitVec 128 := n64 ++ m64
      (pair128 >>> (lsb % 64)).truncate 64
  (fs.writeReg w rd res).advancePC

theorem fastExecExtr_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) (w : Width) (rd rn rm : Reg) (lsb : Nat) :
    (fastExecExtr w rd rn rm lsb fs).Agrees
      (execInstWithSvc svc (.extr w rd rn rm lsb) s) := by
  simp only [fastExecExtr, execInstWithSvc, FastState.readReg32_eq h, FastState.readReg64_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecCondSelect (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) (fs : FastState) : FastState :=
  let holds := ConditionHolds cond fs.pstate
  let res : BitVec 64 :=
    if holds then
      fs.readReg w rn
    else
      let mVal := fs.readReg w rm
      match op with
      | .CSEL  => mVal
      | .CSINC => mVal + 1#64
      | .CSINV => ~~~mVal
      | .CSNEG => 0#64 - mVal
  (fs.writeReg w rd res).advancePC

theorem fastExecCondSelect_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode) :
    (fastExecCondSelect w op rd rn rm cond fs).Agrees
      (execCondSelect w op rd rn rm cond s) := by
  simp only [fastExecCondSelect, execCondSelect, FastState.readReg_eq h, h.pstate]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecCondCompare (w : Width) (isSub : Bool) (isImm : Bool)
    (rn : Reg) (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode)
    (fs : FastState) : FastState :=
  if ConditionHolds cond fs.pstate then
    let x := fs.readReg w rn
    let y := if isImm then rhs else fs.readReg w rm
    let op : AddSubOp := if isSub then .SUBS else .ADDS
    let (_, optPs) := evalAddSub w op x y none
    (applyOptPState fs optPs).advancePC
  else
    (fs.setPState (PState.ofBits4 nzcv)).advancePC

theorem fastExecCondCompare_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64) (rm : Reg)
    (nzcv : BitVec 4) (cond : CondCode) :
    (fastExecCondCompare w isSub isImm rn rhs rm nzcv cond fs).Agrees
      (execCondCompare w isSub isImm rn rhs rm nzcv cond s) := by
  simp only [fastExecCondCompare, execCondCompare, FastState.readReg_eq h, h.pstate]
  split
  · exact FastState.advancePC_agrees (applyOptPState_agrees h _)
  · exact FastState.advancePC_agrees (FastState.setPState_agrees h _)

private theorem forIn_list_yield_scalar {α β : Type} (step : α → β → β) :
    ∀ (xs : List α) (init : β),
      (forIn (m := Id) xs init (fun i acc => pure (ForInStep.yield (step i acc)))).run =
        xs.foldl (fun acc i => step i acc) init
  | [], init => by simp only [List.forIn_nil, pure, Id.run, List.foldl_nil]
  | x :: xs, init => by
    simp only [List.forIn_cons, bind, pure, List.foldl_cons]
    exact forIn_list_yield_scalar step xs (step x init)

def fastReverseBits {n : Nat} (bv : BitVec n) : BitVec n :=
  (List.range' 0 n 1).foldl (fun acc i =>
    if bv.getLsbD i then acc ||| (BitVec.ofNat n 1 <<< (n - 1 - i)) else acc) 0

private theorem fastReverseBits_eq {n : Nat} (bv : BitVec n) :
    fastReverseBits bv = reverseBits bv := by
  unfold fastReverseBits reverseBits
  dsimp only [bind, pure]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← forIn_list_yield_scalar (fun i acc =>
    if bv.getLsbD i then acc ||| (BitVec.ofNat n 1 <<< (n - 1 - i)) else acc) (List.range' 0 n 1) 0]
  congr 1
  apply congrArg (fun f => forIn (m := Id) (List.range' 0 n 1) (0 : BitVec n) f)
  funext i acc
  cases bv.getLsbD i <;> rfl

def fastExecDataProc1 (w : Width) (op : DataProc1Op) (rd rn : Reg) (fs : FastState) : FastState :=
  let v := fs.readReg w rn
  let res : BitVec 64 :=
    match w, op with
    | .W32, .RBIT  => (fastReverseBits (v.truncate 32)).zeroExtend 64
    | .W64, .RBIT  => fastReverseBits v
    | .W32, .REV16 => ((rev16_64 v).truncate 32).zeroExtend 64
    | .W64, .REV16 => rev16_64 v
    | .W32, .REV32 => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV32 => rev32_64 v
    | .W32, .REV   => ((rev32_64 v).truncate 32).zeroExtend 64
    | .W64, .REV   => rev64 v
    | .W32, .CLZ   => BitVec.ofNat 64 (countLeadingZeros (v.truncate 32))
    | .W64, .CLZ   => BitVec.ofNat 64 (countLeadingZeros v)
    | .W32, .CLS   => BitVec.ofNat 64 (countLeadingSigns (v.truncate 32))
    | .W64, .CLS   => BitVec.ofNat 64 (countLeadingSigns v)
  (fs.writeReg w rd res).advancePC

theorem fastExecDataProc1_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : DataProc1Op) (rd rn : Reg) :
    (fastExecDataProc1 w op rd rn fs).Agrees (execDataProc1 w op rd rn s) := by
  simp only [fastExecDataProc1, execDataProc1, fastReverseBits_eq, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecDataProc2 (w : Width) (op : DataProc2Op) (rd rn rm : Reg) (fs : FastState) : FastState :=
  let x := fs.readReg w rn
  let y := fs.readReg w rm
  let res : BitVec 64 :=
    match w, op with
    | .W32, .UDIV =>
      let x32 := x.truncate 32
      let y32 := y.truncate 32
      (if y32 == 0#32 then 0#32 else x32 / y32).zeroExtend 64
    | .W64, .UDIV =>
      if y == 0#64 then 0#64 else x / y
    | .W32, .SDIV =>
      let x32 := x.truncate 32
      let y32 := y.truncate 32
      (if y32 == 0#32 then 0#32 else BitVec.sdiv x32 y32).zeroExtend 64
    | .W64, .SDIV =>
      if y == 0#64 then 0#64 else BitVec.sdiv x y
    | .W32, .LSLV => (shift32 (x.truncate 32) .LSL (y.truncate 32).toNat).zeroExtend 64
    | .W64, .LSLV => shift64 x .LSL y.toNat
    | .W32, .LSRV => (shift32 (x.truncate 32) .LSR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .LSRV => shift64 x .LSR y.toNat
    | .W32, .ASRV => (shift32 (x.truncate 32) .ASR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .ASRV => shift64 x .ASR y.toNat
    | .W32, .RORV => (shift32 (x.truncate 32) .ROR (y.truncate 32).toNat).zeroExtend 64
    | .W64, .RORV => shift64 x .ROR y.toNat
  (fs.writeReg w rd res).advancePC

theorem fastExecDataProc2_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : DataProc2Op) (rd rn rm : Reg) :
    (fastExecDataProc2 w op rd rn rm fs).Agrees (execDataProc2 w op rd rn rm s) := by
  simp only [fastExecDataProc2, execDataProc2, FastState.readReg_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecDataProc3 (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) (fs : FastState) : FastState :=
  let res : BitVec 64 :=
    match op with
    | .MADD =>
      match w with
      | .W32 => ((fs.readReg32 ra) + (fs.readReg32 rn) * (fs.readReg32 rm)).zeroExtend 64
      | .W64 => (fs.readReg64 ra) + (fs.readReg64 rn) * (fs.readReg64 rm)
    | .MSUB =>
      match w with
      | .W32 => ((fs.readReg32 ra) - (fs.readReg32 rn) * (fs.readReg32 rm)).zeroExtend 64
      | .W64 => (fs.readReg64 ra) - (fs.readReg64 rn) * (fs.readReg64 rm)
    | .SMADDL =>
      let n64 := (fs.readReg32 rn).signExtend 64
      let m64 := (fs.readReg32 rm).signExtend 64
      (fs.readReg64 ra) + n64 * m64
    | .SMSUBL =>
      let n64 := (fs.readReg32 rn).signExtend 64
      let m64 := (fs.readReg32 rm).signExtend 64
      (fs.readReg64 ra) - n64 * m64
    | .UMADDL =>
      let n64 := (fs.readReg32 rn).zeroExtend 64
      let m64 := (fs.readReg32 rm).zeroExtend 64
      (fs.readReg64 ra) + n64 * m64
    | .UMSUBL =>
      let n64 := (fs.readReg32 rn).zeroExtend 64
      let m64 := (fs.readReg32 rm).zeroExtend 64
      (fs.readReg64 ra) - n64 * m64
    | .SMULH =>
      let n128 := (fs.readReg64 rn).signExtend 128
      let m128 := (fs.readReg64 rm).signExtend 128
      ((n128 * m128) >>> 64).truncate 64
    | .UMULH =>
      let n128 := (fs.readReg64 rn).zeroExtend 128
      let m128 := (fs.readReg64 rm).zeroExtend 128
      ((n128 * m128) >>> 64).truncate 64
  (fs.writeReg w rd res).advancePC

theorem fastExecDataProc3_agrees {fs : FastState} {s : State} (h : fs.Agrees s)
    (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg) :
    (fastExecDataProc3 w op rd rn rm ra fs).Agrees (execDataProc3 w op rd rn rm ra s) := by
  simp only [fastExecDataProc3, execDataProc3, FastState.readReg32_eq h, FastState.readReg64_eq h]
  exact FastState.advancePC_agrees (FastState.writeReg_agrees h w rd _)

def fastExecLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then
    none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    if !fs.mem.canRead ea size.bytes then
      none
    else
      let val := fs.mem.readSized size signed ea
      let fs1 := applyWriteback fs wb
      some (fs1.writeReg w rt val).advancePC

theorem fastExecLdr_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    {w : Width} {size : MemWidth} {signed : Bool} {rt : Reg} {addr : AddrMode}
    (heval : fastExecLdr w size signed rt addr fs = some fs') :
    fs'.Agrees (execLdr w size signed rt addr s) := by
  unfold fastExecLdr at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  unfold execLdr
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canRead_eq h.mem] at heval
    cases hcr : s.mem.canRead (evalAddrMode s addr).1 size.bytes
    · simp [hcr] at heval
    · simp only [hcr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval
      rw [FastMem.readSized_eq h.mem]
      exact FastState.advancePC_agrees
        (FastState.writeReg_agrees (applyWriteback_agrees h _) w rt _)

def fastExecStr (size : MemWidth) (rt : Reg) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then
    none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    if !fs.mem.canWrite ea size.bytes then
      none
    else
      let val := fs.readReg64 rt
      let fs1 := fs.setMem (fs.mem.writeSized size ea val)
      let fs2 := applyWriteback fs1 wb
      some fs2.advancePC

theorem fastExecStr_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    {size : MemWidth} {rt : Reg} {addr : AddrMode}
    (heval : fastExecStr size rt addr fs = some fs') :
    fs'.Agrees (execStr size rt addr s) := by
  unfold fastExecStr at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  unfold execStr
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canWrite_eq h.mem] at heval
    cases hcw : s.mem.canWrite (evalAddrMode s addr).1 size.bytes
    · simp [hcw] at heval
    · simp only [hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval
      rw [FastState.readReg64_eq h]
      exact FastState.advancePC_agrees
        (applyWriteback_agrees (writeSized_setMem_agrees h size _ _) _)

def fastExecLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then
    none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    let stepBytes : BitVec 64 := if signed then 4#64 else match w with | .W32 => 4#64 | .W64 => 8#64
    let sz : MemWidth := if signed then .W32 else match w with | .W32 => .W32 | .W64 => .X64
    if !(fs.mem.canRead ea sz.bytes && fs.mem.canRead (ea + stepBytes) sz.bytes) then
      none
    else
      let v1 := fs.mem.readSized sz signed ea
      let v2 := fs.mem.readSized sz signed (ea + stepBytes)
      let outW : Width := if signed then .W64 else w
      let fs1 := applyWriteback fs wb
      let fs2 := fs1.writeReg outW rt1 v1
      let fs3 := fs2.writeReg outW rt2 v2
      some fs3.advancePC

theorem fastExecLdp_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    {w : Width} {signed : Bool} {rt1 rt2 : Reg} {addr : AddrMode}
    (heval : fastExecLdp w signed rt1 rt2 addr fs = some fs') :
    fs'.Agrees (execLdp w signed rt1 rt2 addr s) := by
  unfold fastExecLdp at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  unfold execLdp
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canRead_eq h.mem, FastMem.canRead_eq h.mem] at heval
    cases signed <;> cases w <;> simp only [Bool.false_eq_true, ↓reduceIte] at heval ⊢
    all_goals
      split at heval
      · nomatch heval
      · rename_i hok; simp only [hok]
        injection heval with heval; subst heval
        rw [FastMem.readSized_eq h.mem, FastMem.readSized_eq h.mem]
        exact FastState.advancePC_agrees
          (FastState.writeReg_agrees
            (FastState.writeReg_agrees (applyWriteback_agrees h _) _ rt1 _) _ rt2 _)

def fastExecStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then
    none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    let stepBytes : BitVec 64 := match w with | .W32 => 4#64 | .W64 => 8#64
    let sz : MemWidth := match w with | .W32 => .W32 | .W64 => .X64
    if !(fs.mem.canWrite ea sz.bytes && fs.mem.canWrite (ea + stepBytes) sz.bytes) then
      none
    else
      let v1 := fs.readReg64 rt1
      let v2 := fs.readReg64 rt2
      let m1 := fs.mem.writeSized sz ea v1
      let m2 := m1.writeSized sz (ea + stepBytes) v2
      let fs1 := fs.setMem m2
      let fs2 := applyWriteback fs1 wb
      some fs2.advancePC

theorem fastExecStp_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    {w : Width} {rt1 rt2 : Reg} {addr : AddrMode}
    (heval : fastExecStp w rt1 rt2 addr fs = some fs') :
    fs'.Agrees (execStp w rt1 rt2 addr s) := by
  unfold fastExecStp at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  unfold execStp
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canWrite_eq h.mem, FastMem.canWrite_eq h.mem] at heval
    cases w <;> dsimp only at heval ⊢
    all_goals
      split at heval
      · nomatch heval
      · rename_i hok; simp only [hok]
        injection heval with heval; subst heval
        rw [FastState.readReg64_eq h, FastState.readReg64_eq h]
        exact FastState.advancePC_agrees
          (applyWriteback_agrees (writeSized2_setMem_agrees h _ _ _ _ _) _)

def fastExecLdarStlr (sz : MemWidth) (isLoad : Bool) (rn rt : Reg)
    (fs : FastState) : Option FastState :=
  if !fastCheckRegSPAligned fs rn then
    none
  else
    let ea := fs.readReg64 rn
    if !sz.isAligned ea then
      none
    else if isLoad then
      if !fs.mem.canRead ea sz.bytes then
        none
      else
        let w : Width := match sz with | .X64 => .W64 | _ => .W32
        let val := fs.mem.readSized sz false ea
        some (fs.writeReg w rt val).advancePC
    else
      if !fs.mem.canWrite ea sz.bytes then
        none
      else
        let val := fs.readReg64 rt
        some (fs.setMem (fs.mem.writeSized sz ea val)).advancePC

theorem fastExecLdarStlr_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : MemWidth} {isLoad : Bool} {rn rt : Reg}
    (heval : fastExecLdarStlr sz isLoad rn rt fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.ldarStlr sz isLoad rn rt) s) := by
  unfold fastExecLdarStlr at heval
  rw [fastCheckRegSPAligned_eq h, FastState.readReg64_eq h rn] at heval
  simp only [execInstWithSvc]
  cases hsp : checkRegSPAligned s rn
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    cases hal : sz.isAligned (s.readReg64 rn)
    · simp [hal] at heval
    · simp only [hal, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      cases isLoad
      · simp only [Bool.false_eq_true, ↓reduceIte] at heval ⊢
        rw [FastMem.canWrite_eq h.mem] at heval
        cases hcw : s.mem.canWrite (s.readReg64 rn) sz.bytes
        · simp [hcw] at heval
        · simp only [hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
          subst heval
          rw [FastState.readReg64_eq h rt]
          exact FastState.advancePC_agrees (writeSized_setMem_agrees h sz _ _)
      · simp only [↓reduceIte] at heval ⊢
        rw [FastMem.canRead_eq h.mem] at heval
        cases hcr : s.mem.canRead (s.readReg64 rn) sz.bytes
        · simp [hcr] at heval
        · simp only [hcr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
          subst heval
          rw [FastMem.readSized_eq h.mem]
          exact FastState.advancePC_agrees (FastState.writeReg_agrees h _ rt _)

def fastExecLdrSimd (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    if !fs.mem.canRead ea sz.bytes then none
    else
      some ((applyWriteback fs wb).writeVReg128 vt (fs.mem.readSimdSized sz ea)).advancePC

theorem fastExecLdrSimd_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : SimdMemSize} {vt : BitVec 5} {addr : AddrMode}
    (heval : fastExecLdrSimd sz vt addr fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.ldrSimd sz vt addr) s) := by
  unfold fastExecLdrSimd at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  simp only [execInstWithSvc]
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canRead_eq h.mem] at heval
    cases hcr : s.mem.canRead (evalAddrMode s addr).1 sz.bytes
    · simp [hcr] at heval
    · simp only [hcr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval; rw [FastMem.readSimdSized_eq h.mem]
      exact FastState.advancePC_agrees (FastState.writeVReg128_agrees (applyWriteback_agrees h _) vt _)

def fastExecStrSimd (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    if !fs.mem.canWrite ea sz.bytes then none
    else
      some (applyWriteback (fs.setMem (fs.mem.writeSimdSized sz ea (fs.readVReg128 vt))) wb).advancePC

theorem fastExecStrSimd_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : SimdMemSize} {vt : BitVec 5} {addr : AddrMode}
    (heval : fastExecStrSimd sz vt addr fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.strSimd sz vt addr) s) := by
  unfold fastExecStrSimd at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  simp only [execInstWithSvc]
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canWrite_eq h.mem] at heval
    cases hcw : s.mem.canWrite (evalAddrMode s addr).1 sz.bytes
    · simp [hcw] at heval
    · simp only [hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval; rw [FastState.readVReg128_eq h vt]
      exact FastState.advancePC_agrees (applyWriteback_agrees (writeSimdSized_setMem_agrees h sz _ _) _)

def fastExecLdpSimd (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    let stepBytes : BitVec 64 :=
      match sz with | .B8 => 1#64 | .H16 => 2#64 | .S32 => 4#64 | .D64 => 8#64 | .Q128 => 16#64
    if !(fs.mem.canRead ea sz.bytes && fs.mem.canRead (ea + stepBytes) sz.bytes) then none
    else
      let v1 := fs.mem.readSimdSized sz ea
      let v2 := fs.mem.readSimdSized sz (ea + stepBytes)
      some (((applyWriteback fs wb).writeVReg128 vt1 v1).writeVReg128 vt2 v2).advancePC

theorem fastExecLdpSimd_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : SimdMemSize} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    (heval : fastExecLdpSimd sz vt1 vt2 addr fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.ldpSimd sz vt1 vt2 addr) s) := by
  unfold fastExecLdpSimd at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  simp only [execInstWithSvc]
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canRead_eq h.mem, FastMem.canRead_eq h.mem] at heval
    cases sz <;> dsimp only at heval ⊢
    all_goals
      split at heval
      · nomatch heval
      · rename_i hok; simp only [hok]
        injection heval with heval; subst heval
        rw [FastMem.readSimdSized_eq h.mem, FastMem.readSimdSized_eq h.mem]
        exact FastState.advancePC_agrees
          (FastState.writeVReg128_agrees
            (FastState.writeVReg128_agrees (applyWriteback_agrees h _) vt1 _) vt2 _)

def fastExecStpSimd (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode)
    (fs : FastState) : Option FastState :=
  if !fastCheckAddrSPAligned fs addr then none
  else
    let (ea, wb) := fastEvalAddrMode fs addr
    let stepBytes : BitVec 64 :=
      match sz with | .B8 => 1#64 | .H16 => 2#64 | .S32 => 4#64 | .D64 => 8#64 | .Q128 => 16#64
    if !(fs.mem.canWrite ea sz.bytes && fs.mem.canWrite (ea + stepBytes) sz.bytes) then none
    else
      let m2 := (fs.mem.writeSimdSized sz ea (fs.readVReg128 vt1)).writeSimdSized
        sz (ea + stepBytes) (fs.readVReg128 vt2)
      some (applyWriteback (fs.setMem m2) wb).advancePC

theorem fastExecStpSimd_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sz : SimdMemSize} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    (heval : fastExecStpSimd sz vt1 vt2 addr fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.stpSimd sz vt1 vt2 addr) s) := by
  unfold fastExecStpSimd at heval
  rw [fastCheckAddrSPAligned_eq h, fastEvalAddrMode_eq h] at heval
  simp only [execInstWithSvc]
  cases hsp : checkAddrSPAligned s addr
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canWrite_eq h.mem, FastMem.canWrite_eq h.mem] at heval
    cases sz <;> dsimp only at heval ⊢
    all_goals
      split at heval
      · nomatch heval
      · rename_i hok; simp only [hok]
        injection heval with heval; subst heval
        rw [FastState.readVReg128_eq h vt1, FastState.readVReg128_eq h vt2]
        exact FastState.advancePC_agrees
          (applyWriteback_agrees (writeSimdSized2_setMem_agrees h _ _ _ _ _) _)

/-- Evaluates `MRS`/`MSR` on `TPIDR_EL0` (`0x5e82`), `NZCV` (`0x5a10`), `FPCR` (`0x5a20`),
`FPSR` (`0x5a21`), and `DCZID_EL0` (`0x5807`). -/
def fastExecSysReg (isRead : Bool) (sysreg : BitVec 15) (rt : Reg)
    (fs : FastState) : Option FastState :=
  if sysreg == 0x5e82#15 then
    if isRead then
      some (fs.writeReg64 rt fs.tpidrEl0).advancePC
    else
      some (setTpidrEl0 fs (fs.readReg64 rt)).advancePC
  else if sysreg == 0x5a10#15 then
    if isRead then
      let ps := fs.pstate
      let b (x : Bool) (i : Nat) : BitVec 64 := if x then 1#64 <<< i else 0#64
      some (fs.writeReg64 rt (b ps.n 31 ||| b ps.z 30 ||| b ps.c 29 ||| b ps.v 28)).advancePC
    else
      some (fs.setPState (PState.ofBits4 ((fs.readReg64 rt).extractLsb' 28 4))).advancePC
  else if sysreg == 0x5a20#15 then
    if isRead then
      some (fs.writeReg64 rt 0#64).advancePC
    else if fs.readReg64 rt == 0#64 then
      some fs.advancePC
    else
      none
  else if sysreg == 0x5a21#15 then
    if isRead then
      some (fs.writeReg64 rt (fs.fpsr.zeroExtend 64)).advancePC
    else
      some (fs.setFpsr ((fs.readReg64 rt).truncate 32 &&& fpsrMask)).advancePC
  else if sysreg == 0x5807#15 then
    if isRead then
      some (fs.writeReg64 rt 4#64).advancePC
    else
      none
  else
    none

theorem fastExecSysReg_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {isRead : Bool} {sysreg : BitVec 15} {rt : Reg}
    (heval : fastExecSysReg isRead sysreg rt fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.sysReg isRead sysreg rt) s) := by
  unfold fastExecSysReg at heval
  simp only [execInstWithSvc]
  by_cases h1 : (sysreg == 0x5e82#15) = true
  · simp only [h1, ↓reduceIte] at heval ⊢
    cases isRead
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval; rw [FastState.readReg64_eq h]
      exact FastState.advancePC_agrees (setTpidrEl0_agrees h _)
    · simp only [↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval; rw [h.tpidrEl0]
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees h rt _)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases h2 : (sysreg == 0x5a10#15) = true
    · simp only [h2, ↓reduceIte] at heval ⊢
      cases isRead
      · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
        subst heval; rw [FastState.readReg64_eq h]
        exact FastState.advancePC_agrees (FastState.setPState_agrees h _)
      · simp only [↓reduceIte, Option.some.injEq] at heval ⊢
        subst heval; rw [h.pstate]
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees h rt _)
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases h3 : (sysreg == 0x5a20#15) = true
      · simp only [h3, ↓reduceIte] at heval ⊢
        cases isRead
        · simp only [Bool.false_eq_true, ↓reduceIte] at heval ⊢
          rw [FastState.readReg64_eq h] at heval
          cases hz : s.readReg64 rt == 0#64
          · simp [hz] at heval
          · simp only [hz, ↓reduceIte, Option.some.injEq] at heval ⊢
            subst heval; exact FastState.advancePC_agrees h
        · simp only [↓reduceIte, Option.some.injEq] at heval ⊢
          subst heval; exact FastState.advancePC_agrees (FastState.writeReg64_agrees h rt _)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases h4 : (sysreg == 0x5a21#15) = true
        · simp only [h4, ↓reduceIte] at heval ⊢
          cases isRead
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
            subst heval; rw [FastState.readReg64_eq h]
            exact FastState.advancePC_agrees (FastState.setFpsr_agrees h _)
          · simp only [↓reduceIte, Option.some.injEq] at heval ⊢
            subst heval; rw [h.fpsr]
            exact FastState.advancePC_agrees (FastState.writeReg64_agrees h rt _)
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases h5 : (sysreg == 0x5807#15) = true
          · simp only [h5, ↓reduceIte] at heval ⊢
            cases isRead
            · simp at heval
            · simp only [↓reduceIte, Option.some.injEq] at heval ⊢
              subst heval; exact FastState.advancePC_agrees (FastState.writeReg64_agrees h rt _)
          · simp [h5] at heval

def fastExecDcZva (rn : Reg) (fs : FastState) : Option FastState :=
  if !fastCheckRegSPAligned fs rn then none
  else
    let base := fs.readReg64 rn &&& ~~~63#64
    if !fs.mem.canWrite base 64 then none
    else
      let m4 := (((fs.mem.writeSimdSized .Q128 base 0#128).writeSimdSized
        .Q128 (base + 16#64) 0#128).writeSimdSized
        .Q128 (base + 32#64) 0#128).writeSimdSized
        .Q128 (base + 48#64) 0#128
      some (fs.setMem m4).advancePC

theorem fastExecDcZva_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {rn : Reg}
    (heval : fastExecDcZva rn fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.dcZva rn) s) := by
  unfold fastExecDcZva at heval
  rw [fastCheckRegSPAligned_eq h, FastState.readReg64_eq h] at heval
  simp only [execInstWithSvc]
  cases hsp : checkRegSPAligned s rn
  · simp [hsp] at heval
  · simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    rw [FastMem.canWrite_eq h.mem] at heval
    let base := s.readReg64 rn &&& ~~~63#64
    change (if !s.mem.canWrite base 64 then none else _) = some fs' at heval
    cases hcw : s.mem.canWrite base 64
    · simp [hcw] at heval
    · simp only [hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢
      subst heval
      simp only [simdStoreRegs, SimdMemSize.bytes, BitVec.add_assoc]
      exact FastState.advancePC_agrees (writeSimdSized4_setMem_agrees h .Q128 base 0#128
        (base + 16#64) 0#128 (base + 32#64) 0#128 (base + 48#64) 0#128)

/-- Evaluates halt instructions (`BRK #1` exits with status `101`; others halt) and `SVC #0`
for `exit_group` (`x8 = 94`) and `set_tid_address` (`x8 = 96`). -/
def fastExecSystem (isHalt : Bool) (imm : BitVec 16) (fs : FastState) : Option FastState :=
  if isHalt then
    if imm == 1#16 then
      some (fs.setStatus (.Exited 101#64))
    else
      some (fs.setStatus .Halted)
  else if imm == 0#16 then
    let nr := fs.readReg64 Reg.x8
    if nr == 94#64 then
      some (fs.setStatus (.Exited (fs.readReg64 Reg.x0)))
    else if nr == 96#64 then
      some (fs.writeReg64 Reg.x0 SIM_TID).advancePC
    else
      none
  else
    none

private theorem evalSvc_standard_exitGroup {s : State} (hx8 : (s.readReg64 Reg.x8 == 94#64) = true) :
    evalSvc Syscall.standard s = s.setStatus (.Exited (s.readReg64 Reg.x0)) := by
  have hx8' : s.readReg64 Reg.x8 = 94#64 := eq_of_beq hx8
  have hstd : Syscall.standard s = s.setStatus (.Exited (s.readReg64 Reg.x0)) := by
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
      SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, execExit, hx8']
  unfold evalSvc
  rw [hstd]
  cases s with
  | mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk physMemAvail fs
       oracle oracleIdx exclFails trace status sigHandlers sigAltStack symtab =>
    cases mem with
    | mk cells =>
      simp only [State.setStatus, ite_self]

private theorem evalSvc_standard_setTidAddress {s : State}
    (hx8 : (s.readReg64 Reg.x8 == 96#64) = true) :
    evalSvc Syscall.standard s = (s.writeReg64 Reg.x0 SIM_TID).advancePC := by
  have hx8' : s.readReg64 Reg.x8 = 96#64 := eq_of_beq hx8
  have hstd : Syscall.standard s = (s.writeReg64 Reg.x0 SIM_TID).advancePC := by
    simp [Syscall.standard, Syscall.dispatch, Syscall.standardTable, Syscall.stdioTable,
      Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable,
      Syscall.timeTable, Syscall.randomTable, Syscall.miscTable,
      SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL,
      SYS_OPENAT, SYS_CLOSE, SYS_LSEEK, SYS_PREAD64, SYS_FSTAT, SYS_PPOLL, SYS_BRK, SYS_MUNMAP,
      SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE, SYS_TKILL, SYS_TGKILL,
      SYS_SIGALTSTACK, SYS_RT_SIGACTION, SYS_RT_SIGPROCMASK, SYS_CLOCK_GETTIME,
      SYS_GETRANDOM, SYS_SET_TID_ADDRESS, execSetTidAddress, hx8']
  unfold evalSvc
  rw [hstd]
  cases s with
  | mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk physMemAvail fs
       oracle oracleIdx exclFails trace status sigHandlers sigAltStack symtab =>
    cases mem with
    | mk cells =>
      simp [State.writeReg64, State.advancePC]

theorem fastExecSystem_sound {prog : Program} (hsvc : prog.svc = Syscall.standard)
    {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    {isHalt : Bool} {imm : BitVec 16}
    (heval : fastExecSystem isHalt imm fs = some fs') :
    fs'.Agrees (prog.evalInst (.system isHalt imm) s) := by
  unfold fastExecSystem at heval
  simp only [Program.evalInst, hsvc, execInstWithSvc]
  cases isHalt
  · simp only [Bool.false_eq_true, ↓reduceIte] at heval ⊢
    cases himm : imm == 0#16
    · simp [himm] at heval
    · simp only [himm, ↓reduceIte] at heval ⊢
      rw [FastState.readReg64_eq h Reg.x8] at heval
      cases hx94 : s.readReg64 Reg.x8 == 94#64
      · simp only [hx94, Bool.false_eq_true, ↓reduceIte] at heval
        cases hx96 : s.readReg64 Reg.x8 == 96#64
        · simp [hx96] at heval
        · simp only [hx96, ↓reduceIte, Option.some.injEq] at heval
          subst heval
          rw [evalSvc_standard_setTidAddress hx96]
          exact FastState.advancePC_agrees (FastState.writeReg64_agrees h Reg.x0 SIM_TID)
      · simp only [hx94, ↓reduceIte, Option.some.injEq] at heval
        subst heval
        rw [evalSvc_standard_exitGroup hx94, FastState.readReg64_eq h Reg.x0]
        exact FastState.setStatus_agrees h _
  · simp only [↓reduceIte] at heval ⊢
    cases himm : imm == 1#16 <;>
      simp only [himm, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at heval ⊢ <;>
      subst heval <;>
      exact FastState.setStatus_agrees h _

/-- Closure-free evaluator for scalar, memory, system-register, and syscall instructions;
returns `none` on unhandled opcodes or faults. -/
def fastEvalScalar (inst : Instr) (fs : FastState) : Option FastState :=
  match inst with
  | .ldr w sz signed rt addr => fastExecLdr w sz signed rt addr fs
  | .str sz rt addr => fastExecStr sz rt addr fs
  | .ldp w signed rt1 rt2 addr => fastExecLdp w signed rt1 rt2 addr fs
  | .stp w rt1 rt2 addr => fastExecStp w rt1 rt2 addr fs
  | .adr page rd offset =>
    let base := if page then fs.pc &&& ~~~4095#64 else fs.pc
    some (fs.writeReg64 rd (base + offset)).advancePC
  | .addSubImm w op rd rn imm12 shift12 => some (fastExecAddSubImm w op rd rn imm12 shift12 fs)
  | .logicalImm w op rd rn mask => some (fastExecLogicalImm w op rd rn mask fs)
  | .moveWide w op rd imm16 hw => some (fastExecMoveWide w op rd imm16 hw fs)
  | .bitfield w op rd rn immr imms => some (fastExecBitfield w op rd rn immr imms fs)
  | .extr w rd rn rm lsb => some (fastExecExtr w rd rn rm lsb fs)
  | .logicalShift w op rd rn rm shift amount =>
    some (fastExecLogicalShift w op rd rn rm shift amount fs)
  | .addSubShift w op rd rn rm shift amount =>
    some (fastExecAddSubShift w op rd rn rm shift amount fs)
  | .addSubExt w op rd rn rm ext amount => some (fastExecAddSubExt w op rd rn rm ext amount fs)
  | .condCompareReg w isSub rn rm nzcv cond =>
    some (fastExecCondCompare w isSub false rn 0#64 rm nzcv cond fs)
  | .condCompareImm w isSub rn imm5 nzcv cond =>
    some (fastExecCondCompare w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond fs)
  | .condSelect w op rd rn rm cond => some (fastExecCondSelect w op rd rn rm cond fs)
  | .dataProc1 w op rd rn => some (fastExecDataProc1 w op rd rn fs)
  | .dataProc2 w op rd rn rm => some (fastExecDataProc2 w op rd rn rm fs)
  | .dataProc3 w op rd rn rm ra => some (fastExecDataProc3 w op rd rn rm ra fs)
  | .b offset => some (fs.setPC (fs.pc + offset))
  | .bl offset => some ((fs.writeReg64 Reg.lr (fs.pc + 4#64)).setPC (fs.pc + offset))
  | .bCond cond offset =>
    if ConditionHolds cond fs.pstate then some (fs.setPC (fs.pc + offset)) else some fs.advancePC
  | .br rn => some (fs.setPC (fs.readReg64 rn))
  | .blr rn => some ((fs.writeReg64 Reg.lr (fs.pc + 4#64)).setPC (fs.readReg64 rn))
  | .ret rn => some (fs.setPC (fs.readReg64 rn))
  | .cbz w isNonZero rt offset =>
    let val := fs.readReg w rt
    let cond := if isNonZero then (val == 0#64) != true else val == 0#64
    if cond then some (fs.setPC (fs.pc + offset)) else some fs.advancePC
  | .tbz _ isNonZero rt bitPos offset =>
    if (fs.readReg64 rt).getLsbD bitPos == isNonZero then
      some (fs.setPC (fs.pc + offset))
    else
      some fs.advancePC
  | .nop => some fs.advancePC
  | .dcZva rn => fastExecDcZva rn fs
  | .system isHalt imm => fastExecSystem isHalt imm fs
  | .ldarStlr sz isLoad rn rt => fastExecLdarStlr sz isLoad rn rt fs
  | .sysReg isRead sysreg rt => fastExecSysReg isRead sysreg rt fs
  | .ldpSimd sz vt1 vt2 addr => fastExecLdpSimd sz vt1 vt2 addr fs
  | .stpSimd sz vt1 vt2 addr => fastExecStpSimd sz vt1 vt2 addr fs
  | .ldrSimd sz vt addr => fastExecLdrSimd sz vt addr fs
  | .strSimd sz vt addr => fastExecStrSimd sz vt addr fs
  | _ => none

/-- Soundness of `fastEvalScalar` against `prog.evalInst` under `Syscall.standard`. -/
theorem fastEvalScalar_sound {prog : Program} (hsvc : prog.svc = Syscall.standard)
    {inst : Instr} {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (heval : fastEvalScalar inst fs = some fs') :
    fs'.Agrees (prog.evalInst inst s) := by
  delta fastEvalScalar at heval
  cases inst with
  | ldr w sz signed rt addr => exact fastExecLdr_sound hag heval
  | str sz rt addr => exact fastExecStr_sound hag heval
  | ldp w signed rt1 rt2 addr => exact fastExecLdp_sound hag heval
  | stp w rt1 rt2 addr => exact fastExecStp_sound hag heval
  | adr page rd offset =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, hag.pc]
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag rd _)
  | addSubImm w op rd rn imm12 shift12 =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecAddSubImm_agrees hag w op rd rn imm12 shift12
  | logicalImm w op rd rn mask =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecLogicalImm_agrees hag w op rd rn mask
  | moveWide w op rd imm16 hw =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecMoveWide_agrees hag w op rd imm16 hw
  | bitfield w op rd rn immr imms =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecBitfield_agrees hag w op rd rn immr imms
  | extr w rd rn rm lsb =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecExtr_agrees hag (evalSvc prog.svc) w rd rn rm lsb
  | logicalShift w op rd rn rm shift amount =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecLogicalShift_agrees hag w op rd rn rm shift amount
  | addSubShift w op rd rn rm shift amount =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecAddSubShift_agrees hag w op rd rn rm shift amount
  | addSubExt w op rd rn rm ext amount =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecAddSubExt_agrees hag w op rd rn rm ext amount
  | condCompareReg w isSub rn rm nzcv cond =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecCondCompare_agrees hag w isSub false rn 0#64 rm nzcv cond
  | condCompareImm w isSub rn imm5 nzcv cond =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecCondCompare_agrees hag w isSub true rn (imm5.zeroExtend 64) .xzr nzcv cond
  | condSelect w op rd rn rm cond =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecCondSelect_agrees hag w op rd rn rm cond
  | dataProc1 w op rd rn =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecDataProc1_agrees hag w op rd rn
  | dataProc2 w op rd rn rm =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecDataProc2_agrees hag w op rd rn rm
  | dataProc3 w op rd rn rm ra =>
    dsimp only at heval; injection heval with heval; subst heval
    exact fastExecDataProc3_agrees hag w op rd rn rm ra
  | b offset =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, hag.pc]
    exact FastState.setPC_agrees hag _
  | bl offset =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, hag.pc]
    exact FastState.setPC_agrees (FastState.writeReg64_agrees hag Reg.lr _) _
  | bCond cond offset =>
    dsimp only at heval
    simp only [hag.pstate, hag.pc] at heval
    simp only [Program.evalInst, execInstWithSvc]
    split at heval <;> rename_i hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at heval ⊢ <;> subst heval
    · exact FastState.setPC_agrees hag _
    · exact FastState.advancePC_agrees hag
  | br rn =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, FastState.readReg64_eq hag]
    exact FastState.setPC_agrees hag _
  | blr rn =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, FastState.readReg64_eq hag, hag.pc]
    exact FastState.setPC_agrees (FastState.writeReg64_agrees hag Reg.lr _) _
  | ret rn =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc, FastState.readReg64_eq hag]
    exact FastState.setPC_agrees hag _
  | cbz w isNonZero rt offset =>
    dsimp only at heval
    simp only [FastState.readReg_eq hag, hag.pc] at heval
    simp only [Program.evalInst, execInstWithSvc]
    cases isNonZero <;> simp only [Bool.false_eq_true, ↓reduceIte] at heval ⊢
    all_goals
      split at heval <;> rename_i hc <;>
        simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at heval ⊢ <;> subst heval
      · exact FastState.setPC_agrees hag _
      · exact FastState.advancePC_agrees hag
  | tbz w isNonZero rt bitPos offset =>
    dsimp only at heval
    simp only [FastState.readReg64_eq hag, hag.pc] at heval
    simp only [Program.evalInst, execInstWithSvc]
    split at heval <;> rename_i hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true, Option.some.injEq] at heval ⊢ <;> subst heval
    · exact FastState.setPC_agrees hag _
    · exact FastState.advancePC_agrees hag
  | nop =>
    dsimp only at heval; injection heval with heval; subst heval
    simp only [Program.evalInst, execInstWithSvc]
    exact FastState.advancePC_agrees hag
  | dcZva rn => exact fastExecDcZva_sound hag (evalSvc prog.svc) heval
  | system isHalt imm => exact fastExecSystem_sound hsvc hag heval
  | ldarStlr sz isLoad rn rt => exact fastExecLdarStlr_sound hag (evalSvc prog.svc) heval
  | sysReg isRead sysreg rt => exact fastExecSysReg_sound hag (evalSvc prog.svc) heval
  | ldpSimd sz vt1 vt2 addr => exact fastExecLdpSimd_sound hag (evalSvc prog.svc) heval
  | stpSimd sz vt1 vt2 addr => exact fastExecStpSimd_sound hag (evalSvc prog.svc) heval
  | ldrSimd sz vt addr => exact fastExecLdrSimd_sound hag (evalSvc prog.svc) heval
  | strSimd sz vt addr => exact fastExecStrSimd_sound hag (evalSvc prog.svc) heval
  | _ => nomatch heval

end Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar
