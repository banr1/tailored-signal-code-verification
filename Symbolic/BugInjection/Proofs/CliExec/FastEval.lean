/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar

/-!
# Closure-Free AArch64 Instruction Evaluator

Implements closure-free evaluators and `FastState.Agrees` soundness proofs for FP/AdvSIMD
instructions (`fmovGprVec`, `fpCompare`, `simdImmShift`, `simdInsDup`, `simdThreeSame`,
`simdTwoRegMisc`, `simdAcrossLanes`, `simdPmull`), and combines them with `fastEvalScalar` in
`fastEvalInst`.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.FastEval

set_option autoImplicit false

open Arm64
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
open Symbolic.BugInjection.Proofs.CliExec.FastEvalScalar

def fastRangeLoop {β : Type} (start stop : Nat) (init : β) (step : Nat → β → β) : β :=
  (List.range' start (stop - start) 1).foldl (fun acc i => step i acc) init

private theorem forIn_list_yield {α β : Type} (step : α → β → β) :
    ∀ (xs : List α) (init : β),
      (forIn (m := Id) xs init (fun i acc => pure (ForInStep.yield (step i acc)))).run =
        xs.foldl (fun acc i => step i acc) init
  | [], init => by simp only [List.forIn_nil, pure, Id.run, List.foldl_nil]
  | x :: xs, init => by
    simp only [List.forIn_cons, bind, pure, List.foldl_cons]
    exact forIn_list_yield step xs (step x init)

private theorem fastRangeLoop_eq_forIn {β : Type} (start stop : Nat) (init : β)
    (step : Nat → β → β) :
    fastRangeLoop start stop init step =
      (forIn (m := Id) ([start:stop] : Std.Legacy.Range) init
        (fun i acc => pure (ForInStep.yield (step i acc)))).run := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  exact (forIn_list_yield step (List.range' start (stop - start) 1) init).symm

private theorem pure_yield_ite {β : Type} (c : Bool) (t e : β) :
    (pure (ForInStep.yield (if c then t else e)) : Id (ForInStep β)) =
      if c then pure (ForInStep.yield t) else pure (ForInStep.yield e) := by
  cases c <;> rfl

def fastMapSimdLanes (q : Bool) (esize : Nat) (v : BitVec 128)
    (f : BitVec 128 → BitVec 128) : BitVec 128 :=
  let totalBits := if q then 128 else 64
  let numLanes := totalBits / esize
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  fastRangeLoop 0 numLanes 0#128 fun i acc =>
    let lane := (v >>> (i * esize)) &&& mask
    let outLane := (f lane) &&& mask
    acc ||| (outLane <<< (i * esize))

private theorem fastMapSimdLanes_eq (q : Bool) (esize : Nat) (v : BitVec 128)
    (f : BitVec 128 → BitVec 128) :
    fastMapSimdLanes q esize v f = mapSimdLanes q esize v f := by
  unfold fastMapSimdLanes mapSimdLanes
  exact fastRangeLoop_eq_forIn 0 _ 0#128 _

def fastZipSimdLanes (q : Bool) (esize : Nat) (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) : BitVec 128 :=
  let totalBits := if q then 128 else 64
  let numLanes := totalBits / esize
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  fastRangeLoop 0 numLanes 0#128 fun i acc =>
    let a := (vn >>> (i * esize)) &&& mask
    let b := (vm >>> (i * esize)) &&& mask
    let outLane := (f a b) &&& mask
    acc ||| (outLane <<< (i * esize))

private theorem fastZipSimdLanes_eq (q : Bool) (esize : Nat) (vn vm : BitVec 128)
    (f : BitVec 128 → BitVec 128 → BitVec 128) :
    fastZipSimdLanes q esize vn vm f = zipSimdLanes q esize vn vm f := by
  unfold fastZipSimdLanes zipSimdLanes
  exact fastRangeLoop_eq_forIn 0 _ 0#128 _

def fastExecFmovGprVec (sf : Bool) (ftype rmode : BitVec 2) (opcode : BitVec 3)
    (rn rd : BitVec 5) (fs : FastState) : Option FastState :=
  if opcode == 0b110#3 then
    let dstReg := Reg.fromZRBits rd
    if !sf && ftype == 0b00#2 && rmode == 0b00#2 then
      some (fs.writeReg32 dstReg (fs.readVReg32 rn)).advancePC
    else if sf && ftype == 0b01#2 && rmode == 0b00#2 then
      some (fs.writeReg64 dstReg (fs.readVReg64 rn)).advancePC
    else if sf && ftype == 0b10#2 && rmode == 0b01#2 then
      let hi64 := (fs.readVReg128 rn).extractLsb' 64 64
      some (fs.writeReg64 dstReg hi64).advancePC
    else
      none
  else if opcode == 0b111#3 then
    let srcReg := Reg.fromZRBits rn
    if !sf && ftype == 0b00#2 && rmode == 0b00#2 then
      some (fs.writeVReg32 rd (fs.readReg32 srcReg)).advancePC
    else if sf && ftype == 0b01#2 && rmode == 0b00#2 then
      some (fs.writeVReg64 rd (fs.readReg64 srcReg)).advancePC
    else if sf && ftype == 0b10#2 && rmode == 0b01#2 then
      let lo64 := (fs.readVReg128 rd).truncate 64
      let hi64 := fs.readReg64 srcReg
      some (fs.writeVReg128 rd (hi64 ++ lo64)).advancePC
    else
      none
  else if opcode == 0b000#3 || opcode == 0b001#3 then
    let unsigned := opcode == 0b001#3
    let dstReg := Reg.fromZRBits rd
    if !sf && ftype == 0b00#2 then
      let x := fs.readVReg32 rn
      some ((fs.writeReg32 dstReg (evalFpToInt32_32 unsigned rmode x)).orFpsr
        (evalFpToIntFlags32_32 unsigned rmode x)).advancePC
    else if sf && ftype == 0b00#2 then
      let x := fs.readVReg32 rn
      some ((fs.writeReg64 dstReg (evalFpToInt64_32 unsigned rmode x)).orFpsr
        (evalFpToIntFlags64_32 unsigned rmode x)).advancePC
    else if !sf && ftype == 0b01#2 then
      let x := fs.readVReg64 rn
      some ((fs.writeReg32 dstReg (evalFpToInt32_64 unsigned rmode x)).orFpsr
        (evalFpToIntFlags32_64 unsigned rmode x)).advancePC
    else if sf && ftype == 0b01#2 then
      let x := fs.readVReg64 rn
      some ((fs.writeReg64 dstReg (evalFpToInt64_64 unsigned rmode x)).orFpsr
        (evalFpToIntFlags64_64 unsigned rmode x)).advancePC
    else
      none
  else if rmode == 0b00#2 && (opcode == 0b100#3 || opcode == 0b101#3) then
    let unsigned := opcode == 0b101#3
    let dstReg := Reg.fromZRBits rd
    if !sf && ftype == 0b00#2 then
      let x := fs.readVReg32 rn
      some ((fs.writeReg32 dstReg (evalFpToIntRound32_32 unsigned .RNA 0 x)).orFpsr
        (evalFpToIntRoundFlags32_32 unsigned .RNA 0 x)).advancePC
    else if sf && ftype == 0b00#2 then
      let x := fs.readVReg32 rn
      some ((fs.writeReg64 dstReg (evalFpToIntRound64_32 unsigned .RNA 0 x)).orFpsr
        (evalFpToIntRoundFlags64_32 unsigned .RNA 0 x)).advancePC
    else if !sf && ftype == 0b01#2 then
      let x := fs.readVReg64 rn
      some ((fs.writeReg32 dstReg (evalFpToIntRound32_64 unsigned .RNA 0 x)).orFpsr
        (evalFpToIntRoundFlags32_64 unsigned .RNA 0 x)).advancePC
    else if sf && ftype == 0b01#2 then
      let x := fs.readVReg64 rn
      some ((fs.writeReg64 dstReg (evalFpToIntRound64_64 unsigned .RNA 0 x)).orFpsr
        (evalFpToIntRoundFlags64_64 unsigned .RNA 0 x)).advancePC
    else
      none
  else if rmode == 0b00#2 && (opcode == 0b010#3 || opcode == 0b011#3) then
    let unsigned := opcode == 0b011#3
    let srcReg := Reg.fromZRBits rn
    if !sf && ftype == 0b00#2 then
      let x := fs.readReg32 srcReg
      some ((fs.writeVReg32 rd (evalIntToFp32_32 unsigned x)).orFpsr
        (evalIntToFpFlags32_32 unsigned x)).advancePC
    else if sf && ftype == 0b00#2 then
      let x := fs.readReg64 srcReg
      some ((fs.writeVReg32 rd (evalIntToFp32_64 unsigned x)).orFpsr
        (evalIntToFpFlags32_64 unsigned x)).advancePC
    else if !sf && ftype == 0b01#2 then
      let x := fs.readReg32 srcReg
      some ((fs.writeVReg64 rd (evalIntToFp64_32 unsigned x)).orFpsr
        (evalIntToFpFlags64_32 unsigned x)).advancePC
    else if sf && ftype == 0b01#2 then
      let x := fs.readReg64 srcReg
      some ((fs.writeVReg64 rd (evalIntToFp64_64 unsigned x)).orFpsr
        (evalIntToFpFlags64_64 unsigned x)).advancePC
    else
      none
  else
    none

private theorem fmov_leaf_reg32_fpsr {fs : FastState} {s : State} (h : fs.Agrees s)
    (r : Reg) (v : BitVec 32) (f : BitVec 32) :
    (((fs.writeReg32 r v).orFpsr f).advancePC).Agrees
      (((s.writeReg32 r v).orFpsr f).advancePC) :=
  FastState.advancePC_agrees (FastState.orFpsr_agrees (FastState.writeReg32_agrees h r v) f)

private theorem fmov_leaf_reg64_fpsr {fs : FastState} {s : State} (h : fs.Agrees s)
    (r : Reg) (v : BitVec 64) (f : BitVec 32) :
    (((fs.writeReg64 r v).orFpsr f).advancePC).Agrees
      (((s.writeReg64 r v).orFpsr f).advancePC) :=
  FastState.advancePC_agrees (FastState.orFpsr_agrees (FastState.writeReg64_agrees h r v) f)

private theorem fmov_leaf_vreg32_fpsr {fs : FastState} {s : State} (h : fs.Agrees s)
    (rd : BitVec 5) (v : BitVec 32) (f : BitVec 32) :
    (((fs.writeVReg32 rd v).orFpsr f).advancePC).Agrees
      (((s.writeVReg32 rd v).orFpsr f).advancePC) :=
  FastState.advancePC_agrees (FastState.orFpsr_agrees (writeVReg32_agrees h rd v) f)

private theorem fmov_leaf_vreg64_fpsr {fs : FastState} {s : State} (h : fs.Agrees s)
    (rd : BitVec 5) (v : BitVec 64) (f : BitVec 32) :
    (((fs.writeVReg64 rd v).orFpsr f).advancePC).Agrees
      (((s.writeVReg64 rd v).orFpsr f).advancePC) :=
  FastState.advancePC_agrees (FastState.orFpsr_agrees (writeVReg64_agrees h rd v) f)

theorem fastExecFmovGprVec_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {sf : Bool} {ftype rmode : BitVec 2} {opcode : BitVec 3}
    {rn rd : BitVec 5}
    (heval : fastExecFmovGprVec sf ftype rmode opcode rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.fmovGprVec sf ftype rmode opcode rn rd) s) := by
  unfold fastExecFmovGprVec at heval
  simp only [readVReg32_eq h, readVReg64_eq h, FastState.readVReg128_eq h,
      FastState.readReg32_eq h, FastState.readReg64_eq h] at heval
  simp only [execInstWithSvc]
  by_cases h1 : (opcode == 0b110#3) = true
  · simp only [h1, ↓reduceIte] at heval ⊢
    by_cases ha : ((!sf && ftype == 0b00#2) && rmode == 0b00#2) = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
      exact FastState.advancePC_agrees (FastState.writeReg32_agrees h _ _)
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases hb : ((sf && ftype == 0b01#2) && rmode == 0b00#2) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees h _ _)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases hc : ((sf && ftype == 0b10#2) && rmode == 0b01#2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeReg64_agrees h _ _)
        · simp [hc] at heval
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases h2 : (opcode == 0b111#3) = true
    · simp only [h2, ↓reduceIte] at heval ⊢
      by_cases ha : ((!sf && ftype == 0b00#2) && rmode == 0b00#2) = true
      · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (writeVReg32_agrees h _ _)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases hb : ((sf && ftype == 0b01#2) && rmode == 0b00#2) = true
        · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (writeVReg64_agrees h _ _)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases hc : ((sf && ftype == 0b10#2) && rmode == 0b01#2) = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h _ _)
          · simp [hc] at heval
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases h3 : (opcode == 0b000#3 || opcode == 0b001#3) = true
      · simp only [h3, ↓reduceIte] at heval ⊢
        by_cases ha : (!sf && ftype == 0b00#2) = true
        · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact fmov_leaf_reg32_fpsr h _ _ _
        · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases hb : (sf && ftype == 0b00#2) = true
          · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact fmov_leaf_reg64_fpsr h _ _ _
          · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases hc : (!sf && ftype == 0b01#2) = true
            · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact fmov_leaf_reg32_fpsr h _ _ _
            · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases hd : (sf && ftype == 0b01#2) = true
              · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact fmov_leaf_reg64_fpsr h _ _ _
              · simp [hd] at heval
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases h4 : (rmode == 0b00#2 && (opcode == 0b100#3 || opcode == 0b101#3)) = true
        · simp only [h4, ↓reduceIte] at heval ⊢
          by_cases ha : (!sf && ftype == 0b00#2) = true
          · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact fmov_leaf_reg32_fpsr h _ _ _
          · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases hb : (sf && ftype == 0b00#2) = true
            · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact fmov_leaf_reg64_fpsr h _ _ _
            · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases hc : (!sf && ftype == 0b01#2) = true
              · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact fmov_leaf_reg32_fpsr h _ _ _
              · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                by_cases hd : (sf && ftype == 0b01#2) = true
                · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                  exact fmov_leaf_reg64_fpsr h _ _ _
                · simp [hd] at heval
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases h5 : (rmode == 0b00#2 && (opcode == 0b010#3 || opcode == 0b011#3)) = true
          · simp only [h5, ↓reduceIte] at heval ⊢
            by_cases ha : (!sf && ftype == 0b00#2) = true
            · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact fmov_leaf_vreg32_fpsr h _ _ _
            · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases hb : (sf && ftype == 0b00#2) = true
              · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact fmov_leaf_vreg32_fpsr h _ _ _
              · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                by_cases hc : (!sf && ftype == 0b01#2) = true
                · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                  exact fmov_leaf_vreg64_fpsr h _ _ _
                · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                  by_cases hd : (sf && ftype == 0b01#2) = true
                  · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                    exact fmov_leaf_vreg64_fpsr h _ _ _
                  · simp [hd] at heval
          · simp [h5] at heval

def fastExecFpCompare (ftype : BitVec 2) (rm : BitVec 5) (op : BitVec 2)
    (rn opcode2 : BitVec 5) (fs : FastState) : Option FastState :=
  if op == 0b00#2 &&
      (opcode2 == 0b00000#5 || opcode2 == 0b01000#5 ||
       opcode2 == 0b10000#5 || opcode2 == 0b11000#5) then
    let withZero := opcode2.getLsbD 3
    let signalNaN := opcode2.getLsbD 4
    if ftype == 0b00#2 then
      let lhs := fs.readVReg32 rn
      let rhs := if withZero then 0#32 else fs.readVReg32 rm
      some ((fs.setPState (evalFpCmp32 signalNaN lhs rhs)).orFpsr
        (evalFpCmpFlags32 signalNaN lhs rhs)).advancePC
    else if ftype == 0b01#2 then
      let lhs := fs.readVReg64 rn
      let rhs := if withZero then 0#64 else fs.readVReg64 rm
      some ((fs.setPState (evalFpCmp64 signalNaN lhs rhs)).orFpsr
        (evalFpCmpFlags64 signalNaN lhs rhs)).advancePC
    else
      none
  else
    none

theorem fastExecFpCompare_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {ftype : BitVec 2} {rm : BitVec 5} {op : BitVec 2}
    {rn opcode2 : BitVec 5}
    (heval : fastExecFpCompare ftype rm op rn opcode2 fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.fpCompare ftype rm op rn opcode2) s) := by
  unfold fastExecFpCompare at heval
  rw [readVReg32_eq h rn, readVReg32_eq h rm, readVReg64_eq h rn, readVReg64_eq h rm] at heval
  simp only [execInstWithSvc]
  by_cases h1 : (op == 0b00#2 &&
      (opcode2 == 0b00000#5 || opcode2 == 0b01000#5 ||
       opcode2 == 0b10000#5 || opcode2 == 0b11000#5)) = true
  · simp only [h1, ↓reduceIte] at heval ⊢
    by_cases ha : (ftype == 0b00#2) = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
      exact FastState.advancePC_agrees (FastState.orFpsr_agrees (FastState.setPState_agrees h _) _)
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases hb : (ftype == 0b01#2) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees
          (FastState.orFpsr_agrees (FastState.setPState_agrees h _) _)
      · simp [hb] at heval
  · simp [h1] at heval

def fastExecSimdImmShift (q op : Bool) (immh : BitVec 4) (immb : BitVec 3)
    (opc rn rd : BitVec 5) (fs : FastState) : Option FastState :=
  if immh == 0#4 then
    if opc.getLsbD 0 then
      none
    else
      let imm8 : BitVec 8 := immb ++ rn
      let cmode := opc.extractLsb' 1 4
      let writeD64 (d64 : BitVec 64) : Option FastState :=
        let res128 : BitVec 128 := if q then d64 ++ d64 else d64.zeroExtend 128
        some (fs.writeVReg128 rd res128).advancePC
      if !op && cmode == 0b1110#4 then
        writeD64 (imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8 ++ imm8)
      else if op && cmode == 0b1110#4 then
        let b (i : Nat) : BitVec 8 := if imm8.getLsbD i then 0xff#8 else 0x00#8
        writeD64 (b 7 ++ b 6 ++ b 5 ++ b 4 ++ b 3 ++ b 2 ++ b 1 ++ b 0)
      else if !op && (cmode &&& 0b1001#4) == 0b0000#4 then
        let sh := (cmode.extractLsb' 1 2).toNat * 8
        let w32 : BitVec 32 := (imm8.zeroExtend 32) <<< sh
        writeD64 (w32 ++ w32)
      else if !op && (cmode &&& 0b1101#4) == 0b1000#4 then
        let sh := (cmode.extractLsb' 1 1).toNat * 8
        let h16 : BitVec 16 := (imm8.zeroExtend 16) <<< sh
        writeD64 (h16 ++ h16 ++ h16 ++ h16)
      else
        none
  else
    let immhb := (immh ++ immb).toNat
    let esize :=
      if immhb >= 64 then 64 else if immhb >= 32 then 32 else if immhb >= 16 then 16 else 8
    let shiftLeftAmt := immhb - esize
    let shiftRightAmt := 2 * esize - immhb
    let vn := fs.readVReg128 rn
    if !op && opc == 0b01010#5 && !(immh.getLsbD 3 && !q) then
      let res := fastMapSimdLanes q esize vn (fun lane => lane <<< shiftLeftAmt)
      some (fs.writeVReg128 rd res).advancePC
    else if op && opc == 0b10100#5 && !immh.getLsbD 3 then
      let half : BitVec 64 := if q then vn.extractLsb' 64 64 else vn.truncate 64
      let dstEsize := 2 * esize
      let numLanes := 64 / esize
      let srcMask : BitVec 64 := (1#64 <<< esize) - 1#64
      let res : BitVec 128 :=
        fastRangeLoop 0 numLanes 0#128 fun i acc =>
          let lane64 := (half >>> (i * esize)) &&& srcMask
          let wide128 := (lane64.zeroExtend 128) <<< shiftLeftAmt
          acc ||| (wide128 <<< (i * dstEsize))
      some (fs.writeVReg128 rd res).advancePC
    else if op && opc == 0b00000#5 && !(immh.getLsbD 3 && !q) then
      let res := fastMapSimdLanes q esize vn (fun lane => lane >>> shiftRightAmt)
      some (fs.writeVReg128 rd res).advancePC
    else if op && (opc == 0b01000#5 || opc == 0b01010#5) && !(immh.getLsbD 3 && !q) then
      let isSli := opc == 0b01010#5
      let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
      let res := fastZipSimdLanes q esize vn (fs.readVReg128 rd) (fun a d =>
        let m : BitVec 128 :=
          if isSli then (laneMask <<< shiftLeftAmt) &&& laneMask else laneMask >>> shiftRightAmt
        let sh := if isSli then (a <<< shiftLeftAmt) &&& laneMask else a >>> shiftRightAmt
        (d &&& ~~~m) ||| (sh &&& m))
      some (fs.writeVReg128 rd res).advancePC
    else
      none

theorem fastExecSimdImmShift_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q op : Bool} {immh : BitVec 4} {immb : BitVec 3}
    {opc rn rd : BitVec 5}
    (heval : fastExecSimdImmShift q op immh immb opc rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdImmShift q op immh immb opc rn rd) s) := by
  unfold fastExecSimdImmShift at heval
  simp only [fastMapSimdLanes_eq, fastZipSimdLanes_eq, fastRangeLoop_eq_forIn] at heval
  rw [FastState.readVReg128_eq h rd, FastState.readVReg128_eq h rn] at heval
  simp only [execInstWithSvc]
  by_cases h0 : (immh == 0#4) = true
  · simp only [h0, ↓reduceIte] at heval ⊢
    by_cases hopc0 : opc.getLsbD 0 = true
    · simp [hopc0] at heval
    · simp only [hopc0, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      set cmode := opc.extractLsb' 1 4
      by_cases ha : (!op && cmode == 0b1110#4) = true
      · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases hb : (op && cmode == 0b1110#4) = true
        · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases hc : (!op && (cmode &&& 0b1001#4) == 0b0000#4) = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases hd : (!op && (cmode &&& 0b1101#4) == 0b1000#4) = true
            · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
            · simp [hd] at heval
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases ha : ((!op && opc == 0b01010#5) && !(immh.getLsbD 3 && !q)) = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
      exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases hb : ((op && opc == 0b10100#5) && !immh.getLsbD 3) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases hc : ((op && opc == 0b00000#5) && !(immh.getLsbD 3 && !q)) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases hd : ((op && (opc == 0b01000#5 || opc == 0b01010#5)) &&
              !(immh.getLsbD 3 && !q)) = true
          · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · simp only [hd, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at heval

def fastExecSimdInsDup (q op : Bool) (imm5 : BitVec 5) (imm4 : BitVec 4)
    (rn rd : BitVec 5) (fs : FastState) : Option FastState :=
  if (imm5.extractLsb' 0 4) == 0#4 then
    none
  else
    let esize : Nat :=
      if (imm5.extractLsb' 0 1) == 1#1 then 8
      else if (imm5.extractLsb' 0 2) == 2#2 then 16
      else if (imm5.extractLsb' 0 3) == 4#3 then 32
      else 64
    let dstIdx : Nat :=
      if esize == 8 then imm5.toNat >>> 1
      else if esize == 16 then imm5.toNat >>> 2
      else if esize == 32 then imm5.toNat >>> 3
      else imm5.toNat >>> 4
    let mask : BitVec 128 := (1#128 <<< esize) - 1#128
    if !op && imm4 == 0b0001#4 && !(esize == 64 && !q) then
      let elem := ((fs.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
      let res := fastMapSimdLanes q esize 0#128 (fun _ => elem)
      some (fs.writeVReg128 rd res).advancePC
    else if !op && imm4 == 0b0000#4 && !(esize == 64 && !q) then
      let elem := getSimdLane (fs.readVReg128 rn) esize dstIdx
      let res := fastMapSimdLanes q esize 0#128 (fun _ => elem)
      some (fs.writeVReg128 rd res).advancePC
    else if q && !op && imm4 == 0b0011#4 then
      let elem := ((fs.readReg64 (Reg.fromZRBits rn)).zeroExtend 128) &&& mask
      let old := fs.readVReg128 rd
      let clearMask := ~~~(mask <<< (dstIdx * esize))
      let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
      some (fs.writeVReg128 rd res).advancePC
    else if !op && imm4 == 0b0111#4 && ((q && esize == 64) || (!q && esize < 64)) then
      let elem := (getSimdLane (fs.readVReg128 rn) esize dstIdx).truncate 64
      let w : Width := if q then .W64 else .W32
      some (fs.writeReg w (Reg.fromZRBits rd) elem).advancePC
    else if !op && imm4 == 0b0101#4 && ((q && esize < 64) || (!q && esize < 32)) then
      let elem := (getSimdLane (fs.readVReg128 rn) esize dstIdx).truncate 64
      let signExt :=
        if elem.getLsbD (esize - 1) then elem ||| ~~~((1#64 <<< esize) - 1#64) else elem
      let w : Width := if q then .W64 else .W32
      some (fs.writeReg w (Reg.fromZRBits rd) signExt).advancePC
    else if q && op then
      let srcIdx : Nat :=
        if esize == 8 then imm4.toNat
        else if esize == 16 then imm4.toNat >>> 1
        else if esize == 32 then imm4.toNat >>> 2
        else imm4.toNat >>> 3
      let elem := getSimdLane (fs.readVReg128 rn) esize srcIdx
      let old := fs.readVReg128 rd
      let clearMask := ~~~(mask <<< (dstIdx * esize))
      let res := (old &&& clearMask) ||| (elem <<< (dstIdx * esize))
      some (fs.writeVReg128 rd res).advancePC
    else
      none

theorem fastExecSimdInsDup_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q op : Bool} {imm5 : BitVec 5} {imm4 : BitVec 4}
    {rn rd : BitVec 5}
    (heval : fastExecSimdInsDup q op imm5 imm4 rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdInsDup q op imm5 imm4 rn rd) s) := by
  unfold fastExecSimdInsDup at heval
  simp only [fastMapSimdLanes_eq] at heval
  rw [FastState.readReg64_eq h, FastState.readVReg128_eq h rn,
      FastState.readVReg128_eq h rd] at heval
  simp only [execInstWithSvc]
  by_cases h0 : ((imm5.extractLsb' 0 4) == 0#4) = true
  · simp [h0] at heval
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    set esize : Nat :=
      if (imm5.extractLsb' 0 1) == 1#1 then 8
      else if (imm5.extractLsb' 0 2) == 2#2 then 16
      else if (imm5.extractLsb' 0 3) == 4#3 then 32
      else 64
    by_cases ha : ((!op && imm4 == 0b0001#4) && !(esize == 64 && !q)) = true
    · simp only [ha, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
      exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
    · simp only [ha, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases hb : ((!op && imm4 == 0b0000#4) && !(esize == 64 && !q)) = true
      · simp only [hb, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases hc : ((q && !op) && imm4 == 0b0011#4) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases hd : ((!op && imm4 == 0b0111#4) &&
              ((q && esize == 64) || (!q && decide (esize < 64)))) = true
          · simp only [hd, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeReg_agrees h _ _ _)
          · simp only [hd, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases he : ((!op && imm4 == 0b0101#4) &&
                ((q && decide (esize < 64)) || (!q && decide (esize < 32)))) = true
            · simp only [he, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact FastState.advancePC_agrees (FastState.writeReg_agrees h _ _ _)
            · simp only [he, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases hf : (q && op) = true
              · simp only [hf, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
              · simp [hf] at heval

def fastExecSimdThreeSame (q u : Bool) (size : BitVec 2) (rm opcode rn rd : BitVec 5)
    (fs : FastState) : Option FastState :=
  let vn := fs.readVReg128 rn
  let vm := fs.readVReg128 rm
  let esize := 8 <<< size.toNat
  let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
  let truncQ (v : BitVec 128) : BitVec 128 := if q then v else (v.truncate 64).zeroExtend 128
  if opcode == 0b00011#5 then
    match u, size with
    | false, 0b00#2 => some (fs.writeVReg128 rd (truncQ (vn &&& vm))).advancePC
    | false, 0b01#2 => some (fs.writeVReg128 rd (truncQ (vn &&& ~~~vm))).advancePC
    | false, 0b10#2 => some (fs.writeVReg128 rd (truncQ (vn ||| vm))).advancePC
    | false, 0b11#2 => some (fs.writeVReg128 rd (truncQ (vn ||| ~~~vm))).advancePC
    | true,  0b00#2 => some (fs.writeVReg128 rd (truncQ (vn ^^^ vm))).advancePC
    | true,  0b01#2 =>
      some (fs.writeVReg128 rd (truncQ (((vn ^^^ vm) &&& fs.readVReg128 rd) ^^^ vm))).advancePC
    | _, _ => none
  else if size == 0b11#2 && !q then
    none
  else if opcode == 0b10000#5 then
    let res := fastZipSimdLanes q esize vn vm (fun a b => if u then a - b else a + b)
    some (fs.writeVReg128 rd res).advancePC
  else if opcode == 0b10001#5 then
    let res := fastZipSimdLanes q esize vn vm (fun a b =>
      let cond := if u then a == b else (a &&& b) != 0#128
      if cond then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if opcode == 0b00111#5 then
    let res := fastZipSimdLanes q esize vn vm (fun a b =>
      let cond :=
        if u then BitVec.ule b a
        else
          let signBit := 1#128 <<< (esize - 1)
          BitVec.ule (b ^^^ signBit) (a ^^^ signBit)
      if cond then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if opcode == 0b00110#5 then
    let res := fastZipSimdLanes q esize vn vm (fun a b =>
      let cond :=
        if u then BitVec.ult b a
        else
          let signBit := 1#128 <<< (esize - 1)
          BitVec.ult (b ^^^ signBit) (a ^^^ signBit)
      if cond then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if opcode == 0b01000#5 then
    let res := fastZipSimdLanes q esize vn vm (fun a b =>
      let shByte : BitVec 8 := b.truncate 8
      let shInt : Int := shByte.toInt
      if shInt >= 0 then
        let amt := shInt.toNat
        if amt >= esize then 0#128 else (a <<< amt) &&& laneMask
      else
        let amt := (-shInt).toNat
        if u || !a.getLsbD (esize - 1) then
          if amt >= esize then 0#128 else a >>> amt
        else
          if amt >= esize then laneMask
          else ((a >>> amt) ||| (laneMask <<< (esize - amt))) &&& laneMask)
    some (fs.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b10111#5 then
    let elems := (if q then 128 else 64) / esize
    let half := elems / 2
    let pairLane (i : Nat) : BitVec 128 :=
      let src := if i < half then vn else vm
      let j := if i < half then i else i - half
      (getSimdLane src esize (2 * j) + getSimdLane src esize (2 * j + 1)) &&& laneMask
    let res : BitVec 128 :=
      fastRangeLoop 0 elems 0#128 fun i acc =>
        acc ||| (pairLane i <<< (i * esize))
    some (fs.writeVReg128 rd res).advancePC
  else
    none

private theorem bv2_eq_3_of_ne {s : BitVec 2}
    (h0 : s ≠ 0b00#2) (h1 : s ≠ 0b01#2) (h2 : s ≠ 0b10#2) : s = 0b11#2 := by
  apply BitVec.eq_of_toNat_eq
  change s.toNat = 3
  have := s.isLt
  have : s.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have : s.toNat ≠ 1 := fun h => h1 (BitVec.eq_of_toNat_eq h)
  have : s.toNat ≠ 2 := fun h => h2 (BitVec.eq_of_toNat_eq h)
  omega

theorem fastExecSimdThreeSame_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q u : Bool} {size : BitVec 2} {rm opcode rn rd : BitVec 5}
    (heval : fastExecSimdThreeSame q u size rm opcode rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdThreeSame q u size rm opcode rn rd) s) := by
  unfold fastExecSimdThreeSame at heval
  simp only [fastZipSimdLanes_eq, fastRangeLoop_eq_forIn] at heval
  rw [FastState.readVReg128_eq h rn, FastState.readVReg128_eq h rm,
      FastState.readVReg128_eq h rd] at heval
  simp only [execInstWithSvc]
  by_cases h1 : (opcode == 0b00011#5) = true
  · simp only [h1, ↓reduceIte] at heval ⊢
    cases u with
    | false =>
      by_cases hs0 : size = 0b00#2
      · subst hs0; simp only [Option.some.injEq] at heval; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · by_cases hs1 : size = 0b01#2
        · subst hs1; simp only [Option.some.injEq] at heval; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · by_cases hs2 : size = 0b10#2
          · subst hs2; simp only [Option.some.injEq] at heval; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · have hs3 := bv2_eq_3_of_ne hs0 hs1 hs2
            subst hs3; simp only [Option.some.injEq] at heval; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
    | true =>
      by_cases hs0 : size = 0b00#2
      · subst hs0; simp only [Option.some.injEq] at heval; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · by_cases hs1 : size = 0b01#2
        · subst hs1; simp only [Option.some.injEq] at heval; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · by_cases hs2 : size = 0b10#2
          · subst hs2; nomatch heval
          · have hs3 := bv2_eq_3_of_ne hs0 hs1 hs2
            subst hs3; nomatch heval
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases h2 : (size == 0b11#2 && !q) = true
    · simp [h2] at heval
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases h3 : (opcode == 0b10000#5) = true
      · simp only [h3, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases h4 : (opcode == 0b10001#5) = true
        · simp only [h4, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases h5 : (opcode == 0b00111#5) = true
          · simp only [h5, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases h6 : (opcode == 0b00110#5) = true
            · simp only [h6, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases h7 : (opcode == 0b01000#5) = true
              · simp only [h7, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                by_cases h8 : (!u && opcode == 0b10111#5) = true
                · simp only [h8, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                  exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
                · simp [h8] at heval

def fastExecSimdTwoRegMisc (q u : Bool) (size : BitVec 2) (opcode rn rd : BitVec 5)
    (fs : FastState) : Option FastState :=
  let vn := fs.readVReg128 rn
  let esize := 8 <<< size.toNat
  let laneMask : BitVec 128 := (1#128 <<< esize) - 1#128
  if !u && opcode == 0b00000#5 && size != 0b11#2 then
    let subLanes := 64 / esize
    let m64 : BitVec 64 := (1#64 <<< esize) - 1#64
    let revDword (d : BitVec 64) : BitVec 64 :=
      fastRangeLoop 0 subLanes 0#64 fun i acc =>
        let elem := (d >>> (i * esize)) &&& m64
        acc ||| (elem <<< ((subLanes - 1 - i) * esize))
    let lo := revDword (vn.truncate 64)
    let hi := if q then revDword (vn.extractLsb' 64 64) else 0#64
    some (fs.writeVReg128 rd (hi ++ lo)).advancePC
  else if u && opcode == 0b00000#5 && size.toNat < 2 then
    let subLanes := 32 / esize
    let m32 : BitVec 64 := (1#64 <<< esize) - 1#64
    let revWord (w : BitVec 32) : BitVec 32 :=
      fastRangeLoop 0 subLanes 0#32 fun i acc =>
        let elem := (w >>> (i * esize)) &&& (m32.truncate 32)
        acc ||| (elem <<< ((subLanes - 1 - i) * esize))
    let w0 := revWord (vn.extractLsb' 0 32)
    let w1 := revWord (vn.extractLsb' 32 32)
    let w2 := if q then revWord (vn.extractLsb' 64 32) else 0#32
    let w3 := if q then revWord (vn.extractLsb' 96 32) else 0#32
    some (fs.writeVReg128 rd (w3 ++ w2 ++ w1 ++ w0)).advancePC
  else if !u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
    let res := fastMapSimdLanes q esize vn (fun a =>
      if !a.getLsbD (esize - 1) && a != 0#128 then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if u && opcode == 0b01000#5 && !(size == 0b11#2 && !q) then
    let res := fastMapSimdLanes q esize vn (fun a =>
      if !a.getLsbD (esize - 1) then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
    let res := fastMapSimdLanes q esize vn (fun a => if a == 0#128 then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if u && opcode == 0b01001#5 && !(size == 0b11#2 && !q) then
    let res := fastMapSimdLanes q esize vn (fun a =>
      if a.getLsbD (esize - 1) || a == 0#128 then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b01010#5 && !(size == 0b11#2 && !q) then
    let res := fastMapSimdLanes q esize vn (fun a =>
      if a.getLsbD (esize - 1) then laneMask else 0#128)
    some (fs.writeVReg128 rd res).advancePC
  else if u && opcode == 0b00101#5 && size == 0b00#2 then
    let raw := ~~~vn
    let res := if q then raw else (raw.truncate 64).zeroExtend 128
    some (fs.writeVReg128 rd res).advancePC
  else if !u && opcode == 0b00101#5 && size == 0b00#2 then
    let res := fastMapSimdLanes q 8 vn (fun a =>
      BitVec.ofNat 128 ((List.range 8).countP (fun i => a.getLsbD i)))
    some (fs.writeVReg128 rd res).advancePC
  else
    none

theorem fastExecSimdTwoRegMisc_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q u : Bool} {size : BitVec 2} {opcode rn rd : BitVec 5}
    (heval : fastExecSimdTwoRegMisc q u size opcode rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdTwoRegMisc q u size opcode rn rd) s) := by
  unfold fastExecSimdTwoRegMisc at heval
  simp only [fastMapSimdLanes_eq, fastRangeLoop_eq_forIn] at heval
  rw [FastState.readVReg128_eq h rn] at heval
  simp only [execInstWithSvc]
  by_cases h1 : ((!u && opcode == 0b00000#5) && size != 0b11#2) = true
  · simp only [h1, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
    exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases h2 : ((u && opcode == 0b00000#5) && decide (size.toNat < 2)) = true
    · simp only [h2, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
      exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases h3 : ((!u && opcode == 0b01000#5) && !(size == 0b11#2 && !q)) = true
      · simp only [h3, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
        exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases h4 : ((u && opcode == 0b01000#5) && !(size == 0b11#2 && !q)) = true
        · simp only [h4, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases h5 : ((!u && opcode == 0b01001#5) && !(size == 0b11#2 && !q)) = true
          · simp only [h5, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · simp only [h5, Bool.false_eq_true, ↓reduceIte] at heval ⊢
            by_cases h6 : ((u && opcode == 0b01001#5) && !(size == 0b11#2 && !q)) = true
            · simp only [h6, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
              exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
            · simp only [h6, Bool.false_eq_true, ↓reduceIte] at heval ⊢
              by_cases h7 : ((!u && opcode == 0b01010#5) && !(size == 0b11#2 && !q)) = true
              · simp only [h7, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
              · simp only [h7, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                by_cases h8 : ((u && opcode == 0b00101#5) && size == 0b00#2) = true
                · simp only [h8, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                  exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
                · simp only [h8, Bool.false_eq_true, ↓reduceIte] at heval ⊢
                  by_cases h9 : ((!u && opcode == 0b00101#5) && size == 0b00#2) = true
                  · simp only [h9, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
                    exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
                  · simp [h9] at heval

def fastExecSimdAcrossLanes (q u : Bool) (size : BitVec 2) (opcode rn rd : BitVec 5)
    (fs : FastState) : Option FastState :=
  let vn := fs.readVReg128 rn
  let esize := 8 <<< size.toNat
  let numLanes := (if q then 128 else 64) / esize
  let mask : BitVec 128 := (1#128 <<< esize) - 1#128
  if u && opcode == 0b01010#5 && !(size == 0b10#2 && !q) && size != 0b11#2 then
    let maxVal : BitVec 128 :=
      fastRangeLoop 0 numLanes 0#128 fun i cur =>
        if BitVec.ult cur ((vn >>> (i * esize)) &&& mask) then
          (vn >>> (i * esize)) &&& mask
        else cur
    some (fs.writeVReg128 rd maxVal).advancePC
  else if opcode == 0b01100#5 || opcode == 0b11100#5 ||
      opcode == 0b01111#5 || opcode == 0b11111#5 then
    none
  else if (size == 0b10#2 && !q) || size == 0b11#2 then
    none
  else if opcode == 0b00011#5 || (!u && opcode == 0b11011#5) then
    let long := opcode == 0b00011#5
    let outBits := if long then 2 * esize else esize
    let outMask : BitVec 128 := (1#128 <<< outBits) - 1#128
    let signBit : BitVec 128 := 1#128 <<< (esize - 1)
    let total : BitVec 128 :=
      fastRangeLoop 0 numLanes 0#128 fun i acc =>
        let lane := (vn >>> (i * esize)) &&& mask
        let ext := if long && !u && (lane &&& signBit) != 0#128 then lane ||| ~~~mask else lane
        acc + ext
    some (fs.writeVReg128 rd (total &&& outMask)).advancePC
  else if opcode == 0b01010#5 || opcode == 0b11010#5 then
    let isMin := opcode == 0b11010#5
    let signBit : BitVec 128 := 1#128 <<< (esize - 1)
    let key (x : BitVec 128) : BitVec 128 := if u then x else x ^^^ signBit
    let best : BitVec 128 :=
      fastRangeLoop 1 numLanes (vn &&& mask) fun i cur =>
        let lane := (vn >>> (i * esize)) &&& mask
        if (if isMin then BitVec.ult (key lane) (key cur) else BitVec.ult (key cur) (key lane)) then
          lane
        else cur
    some (fs.writeVReg128 rd best).advancePC
  else
    none

theorem fastExecSimdAcrossLanes_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q u : Bool} {size : BitVec 2} {opcode rn rd : BitVec 5}
    (heval : fastExecSimdAcrossLanes q u size opcode rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdAcrossLanes q u size opcode rn rd) s) := by
  unfold fastExecSimdAcrossLanes at heval
  simp only [fastRangeLoop_eq_forIn, pure_yield_ite] at heval
  rw [FastState.readVReg128_eq h rn] at heval
  simp only [execInstWithSvc]
  by_cases h1 : (((u && opcode == 0b01010#5) && !(size == 0b10#2 && !q)) &&
      size != 0b11#2) = true
  · simp only [h1, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
    exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at heval ⊢
    by_cases h2 : (((opcode == 0b01100#5 || opcode == 0b11100#5) ||
        opcode == 0b01111#5) || opcode == 0b11111#5) = true
    · simp [h2] at heval
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at heval ⊢
      by_cases h3 : ((size == 0b10#2 && !q) || size == 0b11#2) = true
      · simp [h3] at heval
      · simp only [h3, Bool.false_eq_true, ↓reduceIte] at heval ⊢
        by_cases h4 : (opcode == 0b00011#5 || (!u && opcode == 0b11011#5)) = true
        · simp only [h4, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
          exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at heval ⊢
          by_cases h5 : (opcode == 0b01010#5 || opcode == 0b11010#5) = true
          · simp only [h5, ↓reduceIte, Option.some.injEq] at heval ⊢; subst heval
            exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)
          · simp [h5] at heval

def fastExecSimdPmull (q is64 : Bool) (rm rn rd : BitVec 5) (fs : FastState) : Option FastState :=
  some (fs.writeVReg128 rd
    (evalPmull q is64 (fs.readVReg128 rn) (fs.readVReg128 rm))).advancePC

theorem fastExecSimdPmull_sound {fs fs' : FastState} {s : State} (h : fs.Agrees s)
    (svc : State → State) {q is64 : Bool} {rm rn rd : BitVec 5}
    (heval : fastExecSimdPmull q is64 rm rn rd fs = some fs') :
    fs'.Agrees (execInstWithSvc svc (.simdPmull q is64 rm rn rd) s) := by
  simp only [fastExecSimdPmull, Option.some.injEq] at heval
  subst heval
  simp only [execInstWithSvc, FastState.readVReg128_eq h rn, FastState.readVReg128_eq h rm]
  exact FastState.advancePC_agrees (FastState.writeVReg128_agrees h rd _)

/-- Evaluates a single AArch64 instruction on `FastState` without closure allocation. -/
def fastEvalInst (inst : Arm64.Instr) (fs : FastState) : Option FastState :=
  match inst with
  | .fmovGprVec sf ftype rmode opcode rn rd =>
    fastExecFmovGprVec sf ftype rmode opcode rn rd fs
  | .fpCompare ftype rm op rn opcode2 =>
    fastExecFpCompare ftype rm op rn opcode2 fs
  | .simdImmShift q op immh immb opc rn rd =>
    fastExecSimdImmShift q op immh immb opc rn rd fs
  | .simdInsDup q op imm5 imm4 rn rd =>
    fastExecSimdInsDup q op imm5 imm4 rn rd fs
  | .simdThreeSame q u size rm opcode rn rd =>
    fastExecSimdThreeSame q u size rm opcode rn rd fs
  | .simdTwoRegMisc q u size opcode rn rd =>
    fastExecSimdTwoRegMisc q u size opcode rn rd fs
  | .simdAcrossLanes q u size opcode rn rd =>
    fastExecSimdAcrossLanes q u size opcode rn rd fs
  | .simdPmull q is64 rm rn rd =>
    fastExecSimdPmull q is64 rm rn rd fs
  | _ =>
    fastEvalScalar inst fs

theorem fastEvalInst_sound {prog : Arm64.Program}
    (hsvc : prog.svc = Arm64.Syscall.standard)
    {inst : Arm64.Instr} {fs fs' : FastState} {s : Arm64.State}
    (hag : fs.Agrees s)
    (heval : fastEvalInst inst fs = some fs') :
    fs'.Agrees (prog.evalInst inst s) := by
  cases inst with
  | fmovGprVec sf ftype rmode opcode rn rd =>
    exact fastExecFmovGprVec_sound hag (evalSvc prog.svc) heval
  | fpCompare ftype rm op rn opcode2 =>
    exact fastExecFpCompare_sound hag (evalSvc prog.svc) heval
  | simdImmShift q op immh immb opc rn rd =>
    exact fastExecSimdImmShift_sound hag (evalSvc prog.svc) heval
  | simdInsDup q op imm5 imm4 rn rd =>
    exact fastExecSimdInsDup_sound hag (evalSvc prog.svc) heval
  | simdThreeSame q u size rm opcode rn rd =>
    exact fastExecSimdThreeSame_sound hag (evalSvc prog.svc) heval
  | simdTwoRegMisc q u size opcode rn rd =>
    exact fastExecSimdTwoRegMisc_sound hag (evalSvc prog.svc) heval
  | simdAcrossLanes q u size opcode rn rd =>
    exact fastExecSimdAcrossLanes_sound hag (evalSvc prog.svc) heval
  | simdPmull q is64 rm rn rd =>
    exact fastExecSimdPmull_sound hag (evalSvc prog.svc) heval
  | _ =>
    exact fastEvalScalar_sound hsvc hag heval

end Symbolic.BugInjection.Proofs.CliExec.FastEval
