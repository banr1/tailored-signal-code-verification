/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Block Symbolic Expressions, Cells, and State

Defines the symbolic value language (`Env`, `SExpr`, `SCond`, `VExpr`), spatial memory cells
(`Cell`, `cellsProp`), and block machine state (`SState`) for the reflective block executor
`ProofLib.SymBlock`, together with their concrete denotations and commuting lemmas.
-/

@[expose] public section

namespace ProofLib.SymBlock

open Arm64

/-! ## Environments and symbolic expressions -/

/-- Width of a non-doubleword memory cell (`↦₈`, `↦₁₆`, `↦₃₂`, or `↦₁₂₈`). -/
inductive CW where
  | b8
  | b16
  | b32
  | b128
  deriving DecidableEq, Repr, Inhabited

/-- Bit width of a cell width. -/
@[reducible] def CW.bits : CW → Nat
  | .b8 => 8
  | .b16 => 16
  | .b32 => 32
  | .b128 => 128

/-- Byte width of a cell width. -/
def CW.bytes : CW → Nat
  | .b8 => 1
  | .b16 => 2
  | .b32 => 4
  | .b128 => 16

/-- `2 ^ w.bits - 1` as a 64-bit mask (for sub-doubleword widths). -/
def CW.mask : CW → BitVec 64
  | .b8 => 0xff#64
  | .b16 => 0xffff#64
  | .b32 => 0xffffffff#64
  | .b128 => 0xffffffffffffffff#64

/-- The `MemWidth` of a sub-doubleword narrow access (`none` for `b128`). -/
def CW.memWidth? : CW → Option MemWidth
  | .b8 => some .B8
  | .b16 => some .H16
  | .b32 => some .W32
  | .b128 => none

/-- Convert a sub-doubleword `MemWidth` (`B8`, `H16`, `W32`) to `CW`. -/
def CW.ofMemWidth? : MemWidth → Option CW
  | .B8 => some .b8
  | .H16 => some .b16
  | .W32 => some .b32
  | .X64 => none

/-- Symbolic environment: 64-bit leaves, opaque spatial atoms, 8/16/32/128-bit cell leaves,
    and initial `TPIDR_EL0`. -/
structure Env where
  v : List (BitVec 64)
  p : List SepProp := []
  v8 : List (BitVec 8) := []
  v16 : List (BitVec 16) := []
  v32 : List (BitVec 32) := []
  v128 : List (BitVec 128) := []
  tpidr : BitVec 64 := 0#64

/-- 64-bit leaf `i` (zero if out of range). -/
@[reducible] def Env.get (env : Env) (i : Nat) : BitVec 64 := env.v.getD i 0#64

/-- 128-bit leaf `i` (zero if out of range). -/
@[reducible] def Env.get128 (env : Env) (i : Nat) : BitVec 128 := env.v128.getD i 0#128

/-- Non-doubleword leaf `i` of width `w` (zero if out of range). -/
@[reducible] def Env.getN (env : Env) : (w : CW) → Nat → BitVec w.bits
  | .b8, i => env.v8.getD i 0#8
  | .b16, i => env.v16.getD i 0#16
  | .b32, i => env.v32.getD i 0#32
  | .b128, i => env.get128 i

/-- Pure 1-source data-processing value (`RBIT`, `REV16`, `REV32`, `REV`, `CLZ`, `CLS`) at width `w`
    on operand `v = s.readReg w rn`. -/
@[wp_norm, reducible] def evalDataProc1Val (w : Width) (op : DataProc1Op) (v : BitVec 64) : BitVec 64 :=
  match w, op with
  | .W32, .RBIT  => (reverseBits (v.truncate 32)).zeroExtend 64
  | .W64, .RBIT  => reverseBits v
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

/-- Pure 3-source data-processing value (`MADD`, `MSUB`, `SMADDL`, `SMSUBL`, `UMADDL`, `UMSUBL`,
    `SMULH`, `UMULH`) at width `w` on 64-bit register values `vn, vm, va`. -/
@[wp_norm, reducible] def evalDataProc3Val (w : Width) (op : DataProc3Op) (vn vm va : BitVec 64) : BitVec 64 :=
  match op with
  | .MADD =>
    match w with
    | .W32 => (va.truncate 32 + vn.truncate 32 * vm.truncate 32).zeroExtend 64
    | .W64 => va + vn * vm
  | .MSUB =>
    match w with
    | .W32 => (va.truncate 32 - vn.truncate 32 * vm.truncate 32).zeroExtend 64
    | .W64 => va - vn * vm
  | .SMADDL =>
    let n64 := (vn.truncate 32).signExtend 64
    let m64 := (vm.truncate 32).signExtend 64
    va + n64 * m64
  | .SMSUBL =>
    let n64 := (vn.truncate 32).signExtend 64
    let m64 := (vm.truncate 32).signExtend 64
    va - n64 * m64
  | .UMADDL =>
    let n64 := (vn.truncate 32).zeroExtend 64
    let m64 := (vm.truncate 32).zeroExtend 64
    va + n64 * m64
  | .UMSUBL =>
    let n64 := (vn.truncate 32).zeroExtend 64
    let m64 := (vm.truncate 32).zeroExtend 64
    va - n64 * m64
  | .SMULH =>
    let n128 := vn.signExtend 128
    let m128 := vm.signExtend 128
    ((n128 * m128) >>> 64).truncate 64
  | .UMULH =>
    let n128 := vn.zeroExtend 128
    let m128 := vm.zeroExtend 128
    ((n128 * m128) >>> 64).truncate 64

mutual
  /-- Symbolic 64-bit expressions. Nodes mirror the evaluation helpers of the ISA model
      (`evalAddSub`, `evalLogical`, `shiftVal`, `evalBitfield`, `extendVal`, `evalDataProc1Val`,
      `evalDataProc3Val`) so the denotation of each node is literally the trusted semantics. -/
  inductive SExpr where
    | var (i : Nat)
    | const (v : BitVec 64)
    | add (a b : SExpr)
    | sub (a b : SExpr)
    | and (a b : SExpr)
    | or (a b : SExpr)
    | xor (a b : SExpr)
    | mul (a b : SExpr)
    | shl (a : SExpr) (k : Nat)
    | lshr (a : SExpr) (k : Nat)
    | shlBV (a b : SExpr)
    | lshrBV (a b : SExpr)
    | zext32 (a : SExpr)
    | sext (bits : Nat) (a : SExpr)
    | extendVal (w : Width) (a : SExpr) (ext : ExtendType) (amount : Nat)
    | addSub (w : Width) (op : AddSubOp) (a b : SExpr)
    | logical (w : Width) (op : LogicalOp) (a b : SExpr)
    | shiftVal (w : Width) (a : SExpr) (op : ShiftType) (k : Nat)
    | bitfield (w : Width) (op : BitfieldOp) (d s : SExpr) (immr imms : Nat)
    | dataProc1 (w : Width) (op : DataProc1Op) (a : SExpr)
    | dataProc3 (w : Width) (op : DataProc3Op) (rn rm ra : SExpr)
    /-- Zero-extended narrow leaf. -/
    | zleaf (w : CW) (i : Nat)
    /-- Low 64 bits of 128-bit leaf `i`. -/
    | lo128 (i : Nat)
    /-- High 64 bits of 128-bit leaf `i`. -/
    | hi128 (i : Nat)
    /-- Initial `TPIDR_EL0` leaf. -/
    | tpidr0
    /-- 4 KiB page address `Obj.pageOf a`. -/
    | pageOf (a : SExpr)
    /-- Low 12-bit page offset `Obj.lo12Of a`. -/
    | lo12Of (a : SExpr)
    /-- Conditional select `if c then t else f`. -/
    | ite (c : SCond) (t f : SExpr)
    deriving DecidableEq, Repr, Inhabited

  /-- Symbolic boolean condition over `SExpr`s (for branches and `CSEL`/`CSINC`/`CSINV`/`CSNEG`). -/
  inductive SCond where
    | tt
    | ff
    | eq64 (a b : SExpr)
    | eq32 (a b : SExpr)
    | ult64 (a b : SExpr)
    | ule64 (a b : SExpr)
    | slt64 (a b : SExpr)
    | sle64 (a b : SExpr)
    | ult32 (a b : SExpr)
    | ule32 (a b : SExpr)
    | slt32 (a b : SExpr)
    | sle32 (a b : SExpr)
    | msb32 (a : SExpr)
    | msb64 (a : SExpr)
    | addC32 (a b : SExpr)
    | addC64 (a b : SExpr)
    | addV32 (a b : SExpr)
    | addV64 (a b : SExpr)
    | subV32 (a b : SExpr)
    | subV64 (a b : SExpr)
    | bit (a : SExpr) (k : Nat)
    | not (c : SCond)
    | and (a b : SCond)
    | or (a b : SCond)
    deriving DecidableEq, Repr, Inhabited
end

mutual
  /-- Denotation of a symbolic 64-bit expression. -/
  def SExpr.eval (env : Env) : SExpr → BitVec 64
    | .var i => env.get i
    | .const v => v
    | .add a b => a.eval env + b.eval env
    | .sub a b => a.eval env - b.eval env
    | .and a b => a.eval env &&& b.eval env
    | .or a b => a.eval env ||| b.eval env
    | .xor a b => a.eval env ^^^ b.eval env
    | .mul a b => a.eval env * b.eval env
    | .shl a k => a.eval env <<< k
    | .lshr a k => a.eval env >>> k
    | .shlBV a b => a.eval env <<< b.eval env
    | .lshrBV a b => a.eval env >>> b.eval env
    | .zext32 a => ((a.eval env).truncate 32).zeroExtend 64
    | .sext bits a => ((a.eval env).truncate bits).signExtend 64
    | .extendVal w a ext amount => Arm64.extendVal w (a.eval env) ext amount
    | .addSub w op a b => (evalAddSub w op (a.eval env) (b.eval env) none).1
    | .logical w op a b => (evalLogical w op (a.eval env) (b.eval env) PState.zero).1
    | .shiftVal w a op k => Arm64.shiftVal w (a.eval env) op k
    | .bitfield w op d s immr imms => evalBitfield w op (d.eval env) (s.eval env) immr imms
    | .dataProc1 w op a => evalDataProc1Val w op (a.eval env)
    | .dataProc3 w op rn rm ra => evalDataProc3Val w op (rn.eval env) (rm.eval env) (ra.eval env)
    | .zleaf w i => (env.getN w i).zeroExtend 64
    | .lo128 i => (env.get128 i).extractLsb' 0 64
    | .hi128 i => (env.get128 i).extractLsb' 64 64
    | .tpidr0 => env.tpidr
    | .pageOf a => Obj.pageOf (a.eval env)
    | .lo12Of a => Obj.lo12Of (a.eval env)
    | .ite c t f => if c.eval env then t.eval env else f.eval env

  /-- Denotation of a symbolic boolean condition. -/
  def SCond.eval (env : Env) : SCond → Bool
    | .tt => true
    | .ff => false
    | .eq64 a b => a.eval env == b.eval env
    | .eq32 a b => (a.eval env).truncate 32 == (b.eval env).truncate 32
    | .ult64 a b => BitVec.ult (a.eval env) (b.eval env)
    | .ule64 a b => BitVec.ule (a.eval env) (b.eval env)
    | .slt64 a b => BitVec.slt (a.eval env) (b.eval env)
    | .sle64 a b => BitVec.sle (a.eval env) (b.eval env)
    | .ult32 a b => BitVec.ult ((a.eval env).truncate 32) ((b.eval env).truncate 32)
    | .ule32 a b => BitVec.ule ((a.eval env).truncate 32) ((b.eval env).truncate 32)
    | .slt32 a b => BitVec.slt ((a.eval env).truncate 32) ((b.eval env).truncate 32)
    | .sle32 a b => BitVec.sle ((a.eval env).truncate 32) ((b.eval env).truncate 32)
    | .msb32 a => ((a.eval env).truncate 32).msb
    | .msb64 a => (a.eval env).msb
    | .addC32 a b => (AddWithCarry32 ((a.eval env).truncate 32) ((b.eval env).truncate 32) false).2.c
    | .addC64 a b => (AddWithCarry64 (a.eval env) (b.eval env) false).2.c
    | .addV32 a b => (AddWithCarry32 ((a.eval env).truncate 32) ((b.eval env).truncate 32) false).2.v
    | .addV64 a b => (AddWithCarry64 (a.eval env) (b.eval env) false).2.v
    | .subV32 a b => (AddWithCarry32 ((a.eval env).truncate 32) (~~~((b.eval env).truncate 32)) true).2.v
    | .subV64 a b => (AddWithCarry64 (a.eval env) (~~~(b.eval env)) true).2.v
    | .bit a k => (a.eval env).getLsbD k
    | .not c => !(c.eval env)
    | .and a b => (a.eval env) && (b.eval env)
    | .or a b => (a.eval env) || (b.eval env)
end

/-! ### Smart constructors (light normalization performed inside the checker) -/

/-- `e + c` written as `e - (-c)` when `c` is negative as a signed 64-bit value, and `e` when
    `c = 0`. This matches the way specifications write frame-relative addresses (`sp - 16#64`). -/
def mkOff (e : SExpr) (c : BitVec 64) : SExpr :=
  if c = 0#64 then e
  else if c.toNat < 2 ^ 63 then .add e (.const c)
  else .sub e (.const (-c))

theorem mkOff_eval (env : Env) (e : SExpr) (c : BitVec 64) :
    (mkOff e c).eval env = e.eval env + c := by
  unfold mkOff
  split
  · subst_vars; simp
  · split
    · rfl
    · simp only [SExpr.eval, BitVec.sub_eq_add_neg, BitVec.neg_neg]

/-- `a + b` with constant folding, `(e ± c₁) + c₂ ↦ e ± c`, and `pageOf a + lo12Of a ↦ a`. -/
def mkAdd : SExpr → SExpr → SExpr
  | .const x, .const y => .const (x + y)
  | .add e (.const x), .const y => mkOff e (x + y)
  | .sub e (.const x), .const y => mkOff e (y - x)
  | a, .const y => mkOff a y
  | .pageOf a, .lo12Of b => if a = b then a else .add (.pageOf a) (.lo12Of b)
  | .add (.pageOf a) idx, .lo12Of b => if a = b then .add a idx else .add (.add (.pageOf a) idx) (.lo12Of b)
  | a, b => .add a b

theorem mkAdd_eval (env : Env) (a b : SExpr) :
    (mkAdd a b).eval env = a.eval env + b.eval env := by
  unfold mkAdd
  split
  · rfl
  · simp only [SExpr.eval, mkOff_eval, BitVec.add_assoc]
  · simp only [SExpr.eval, mkOff_eval]
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm _ (-_)]
  · simp only [SExpr.eval, mkOff_eval]
  · split
    · subst_vars; simp only [SExpr.eval, Obj.pageOf_add_lo12Of]
    · rfl
  · split
    · subst_vars; simp only [SExpr.eval, Obj.pageOf_add_idx_add_lo12Of]
    · rfl
  · rfl

/-- `a - b` with `e - c ↦ mkAdd e (-c)`. -/
def mkSub : SExpr → SExpr → SExpr
  | a, .const y => mkAdd a (.const (-y))
  | a, b => .sub a b

theorem mkSub_eval (env : Env) (a b : SExpr) :
    (mkSub a b).eval env = a.eval env - b.eval env := by
  unfold mkSub
  split
  · rw [mkAdd_eval]; simp only [SExpr.eval, BitVec.sub_eq_add_neg]
  · rfl

/-- `-e` with constant folding. -/
def mkNeg : SExpr → SExpr
  | .const c => .const (-c)
  | e => .sub (.const 0#64) e

theorem mkNeg_eval (env : Env) (e : SExpr) :
    (mkNeg e).eval env = -e.eval env := by
  unfold mkNeg
  split
  · rfl
  · simp only [SExpr.eval, BitVec.zero_sub]

/-- `((e.truncate 32).zeroExtend 64)`, idempotent on already-32-bit expressions and folding
    constants. -/
def mkZext32 : SExpr → SExpr
  | .const v => .const ((v.truncate 32).zeroExtend 64)
  | .zext32 a => .zext32 a
  | .zleaf .b8 i => .zleaf .b8 i
  | .zleaf .b16 i => .zleaf .b16 i
  | .zleaf .b32 i => .zleaf .b32 i
  | a => .zext32 a

theorem mkZext32_eval (env : Env) (e : SExpr) :
    (mkZext32 e).eval env = ((e.eval env).truncate 32).zeroExtend 64 := by
  unfold mkZext32
  split
  · rfl
  · simp only [SExpr.eval]; bv_bits
  · simp only [SExpr.eval, CW.bits]; bv_bits
  · simp only [SExpr.eval, CW.bits]; bv_bits
  · simp only [SExpr.eval, CW.bits]; bv_bits
  · rfl

/-- `((e.truncate bits).signExtend 64)`, folding constants. -/
def mkSext (bits : Nat) : SExpr → SExpr
  | .const v => .const ((v.truncate bits).signExtend 64)
  | a => .sext bits a

theorem mkSext_eval (env : Env) (bits : Nat) (e : SExpr) :
    (mkSext bits e).eval env = ((e.eval env).truncate bits).signExtend 64 := by
  unfold mkSext
  split <;> rfl

/-- `Arm64.extendVal w a ext amount`, simplifying common 64-bit index extensions (`UXTX`/`SXTX`,
    `UXTW`, `SXTW`) and folding constants. -/
def mkExtendVal (w : Width) (a : SExpr) (ext : ExtendType) (amount : Nat) : SExpr :=
  match a with
  | .const v => .const (Arm64.extendVal w v ext amount)
  | _ =>
    match w with
    | .W64 =>
      match ext with
      | .UXTX => if amount = 0 then a else .shl a amount
      | .SXTX => if amount = 0 then a else .shl a amount
      | .UXTW =>
        let z := mkZext32 a
        if amount = 0 then z else .shl z amount
      | .SXTW =>
        let sx := mkSext 32 a
        if amount = 0 then sx else .shl sx amount
      | _ => .extendVal w a ext amount
    | .W32 => .extendVal w a ext amount

theorem mkExtendVal_eval (env : Env) (w : Width) (a : SExpr) (ext : ExtendType) (amount : Nat) :
    (mkExtendVal w a ext amount).eval env = Arm64.extendVal w (a.eval env) ext amount := by
  by_cases hc : ∃ v, a = .const v
  · obtain ⟨v, rfl⟩ := hc; rfl
  · have hnc : mkExtendVal w a ext amount =
        match w with
        | .W64 =>
          match ext with
          | .UXTX => if amount = 0 then a else .shl a amount
          | .SXTX => if amount = 0 then a else .shl a amount
          | .UXTW =>
            let z := mkZext32 a
            if amount = 0 then z else .shl z amount
          | .SXTW =>
            let sx := mkSext 32 a
            if amount = 0 then sx else .shl sx amount
          | _ => .extendVal w a ext amount
        | .W32 => .extendVal w a ext amount := by
      cases a <;> simp_all [mkExtendVal] <;> rfl
    rw [hnc]
    cases w with
    | W32 => rfl
    | W64 =>
      cases ext
      · rfl
      · rfl
      · dsimp only
        split <;> subst_vars <;> simp only [SExpr.eval, mkZext32_eval, Arm64.extendVal]
        bv_bits
      · dsimp only
        split <;> subst_vars <;> simp only [SExpr.eval, Arm64.extendVal]
        bv_bits
      · rfl
      · rfl
      · dsimp only
        split <;> subst_vars <;> simp only [SExpr.eval, mkSext_eval, Arm64.extendVal]
        bv_bits
      · dsimp only
        split <;> subst_vars <;> simp only [SExpr.eval, Arm64.extendVal]
        bv_bits

/-- `(evalAddSub w op a b none).1`, simplified to `+` / `-` at width 64. -/
def mkAddSub : Width → AddSubOp → SExpr → SExpr → SExpr
  | .W64, .ADD, a, b => mkAdd a b
  | .W64, .ADDS, a, b => mkAdd a b
  | .W64, .SUB, a, b => mkSub a b
  | .W64, .SUBS, a, b => mkSub a b
  | w, op, a, b => .addSub w op a b

theorem mkAddSub_eval (env : Env) (w : Width) (op : AddSubOp) (a b : SExpr) :
    (mkAddSub w op a b).eval env = (evalAddSub w op (a.eval env) (b.eval env) none).1 := by
  unfold mkAddSub
  split <;>
    simp only [mkAdd_eval, mkSub_eval, SExpr.eval, evalAddSub_w64_add, evalAddSub_w64_adds,
      evalAddSub_w64_sub, evalAddSub_w64_subs]

/-- The result of `evalLogical` does not depend on the incoming flags. -/
theorem evalLogical_fst_psOld (w : Width) (op : LogicalOp) (x y : BitVec 64) (ps : PState) :
    (evalLogical w op x y ps).1 = (evalLogical w op x y PState.zero).1 := by
  cases w <;> rfl

/-- The updated flags of `evalLogical` do not depend on the incoming flags. -/
theorem evalLogical_snd_psOld (w : Width) (op : LogicalOp) (x y : BitVec 64) (ps : PState) :
    (evalLogical w op x y ps).2 = (evalLogical w op x y PState.zero).2 := by
  cases w <;> rfl

/-- `(evalLogical w op a b _).1`, folding constants and simplifying `&&&` / `|||` / `^^^` at width 64. -/
def mkLogical : Width → LogicalOp → SExpr → SExpr → SExpr
  | w, op, .const a, .const b => .const ((evalLogical w op a b PState.zero).1)
  | .W64, .AND, a, b => .and a b
  | .W64, .ORR, .const 0, b => b
  | .W64, .ORR, a, b => .or a b
  | .W64, .EOR, a, b => .xor a b
  | w, op, a, b => .logical w op a b

theorem mkLogical_eval (env : Env) (w : Width) (op : LogicalOp) (a b : SExpr) :
    (mkLogical w op a b).eval env = (evalLogical w op (a.eval env) (b.eval env) PState.zero).1 := by
  unfold mkLogical
  split
  · rfl
  · simp [SExpr.eval, evalLogical]
  · simp [SExpr.eval, evalLogical]
  · simp [SExpr.eval, evalLogical]
  · simp [SExpr.eval, evalLogical]
  · rfl

/-- `shiftVal w a op k`, folding constants and simplifying `<<<` / `>>>` at width 64 and `.LSL 0` at width 32. -/
def mkShiftVal : Width → SExpr → ShiftType → Nat → SExpr
  | w, .const a, op, k => .const (Arm64.shiftVal w a op k)
  | .W64, a, .LSL, 0 => a
  | .W64, a, .LSL, k => .shl a (k % 64)
  | .W64, a, .LSR, k => .lshr a (k % 64)
  | .W32, a, .LSL, 0 => mkZext32 a
  | w, a, op, k => .shiftVal w a op k

theorem mkShiftVal_eval (env : Env) (w : Width) (a : SExpr) (op : ShiftType) (k : Nat) :
    (mkShiftVal w a op k).eval env = Arm64.shiftVal w (a.eval env) op k := by
  unfold mkShiftVal
  split
  · rfl
  · simp [shiftVal, shift64]
  · simp [SExpr.eval, shiftVal, shift64]
  · simp [SExpr.eval, shiftVal, shift64]
  · simp only [mkZext32_eval, shiftVal, shift32]; bv_bits
  · rfl

/-- `MOVK` halfword insertion, folding constants when `old` is `.const`. -/
def mkMovk (old : SExpr) (imm16 : BitVec 16) (hw : Nat) : SExpr :=
  let shifted : BitVec 64 := (imm16.zeroExtend 64) <<< hw
  let clearMask : BitVec 64 := ~~~(0xffff#64 <<< hw)
  match old with
  | .const c => .const ((c &&& clearMask) ||| shifted)
  | _ => .or (.and old (.const clearMask)) (.const shifted)

theorem mkMovk_eval (env : Env) (old : SExpr) (imm16 : BitVec 16) (hw : Nat) :
    (mkMovk old imm16 hw).eval env =
      ((old.eval env &&& ~~~(0xffff#64 <<< hw)) ||| ((imm16.zeroExtend 64) <<< hw)) := by
  unfold mkMovk
  split <;> rfl

/-- `evalDataProc3Val w op rn rm ra`, simplifying 64-bit `MADD` / `MSUB` to `+` / `-` / `*`. -/
def mkDataProc3 (w : Width) (op : DataProc3Op) (rn rm ra : SExpr) : SExpr :=
  match w, op, ra with
  | .W64, .MADD, .const 0#64 => .mul rn rm
  | .W64, .MADD, _ => .add ra (.mul rn rm)
  | .W64, .MSUB, _ => .sub ra (.mul rn rm)
  | _, _, _ => .dataProc3 w op rn rm ra

theorem mkDataProc3_eval (env : Env) (w : Width) (op : DataProc3Op) (rn rm ra : SExpr) :
    (mkDataProc3 w op rn rm ra).eval env =
      evalDataProc3Val w op (rn.eval env) (rm.eval env) (ra.eval env) := by
  unfold mkDataProc3
  split
  · simp [SExpr.eval, evalDataProc3Val]
  · simp [SExpr.eval, evalDataProc3Val]
  · simp [SExpr.eval, evalDataProc3Val]
  · rfl

/-! ## 128-bit SIMD values and spatial cells -/

/-- Symbolic 128-bit SIMD/FP value. -/
inductive VExpr where
  | var (i : Nat)
  | const (v : BitVec 128)
  | pair64 (hi lo : SExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Denotation of a symbolic 128-bit value. -/
def VExpr.eval (env : Env) : VExpr → BitVec 128
  | .var i => env.get128 i
  | .const v => v
  | .pair64 hi lo => hi.eval env ++ lo.eval env

/-- Low 64 bits of a symbolic 128-bit value. -/
def VExpr.lo64 : VExpr → SExpr
  | .var i => .lo128 i
  | .const v => .const (v.extractLsb' 0 64)
  | .pair64 _ lo => lo

/-- High 64 bits of a symbolic 128-bit value. -/
def VExpr.hi64 : VExpr → SExpr
  | .var i => .hi128 i
  | .const v => .const (v.extractLsb' 64 64)
  | .pair64 hi _ => hi

theorem VExpr.lo64_eval (env : Env) (v : VExpr) :
    (v.lo64).eval env = (v.eval env).extractLsb' 0 64 := by
  cases v with
  | var _ => rfl
  | const _ => rfl
  | pair64 hi lo =>
    simp only [VExpr.lo64, VExpr.eval]
    bv_bits

theorem VExpr.hi64_eval (env : Env) (v : VExpr) :
    (v.hi64).eval env = (v.eval env).extractLsb' 64 64 := by
  cases v with
  | var _ => rfl
  | const _ => rfl
  | pair64 hi lo =>
    simp only [VExpr.hi64, VExpr.eval]
    bv_bits

/-- Value of a non-doubleword cell: a native-width leaf, the low bits of a 64-bit expression,
    or a 128-bit SIMD expression. -/
inductive NVal where
  | leaf (i : Nat)
  | trunc (e : SExpr)
  | v128 (v : VExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Denotation of a non-doubleword value at width `w`. -/
def NVal.eval (env : Env) (w : CW) : NVal → BitVec w.bits
  | .leaf i => env.getN w i
  | .trunc e => (e.eval env).truncate w.bits
  | .v128 v =>
    match w with
    | .b8 => (v.eval env).truncate 8
    | .b16 => (v.eval env).truncate 16
    | .b32 => (v.eval env).truncate 32
    | .b128 => v.eval env

/-- Convert a `.b128` cell value to a `VExpr`. -/
def NVal.toVExpr : NVal → VExpr
  | .leaf i => .var i
  | .trunc e => .pair64 (.const 0#64) e
  | .v128 v => v

theorem NVal.toVExpr_eval (env : Env) (v : NVal) :
    (v.toVExpr).eval env = v.eval env .b128 := by
  cases v with
  | leaf _ => rfl
  | trunc e =>
    simp only [NVal.toVExpr, VExpr.eval, NVal.eval, SExpr.eval, CW.bits]
    bv_bits
  | v128 _ => rfl

/-- Smart narrow-value constructor: collapses `(x.zeroExtend 64).truncate w.bits` back to
    the native leaf `x` when `w` matches the leaf's width (`w ≠ .b128`), and collapses
    `((x.truncate 32).zeroExtend 64).truncate 32` to `x.truncate 32`. -/
def mkTrunc (w : CW) : SExpr → NVal
  | .zleaf w' i => if w == w' && w != .b128 then .leaf i else .trunc (.zleaf w' i)
  | .zext32 e => if w == .b32 then .trunc e else .trunc (.zext32 e)
  | e => .trunc e

theorem mkTrunc_eval (env : Env) (w : CW) (e : SExpr) :
    (mkTrunc w e).eval env w = (e.eval env).truncate w.bits := by
  unfold mkTrunc
  split
  · rename_i w' i
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
      rcases h with ⟨rfl, hw⟩
      simp only [NVal.eval, SExpr.eval]
      cases w with
      | b8 =>
        have h8 : ∀ (x : BitVec 8), x = (x.zeroExtend 64).truncate 8 := fun x => by bv_bits
        exact h8 _
      | b16 =>
        have h16 : ∀ (x : BitVec 16), x = (x.zeroExtend 64).truncate 16 := fun x => by bv_bits
        exact h16 _
      | b32 =>
        have h32 : ∀ (x : BitVec 32), x = (x.zeroExtend 64).truncate 32 := fun x => by bv_bits
        exact h32 _
      | b128 => simp at hw
    · rfl
  · rename_i e'
    split
    · rename_i h
      simp only [beq_iff_eq] at h
      subst h
      simp only [NVal.eval, SExpr.eval, CW.bits]
      bv_bits
    · rfl
  · rfl

/-- The zero-extension of a narrow value as a 64-bit expression. -/
def NVal.zext (w : CW) : NVal → SExpr
  | .leaf i => .zleaf w i
  | .trunc e => .and e (.const w.mask)
  | .v128 v => .and v.lo64 (.const w.mask)

theorem NVal.zext_eval (env : Env) (w : CW) (v : NVal) :
    (v.zext w).eval env = (v.eval env w).zeroExtend 64 := by
  cases v with
  | leaf i => rfl
  | trunc e =>
    simp only [NVal.zext, NVal.eval, SExpr.eval]
    cases w <;> simp only [CW.mask, CW.bits] <;> bv_bits
  | v128 ve =>
    simp only [NVal.zext, NVal.eval, SExpr.eval, VExpr.lo64_eval]
    cases w <;> simp only [CW.mask, CW.bits] <;> bv_bits

/-- The sign-extension of a sub-doubleword narrow value (`w ∈ {.b8, .b16, .b32}`) to 64 bits. -/
def NVal.sext (w : CW) : NVal → SExpr
  | .leaf i => mkSext w.bits (.zleaf w i)
  | .trunc e => mkSext w.bits e
  | .v128 ve => mkSext w.bits ve.lo64

theorem NVal.sext_eval (env : Env) (w : CW) (v : NVal) :
    (v.sext w).eval env = (v.eval env w).signExtend 64 := by
  cases v with
  | leaf i =>
    simp only [NVal.sext, mkSext_eval, NVal.eval, SExpr.eval]
    cases w <;> simp only [CW.bits] <;> bv_bits
  | trunc e =>
    simp only [NVal.sext, mkSext_eval, NVal.eval]
  | v128 ve =>
    simp only [NVal.sext, mkSext_eval, NVal.eval, VExpr.lo64_eval]
    cases w <;> simp only [CW.bits] <;> bv_bits

/-- Writable non-doubleword points-to assertion. -/
def CW.pointsTo : (w : CW) → BitVec 64 → BitVec w.bits → SepProp
  | .b8, a, v => a ↦₈ v
  | .b16, a, v => a ↦₁₆ v
  | .b32, a, v => a ↦₃₂ v
  | .b128, a, v => a ↦₁₂₈ v

/-- Read-only non-doubleword points-to assertion. -/
def CW.pointsToRO : (w : CW) → BitVec 64 → BitVec w.bits → SepProp
  | .b8, a, v => a ↦₈ᵣ v
  | .b16, a, v => a ↦₁₆ᵣ v
  | .b32, a, v => a ↦₃₂ᵣ v
  | .b128, a, v => a ↦₁₂₈ᵣ v

/-- Points-to assertion parameterized by read-only flag `ro`. -/
def CW.pointsToWithRO (ro : Bool) (w : CW) (a : BitVec 64) (v : BitVec w.bits) : SepProp :=
  if ro then w.pointsToRO a v else w.pointsTo a v

/-- Non-doubleword memory read. -/
def CW.read (m : Memory) : (w : CW) → BitVec 64 → BitVec w.bits
  | .b8, a => m.read8 a
  | .b16, a => m.read16 a
  | .b32, a => m.read32 a
  | .b128, a => m.read128 a

/-- Non-doubleword memory write. -/
def CW.write (m : Memory) : (w : CW) → BitVec 64 → BitVec w.bits → Memory
  | .b8, a, v => m.write8 a v
  | .b16, a, v => m.write16 a v
  | .b32, a, v => m.write32 a v
  | .b128, a, v => m.write128 a v

/-- A spatial atom of the block precondition: a 64-bit or non-doubleword points-to cell (with
    read-only flag `ro`), or an opaque atom. -/
inductive Cell where
  | pt64 (ro : Bool) (addr val : SExpr)
  | opaque (k : Nat)
  | ptN (w : CW) (ro : Bool) (addr : SExpr) (val : NVal)
  deriving DecidableEq, Repr, Inhabited

/-- Denotation of a cell. -/
def Cell.denote (env : Env) : Cell → SepProp
  | .pt64 false a v => (a.eval env) ↦₆₄ (v.eval env)
  | .pt64 true a v => (a.eval env) ↦₆₄ᵣ (v.eval env)
  | .opaque k => env.p.getD k emp
  | .ptN w false a v => w.pointsTo (a.eval env) (v.eval env w)
  | .ptN w true a v => w.pointsToRO (a.eval env) (v.eval env w)

/-- Right-nested separating conjunction of cells, `c₀ ∗ (c₁ ∗ (⋯ ∗ cₙ))` (no trailing `emp`),
    matching the spatial context shape produced by `wp_init` / `wp_entry`. -/
def cellsProp (env : Env) : List Cell → SepProp
  | [] => emp
  | [c] => c.denote env
  | c :: cs => c.denote env ∗ cellsProp env cs

/-- `emp`-terminated variant of `cellsProp` used in proofs. -/
def cellsPropE (env : Env) : List Cell → SepProp
  | [] => emp
  | c :: cs => c.denote env ∗ cellsPropE env cs

theorem cellsProp_eq (env : Env) : ∀ cs : List Cell, cellsProp env cs = cellsPropE env cs
  | [] => rfl
  | [c] => by simp only [cellsProp, cellsPropE, sepConj_emp]
  | c :: d :: cs => by
    show c.denote env ∗ cellsProp env (d :: cs) = c.denote env ∗ cellsPropE env (d :: cs)
    rw [cellsProp_eq env (d :: cs)]

theorem cellsPropE_focus (env : Env) :
    ∀ (cs : List Cell) (k : Nat) (c : Cell), cs[k]? = some c →
      cellsPropE env cs = c.denote env ∗ cellsPropE env (cs.eraseIdx k)
  | [], _, _, h => by simp at h
  | d :: cs, 0, c, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rfl
  | d :: cs, k + 1, c, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.eraseIdx_cons_succ, cellsPropE, cellsPropE, cellsPropE_focus env cs k c h,
      sepConj_left_comm]

theorem cellsPropE_set (env : Env) :
    ∀ (cs : List Cell) (k : Nat) (c c' : Cell), cs[k]? = some c →
      cellsPropE env (cs.set k c') = c'.denote env ∗ cellsPropE env (cs.eraseIdx k)
  | [], _, _, _, h => by simp at h
  | d :: cs, 0, c, c', _ => rfl
  | d :: cs, k + 1, c, c', h => by
    simp only [List.getElem?_cons_succ] at h
    rw [List.set_cons_succ, List.eraseIdx_cons_succ, cellsPropE, cellsPropE,
      cellsPropE_set env cs k c c' h, sepConj_left_comm]

/-- Generic load from 64-bit cell `k` (writable or read-only). -/
theorem cellsProp_load64 {env : Env} {cs : List Cell} {k : Nat} {ro : Bool} {a v : SExpr}
    {m : Memory} {R : SepProp}
    (hk : cs[k]? = some (.pt64 ro a v)) (hm : m ⊨ cellsProp env cs ∗ R) :
    m.read64 (a.eval env) = v.eval env ∧ m.canRead (a.eval env) 8 = true := by
  have h : cellsProp env cs = (Cell.pt64 ro a v).denote env ∗ cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_focus env cs k _ hk]
  rw [h, sepConj_assoc] at hm
  cases ro
  · exact ⟨(IsBlock.pointsTo64 (a.eval env) (v.eval env)).read hm,
      (IsBlock.pointsTo64 (a.eval env) (v.eval env)).canRead (by decide) hm⟩
  · exact ⟨(IsBlockRO.pointsTo64RO (a.eval env) (v.eval env)).read hm,
      (IsBlockRO.pointsTo64RO (a.eval env) (v.eval env)).canRead (by decide) hm⟩

/-- Generic store to writable 64-bit cell `k` (the cell keeps its address expression). -/
theorem cellsProp_store64 {env : Env} {cs : List Cell} {k : Nat} {a v : SExpr} (v' : SExpr)
    {m : Memory} {R : SepProp}
    (hk : cs[k]? = some (.pt64 false a v)) (hm : m ⊨ cellsProp env cs ∗ R) :
    (m.write64 (a.eval env) (v'.eval env) ⊨ cellsProp env (cs.set k (.pt64 false a v')) ∗ R) ∧
      m.canWrite (a.eval env) 8 = true := by
  have h : cellsProp env cs = (a.eval env ↦₆₄ v.eval env) ∗ cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_focus env cs k _ hk]; rfl
  have h' : cellsProp env (cs.set k (.pt64 false a v')) =
      (a.eval env ↦₆₄ v'.eval env) ∗ cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_set env cs k _ _ hk]; rfl
  rw [h, sepConj_assoc] at hm
  rw [h', sepConj_assoc]
  exact ⟨(IsBlock.pointsTo64 (a.eval env) (v.eval env)).write64 hm (v'.eval env),
    (IsBlock.pointsTo64 (a.eval env) (v.eval env)).canWrite (by decide) hm⟩

/-- Generic non-doubleword load from cell `k` (writable or read-only). -/
theorem cellsProp_loadN {env : Env} {cs : List Cell} {k : Nat} {w : CW} {ro : Bool}
    {a : SExpr} {v : NVal} {m : Memory} {R : SepProp}
    (hk : cs[k]? = some (.ptN w ro a v)) (hm : m ⊨ cellsProp env cs ∗ R) :
    CW.read m w (a.eval env) = v.eval env w ∧ m.canRead (a.eval env) w.bytes = true := by
  have h : cellsProp env cs = (Cell.ptN w ro a v).denote env ∗ cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_focus env cs k _ hk]
  rw [h, sepConj_assoc] at hm
  cases ro <;> cases w
  · exact ⟨(IsBlock.pointsTo8 (a.eval env) (v.eval env .b8)).read hm,
      (IsBlock.pointsTo8 (a.eval env) (v.eval env .b8)).canRead (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo16 (a.eval env) (v.eval env .b16)).read hm,
      (IsBlock.pointsTo16 (a.eval env) (v.eval env .b16)).canRead (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo32 (a.eval env) (v.eval env .b32)).read hm,
      (IsBlock.pointsTo32 (a.eval env) (v.eval env .b32)).canRead (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo128 (a.eval env) (v.eval env .b128)).read hm,
      (IsBlock.pointsTo128 (a.eval env) (v.eval env .b128)).canRead (by decide) hm⟩
  · exact ⟨(IsBlockRO.pointsTo8RO (a.eval env) (v.eval env .b8)).read hm,
      (IsBlockRO.pointsTo8RO (a.eval env) (v.eval env .b8)).canRead (by decide) hm⟩
  · exact ⟨(IsBlockRO.pointsTo16RO (a.eval env) (v.eval env .b16)).read hm,
      (IsBlockRO.pointsTo16RO (a.eval env) (v.eval env .b16)).canRead (by decide) hm⟩
  · exact ⟨(IsBlockRO.pointsTo32RO (a.eval env) (v.eval env .b32)).read hm,
      (IsBlockRO.pointsTo32RO (a.eval env) (v.eval env .b32)).canRead (by decide) hm⟩
  · exact ⟨(IsBlockRO.pointsTo128RO (a.eval env) (v.eval env .b128)).read hm,
      (IsBlockRO.pointsTo128RO (a.eval env) (v.eval env .b128)).canRead (by decide) hm⟩

/-- Generic non-doubleword store of an `NVal` to writable cell `k`. -/
theorem cellsProp_storeN_val {env : Env} {cs : List Cell} {k : Nat} {w : CW} {a : SExpr}
    {v : NVal} (nv : NVal) {m : Memory} {R : SepProp}
    (hk : cs[k]? = some (.ptN w false a v)) (hm : m ⊨ cellsProp env cs ∗ R) :
    (CW.write m w (a.eval env) (nv.eval env w) ⊨
        cellsProp env (cs.set k (.ptN w false a nv)) ∗ R) ∧
      m.canWrite (a.eval env) w.bytes = true := by
  have h : cellsProp env cs = w.pointsTo (a.eval env) (v.eval env w) ∗
      cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_focus env cs k _ hk]; rfl
  have h' : cellsProp env (cs.set k (.ptN w false a nv)) =
      w.pointsTo (a.eval env) (nv.eval env w) ∗ cellsPropE env (cs.eraseIdx k) := by
    rw [cellsProp_eq, cellsPropE_set env cs k _ _ hk]; rfl
  rw [h, sepConj_assoc] at hm
  rw [h', sepConj_assoc]
  cases w
  · exact ⟨(IsBlock.pointsTo8 (a.eval env) (v.eval env .b8)).write8 hm (nv.eval env .b8),
      (IsBlock.pointsTo8 (a.eval env) (v.eval env .b8)).canWrite (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo16 (a.eval env) (v.eval env .b16)).write16 hm (nv.eval env .b16),
      (IsBlock.pointsTo16 (a.eval env) (v.eval env .b16)).canWrite (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo32 (a.eval env) (v.eval env .b32)).write32 hm (nv.eval env .b32),
      (IsBlock.pointsTo32 (a.eval env) (v.eval env .b32)).canWrite (by decide) hm⟩
  · exact ⟨(IsBlock.pointsTo128 (a.eval env) (v.eval env .b128)).write128 hm (nv.eval env .b128),
      (IsBlock.pointsTo128 (a.eval env) (v.eval env .b128)).canWrite (by decide) hm⟩

/-- Generic narrow store to writable cell `k`: the cell value becomes the low bits of `v'`. -/
theorem cellsProp_storeN {env : Env} {cs : List Cell} {k : Nat} {w : CW} {a : SExpr} {v : NVal}
    (v' : SExpr) {m : Memory} {R : SepProp}
    (hk : cs[k]? = some (.ptN w false a v)) (hm : m ⊨ cellsProp env cs ∗ R) :
    (CW.write m w (a.eval env) ((v'.eval env).truncate w.bits) ⊨
        cellsProp env (cs.set k (.ptN w false a (mkTrunc w v'))) ∗ R) ∧
      m.canWrite (a.eval env) w.bytes = true := by
  rw [← mkTrunc_eval env w v']
  exact cellsProp_storeN_val (mkTrunc w v') hk hm

/-! ## Symbolic machine state -/

/-- Symbolic program counter: `base + off` (fetchable from the block's code table) or an
    arbitrary symbolic value (after `RET` / `BR`). -/
inductive SPc where
  | rel (off : BitVec 64)
  | abs (e : SExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Denotation of a symbolic program counter relative to code base `b`. -/
def SPc.denote (b : BitVec 64) (env : Env) : SPc → BitVec 64
  | .rel off => b + off
  | .abs e => e.eval env

/-- Symbolic `NZCV` flags: the entry flags, or the flags set by an `ADDS`/`SUBS` or `ANDS`/`BICS`
    on top of a previous flag state. -/
inductive SFlags where
  | orig
  | addSubOr (w : Width) (op : AddSubOp) (a b : SExpr) (prev : SFlags)
  | logicalOr (w : Width) (op : LogicalOp) (a b : SExpr) (prev : SFlags)
  deriving DecidableEq, Repr, Inhabited

/-- Denotation of symbolic flags given the entry flags `ps0`. -/
def SFlags.denote (env : Env) (ps0 : PState) : SFlags → PState
  | .orig => ps0
  | .addSubOr w op a b prev =>
    ((evalAddSub w op (a.eval env) (b.eval env) none).2).getD (prev.denote env ps0)
  | .logicalOr w op a b prev =>
    ((evalLogical w op (a.eval env) (b.eval env) PState.zero).2).getD (prev.denote env ps0)

/-- Symbolic machine state for one block. -/
structure SState where
  /-- `x0` .. `x30`. -/
  regs : List SExpr
  /-- `v0` .. `v31` (empty when no SIMD registers are touched; 32 entries when active). -/
  vregs : List VExpr := []
  sp : SExpr
  /-- `TPIDR_EL0` (`tpidr0` when untouched). -/
  tpidr : SExpr := .tpidr0
  pc : SPc
  flags : SFlags
  cells : List Cell
  deriving Repr, Inhabited

namespace SState

/-- Expression held by GPR `i`. -/
@[reducible] def reg (ss : SState) (i : Nat) : SExpr := ss.regs.getD i (.const 0)

/-- Expression held by 128-bit SIMD register `i`. -/
@[reducible] def vreg (ss : SState) (i : Nat) : VExpr := ss.vregs.getD i (.const 0)

/-- Symbolic `readReg64`. -/
def readReg64 (ss : SState) : Reg → SExpr
  | .gpr i => if i = 31#5 then .const 0 else ss.reg i.toNat
  | .sp => ss.sp
  | .xzr => .const 0

/-- Symbolic `readReg`. -/
def readReg (ss : SState) (w : Width) (r : Reg) : SExpr :=
  match w with
  | .W32 => mkZext32 (ss.readReg64 r)
  | .W64 => ss.readReg64 r

/-- Symbolic `writeReg64`. -/
def setReg64 (ss : SState) : Reg → SExpr → SState
  | .gpr i, e => if i = 31#5 then ss else { ss with regs := ss.regs.set i.toNat e }
  | .sp, e => { ss with sp := e }
  | .xzr, _ => ss

/-- Symbolic `writeReg`. -/
def setReg (ss : SState) (w : Width) (r : Reg) (e : SExpr) : SState :=
  ss.setReg64 r (match w with | .W32 => mkZext32 e | .W64 => e)

/-- Symbolic `writeVReg128`. -/
def setVReg128 (ss : SState) (idx : BitVec 5) (ve : VExpr) : SState :=
  { ss with vregs := ss.vregs.set idx.toNat ve }

/-- Symbolic `setTpidrEl0`. -/
def setTpidr (ss : SState) (e : SExpr) : SState :=
  { ss with tpidr := e }

/-- Symbolic `advancePC`. -/
def advance (ss : SState) : SState :=
  { ss with pc := match ss.pc with
    | .rel off => .rel (off + 4#64)
    | .abs e => .abs (mkAdd e (.const 4#64)) }

/-- Concrete state denoted by `ss`: all fields not tracked symbolically are taken from `s0`. -/
def toState (ss : SState) (b : BitVec 64) (env : Env) (s0 : State) (m : Memory) : State :=
  { s0 with
    regs := ⟨fun j => if j = 31#5 then s0.regs.regs j else (ss.reg j.toNat).eval env⟩
    vregs := ⟨fun j => match ss.vregs[j.toNat]? with
      | some ve => ve.eval env
      | none => s0.vregs.regs j⟩
    sp := ss.sp.eval env
    tpidrEl0 := ss.tpidr.eval env
    pc := ss.pc.denote b env
    pstate := ss.flags.denote env s0.pstate
    mem := m
    status := .Running }

/-! ### Commuting lemmas between symbolic and concrete state operations -/

variable {b : BitVec 64} {env : Env} {s0 : State} {m : Memory}

@[simp] theorem toState_mem (ss : SState) : (ss.toState b env s0 m).mem = m := rfl
@[simp] theorem toState_status (ss : SState) : (ss.toState b env s0 m).status = .Running := rfl
@[simp] theorem toState_pc (ss : SState) : (ss.toState b env s0 m).pc = ss.pc.denote b env := rfl
@[simp] theorem toState_sp (ss : SState) : (ss.toState b env s0 m).sp = ss.sp.eval env := rfl
@[simp] theorem toState_tpidrEl0 (ss : SState) :
    (ss.toState b env s0 m).tpidrEl0 = ss.tpidr.eval env := rfl
@[simp] theorem toState_pstate (ss : SState) :
    (ss.toState b env s0 m).pstate = ss.flags.denote env s0.pstate := rfl

theorem toState_readReg64 (ss : SState) (r : Reg) :
    (ss.toState b env s0 m).readReg64 r = (ss.readReg64 r).eval env := by
  cases r with
  | gpr i =>
    simp only [State.readReg64, SState.readReg64, toState, RegFile.read]
    by_cases h : i = 31#5 <;> simp [h, SExpr.eval]
  | sp => rfl
  | xzr => rfl

theorem toState_readReg (ss : SState) (w : Width) (r : Reg) :
    (ss.toState b env s0 m).readReg w r = (ss.readReg w r).eval env := by
  cases w <;>
    simp only [State.readReg, State.readReg32, SState.readReg, mkZext32_eval,
      toState_readReg64]

theorem toState_writeReg64 (ss : SState) (hlen : ss.regs.length = 31) (r : Reg) (e : SExpr) :
    (ss.toState b env s0 m).writeReg64 r (e.eval env) = (ss.setReg64 r e).toState b env s0 m := by
  cases r with
  | gpr i =>
    by_cases h : i = 31#5
    · subst h; rfl
    · have hb : (i == 31#5) = false := by simpa using h
      simp only [State.writeReg64, setReg64, h, hb, toState, ite_false, Bool.false_eq_true]
      congr 1
      simp only [RegFile.write, RegFile.mk.injEq]
      funext j
      by_cases hj : j = i
      · subst hj
        have hi : j.toNat < 31 := by
          have := j.isLt; have : j.toNat ≠ 31 := fun h' => h (BitVec.eq_of_toNat_eq h'); omega
        simp [h, reg, List.getD_eq_getElem?_getD, hi, hlen]
      · have hne : j.toNat ≠ i.toNat := fun h' => hj (BitVec.eq_of_toNat_eq h')
        by_cases h31 : j = 31#5
        · subst h31; simp [hj]
        · simp [hj, h31, reg, List.getD_eq_getElem?_getD, Ne.symm hne]
  | sp => rfl
  | xzr => rfl

theorem setReg64_length (ss : SState) (r : Reg) (e : SExpr) :
    (ss.setReg64 r e).regs.length = ss.regs.length := by
  cases r with
  | gpr i => by_cases h : i = 31#5 <;> simp [setReg64, h]
  | sp => rfl
  | xzr => rfl

theorem toState_writeReg (ss : SState) (hlen : ss.regs.length = 31) (w : Width) (r : Reg)
    (e : SExpr) :
    (ss.toState b env s0 m).writeReg w r (e.eval env) = (ss.setReg w r e).toState b env s0 m := by
  cases w with
  | W32 =>
    simp only [State.writeReg, setReg]
    rw [← mkZext32_eval env e, toState_writeReg64 ss hlen]
  | W64 =>
    simp only [State.writeReg, setReg]
    rw [toState_writeReg64 ss hlen]

theorem setReg_length (ss : SState) (w : Width) (r : Reg) (e : SExpr) :
    (ss.setReg w r e).regs.length = ss.regs.length := setReg64_length ss r _

theorem toState_readVReg128 (ss : SState) (hvlen : ss.vregs.length = 32) (idx : BitVec 5) :
    (ss.toState b env s0 m).readVReg128 idx = (ss.vreg idx.toNat).eval env := by
  have hi : idx.toNat < ss.vregs.length := hvlen ▸ idx.isLt
  simp only [State.readVReg128, VRegFile.read, toState, vreg, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem toState_writeVReg128 (ss : SState) (hvlen : ss.vregs.length = 32) (idx : BitVec 5)
    (ve : VExpr) :
    (ss.toState b env s0 m).writeVReg128 idx (ve.eval env) =
      (ss.setVReg128 idx ve).toState b env s0 m := by
  simp only [State.writeVReg128, setVReg128, toState]
  congr 1
  simp only [VRegFile.write, VRegFile.mk.injEq]
  funext j
  by_cases hj : j = idx
  · subst hj
    have hi : j.toNat < (ss.vregs.set j.toNat ve).length := by simp [hvlen, j.isLt]
    rw [List.getElem?_eq_getElem hi]
    simp
  · have hne : j.toNat ≠ idx.toNat := fun h' => hj (BitVec.eq_of_toNat_eq h')
    simp [hj, List.getElem?_set_ne (Ne.symm hne)]

theorem setVReg128_length (ss : SState) (idx : BitVec 5) (ve : VExpr) :
    (ss.setVReg128 idx ve).vregs.length = ss.vregs.length := by
  simp [setVReg128]

theorem toState_setTpidr (ss : SState) (e : SExpr) :
    ({ ss.toState b env s0 m with tpidrEl0 := e.eval env } : State) =
      (ss.setTpidr e).toState b env s0 m :=
  rfl

theorem toState_advancePC (ss : SState) :
    (ss.toState b env s0 m).advancePC = ss.advance.toState b env s0 m := by
  simp only [State.advancePC, toState, advance]
  congr 1
  cases ss.pc <;> simp [SPc.denote, mkAdd_eval, SExpr.eval, BitVec.add_assoc]

theorem toState_setPC (ss : SState) (pc : SPc) :
    (ss.toState b env s0 m).setPC (pc.denote b env) = { ss with pc := pc }.toState b env s0 m :=
  rfl

theorem toState_setMem (ss : SState) (m' : Memory) :
    (ss.toState b env s0 m).setMem m' = ss.toState b env s0 m' := rfl

end SState

end ProofLib.SymBlock
