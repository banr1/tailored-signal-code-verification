/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SymBlock.Lower
public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Symbolic Step Checker and Soundness

Defines the total per-instruction symbolic execution step (`stepOp`, `stepSymInsn`), untrusted
cell and branch hints (`Hint`), residual side conditions (`SProp`, `allHold`), and one-step
soundness theorems (`stepOp_sound`, `stepSymInsn_sound`). Whole-block iteration lives in
`ProofLib.SepLogic.SymBlock.Block` and the tactic front end in
`ProofLib.SepLogic.SymBlock.Tactic`.
-/

@[expose] public section

namespace ProofLib.SymBlock

open Arm64

/-! ## Residual Obligations -/

/-- Side conditions returned by the checker. -/
inductive SProp where
  | eq (a b : SExpr)
  | ne (a b : SExpr)
  | ult (a b : SExpr) (v : Bool)
  | ule (a b : SExpr) (v : Bool)
  | slt (a b : SExpr) (v : Bool)
  | sle (a b : SExpr) (v : Bool)
  | aligned16 (a : SExpr)
  | cond (c : SCond) (v : Bool)
  deriving DecidableEq, Repr, Inhabited

def SProp.denote (env : Env) : SProp → Prop
  | .eq a b => a.eval env = b.eval env
  | .ne a b => a.eval env ≠ b.eval env
  | .ult a b v => BitVec.ult (a.eval env) (b.eval env) = v
  | .ule a b v => BitVec.ule (a.eval env) (b.eval env) = v
  | .slt a b v => BitVec.slt (a.eval env) (b.eval env) = v
  | .sle a b v => BitVec.sle (a.eval env) (b.eval env) = v
  | .aligned16 a => (a.eval env &&& 15#64 == 0#64) = true
  | .cond c v => c.eval env = v

def allHold (env : Env) : List SProp → Prop
  | [] => True
  | p :: ps => p.denote env ∧ allHold env ps

theorem allHold_append {env : Env} :
    ∀ {l₁ l₂ : List SProp}, allHold env (l₁ ++ l₂) ↔ allHold env l₁ ∧ allHold env l₂
  | [], _ => by simp [allHold]
  | p :: ps, _ => by simp only [List.cons_append, allHold, allHold_append, and_assoc]

/-- Equality obligation, dropped when both sides are syntactically equal. -/
def oblEq (a b : SExpr) : List SProp := if a = b then [] else [.eq a b]

theorem oblEq_sound {env : Env} {a b : SExpr} (h : allHold env (oblEq a b)) :
    a.eval env = b.eval env := by
  unfold oblEq at h
  split at h
  · subst_vars; rfl
  · exact h.1

theorem aligned16_iff (y : BitVec 64) : (y &&& 15#64 == 0#64) = true ↔ y.toNat % 16 = 0 := by
  have h : (y &&& 15#64).toNat = y.toNat % 16 := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp only [beq_iff_eq]
  constructor
  · intro he; rw [he] at h; simp at h; omega
  · intro hm; apply BitVec.eq_of_toNat_eq; rw [h, hm]; rfl

theorem aligned16_add {x c : BitVec 64} (hc : (c &&& 15#64 == 0#64) = true)
    (hx : (x &&& 15#64 == 0#64) = true) : (x + c &&& 15#64 == 0#64) = true := by
  rw [aligned16_iff] at *
  simp only [BitVec.toNat_add]
  omega

theorem aligned16_sub {x c : BitVec 64} (hc : (c &&& 15#64 == 0#64) = true)
    (hx : (x &&& 15#64 == 0#64) = true) : (x - c &&& 15#64 == 0#64) = true := by
  rw [aligned16_iff] at *
  simp only [BitVec.toNat_sub]
  omega

/-- Split `x + c` / `x - c` with constant `c`. -/
def peelOff : SExpr → Option (SExpr × BitVec 64 × Bool)
  | .add x (.const c) => some (x, c, false)
  | .sub x (.const c) => some (x, c, true)
  | _ => none

theorem peelOff_sound {env : Env} {a x : SExpr} {c : BitVec 64} {sb : Bool}
    (h : peelOff a = some (x, c, sb)) :
    a.eval env = if sb then x.eval env - c else x.eval env + c := by
  unfold peelOff at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

/-- `SP`-alignment obligation, peeling one `± c` with `c ≡ 0 (mod 16)` syntactically. -/
def oblAligned (a : SExpr) : List SProp :=
  match peelOff a with
  | some (x, c, _) => if (c &&& 15#64 == 0#64) = true then [.aligned16 x] else [.aligned16 a]
  | none => [.aligned16 a]

theorem oblAligned_sound {env : Env} {a : SExpr} (h : allHold env (oblAligned a)) :
    (a.eval env &&& 15#64 == 0#64) = true := by
  unfold oblAligned at h
  split at h
  · rename_i x c sb hp
    split at h
    · rename_i hc
      rw [peelOff_sound hp]
      cases sb
      · exact aligned16_add hc h.1
      · exact aligned16_sub hc h.1
    · exact h.1
  · exact h.1

/-- Convert a symbolic condition `c` into residual side conditions for `c.eval env = taken`. -/
def condToObl : SCond → Bool → List SProp
  | .tt, taken => if taken then [] else [.cond .tt false]
  | .ff, taken => if taken then [.cond .ff true] else []
  | .eq64 a b, taken => if taken then oblEq a b else [.ne a b]
  | .eq32 a b, taken =>
    if taken then oblEq (mkZext32 a) (mkZext32 b) else [.ne (mkZext32 a) (mkZext32 b)]
  | .ult64 a b, taken => [.ult a b taken]
  | .ule64 a b, taken => [.ule a b taken]
  | .slt64 a b, taken => [.slt a b taken]
  | .sle64 a b, taken => [.sle a b taken]
  | .ult32 a b, taken => [.ult (mkZext32 a) (mkZext32 b) taken]
  | .ule32 a b, taken => [.ule (mkZext32 a) (mkZext32 b) taken]
  | .slt32 a b, taken => [.slt (mkSext 32 a) (mkSext 32 b) taken]
  | .sle32 a b, taken => [.sle (mkSext 32 a) (mkSext 32 b) taken]
  | .not c, taken => condToObl c (!taken)
  | .bit (.const c) k, taken =>
    if c.getLsbD k == taken then [] else [.cond (.bit (.const c) k) taken]
  | c, taken => [.cond c taken]

theorem getLsbD_eq_testBit_toNat {w : Nat} (x : BitVec w) (k : Nat) :
    x.getLsbD k = decide ((x.toNat / 2 ^ k) % 2 = 1) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm 1,
    Nat.and_one_is_mod, bne_iff_ne, ne_eq, decide_eq_true_eq]
  omega

theorem zext32_eq_iff (x y : BitVec 64) :
    ((x.truncate 32).zeroExtend 64 = (y.truncate 32).zeroExtend 64) ↔
      x.truncate 32 = y.truncate 32 := by
  constructor
  · intro h; bv_bits
  · intro h; rw [h]

theorem ult_zext32_eq (x y : BitVec 64) :
    BitVec.ult ((x.truncate 32).zeroExtend 64) ((y.truncate 32).zeroExtend 64) =
      BitVec.ult (x.truncate 32) (y.truncate 32) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ult, BitVec.zeroExtend, BitVec.truncate, BitVec.toNat_setWidth, decide_eq_true_eq]
  omega

theorem ule_zext32_eq (x y : BitVec 64) :
    BitVec.ule ((x.truncate 32).zeroExtend 64) ((y.truncate 32).zeroExtend 64) =
      BitVec.ule (x.truncate 32) (y.truncate 32) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ule, BitVec.zeroExtend, BitVec.truncate, BitVec.toNat_setWidth, decide_eq_true_eq]
  omega

theorem toInt_signExtend32_64 (x : BitVec 32) : (x.signExtend 64).toInt = x.toInt := by
  rw [BitVec.toInt_signExtend, show min 64 32 = 32 from rfl]
  have hx := x.isLt
  simp only [Int.bmod, BitVec.toInt]
  omega

theorem slt_sext32_eq (x y : BitVec 64) :
    BitVec.slt ((x.truncate 32).signExtend 64) ((y.truncate 32).signExtend 64) =
      BitVec.slt (x.truncate 32) (y.truncate 32) := by
  simp only [BitVec.slt, toInt_signExtend32_64]

theorem sle_sext32_eq (x y : BitVec 64) :
    BitVec.sle ((x.truncate 32).signExtend 64) ((y.truncate 32).signExtend 64) =
      BitVec.sle (x.truncate 32) (y.truncate 32) := by
  simp only [BitVec.sle, toInt_signExtend32_64]

theorem condToObl_sound {env : Env} :
    ∀ (c : SCond) (taken : Bool), allHold env (condToObl c taken) → c.eval env = taken
  | .tt, true, _ => rfl
  | .tt, false, h => h.1
  | .ff, true, h => h.1
  | .ff, false, _ => rfl
  | .eq64 a b, true, h => by
    simp only [SCond.eval, beq_iff_eq]
    exact oblEq_sound h
  | .eq64 a b, false, h => by
    simp only [SCond.eval, beq_eq_false_iff_ne]
    exact h.1
  | .eq32 a b, true, h => by
    simp only [SCond.eval, beq_iff_eq]
    have h' := oblEq_sound h
    simp only [mkZext32_eval] at h'
    exact (zext32_eq_iff _ _).mp h'
  | .eq32 a b, false, h => by
    simp only [SCond.eval, beq_eq_false_iff_ne]
    have h' : (mkZext32 a).eval env ≠ (mkZext32 b).eval env := h.1
    simp only [mkZext32_eval] at h'
    intro heq
    exact h' ((zext32_eq_iff _ _).mpr heq)
  | .ult64 a b, taken, h => h.1
  | .ule64 a b, taken, h => h.1
  | .slt64 a b, taken, h => h.1
  | .sle64 a b, taken, h => h.1
  | .ult32 a b, taken, h => by
    have h' : BitVec.ult ((mkZext32 a).eval env) ((mkZext32 b).eval env) = taken := h.1
    simpa only [SCond.eval, mkZext32_eval, ult_zext32_eq] using h'
  | .ule32 a b, taken, h => by
    have h' : BitVec.ule ((mkZext32 a).eval env) ((mkZext32 b).eval env) = taken := h.1
    simpa only [SCond.eval, mkZext32_eval, ule_zext32_eq] using h'
  | .slt32 a b, taken, h => by
    have h' : BitVec.slt ((mkSext 32 a).eval env) ((mkSext 32 b).eval env) = taken := h.1
    simpa only [SCond.eval, mkSext_eval, slt_sext32_eq] using h'
  | .sle32 a b, taken, h => by
    have h' : BitVec.sle ((mkSext 32 a).eval env) ((mkSext 32 b).eval env) = taken := h.1
    simpa only [SCond.eval, mkSext_eval, sle_sext32_eq] using h'
  | .not c, taken, h => by
    have ih := condToObl_sound c (!taken) h
    simp only [SCond.eval, ih]
    cases taken <;> rfl
  | .msb32 _, _, h => h.1
  | .msb64 _, _, h => h.1
  | .addC32 _ _, _, h => h.1
  | .addC64 _ _, _, h => h.1
  | .addV32 _ _, _, h => h.1
  | .addV64 _ _, _, h => h.1
  | .subV32 _ _, _, h => h.1
  | .subV64 _ _, _, h => h.1
  | .bit a k, taken, h => by
    cases a with
    | const c =>
      dsimp only [condToObl] at h
      split at h
      · rename_i heq
        exact beq_iff_eq.mp heq
      · exact h.1
    | _ => exact h.1
  | .and _ _, _, h => h.1
  | .or _ _, _, h => h.1

/-! ## Per-Instruction Advice -/

/-- Untrusted per-instruction advice. -/
inductive Hint where
  | none
  | cell (k : Nat)
  | cell2 (k₁ k₂ : Nat)
  | cell4 (k₁ k₂ k₃ k₄ : Nat)
  | br (taken : Bool)
  deriving DecidableEq, Repr, Inhabited

/-! ## Symbolic Helpers and Soundness -/

/-- Symbolic `evalAddrMode` (immediate, pre/post-indexed, and register-offset modes). -/
def symAddr (ss : SState) : AddrMode → Option (SExpr × Option (Reg × SExpr))
  | .Offset base off => some (mkAdd (ss.readReg64 base) (.const off), none)
  | .UnscaledOffset base off => some (mkAdd (ss.readReg64 base) (.const off), none)
  | .PreIndex base off =>
    some (mkAdd (ss.readReg64 base) (.const off), some (base, mkAdd (ss.readReg64 base) (.const off)))
  | .PostIndex base off => some (ss.readReg64 base, some (base, mkAdd (ss.readReg64 base) (.const off)))
  | .RegOffset base index ext amount =>
    some (mkAdd (ss.readReg64 base) (mkExtendVal .W64 (ss.readReg64 index) ext amount), none)

def SState.applyWb (ss : SState) : Option (Reg × SExpr) → SState
  | some (r, e) => ss.setReg64 r e
  | none => ss

/-- Obligation for the architectural `SP`-alignment check of an addressing mode. -/
def alignObl (ss : SState) (am : AddrMode) : List SProp :=
  match am.baseReg with
  | .sp => oblAligned ss.sp
  | _ => []

def pt64At? (cs : List Cell) (k : Nat) : Option (Bool × SExpr × SExpr) :=
  match cs[k]? with
  | some (.pt64 ro a v) => some (ro, a, v)
  | _ => none

def pt64MutAt? (cs : List Cell) (k : Nat) : Option (SExpr × SExpr) :=
  match cs[k]? with
  | some (.pt64 false a v) => some (a, v)
  | _ => none

def ptNAt? (cs : List Cell) (k : Nat) : Option (Bool × CW × SExpr × NVal) :=
  match cs[k]? with
  | some (.ptN w ro a v) => some (ro, w, a, v)
  | _ => none

def ptNMutAt? (cs : List Cell) (k : Nat) : Option (CW × SExpr × NVal) :=
  match cs[k]? with
  | some (.ptN w false a v) => some (w, a, v)
  | _ => none

def SPc.addOff (pc : SPc) (t : BitVec 64) : SPc :=
  match pc with
  | .rel o => .rel (o + t)
  | .abs e => .abs (mkAdd e (.const t))

/-- Flag update for `ADDS` / `SUBS` (other add/sub operations keep the flags). -/
def mkFlags (w : Width) (op : AddSubOp) (a c : SExpr) (prev : SFlags) : SFlags :=
  match op with
  | .ADDS | .SUBS => .addSubOr w op a c prev
  | _ => prev

def logicalSetsFlags : LogicalOp → Bool
  | .ANDS | .BICS => true
  | _ => false

/-- Flag update for `ANDS` / `BICS` (other logical operations keep the flags). -/
def mkLogicalFlags (w : Width) (op : LogicalOp) (a b : SExpr) (prev : SFlags) : SFlags :=
  if logicalSetsFlags op then .logicalOr w op a b prev else prev

/-- Conditional select smart constructor, collapsing `ite c t t` to `t`. -/
def mkIte (c : SCond) (t f : SExpr) : SExpr :=
  if t = f then t else .ite c t f

theorem mkIte_eval (env : Env) (c : SCond) (t f : SExpr) :
    (mkIte c t f).eval env = if c.eval env then t.eval env else f.eval env := by
  unfold mkIte
  split
  · subst_vars; simp
  · rfl

/-! ### Flag-condition classifier across `SUBS`, `ADDS`, `ANDS`, `BICS` -/

/-- Condition for flags produced by `SUBS` (`CMP`) at width `w`. -/
def subsCond? (w : Width) (a c : SExpr) (cond : CondCode) : Option SCond :=
  match w with
  | .W64 =>
    match cond with
    | .EQ => some (.eq64 a c)
    | .NE => some (.not (.eq64 a c))
    | .CS => some (.ule64 c a)
    | .CC => some (.ult64 a c)
    | .MI => some (.msb64 (.sub a c))
    | .PL => some (.not (.msb64 (.sub a c)))
    | .VS => some (.subV64 a c)
    | .VC => some (.not (.subV64 a c))
    | .HI => some (.ult64 c a)
    | .LS => some (.ule64 a c)
    | .GE => some (.sle64 c a)
    | .LT => some (.slt64 a c)
    | .GT => some (.slt64 c a)
    | .LE => some (.sle64 a c)
    | .AL | .NV => some .tt
  | .W32 =>
    match cond with
    | .EQ => some (.eq32 a c)
    | .NE => some (.not (.eq32 a c))
    | .CS => some (.ule32 c a)
    | .CC => some (.ult32 a c)
    | .MI => some (.msb32 (.sub a c))
    | .PL => some (.not (.msb32 (.sub a c)))
    | .VS => some (.subV32 a c)
    | .VC => some (.not (.subV32 a c))
    | .HI => some (.ult32 c a)
    | .LS => some (.ule32 a c)
    | .GE => some (.sle32 c a)
    | .LT => some (.slt32 a c)
    | .GT => some (.slt32 c a)
    | .LE => some (.sle32 a c)
    | .AL | .NV => some .tt

/-- Negated nonzero immediate for `ADDS`/`CMN` unsigned range checks at 64-bit width. -/
def addsConstNeg64? : SExpr → Option SExpr
  | .const k => if k ≠ 0#64 then some (.const (0#64 - k)) else none
  | _ => none

/-- Negated nonzero immediate for `ADDS`/`CMN` unsigned range checks at 32-bit width. -/
def addsConstNeg32? : SExpr → Option SExpr
  | .const k =>
    let k32 := k.truncate 32
    if k32 ≠ 0#32 then some (.const ((0#32 - k32).zeroExtend 64)) else none
  | _ => none

/-- Condition for flags produced by `ADDS` (`CMN`) at width `w`. -/
def addsCond? (w : Width) (a c : SExpr) (cond : CondCode) : Option SCond :=
  match w with
  | .W64 =>
    match cond, addsConstNeg64? c with
    | .CS, some nk => some (.ule64 nk a)
    | .CC, some nk => some (.ult64 a nk)
    | .HI, some nk => some (.ult64 nk a)
    | .LS, some nk => some (.ule64 a nk)
    | .EQ, _ => some (.eq64 a (mkNeg c))
    | .NE, _ => some (.not (.eq64 a (mkNeg c)))
    | .CS, none => some (.addC64 a c)
    | .CC, none => some (.not (.addC64 a c))
    | .MI, _ => some (.msb64 (.add a c))
    | .PL, _ => some (.not (.msb64 (.add a c)))
    | .VS, _ => some (.addV64 a c)
    | .VC, _ => some (.not (.addV64 a c))
    | .HI, none => some (.and (.addC64 a c) (.not (.eq64 a (mkNeg c))))
    | .LS, none => some (.not (.and (.addC64 a c) (.not (.eq64 a (mkNeg c)))))
    | .GE, _ =>
      let n := SCond.msb64 (.add a c)
      let v := SCond.addV64 a c
      some (.or (.and n v) (.and (.not n) (.not v)))
    | .LT, _ =>
      let n := SCond.msb64 (.add a c)
      let v := SCond.addV64 a c
      some (.or (.and n (.not v)) (.and (.not n) v))
    | .GT, _ =>
      let z := SCond.eq64 a (mkNeg c)
      let n := SCond.msb64 (.add a c)
      let v := SCond.addV64 a c
      some (.and (.not z) (.or (.and n v) (.and (.not n) (.not v))))
    | .LE, _ =>
      let z := SCond.eq64 a (mkNeg c)
      let n := SCond.msb64 (.add a c)
      let v := SCond.addV64 a c
      some (.or z (.or (.and n (.not v)) (.and (.not n) v)))
    | .AL, _ | .NV, _ => some .tt
  | .W32 =>
    match cond, addsConstNeg32? c with
    | .CS, some nk => some (.ule32 nk a)
    | .CC, some nk => some (.ult32 a nk)
    | .HI, some nk => some (.ult32 nk a)
    | .LS, some nk => some (.ule32 a nk)
    | .EQ, _ => some (.eq32 a (mkNeg c))
    | .NE, _ => some (.not (.eq32 a (mkNeg c)))
    | .CS, none => some (.addC32 a c)
    | .CC, none => some (.not (.addC32 a c))
    | .MI, _ => some (.msb32 (.add a c))
    | .PL, _ => some (.not (.msb32 (.add a c)))
    | .VS, _ => some (.addV32 a c)
    | .VC, _ => some (.not (.addV32 a c))
    | .HI, none => some (.and (.addC32 a c) (.not (.eq32 a (mkNeg c))))
    | .LS, none => some (.not (.and (.addC32 a c) (.not (.eq32 a (mkNeg c)))))
    | .GE, _ =>
      let n := SCond.msb32 (.add a c)
      let v := SCond.addV32 a c
      some (.or (.and n v) (.and (.not n) (.not v)))
    | .LT, _ =>
      let n := SCond.msb32 (.add a c)
      let v := SCond.addV32 a c
      some (.or (.and n (.not v)) (.and (.not n) v))
    | .GT, _ =>
      let z := SCond.eq32 a (mkNeg c)
      let n := SCond.msb32 (.add a c)
      let v := SCond.addV32 a c
      some (.and (.not z) (.or (.and n v) (.and (.not n) (.not v))))
    | .LE, _ =>
      let z := SCond.eq32 a (mkNeg c)
      let n := SCond.msb32 (.add a c)
      let v := SCond.addV32 a c
      some (.or z (.or (.and n (.not v)) (.and (.not n) v)))
    | .AL, _ | .NV, _ => some .tt

/-- If `mask = 1#64 <<< k` for some `k < n`, return `some k`. -/
def findBit (mask : BitVec 64) : Nat → Option Nat
  | 0 => none
  | n + 1 => if mask == (1#64 <<< n) then some n else findBit mask n

theorem findBit_sound (mask : BitVec 64) :
    ∀ {n k : Nat}, findBit mask n = some k → k < n ∧ mask = 1#64 <<< k
  | 0, _, h => by simp [findBit] at h
  | n + 1, k, h => by
    unfold findBit at h
    split at h
    · rename_i hbeq
      simp only [Option.some.injEq] at h; subst h
      exact ⟨Nat.lt_succ_self _, beq_iff_eq.mp hbeq⟩
    · obtain ⟨hk, hm⟩ := findBit_sound mask h
      exact ⟨Nat.lt_succ_of_lt hk, hm⟩

/-- Symbolic result expression of `ANDS` / `BICS`. -/
def logicalResExpr (w : Width) (op : LogicalOp) (a c : SExpr) : SExpr :=
  match op with
  | .ANDS => mkLogical w .AND a c
  | _ => mkLogical w .BIC a c

/-- Zero-flag condition for `ANDS` / `BICS` (`TST`). -/
def logicalIsZero (w : Width) (op : LogicalOp) (a c : SExpr) : SCond :=
  let resExpr := logicalResExpr w op a c
  let maxBits : Nat := match w with | .W32 => 32 | .W64 => 64
  match op, c with
  | .ANDS, .const mask =>
    match findBit mask maxBits with
    | some k => .not (.bit a k)
    | none =>
      match w with
      | .W32 => .eq32 resExpr (.const 0#64)
      | .W64 => .eq64 resExpr (.const 0#64)
  | _, _ =>
    match w with
    | .W32 => .eq32 resExpr (.const 0#64)
    | .W64 => .eq64 resExpr (.const 0#64)

/-- Sign-flag condition for `ANDS` / `BICS` (`TST`). -/
def logicalIsNeg (w : Width) (op : LogicalOp) (a c : SExpr) : SCond :=
  let resExpr := logicalResExpr w op a c
  match w with
  | .W32 => .msb32 resExpr
  | .W64 => .msb64 resExpr

/-- Condition for flags produced by `ANDS` / `BICS` (`TST`) at width `w`. -/
def logicalCond? (w : Width) (op : LogicalOp) (a c : SExpr) (cond : CondCode) : Option SCond :=
  match op with
  | .ANDS | .BICS =>
    let isZero := logicalIsZero w op a c
    let isNeg := logicalIsNeg w op a c
    match cond with
    | .EQ => some isZero
    | .NE => some (.not isZero)
    | .CS => some .ff
    | .CC => some .tt
    | .MI => some isNeg
    | .PL => some (.not isNeg)
    | .VS => some .ff
    | .VC => some .tt
    | .HI => some .ff
    | .LS => some .tt
    | .GE => some (.not isNeg)
    | .LT => some isNeg
    | .GT => some (.and (.not isZero) (.not isNeg))
    | .LE => some (.or isZero isNeg)
    | .AL | .NV => some .tt
  | _ => none

/-- Symbolic condition `SCond` corresponding to `ConditionHolds cond fl`, if `fl` was produced by
    a supported flag-setting instruction (`SUBS`, `ADDS`, `ANDS`, `BICS` at `.W32` or `.W64`). -/
def flagsCond? (fl : SFlags) (cond : CondCode) : Option SCond :=
  match fl with
  | .addSubOr w .SUBS a c _ => subsCond? w a c cond
  | .addSubOr w .ADDS a c _ => addsCond? w a c cond
  | .logicalOr w op a c _ => logicalCond? w op a c cond
  | _ => none

/-- Branch-condition obligation for `B.cond`. -/
def condObl (fl : SFlags) (cond : CondCode) (taken : Bool) : Option (List SProp) :=
  (flagsCond? fl cond).map (fun c => condToObl c taken)

/-! ### Flag-condition soundness helpers -/

section FlagLemmas

theorem addsConstNeg64?_sound {c nk : SExpr} (h : addsConstNeg64? c = some nk) (env : Env) :
    c.eval env ≠ 0#64 ∧ nk.eval env = 0#64 - c.eval env := by
  cases c <;> simp only [addsConstNeg64?] at h <;> try cases h
  split at h <;> cases h
  exact ⟨by assumption, rfl⟩

theorem addsConstNeg32?_sound {c nk : SExpr} (h : addsConstNeg32? c = some nk) (env : Env) :
    (c.eval env).truncate 32 ≠ 0#32 ∧ (nk.eval env).truncate 32 = 0#32 - (c.eval env).truncate 32 := by
  cases c <;> simp only [addsConstNeg32?] at h <;> try cases h
  split at h <;> cases h
  refine ⟨by assumption, ?_⟩
  simp only [SExpr.eval]
  bv_bits

theorem bit64_zero_iff (x : BitVec 64) (k : Nat) (hk : k < 64) :
    ((x &&& (1#64 <<< k)) == 0#64) = !(x.getLsbD k) := by
  have h1 : ((x &&& (1#64 <<< k)) == 0#64) = true ↔ x.getLsbD k = false := by
    simp only [beq_iff_eq]
    constructor
    · intro h
      have hb := congrArg (fun v => v.getLsbD k) h
      simp [hk] at hb
      exact hb
    · intro h
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
      by_cases hi : i = k
      · subst hi; simp [h]
      · intro hi64
        simp only [hi64, decide_true, Bool.true_and]
        have hbit : (!decide (i < k) && (1#64).getLsbD (i - k)) = false := by
          by_cases hlt : i < k
          · simp [hlt]
          · have hne : i - k ≠ 0 := by omega
            simp [hlt, BitVec.getLsbD_one, hne]
        rw [hbit]; simp
  cases hx : x.getLsbD k
  · simp [h1.mpr hx]
  · have hne : ((x &&& (1#64 <<< k)) == 0#64) ≠ true := fun ht => by simp [h1.mp ht] at hx
    cases hb : ((x &&& (1#64 <<< k)) == 0#64) <;> simp_all

theorem bit32_zero_iff (x : BitVec 64) (k : Nat) (hk : k < 32) :
    (((x &&& (1#64 <<< k)).truncate 32) == 0#32) = !(x.getLsbD k) := by
  have hk64 : k < 64 := by omega
  have h1 : (((x &&& (1#64 <<< k)).truncate 32) == 0#32) = ((x &&& (1#64 <<< k)) == 0#64) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h
      apply BitVec.eq_of_getLsbD_eq
      intro i
      by_cases hi : i < 32
      · have hb := congrArg (fun v => v.getLsbD i) h
        simp only [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero,
          hi, decide_true, Bool.true_and] at hb
        rw [hb]; simp
      · simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
        intro hi64
        simp only [hi64, decide_true, Bool.true_and]
        have hbit : (!decide (i < k) && (1#64).getLsbD (i - k)) = false := by
          have hge : ¬(i < k) := by omega
          have hne : i - k ≠ 0 := by omega
          simp [hge, BitVec.getLsbD_one, hne]
        rw [hbit]; simp
    · intro h
      apply BitVec.eq_of_getLsbD_eq
      intro i
      have hb := congrArg (fun v => v.getLsbD i) h
      simp only [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero] at hb ⊢
      by_cases hi : i < 32
      · simp [hi, hb]
      · simp [hi]
  rw [h1, bit64_zero_iff x k hk64]

end FlagLemmas

theorem subs64_n (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.n = (x - y).msb :=
  congrArg BitVec.msb (addWithCarry64_sub_fst x y)

theorem subs32_n (x y : BitVec 32) : (AddWithCarry32 x (~~~y) true).2.n = (x - y).msb :=
  congrArg BitVec.msb (addWithCarry32_sub_fst x y)

theorem subs64_v (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.v = BitVec.ssubOverflow x y := by
  have hge := conditionHolds_ge_subs64 x y
  dsimp only [ConditionHolds] at hge
  rw [subs64_n] at hge
  have hv : (AddWithCarry64 x (~~~y) true).2.v = ((x - y).msb == BitVec.sle y x) := by
    cases h1 : (x - y).msb <;> cases h2 : (AddWithCarry64 x (~~~y) true).2.v <;> simp_all
  rw [hv, Bool.eq_iff_iff]
  have hxl := x.isLt; have hyl := y.isLt
  simp only [BitVec.ssubOverflow, BitVec.sle, BitVec.toInt, BitVec.msb_eq_decide,
    BitVec.toNat_sub, beq_iff_eq, decide_eq_decide, decide_eq_true_eq, Bool.or_eq_true,
    Nat.reduceSub, Nat.reducePow]
  omega

theorem subs32_v (x y : BitVec 32) : (AddWithCarry32 x (~~~y) true).2.v = BitVec.ssubOverflow x y := by
  have hge := conditionHolds_ge_subs32 x y
  dsimp only [ConditionHolds] at hge
  rw [subs32_n] at hge
  have hv : (AddWithCarry32 x (~~~y) true).2.v = ((x - y).msb == BitVec.sle y x) := by
    cases h1 : (x - y).msb <;> cases h2 : (AddWithCarry32 x (~~~y) true).2.v <;> simp_all
  rw [hv, Bool.eq_iff_iff]
  have hxl := x.isLt; have hyl := y.isLt
  simp only [BitVec.ssubOverflow, BitVec.sle, BitVec.toInt, BitVec.msb_eq_decide,
    BitVec.toNat_sub, beq_iff_eq, decide_eq_decide, decide_eq_true_eq, Bool.or_eq_true,
    Nat.reduceSub, Nat.reducePow]
  omega

theorem adds64_n (x y : BitVec 64) : (AddWithCarry64 x y false).2.n = (x + y).msb :=
  congrArg BitVec.msb (addWithCarry64_add_fst x y)

theorem adds32_n (x y : BitVec 32) : (AddWithCarry32 x y false).2.n = (x + y).msb :=
  congrArg BitVec.msb (addWithCarry32_add_fst x y)

theorem adds64_c (x y : BitVec 64) : (AddWithCarry64 x y false).2.c = BitVec.uaddOverflow x y := by
  simp only [AddWithCarry64, BitVec.uaddOverflow, Bool.false_eq_true, ite_false,
    BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hxl := x.isLt; have hyl := y.isLt
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem adds32_c (x y : BitVec 32) : (AddWithCarry32 x y false).2.c = BitVec.uaddOverflow x y := by
  simp only [AddWithCarry32, BitVec.uaddOverflow, Bool.false_eq_true, ite_false,
    BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hxl := x.isLt; have hyl := y.isLt
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem adds64_v (x y : BitVec 64) : (AddWithCarry64 x y false).2.v = BitVec.saddOverflow x y := by
  simp only [AddWithCarry64, Bool.false_eq_true, ite_false, BitVec.zero_add,
    BitVec.saddOverflow, BitVec.toInt, BitVec.msb_eq_decide, BitVec.toNat_add,
    BitVec.toNat_signExtend, BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.reduceSub, Nat.reducePow]
  have hxl := x.isLt; have hyl := y.isLt
  simp only [Nat.reducePow] at hxl hyl
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_decide, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : 9223372036854775808 ≤ x.toNat <;> by_cases hy : 9223372036854775808 ≤ y.toNat <;>
    simp only [hx, hy, ↓reduceIte] <;> omega

theorem adds32_v (x y : BitVec 32) : (AddWithCarry32 x y false).2.v = BitVec.saddOverflow x y := by
  simp only [AddWithCarry32, Bool.false_eq_true, ite_false, BitVec.zero_add,
    BitVec.saddOverflow, BitVec.toInt, BitVec.msb_eq_decide, BitVec.toNat_add,
    BitVec.toNat_signExtend, BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.reduceSub, Nat.reducePow]
  have hxl := x.isLt; have hyl := y.isLt
  simp only [Nat.reducePow] at hxl hyl
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_decide, Bool.or_eq_true, decide_eq_true_eq]
  by_cases hx : 2147483648 ≤ x.toNat <;> by_cases hy : 2147483648 ≤ y.toNat <;>
    simp only [hx, hy, ↓reduceIte] <;> omega

theorem saddOverflow_64_eq (x y : BitVec 64) :
    BitVec.saddOverflow x y =
      ((x.toNat < 9223372036854775808 && y.toNat < 9223372036854775808 &&
        9223372036854775808 ≤ (x.toNat + y.toNat) % 18446744073709551616) ||
       (9223372036854775808 ≤ x.toNat && 9223372036854775808 ≤ y.toNat &&
        (x.toNat + y.toNat) % 18446744073709551616 < 9223372036854775808)) := by
  have hxl := x.isLt; have hyl := y.isLt
  simp only [BitVec.saddOverflow, BitVec.toInt, Nat.reduceSub, Nat.reducePow] at hxl hyl ⊢
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> omega

theorem saddOverflow_32_eq (x y : BitVec 32) :
    BitVec.saddOverflow x y =
      ((x.toNat < 2147483648 && y.toNat < 2147483648 &&
        2147483648 ≤ (x.toNat + y.toNat) % 4294967296) ||
       (2147483648 ≤ x.toNat && 2147483648 ≤ y.toNat &&
        (x.toNat + y.toNat) % 4294967296 < 2147483648)) := by
  have hxl := x.isLt; have hyl := y.isLt
  simp only [BitVec.saddOverflow, BitVec.toInt, Nat.reduceSub, Nat.reducePow] at hxl hyl ⊢
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  split <;> split <;> omega

theorem adds64_eq_neg (x y : BitVec 64) : (x + y == 0#64) = (x == -y) := by
  bv_bits

theorem adds32_eq_neg (x y : BitVec 32) : (x + y == 0#32) = (x == -y) := by
  bv_bits

theorem adds64_c_neg (x nk : BitVec 64) (hne : nk ≠ 0#64) :
    (AddWithCarry64 x (0#64 - nk) false).2.c = BitVec.ule nk x := by
  rw [adds64_c]
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.uaddOverflow, BitVec.ule, decide_eq_true_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hnk0 : nk.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  have hxl := x.isLt; have hnkl := nk.isLt
  omega

theorem adds32_c_neg (x nk : BitVec 32) (hne : nk ≠ 0#32) :
    (AddWithCarry32 x (0#32 - nk) false).2.c = BitVec.ule nk x := by
  rw [adds32_c]
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.uaddOverflow, BitVec.ule, decide_eq_true_eq, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have hnk0 : nk.toNat ≠ 0 := fun h0 => hne (BitVec.eq_of_toNat_eq h0)
  have hxl := x.isLt; have hnkl := nk.isLt
  omega

theorem trunc32_sub (x y : BitVec 64) : (x - y).truncate 32 = x.truncate 32 - y.truncate 32 := by
  bv_bits

theorem subsCond?_sound {env : Env} {w : Width} {a c : SExpr} {cond : CondCode} {sc : SCond}
    (h : subsCond? w a c cond = some sc) :
    ConditionHolds cond (((evalAddSub w .SUBS (a.eval env) (c.eval env) none).2).getD PState.zero) =
      sc.eval env := by
  cases w
  · simp only [evalAddSub, ite_true, Option.getD_some]
    cases cond <;> simp only [subsCond?] at h <;> cases h <;>
      simp only [SCond.eval, SExpr.eval, conditionHolds_eq_subs32, conditionHolds_ne_subs32,
        conditionHolds_cs_subs32, conditionHolds_cc_subs32, conditionHolds_hi_subs32,
        conditionHolds_ls_subs32, conditionHolds_ge_subs32, conditionHolds_lt_subs32,
        conditionHolds_gt_subs32, conditionHolds_le_subs32, trunc32_sub] <;>
      try rfl
    all_goals (simp only [ConditionHolds, subs32_n])
  · simp only [evalAddSub, ite_true, Option.getD_some]
    cases cond <;> simp only [subsCond?] at h <;> cases h <;>
      simp only [SCond.eval, SExpr.eval, conditionHolds_eq_subs64, conditionHolds_ne_subs64,
        conditionHolds_cs_subs64, conditionHolds_cc_subs64, conditionHolds_hi_subs64,
        conditionHolds_ls_subs64, conditionHolds_ge_subs64, conditionHolds_lt_subs64,
        conditionHolds_gt_subs64, conditionHolds_le_subs64] <;>
      try rfl
    all_goals (simp only [ConditionHolds, subs64_n])

theorem trunc32_add (x y : BitVec 64) : (x + y).truncate 32 = x.truncate 32 + y.truncate 32 := by
  bv_bits

theorem trunc32_neg (x : BitVec 64) : (-x).truncate 32 = -x.truncate 32 := by
  bv_bits

theorem sub_zero_sub_32 (x : BitVec 32) : 0#32 - (0#32 - x) = x := by
  bv_bits

theorem sub_zero_sub_64 (x : BitVec 64) : 0#64 - (0#64 - x) = x := by
  bv_bits

theorem adds64_z_neg (x y : BitVec 64) : (AddWithCarry64 x y false).2.z = (x == -y) := by
  rw [← adds64_eq_neg]; exact conditionHolds_eq_adds64 x y

theorem adds32_z_neg (x y : BitVec 32) : (AddWithCarry32 x y false).2.z = (x == -y) := by
  rw [← adds32_eq_neg]; exact conditionHolds_eq_adds32 x y

theorem addsCond32_base (x y : BitVec 32) : ∀ cond : CondCode,
    ConditionHolds cond (AddWithCarry32 x y false).2 =
      match cond with
      | .EQ => (x == -y)
      | .NE => !(x == -y)
      | .CS => BitVec.uaddOverflow x y
      | .CC => !BitVec.uaddOverflow x y
      | .MI => (x + y).msb
      | .PL => !(x + y).msb
      | .VS => BitVec.saddOverflow x y
      | .VC => !BitVec.saddOverflow x y
      | .HI => BitVec.uaddOverflow x y && !(x == -y)
      | .LS => !(BitVec.uaddOverflow x y && !(x == -y))
      | .GE => ((x + y).msb && BitVec.saddOverflow x y) || (!(x + y).msb && !BitVec.saddOverflow x y)
      | .LT => ((x + y).msb && !BitVec.saddOverflow x y) || (!(x + y).msb && BitVec.saddOverflow x y)
      | .GT => !(x == -y) && (((x + y).msb && BitVec.saddOverflow x y) || (!(x + y).msb && !BitVec.saddOverflow x y))
      | .LE => (x == -y) || (((x + y).msb && !BitVec.saddOverflow x y) || (!(x + y).msb && BitVec.saddOverflow x y))
      | .AL | .NV => true
  | .EQ => adds32_z_neg x y
  | .NE => congrArg not (adds32_z_neg x y)
  | .CS => adds32_c x y
  | .CC => congrArg not (adds32_c x y)
  | .MI => adds32_n x y
  | .PL => congrArg not (adds32_n x y)
  | .VS => adds32_v x y
  | .VC => congrArg not (adds32_v x y)
  | .HI => by simp only [ConditionHolds, adds32_c, adds32_z_neg]
  | .LS => by simp only [ConditionHolds, adds32_c, adds32_z_neg]
  | .GE => by
    simp only [ConditionHolds, adds32_n, adds32_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .LT => by
    simp only [ConditionHolds, adds32_n, adds32_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .GT => by
    simp only [ConditionHolds, adds32_z_neg, adds32_n, adds32_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .LE => by
    simp only [ConditionHolds, adds32_z_neg, adds32_n, adds32_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .AL => rfl
  | .NV => rfl

theorem addsCond64_base (x y : BitVec 64) : ∀ cond : CondCode,
    ConditionHolds cond (AddWithCarry64 x y false).2 =
      match cond with
      | .EQ => (x == -y)
      | .NE => !(x == -y)
      | .CS => BitVec.uaddOverflow x y
      | .CC => !BitVec.uaddOverflow x y
      | .MI => (x + y).msb
      | .PL => !(x + y).msb
      | .VS => BitVec.saddOverflow x y
      | .VC => !BitVec.saddOverflow x y
      | .HI => BitVec.uaddOverflow x y && !(x == -y)
      | .LS => !(BitVec.uaddOverflow x y && !(x == -y))
      | .GE => ((x + y).msb && BitVec.saddOverflow x y) || (!(x + y).msb && !BitVec.saddOverflow x y)
      | .LT => ((x + y).msb && !BitVec.saddOverflow x y) || (!(x + y).msb && BitVec.saddOverflow x y)
      | .GT => !(x == -y) && (((x + y).msb && BitVec.saddOverflow x y) || (!(x + y).msb && !BitVec.saddOverflow x y))
      | .LE => (x == -y) || (((x + y).msb && !BitVec.saddOverflow x y) || (!(x + y).msb && BitVec.saddOverflow x y))
      | .AL | .NV => true
  | .EQ => adds64_z_neg x y
  | .NE => congrArg not (adds64_z_neg x y)
  | .CS => adds64_c x y
  | .CC => congrArg not (adds64_c x y)
  | .MI => adds64_n x y
  | .PL => congrArg not (adds64_n x y)
  | .VS => adds64_v x y
  | .VC => congrArg not (adds64_v x y)
  | .HI => by simp only [ConditionHolds, adds64_c, adds64_z_neg]
  | .LS => by simp only [ConditionHolds, adds64_c, adds64_z_neg]
  | .GE => by
    simp only [ConditionHolds, adds64_n, adds64_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .LT => by
    simp only [ConditionHolds, adds64_n, adds64_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .GT => by
    simp only [ConditionHolds, adds64_z_neg, adds64_n, adds64_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .LE => by
    simp only [ConditionHolds, adds64_z_neg, adds64_n, adds64_v]
    cases (x + y).msb <;> cases BitVec.saddOverflow x y <;> simp
  | .AL => rfl
  | .NV => rfl

theorem not_ule_eq_ult_bv {w : Nat} (a b : BitVec w) : (!BitVec.ule a b) = BitVec.ult b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem not_ult_eq_ule_bv {w : Nat} (a b : BitVec w) : (!BitVec.ult a b) = BitVec.ule b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ule, BitVec.ult, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  omega

theorem ule_and_not_beq_eq_ult_bv {w : Nat} (a b : BitVec w) :
    (BitVec.ule a b && !(b == a)) = BitVec.ult a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ule, BitVec.ult, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨hle, hne⟩
    have : a.toNat ≠ b.toNat := fun h => hne (BitVec.eq_of_toNat_eq h.symm)
    omega
  · intro hlt
    exact ⟨by omega, fun h => by subst h; omega⟩

theorem addsCond?_sound {env : Env} {w : Width} {a c : SExpr} {cond : CondCode} {sc : SCond}
    (h : addsCond? w a c cond = some sc) :
    ConditionHolds cond (((evalAddSub w .ADDS (a.eval env) (c.eval env) none).2).getD PState.zero) =
      sc.eval env := by
  have heval32 : (((evalAddSub .W32 .ADDS (a.eval env) (c.eval env) none).2).getD PState.zero) =
      (AddWithCarry32 ((a.eval env).truncate 32) ((c.eval env).truncate 32) false).2 := by
    simp only [evalAddSub, Bool.false_eq_true, ite_false, ite_true, Option.getD_some]
  have heval64 : (((evalAddSub .W64 .ADDS (a.eval env) (c.eval env) none).2).getD PState.zero) =
      (AddWithCarry64 (a.eval env) (c.eval env) false).2 := by
    simp only [evalAddSub, Bool.false_eq_true, ite_false, ite_true, Option.getD_some]
  cases w
  · rw [heval32, addsCond32_base]
    cases hcn : addsConstNeg32? c with
    | none =>
      cases cond <;> simp only [addsCond?, hcn] at h <;> cases h <;>
        simp only [SCond.eval, mkNeg_eval, SExpr.eval, trunc32_add, trunc32_neg,
          adds32_c, adds32_v]
    | some nk =>
      obtain ⟨hc0, hnk⟩ := addsConstNeg32?_sound hcn env
      have hnk_ne : (nk.eval env).truncate 32 ≠ 0#32 := by
        rw [hnk]; intro h0; apply hc0
        have := congrArg (fun z : BitVec 32 => 0#32 - z) h0
        simpa [sub_zero_sub_32] using this
      have hc_eq : (c.eval env).truncate 32 = 0#32 - (nk.eval env).truncate 32 := by
        rw [hnk, sub_zero_sub_32]
      cases cond <;> simp only [addsCond?, hcn] at h <;> cases h <;>
        simp only [SCond.eval, mkNeg_eval, SExpr.eval, trunc32_add, trunc32_neg,
          adds32_v]
      · have hcs := adds32_c_neg ((a.eval env).truncate 32) ((nk.eval env).truncate 32) hnk_ne
        rw [adds32_c] at hcs; rw [hc_eq]; exact hcs
      · have hcs := adds32_c_neg ((a.eval env).truncate 32) ((nk.eval env).truncate 32) hnk_ne
        rw [adds32_c] at hcs; rw [hc_eq, hcs]; exact not_ule_eq_ult_bv _ _
      · have hcs := adds32_c_neg ((a.eval env).truncate 32) ((nk.eval env).truncate 32) hnk_ne
        rw [adds32_c] at hcs
        have hz : ((a.eval env).truncate 32 == -(0#32 - (nk.eval env).truncate 32)) =
            ((a.eval env).truncate 32 == (nk.eval env).truncate 32) := by bv_bits
        rw [hc_eq, hcs, hz]; exact ule_and_not_beq_eq_ult_bv _ _
      · have hcs := adds32_c_neg ((a.eval env).truncate 32) ((nk.eval env).truncate 32) hnk_ne
        rw [adds32_c] at hcs
        have hz : ((a.eval env).truncate 32 == -(0#32 - (nk.eval env).truncate 32)) =
            ((a.eval env).truncate 32 == (nk.eval env).truncate 32) := by bv_bits
        rw [hc_eq, hcs, hz, ule_and_not_beq_eq_ult_bv, not_ult_eq_ule_bv]
  · rw [heval64, addsCond64_base]
    cases hcn : addsConstNeg64? c with
    | none =>
      cases cond <;> simp only [addsCond?, hcn] at h <;> cases h <;>
        simp only [SCond.eval, mkNeg_eval, SExpr.eval, adds64_c, adds64_v]
    | some nk =>
      obtain ⟨hc0, hnk⟩ := addsConstNeg64?_sound hcn env
      have hnk_ne : nk.eval env ≠ 0#64 := by
        rw [hnk]; intro h0; apply hc0
        have := congrArg (fun z : BitVec 64 => 0#64 - z) h0
        simpa [sub_zero_sub_64] using this
      have hc_eq : c.eval env = 0#64 - nk.eval env := by
        rw [hnk, sub_zero_sub_64]
      cases cond <;> simp only [addsCond?, hcn] at h <;> cases h <;>
        simp only [SCond.eval, mkNeg_eval, SExpr.eval, adds64_v]
      · have hcs := adds64_c_neg (a.eval env) (nk.eval env) hnk_ne
        rw [adds64_c] at hcs; rw [hc_eq]; exact hcs
      · have hcs := adds64_c_neg (a.eval env) (nk.eval env) hnk_ne
        rw [adds64_c] at hcs; rw [hc_eq, hcs]; exact not_ule_eq_ult_bv _ _
      · have hcs := adds64_c_neg (a.eval env) (nk.eval env) hnk_ne
        rw [adds64_c] at hcs
        have hz : (a.eval env == -(0#64 - nk.eval env)) = (a.eval env == nk.eval env) := by bv_bits
        rw [hc_eq, hcs, hz]; exact ule_and_not_beq_eq_ult_bv _ _
      · have hcs := adds64_c_neg (a.eval env) (nk.eval env) hnk_ne
        rw [adds64_c] at hcs
        have hz : (a.eval env == -(0#64 - nk.eval env)) = (a.eval env == nk.eval env) := by bv_bits
        rw [hc_eq, hcs, hz, ule_and_not_beq_eq_ult_bv, not_ult_eq_ule_bv]

theorem logicalCond?_sound {env : Env} {w : Width} {op : LogicalOp} {a c : SExpr}
    {cond : CondCode} {sc : SCond} (h : logicalCond? w op a c cond = some sc) :
    ConditionHolds cond (((evalLogical w op (a.eval env) (c.eval env) PState.zero).2).getD PState.zero) =
      sc.eval env := by
  have hop : op = .ANDS ∨ op = .BICS := by
    cases op <;> simp [logicalCond?] at h <;> simp
  have hres32 : ∀ op' c', (op' = .ANDS ∨ op' = .BICS) →
      ((logicalResExpr .W32 op' a c').eval env).truncate 32 =
        (a.eval env &&& (match op' with | .BICS => ~~~(c'.eval env) | _ => c'.eval env)).truncate 32 := by
    intro op' c' hop'
    unfold logicalResExpr
    rcases hop' with rfl | rfl <;> simp [mkLogical_eval, evalLogical] <;> bv_bits
  have hres64 : ∀ op' c', (op' = .ANDS ∨ op' = .BICS) →
      (logicalResExpr .W64 op' a c').eval env =
        a.eval env &&& (match op' with | .BICS => ~~~(c'.eval env) | _ => c'.eval env) := by
    intro op' c' hop'
    unfold logicalResExpr
    rcases hop' with rfl | rfl <;> simp [mkLogical_eval, evalLogical]
  have hz_eq :
      (((evalLogical w op (a.eval env) (c.eval env) PState.zero).2).getD PState.zero).z =
        (logicalIsZero w op a c).eval env := by
    unfold logicalIsZero
    rcases hop with rfl | rfl
    · cases c with
      | const mask =>
        dsimp only
        split
        · rename_i k hfb
          obtain ⟨hk, hmask⟩ := findBit_sound mask hfb
          cases w <;> simp only [evalLogical, ite_true, Option.getD_some, SExpr.eval, SCond.eval] at hk ⊢
          · rw [hmask, bit32_zero_iff _ _ hk]
          · rw [hmask, bit64_zero_iff _ _ hk]
        · cases w
          · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres32 _ _ (Or.inl rfl)]
            rfl
          · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres64 _ _ (Or.inl rfl)]
            rfl
      | _ =>
        cases w
        · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres32 _ _ (Or.inl rfl)]
          rfl
        · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres64 _ _ (Or.inl rfl)]
          rfl
    · cases w
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres32 _ _ (Or.inr rfl)]
        rfl
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres64 _ _ (Or.inr rfl)]
        rfl
  have hn_eq :
      (((evalLogical w op (a.eval env) (c.eval env) PState.zero).2).getD PState.zero).n =
        (logicalIsNeg w op a c).eval env := by
    unfold logicalIsNeg
    rcases hop with rfl | rfl
    · cases w
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres32 _ _ (Or.inl rfl)]
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres64 _ _ (Or.inl rfl)]
    · cases w
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres32 _ _ (Or.inr rfl)]
      · simp only [evalLogical, ite_true, Option.getD_some, SCond.eval, hres64 _ _ (Or.inr rfl)]
  have hc_eq : (((evalLogical w op (a.eval env) (c.eval env) PState.zero).2).getD PState.zero).c = false := by
    rcases hop with rfl | rfl <;> cases w <;> rfl
  have hv_eq : (((evalLogical w op (a.eval env) (c.eval env) PState.zero).2).getD PState.zero).v = false := by
    rcases hop with rfl | rfl <;> cases w <;> rfl
  rcases hop with rfl | rfl
  · simp only [logicalCond?] at h
    cases cond <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp only [ConditionHolds, SCond.eval, hz_eq, hn_eq, hc_eq, hv_eq] <;>
      (try generalize (logicalIsZero w .ANDS a c).eval env = bz) <;>
      (try generalize (logicalIsNeg w .ANDS a c).eval env = bn) <;>
      (try cases bz) <;> (try cases bn) <;> rfl
  · simp only [logicalCond?] at h
    cases cond <;> simp only [Option.some.injEq] at h <;> subst h <;>
      simp only [ConditionHolds, SCond.eval, hz_eq, hn_eq, hc_eq, hv_eq] <;>
      (try generalize (logicalIsZero w .BICS a c).eval env = bz) <;>
      (try generalize (logicalIsNeg w .BICS a c).eval env = bn) <;>
      (try cases bz) <;> (try cases bn) <;> rfl

theorem flagsCond?_sound {env : Env} {ps0 : PState} {fl : SFlags} {cond : CondCode} {sc : SCond}
    (h : flagsCond? fl cond = some sc) :
    ConditionHolds cond (fl.denote env ps0) = sc.eval env := by
  unfold flagsCond? at h
  split at h
  · rename_i w a c _
    have h' := subsCond?_sound (env := env) h
    cases w <;> simp only [SFlags.denote, evalAddSub, ite_true, Option.getD_some] at h' ⊢ <;> exact h'
  · rename_i w a c _
    have h' := addsCond?_sound (env := env) h
    cases w <;> simp only [SFlags.denote, evalAddSub, ite_true, Option.getD_some] at h' ⊢ <;> exact h'
  · rename_i w op a c _
    have h' := logicalCond?_sound (env := env) h
    have hop : op = .ANDS ∨ op = .BICS := by cases op <;> simp [logicalCond?] at h <;> simp
    rcases hop with rfl | rfl <;> cases w <;>
      simp only [SFlags.denote, evalLogical, ite_true, Option.getD_some] at h' ⊢ <;> exact h'
  · simp at h

theorem condObl_sound {env : Env} {ps0 : PState} {fl : SFlags} {cond : CondCode} {taken : Bool}
    {o : List SProp} (h : condObl fl cond taken = some o) (ho : allHold env o) :
    ConditionHolds cond (fl.denote env ps0) = taken := by
  unfold condObl at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨sc, hfc, rfl⟩ := h
  rw [flagsCond?_sound hfc]
  exact condToObl_sound sc taken ho

/-! ### `SState` Frame Lemmas -/

namespace SState

def setCell (ss : SState) (k : Nat) (c : Cell) : SState := { ss with cells := ss.cells.set k c }

@[simp] theorem setCell_cells (ss : SState) (k : Nat) (c : Cell) :
    (ss.setCell k c).cells = ss.cells.set k c := rfl
@[simp] theorem setCell_regs (ss : SState) (k : Nat) (c : Cell) :
    (ss.setCell k c).regs = ss.regs := rfl
@[simp] theorem setCell_vregs (ss : SState) (k : Nat) (c : Cell) :
    (ss.setCell k c).vregs = ss.vregs := rfl

theorem toState_setCell (ss : SState) (k : Nat) (c : Cell) (b : BitVec 64) (env : Env)
    (s0 : State) (m : Memory) : (ss.setCell k c).toState b env s0 m = ss.toState b env s0 m := rfl

variable {b : BitVec 64} {env : Env} {s0 : State} {m : Memory}

@[simp] theorem setReg64_cells (ss : SState) (r : Reg) (e : SExpr) :
    (ss.setReg64 r e).cells = ss.cells := by
  cases r with
  | gpr i => by_cases h : i = 31#5 <;> simp [setReg64, h]
  | sp => rfl
  | xzr => rfl

@[simp] theorem setReg64_vregs (ss : SState) (r : Reg) (e : SExpr) :
    (ss.setReg64 r e).vregs = ss.vregs := by
  cases r with
  | gpr i => by_cases h : i = 31#5 <;> simp [setReg64, h]
  | sp => rfl
  | xzr => rfl

@[simp] theorem setReg64_flags (ss : SState) (r : Reg) (e : SExpr) :
    (ss.setReg64 r e).flags = ss.flags := by
  cases r with
  | gpr i => by_cases h : i = 31#5 <;> simp [setReg64, h]
  | sp => rfl
  | xzr => rfl

@[simp] theorem setReg64_pc (ss : SState) (r : Reg) (e : SExpr) :
    (ss.setReg64 r e).pc = ss.pc := by
  cases r with
  | gpr i => by_cases h : i = 31#5 <;> simp [setReg64, h]
  | sp => rfl
  | xzr => rfl

@[simp] theorem setReg_cells (ss : SState) (w : Width) (r : Reg) (e : SExpr) :
    (ss.setReg w r e).cells = ss.cells := setReg64_cells ss r _

@[simp] theorem setReg_vregs (ss : SState) (w : Width) (r : Reg) (e : SExpr) :
    (ss.setReg w r e).vregs = ss.vregs := setReg64_vregs ss r _

@[simp] theorem setReg_flags (ss : SState) (w : Width) (r : Reg) (e : SExpr) :
    (ss.setReg w r e).flags = ss.flags := setReg64_flags ss r _

@[simp] theorem setVReg128_cells (ss : SState) (idx : BitVec 5) (ve : VExpr) :
    (ss.setVReg128 idx ve).cells = ss.cells := rfl
@[simp] theorem setVReg128_regs (ss : SState) (idx : BitVec 5) (ve : VExpr) :
    (ss.setVReg128 idx ve).regs = ss.regs := rfl

@[simp] theorem setTpidr_cells (ss : SState) (e : SExpr) :
    (ss.setTpidr e).cells = ss.cells := rfl
@[simp] theorem setTpidr_regs (ss : SState) (e : SExpr) :
    (ss.setTpidr e).regs = ss.regs := rfl
@[simp] theorem setTpidr_vregs (ss : SState) (e : SExpr) :
    (ss.setTpidr e).vregs = ss.vregs := rfl

@[simp] theorem applyWb_cells (ss : SState) (wb : Option (Reg × SExpr)) :
    (ss.applyWb wb).cells = ss.cells := by
  cases wb with
  | none => rfl
  | some p => obtain ⟨r, e⟩ := p; exact setReg64_cells ss r e

@[simp] theorem applyWb_vregs (ss : SState) (wb : Option (Reg × SExpr)) :
    (ss.applyWb wb).vregs = ss.vregs := by
  cases wb with
  | none => rfl
  | some p => obtain ⟨r, e⟩ := p; exact setReg64_vregs ss r e

theorem applyWb_length (ss : SState) (wb : Option (Reg × SExpr)) :
    (ss.applyWb wb).regs.length = ss.regs.length := by
  cases wb with
  | none => rfl
  | some p => obtain ⟨r, e⟩ := p; exact setReg64_length ss r e

@[simp] theorem advance_cells (ss : SState) : ss.advance.cells = ss.cells := rfl
@[simp] theorem advance_regs (ss : SState) : ss.advance.regs = ss.regs := rfl
@[simp] theorem advance_vregs (ss : SState) : ss.advance.vregs = ss.vregs := rfl

theorem symAddr_sound {ss : SState} {am : AddrMode} {ea : SExpr} {wb : Option (Reg × SExpr)}
    (h : symAddr ss am = some (ea, wb)) :
    evalAddrMode (ss.toState b env s0 m) am = (ea.eval env, wb.map fun p => (p.1, p.2.eval env)) := by
  cases am <;> simp only [symAddr, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    simp [evalAddrMode, mkAdd_eval, mkExtendVal_eval, toState_readReg64, SExpr.eval]

theorem applyWb_sound (ss : SState) (hlen : ss.regs.length = 31) (wb : Option (Reg × SExpr)) :
    applyWriteback (ss.toState b env s0 m) (wb.map fun p => (p.1, p.2.eval env)) =
      (ss.applyWb wb).toState b env s0 m := by
  cases wb with
  | none => rfl
  | some p =>
    obtain ⟨r, e⟩ := p
    simp only [Option.map_some, applyWriteback, applyWb]
    exact toState_writeReg64 ss hlen r e

theorem alignObl_sound {ss : SState} {am : AddrMode} (h : allHold env (alignObl ss am)) :
    checkAddrSPAligned (ss.toState b env s0 m) am = true := by
  unfold alignObl at h
  unfold checkAddrSPAligned checkRegSPAligned
  split at h
  · rename_i hb; rw [hb]; exact oblAligned_sound h
  · split <;> simp_all

end SState

theorem pt64At?_some {cs : List Cell} {k : Nat} {ro : Bool} {a v : SExpr}
    (h : pt64At? cs k = some (ro, a, v)) : cs[k]? = some (.pt64 ro a v) := by
  unfold pt64At? at h
  split at h
  · rename_i ro' a' v' hk; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact hk
  · simp at h

theorem pt64MutAt?_some {cs : List Cell} {k : Nat} {a v : SExpr}
    (h : pt64MutAt? cs k = some (a, v)) : cs[k]? = some (.pt64 false a v) := by
  unfold pt64MutAt? at h
  split at h
  · rename_i a' v' hk; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact hk
  · simp at h

theorem ptNAt?_some {cs : List Cell} {k : Nat} {ro : Bool} {w : CW} {a : SExpr} {v : NVal}
    (h : ptNAt? cs k = some (ro, w, a, v)) : cs[k]? = some (.ptN w ro a v) := by
  unfold ptNAt? at h
  split at h
  · rename_i w' ro' a' v' hk; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact hk
  · simp at h

theorem ptNMutAt?_some {cs : List Cell} {k : Nat} {w : CW} {a : SExpr} {v : NVal}
    (h : ptNMutAt? cs k = some (w, a, v)) : cs[k]? = some (.ptN w false a v) := by
  unfold ptNMutAt? at h
  split at h
  · rename_i w' a' v' hk; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; exact hk
  · simp at h

theorem SPc.addOff_denote (b : BitVec 64) (env : Env) (pc : SPc) (t : BitVec 64) :
    (pc.addOff t).denote b env = pc.denote b env + t := by
  cases pc <;> simp [SPc.addOff, SPc.denote, mkAdd_eval, SExpr.eval, BitVec.add_assoc]

theorem mkFlags_denote (env : Env) (ps0 : PState) (w : Width) (op : AddSubOp) (a c : SExpr)
    (prev : SFlags) :
    (mkFlags w op a c prev).denote env ps0 =
      ((evalAddSub w op (a.eval env) (c.eval env) none).2).getD (prev.denote env ps0) := by
  cases op <;> simp only [mkFlags, SFlags.denote] <;> cases w <;> simp

theorem mkLogicalFlags_denote (env : Env) (ps0 : PState) (w : Width) (op : LogicalOp)
    (a b : SExpr) (prev : SFlags) :
    (mkLogicalFlags w op a b prev).denote env ps0 =
      ((evalLogical w op (a.eval env) (b.eval env) PState.zero).2).getD (prev.denote env ps0) := by
  unfold mkLogicalFlags
  cases op <;> cases w <;> rfl

/-! ## Concrete Memory and ALU Execution Shapes -/

theorem allPerm_eight_eight (m : Memory) (p : Option Perm → Bool) (a : BitVec 64)
    (h1 : m.allPerm p a 8 = true) (h2 : m.allPerm p (a + 8#64) 8 = true) :
    m.allPerm p a 16 = true := by
  have ha : a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 = a + 8#64 := by bv_arith
  simp only [Memory.allPerm, Bool.and_eq_true, Bool.and_true] at h1 h2 ⊢
  rw [ha]
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem allNoLazyFree_eight_eight (m : Memory) (a : BitVec 64)
    (h1 : m.allNoLazyFree a 8 = true) (h2 : m.allNoLazyFree (a + 8#64) 8 = true) :
    m.allNoLazyFree a 16 = true := by
  have ha : a + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 + 1#64 = a + 8#64 := by bv_arith
  simp only [Memory.allNoLazyFree, Bool.and_eq_true, Bool.and_true] at h1 h2 ⊢
  rw [ha]
  rcases h1 with ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
  rcases h2 with ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem canRead_16_of_8 {m : Memory} {a : BitVec 64}
    (h1 : m.canRead a 8 = true) (h2 : m.canRead (a + 8#64) 8 = true) :
    m.canRead a 16 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h1 h2 ⊢
  exact ⟨allPerm_eight_eight m (·.r) a h1.1 h2.1, allNoLazyFree_eight_eight m a h1.2 h2.2⟩

theorem canWrite_16_of_8 {m : Memory} {a : BitVec 64}
    (h1 : m.canWrite a 8 = true) (h2 : m.canWrite (a + 8#64) 8 = true) :
    m.canWrite a 16 = true := by
  unfold Memory.canWrite at h1 h2 ⊢
  exact allPerm_eight_eight m (fun p => p.w && !p.x) a h1 h2

theorem execLdr_x64 {s : State} {rt : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canRead ea 8 = true) :
    execLdr .W64 .X64 false rt am s =
      ((applyWriteback s wb).writeReg .W64 rt (s.mem.read64 ea)).advancePC := by
  cases wb <;> simp [execLdr, hal, ha, hcan, Memory.readSized, applyWriteback, MemWidth.bytes]

theorem execStr_x64 {s : State} {rt : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canWrite ea 8 = true) :
    execStr .X64 rt am s =
      (applyWriteback (s.setMem (s.mem.write64 ea (s.readReg64 rt))) wb).advancePC := by
  cases wb <;> simp [execStr, hal, ha, hcan, Memory.writeSized, applyWriteback, MemWidth.bytes]

theorem execLdr_n {w : Width} {cw : CW} {s : State} {rt : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canRead ea cw.bytes = true) (hcw : cw ≠ .b128 := by decide) :
    execLdr w cw.size false rt am s =
      ((applyWriteback s wb).writeReg w rt ((CW.read s.mem cw ea).zeroExtend 64)).advancePC := by
  cases cw <;> simp only [CW.bytes, ne_eq, not_true_eq_false] at hcan hcw <;> cases wb <;>
    simp [execLdr, hal, ha, hcan, Memory.readSized, applyWriteback, CW.size, CW.read]

theorem execLdr_s {w : Width} {cw : CW} {s : State} {rt : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canRead ea cw.bytes = true) (hcw : cw ≠ .b128 := by decide) :
    execLdr w cw.size true rt am s =
      ((applyWriteback s wb).writeReg w rt ((CW.read s.mem cw ea).signExtend 64)).advancePC := by
  cases cw <;> simp only [CW.bytes, ne_eq, not_true_eq_false] at hcan hcw <;> cases wb <;>
    simp [execLdr, hal, ha, hcan, Memory.readSized, applyWriteback, CW.size, CW.read]

/-- A zero-extended narrow value is unchanged by a 32-bit register write. -/
theorem writeReg_zext (s : State) (w : Width) (cw : CW) (r : Reg) (x : BitVec cw.bits)
    (hcw : cw ≠ .b128 := by decide) :
    s.writeReg w r (x.zeroExtend 64) = s.writeReg64 r (x.zeroExtend 64) := by
  cases w
  · simp only [State.writeReg]
    congr 1
    cases cw <;> simp only [CW.bits, ne_eq, not_true_eq_false] at x hcw ⊢ <;> bv_bits
  · rfl

theorem execStr_n {cw : CW} {s : State} {rt : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canWrite ea cw.bytes = true) (hcw : cw ≠ .b128 := by decide) :
    execStr cw.size rt am s =
      (applyWriteback (s.setMem (CW.write s.mem cw ea ((s.readReg64 rt).truncate cw.bits))) wb).advancePC := by
  cases cw <;> simp only [CW.bytes, ne_eq, not_true_eq_false] at hcan hcw <;> cases wb <;>
    simp [execStr, hal, ha, hcan, Memory.writeSized, applyWriteback, CW.size, CW.write]

theorem execLdp_x64 {s : State} {rt1 rt2 : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canRead ea 8 = true) (hcan2 : s.mem.canRead (ea + 8#64) 8 = true) :
    execLdp .W64 false rt1 rt2 am s =
      (((applyWriteback s wb).writeReg .W64 rt1 (s.mem.read64 ea)).writeReg .W64 rt2
        (s.mem.read64 (ea + 8#64))).advancePC := by
  cases wb <;>
    simp [execLdp, hal, ha, hcan1, hcan2, Memory.readSized, applyWriteback, MemWidth.bytes]

theorem execLdp_w32 {s : State} {rt1 rt2 : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canRead ea 4 = true) (hcan2 : s.mem.canRead (ea + 4#64) 4 = true) :
    execLdp .W32 false rt1 rt2 am s =
      (((applyWriteback s wb).writeReg64 rt1 ((s.mem.read32 ea).zeroExtend 64)).writeReg64 rt2
        ((s.mem.read32 (ea + 4#64)).zeroExtend 64)).advancePC := by
  have hz1 : ∀ st : State, st.writeReg .W32 rt1 ((s.mem.read32 ea).zeroExtend 64) =
      st.writeReg64 rt1 ((s.mem.read32 ea).zeroExtend 64) :=
    fun st => writeReg_zext st .W32 .b32 rt1 (s.mem.read32 ea)
  have hz2 : ∀ st : State, st.writeReg .W32 rt2 ((s.mem.read32 (ea + 4#64)).zeroExtend 64) =
      st.writeReg64 rt2 ((s.mem.read32 (ea + 4#64)).zeroExtend 64) :=
    fun st => writeReg_zext st .W32 .b32 rt2 (s.mem.read32 (ea + 4#64))
  cases wb <;>
    simp [execLdp, hal, ha, hcan1, hcan2, Memory.readSized, applyWriteback, MemWidth.bytes, hz1, hz2]

theorem execLdp_sw {s : State} {rt1 rt2 : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canRead ea 4 = true) (hcan2 : s.mem.canRead (ea + 4#64) 4 = true) :
    execLdp .W64 true rt1 rt2 am s =
      (((applyWriteback s wb).writeReg64 rt1 ((s.mem.read32 ea).signExtend 64)).writeReg64 rt2
        ((s.mem.read32 (ea + 4#64)).signExtend 64)).advancePC := by
  cases wb <;>
    simp [execLdp, hal, ha, hcan1, hcan2, Memory.readSized, applyWriteback, MemWidth.bytes]

theorem execStp_x64 {s : State} {rt1 rt2 : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canWrite ea 8 = true) (hcan2 : s.mem.canWrite (ea + 8#64) 8 = true) :
    execStp .W64 rt1 rt2 am s =
      (applyWriteback (s.setMem ((s.mem.write64 ea (s.readReg64 rt1)).write64 (ea + 8#64)
        (s.readReg64 rt2))) wb).advancePC := by
  cases wb <;>
    simp [execStp, hal, ha, hcan1, hcan2, Memory.writeSized, applyWriteback, MemWidth.bytes]

theorem execStp_w32 {s : State} {rt1 rt2 : Reg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canWrite ea 4 = true) (hcan2 : s.mem.canWrite (ea + 4#64) 4 = true) :
    execStp .W32 rt1 rt2 am s =
      (applyWriteback (s.setMem ((s.mem.write32 ea ((s.readReg64 rt1).truncate 32)).write32
        (ea + 4#64) ((s.readReg64 rt2).truncate 32))) wb).advancePC := by
  cases wb <;>
    simp [execStp, hal, ha, hcan1, hcan2, Memory.writeSized, applyWriteback, MemWidth.bytes]

theorem execLdrSimdQ_eq {s : State} {vt : VReg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canRead ea 16 = true) :
    execLdrSimdQ vt am s =
      ((applyWriteback s wb).writeVReg128 vt (s.mem.read128 ea)).advancePC := by
  cases wb <;> simp [execLdrSimdQ, hal, ha, hcan, applyWriteback]

theorem execStrSimdQ_eq {s : State} {vt : VReg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan : s.mem.canWrite ea 16 = true) :
    execStrSimdQ vt am s =
      (applyWriteback (s.setMem (s.mem.write128 ea (s.readVReg128 vt))) wb).advancePC := by
  cases wb <;> simp [execStrSimdQ, hal, ha, hcan, applyWriteback]

theorem execLdpSimdQ_eq {s : State} {vt1 vt2 : VReg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canRead ea 16 = true) (hcan2 : s.mem.canRead (ea + 16#64) 16 = true) :
    execLdpSimdQ vt1 vt2 am s =
      (((applyWriteback s wb).writeVReg128 vt1 (s.mem.read128 ea)).writeVReg128 vt2
        (s.mem.read128 (ea + 16#64))).advancePC := by
  cases wb <;> simp [execLdpSimdQ, hal, ha, hcan1, hcan2, applyWriteback]

theorem execStpSimdQ_eq {s : State} {vt1 vt2 : VReg} {am : AddrMode} {ea : BitVec 64}
    {wb : Option (Reg × BitVec 64)}
    (hal : checkAddrSPAligned s am = true) (ha : evalAddrMode s am = (ea, wb))
    (hcan1 : s.mem.canWrite ea 16 = true) (hcan2 : s.mem.canWrite (ea + 16#64) 16 = true) :
    execStpSimdQ vt1 vt2 am s =
      (applyWriteback (s.setMem ((s.mem.write128 ea (s.readVReg128 vt1)).write128 (ea + 16#64)
        (s.readVReg128 vt2))) wb).advancePC := by
  cases wb <;> simp [execStpSimdQ, hal, ha, hcan1, hcan2, applyWriteback]

theorem execAddSubImm_eq (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (shift12 : Bool) (s : State) :
    let imm := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
    execAddSubImm w op rd rn imm12 shift12 s =
      ((s.writeReg w rd (evalAddSub w op (s.readReg w rn) imm none).1).setPState
        ((evalAddSub w op (s.readReg w rn) imm none).2.getD s.pstate)).advancePC := by
  simp only [execAddSubImm]
  generalize evalAddSub w op (s.readReg w rn)
    (if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64) none = p
  obtain ⟨r, o⟩ := p; cases o <;> rfl

theorem execAddSubShift_eq (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType)
    (amount : Nat) (s : State) :
    execAddSubShift w op rd rn rm shift amount s =
      ((s.writeReg w rd (evalAddSub w op (s.readReg w rn) (shiftVal w (s.readReg w rm) shift amount) none).1).setPState
        ((evalAddSub w op (s.readReg w rn) (shiftVal w (s.readReg w rm) shift amount) none).2.getD s.pstate)).advancePC := by
  simp only [execAddSubShift]
  generalize evalAddSub w op _ _ none = p
  obtain ⟨r, o⟩ := p; cases o <;> rfl

theorem execAddSubExt_eq (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amount : Nat) (s : State) :
    execAddSubExt w op rd rn rm ext amount s =
      ((s.writeReg w rd (evalAddSub w op (s.readReg w rn) (extendVal w (s.readReg64 rm) ext amount) none).1).setPState
        ((evalAddSub w op (s.readReg w rn) (extendVal w (s.readReg64 rm) ext amount) none).2.getD s.pstate)).advancePC := by
  simp only [execAddSubExt]
  generalize evalAddSub w op _ _ none = p
  obtain ⟨r, o⟩ := p; cases o <;> rfl

theorem execLogicalImm_eq (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64) (s : State) :
    execLogicalImm w op rd rn imm s =
      ((s.writeReg w rd (evalLogical w op (s.readReg w rn) imm PState.zero).1).setPState
        ((evalLogical w op (s.readReg w rn) imm PState.zero).2.getD s.pstate)).advancePC := by
  simp only [execLogicalImm, evalLogical_fst_psOld, evalLogical_snd_psOld]
  generalize evalLogical w op (s.readReg w rn) imm PState.zero = p
  obtain ⟨r, o⟩ := p; cases o <;> rfl

theorem execLogicalShift_eq (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType)
    (amount : Nat) (s : State) :
    execLogicalShift w op rd rn rm shift amount s =
      ((s.writeReg w rd (evalLogical w op (s.readReg w rn) (shiftVal w (s.readReg w rm) shift amount) PState.zero).1).setPState
        ((evalLogical w op (s.readReg w rn) (shiftVal w (s.readReg w rm) shift amount) PState.zero).2.getD s.pstate)).advancePC := by
  simp only [execLogicalShift, evalLogical_fst_psOld, evalLogical_snd_psOld]
  generalize evalLogical w op (s.readReg w rn) _ PState.zero = p
  obtain ⟨r, o⟩ := p; cases o <;> rfl

/-! ## Symbolic Step -/

/-- Page base of a PC-relative address when the code base `b` is 4 KiB aligned. -/
theorem adrp_page_add {b o : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (b + o) &&& 0xfffffffffffff000#64 = b + (o &&& 0xfffffffffffff000#64) := by
  bv_bits

/-- Split `e + c` into `(e, c)` (otherwise `(e, 0)`); used to find the page-aligned root of the
    code base. -/
def splitOff : SExpr → SExpr × BitVec 64
  | .add e (.const c) => (e, c)
  | e => (e, 0#64)

theorem splitOff_eval (env : Env) (e : SExpr) :
    e.eval env = (splitOff e).1.eval env + (splitOff e).2 := by
  unfold splitOff
  split <;> simp [SExpr.eval]

/-- Invariant on `ss.vregs`: either empty (no SIMD instructions executed yet) or length 32. -/
def VRegsValid (vregs : List VExpr) : Prop :=
  vregs = [] ∨ vregs.length = 32

/-- Symbolic execution of one micro-op under advice `h`. `base` is a symbolic expression for the
    code base `b` (the PC is `b + o`); it is only used by PC-relative instructions. -/
def stepOp (base : SExpr) (ss : SState) (op : MOp) (h : Hint) : Option (SState × List SProp) :=
  match op, h with
  | .ldr .W64 .X64 rt am, .cell k =>
    match symAddr ss am, pt64At? ss.cells k with
    | some (ea, wb), some (_, ca, cv) =>
      some (((ss.applyWb wb).setReg .W64 rt cv).advance, alignObl ss am ++ oblEq ea ca)
    | _, _ => none
  | .str .X64 rt am, .cell k =>
    match symAddr ss am, pt64MutAt? ss.cells k with
    | some (ea, wb), some (ca, _) =>
      some (((ss.setCell k (.pt64 false ca (ss.readReg64 rt))).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca)
    | _, _ => none
  | .ldp .W64 false rt1 rt2 am, .cell2 k1 k2 =>
    match symAddr ss am, pt64At? ss.cells k1, pt64At? ss.cells k2 with
    | some (ea, wb), some (_, ca1, cv1), some (_, ca2, cv2) =>
      some ((((ss.applyWb wb).setReg .W64 rt1 cv1).setReg .W64 rt2 cv2).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2)
    | _, _, _ => none
  | .ldp .W32 false rt1 rt2 am, .cell2 k1 k2 =>
    match symAddr ss am, ptNAt? ss.cells k1, ptNAt? ss.cells k2 with
    | some (ea, wb), some (_, .b32, ca1, cv1), some (_, .b32, ca2, cv2) =>
      some ((((ss.applyWb wb).setReg64 rt1 (cv1.zext .b32)).setReg64 rt2 (cv2.zext .b32)).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 4#64)) ca2)
    | _, _, _ => none
  | .ldp .W64 true rt1 rt2 am, .cell2 k1 k2 =>
    match symAddr ss am, ptNAt? ss.cells k1, ptNAt? ss.cells k2 with
    | some (ea, wb), some (_, .b32, ca1, cv1), some (_, .b32, ca2, cv2) =>
      some ((((ss.applyWb wb).setReg64 rt1 (cv1.sext .b32)).setReg64 rt2 (cv2.sext .b32)).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 4#64)) ca2)
    | _, _, _ => none
  | .stp .W64 rt1 rt2 am, .cell2 k1 k2 =>
    if k1 = k2 then none else
    match symAddr ss am, pt64MutAt? ss.cells k1, pt64MutAt? ss.cells k2 with
    | some (ea, wb), some (ca1, _), some (ca2, _) =>
      some ((((ss.setCell k1 (.pt64 false ca1 (ss.readReg64 rt1))).setCell k2
          (.pt64 false ca2 (ss.readReg64 rt2))).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2)
    | _, _, _ => none
  | .stp .W32 rt1 rt2 am, .cell2 k1 k2 =>
    if k1 = k2 then none else
    match symAddr ss am, ptNMutAt? ss.cells k1, ptNMutAt? ss.cells k2 with
    | some (ea, wb), some (.b32, ca1, _), some (.b32, ca2, _) =>
      some ((((ss.setCell k1 (.ptN .b32 false ca1 (mkTrunc .b32 (ss.readReg64 rt1)))).setCell k2
          (.ptN .b32 false ca2 (mkTrunc .b32 (ss.readReg64 rt2)))).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 4#64)) ca2)
    | _, _, _ => none
  | .ldrSimdQ vt am, .cell k =>
    if ss.vregs.length ≠ 32 then none else
    match symAddr ss am, ptNAt? ss.cells k with
    | some (ea, wb), some (_, .b128, ca, cv) =>
      some (((ss.applyWb wb).setVReg128 vt cv.toVExpr).advance,
        alignObl ss am ++ oblEq ea ca)
    | _, _ => none
  | .ldrSimdQ vt am, .cell2 k1 k2 =>
    if ss.vregs.length ≠ 32 then none else
    match symAddr ss am, pt64At? ss.cells k1, pt64At? ss.cells k2 with
    | some (ea, wb), some (_, ca1, cv1), some (_, ca2, cv2) =>
      some (((ss.applyWb wb).setVReg128 vt (.pair64 cv2 cv1)).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2)
    | _, _, _ => none
  | .strSimdQ vt am, .cell k =>
    if ss.vregs.length ≠ 32 then none else
    match symAddr ss am, ptNMutAt? ss.cells k with
    | some (ea, wb), some (.b128, ca, _) =>
      some (((ss.setCell k (.ptN .b128 false ca (.v128 (ss.vreg vt.toNat)))).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca)
    | _, _ => none
  | .strSimdQ vt am, .cell2 k1 k2 =>
    if ss.vregs.length ≠ 32 || k1 = k2 then none else
    match symAddr ss am, pt64MutAt? ss.cells k1, pt64MutAt? ss.cells k2 with
    | some (ea, wb), some (ca1, _), some (ca2, _) =>
      let ve := ss.vreg vt.toNat
      some ((((ss.setCell k1 (.pt64 false ca1 ve.lo64)).setCell k2
          (.pt64 false ca2 ve.hi64)).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2)
    | _, _, _ => none
  | .ldpSimdQ vt1 vt2 am, .cell2 k1 k2 =>
    if ss.vregs.length ≠ 32 then none else
    match symAddr ss am, ptNAt? ss.cells k1, ptNAt? ss.cells k2 with
    | some (ea, wb), some (_, .b128, ca1, cv1), some (_, .b128, ca2, cv2) =>
      some ((((ss.applyWb wb).setVReg128 vt1 cv1.toVExpr).setVReg128 vt2 cv2.toVExpr).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 16#64)) ca2)
    | _, _, _ => none
  | .ldpSimdQ vt1 vt2 am, .cell4 k1 k2 k3 k4 =>
    if ss.vregs.length ≠ 32 then none else
    match symAddr ss am, pt64At? ss.cells k1, pt64At? ss.cells k2,
        pt64At? ss.cells k3, pt64At? ss.cells k4 with
    | some (ea, wb), some (_, ca1, cv1), some (_, ca2, cv2),
        some (_, ca3, cv3), some (_, ca4, cv4) =>
      some ((((ss.applyWb wb).setVReg128 vt1 (.pair64 cv2 cv1)).setVReg128 vt2
          (.pair64 cv4 cv3)).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2 ++
          oblEq (mkAdd ea (.const 16#64)) ca3 ++ oblEq (mkAdd ea (.const 24#64)) ca4)
    | _, _, _, _, _ => none
  | .stpSimdQ vt1 vt2 am, .cell2 k1 k2 =>
    if ss.vregs.length ≠ 32 || k1 = k2 then none else
    match symAddr ss am, ptNMutAt? ss.cells k1, ptNMutAt? ss.cells k2 with
    | some (ea, wb), some (.b128, ca1, _), some (.b128, ca2, _) =>
      some ((((ss.setCell k1 (.ptN .b128 false ca1 (.v128 (ss.vreg vt1.toNat)))).setCell k2
          (.ptN .b128 false ca2 (.v128 (ss.vreg vt2.toNat)))).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 16#64)) ca2)
    | _, _, _ => none
  | .stpSimdQ vt1 vt2 am, .cell4 k1 k2 k3 k4 =>
    if ss.vregs.length ≠ 32 ||
        k1 = k2 || k1 = k3 || k1 = k4 || k2 = k3 || k2 = k4 || k3 = k4 then none else
    match symAddr ss am, pt64MutAt? ss.cells k1, pt64MutAt? ss.cells k2,
        pt64MutAt? ss.cells k3, pt64MutAt? ss.cells k4 with
    | some (ea, wb), some (ca1, _), some (ca2, _), some (ca3, _), some (ca4, _) =>
      let ve1 := ss.vreg vt1.toNat
      let ve2 := ss.vreg vt2.toNat
      some ((((((ss.setCell k1 (.pt64 false ca1 ve1.lo64)).setCell k2
          (.pt64 false ca2 ve1.hi64)).setCell k3 (.pt64 false ca3 ve2.lo64)).setCell k4
          (.pt64 false ca4 ve2.hi64)).applyWb wb).advance,
        alignObl ss am ++ oblEq ea ca1 ++ oblEq (mkAdd ea (.const 8#64)) ca2 ++
          oblEq (mkAdd ea (.const 16#64)) ca3 ++ oblEq (mkAdd ea (.const 24#64)) ca4)
    | _, _, _, _, _ => none
  | .addSubImm w op rd rn imm12 shift12, _ =>
    let x := ss.readReg w rn
    let imm := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
    let y := SExpr.const imm
    some ({ ss.setReg w rd (mkAddSub w op x y) with flags := mkFlags w op x y ss.flags }.advance, [])
  | .addSubShift w op rd rn rm shift amount, _ =>
    let x := ss.readReg w rn
    let y := mkShiftVal w (ss.readReg w rm) shift amount
    some ({ ss.setReg w rd (mkAddSub w op x y) with flags := mkFlags w op x y ss.flags }.advance, [])
  | .addSubExt w op rd rn rm ext amount, _ =>
    let x := ss.readReg w rn
    let y := mkExtendVal w (ss.readReg64 rm) ext amount
    some ({ ss.setReg w rd (mkAddSub w op x y) with flags := mkFlags w op x y ss.flags }.advance, [])
  | .logicalImm w op rd rn imm, _ =>
    let x := ss.readReg w rn
    let y := SExpr.const imm
    some ({ ss.setReg w rd (mkLogical w op x y) with
            flags := mkLogicalFlags w op x y ss.flags }.advance, [])
  | .logicalShift w op rd rn rm shift amount, _ =>
    let x := ss.readReg w rn
    let y := mkShiftVal w (ss.readReg w rm) shift amount
    some ({ ss.setReg w rd (mkLogical w op x y) with
            flags := mkLogicalFlags w op x y ss.flags }.advance, [])
  | .bitfield w op rd rn immr imms, _ =>
    some ((ss.setReg w rd (.bitfield w op (ss.readReg w rd) (ss.readReg w rn) immr imms)).advance, [])
  | .movWide w .MOVZ rd imm16 hw, _ =>
    some ((ss.setReg w rd (.const ((imm16.zeroExtend 64) <<< hw))).advance, [])
  | .movWide w .MOVN rd imm16 hw, _ =>
    some ((ss.setReg w rd (.const (~~~((imm16.zeroExtend 64) <<< hw)))).advance, [])
  | .movWide w .MOVK rd imm16 hw, _ =>
    some ((ss.setReg w rd (mkMovk (ss.readReg w rd) imm16 hw)).advance, [])
  | .condSelect w op rd rn rm cond, _ =>
    match flagsCond? ss.flags cond with
    | some c =>
      let tExpr := ss.readReg w rn
      let mExpr := ss.readReg w rm
      let fExpr :=
        match op with
        | .CSEL  => mExpr
        | .CSINC => mkAdd mExpr (.const 1#64)
        | .CSINV => .xor mExpr (.const 0xffffffffffffffff#64)
        | .CSNEG => mkNeg mExpr
      some ((ss.setReg w rd (mkIte c tExpr fExpr)).advance, [])
    | none => none
  | .dataProc1 w op rd rn, _ =>
    some ((ss.setReg w rd (.dataProc1 w op (ss.readReg w rn))).advance, [])
  | .dataProc3 w op rd rn rm ra, _ =>
    some ((ss.setReg w rd (mkDataProc3 w op (ss.readReg64 rn) (ss.readReg64 rm)
      (ss.readReg64 ra))).advance, [])
  | .b target, _ => some ({ ss with pc := ss.pc.addOff target }, [])
  | .bcond cond target, .br taken =>
    match condObl ss.flags cond taken with
    | some o => some (if taken then { ss with pc := ss.pc.addOff target } else ss.advance, o)
    | none => none
  | .cbz w rt target, .br taken =>
    some (if taken then { ss with pc := ss.pc.addOff target } else ss.advance,
      if taken then oblEq (ss.readReg w rt) (.const 0#64) else [.ne (ss.readReg w rt) (.const 0#64)])
  | .cbnz w rt target, .br taken =>
    some (if taken then { ss with pc := ss.pc.addOff target } else ss.advance,
      if taken then [.ne (ss.readReg w rt) (.const 0#64)] else oblEq (ss.readReg w rt) (.const 0#64))
  | .tbz isNonZero rt bitPos target, .br taken =>
    some (if taken then { ss with pc := ss.pc.addOff target } else ss.advance,
      condToObl (.bit (ss.readReg64 rt) bitPos) (if taken then isNonZero else !isNonZero))
  | .ret rn, _ => some ({ ss with pc := .abs (ss.readReg64 rn) }, [])
  | .adr rd target, _ =>
    match ss.pc with
    | .rel o =>
      some ((ss.setReg64 rd (mkAdd base (.const (o + target)))).advance, [])
    | .abs _ => none
  | .adrp rd target, _ =>
    match ss.pc with
    | .rel o =>
      some ((ss.setReg64 rd (mkAdd (splitOff base).1
          (.const ((((splitOff base).2 + o) &&& 0xfffffffffffff000#64) + target)))).advance,
        oblEq (.and (splitOff base).1 (.const 0xfff#64)) (.const 0#64))
    | .abs _ => none
  | .nop, _ => some (ss.advance, [])
  | .mrsTpidr rt, _ => some ((ss.setReg64 rt ss.tpidr).advance, [])
  | .msrTpidr rt, _ => some ((ss.setTpidr (ss.readReg64 rt)).advance, [])
  | .mrsDczid rt, _ => some ((ss.setReg64 rt (.const 4#64)).advance, [])
  | .ldrN _ cw rt am, .cell k =>
    if cw == .b128 then none else
    match symAddr ss am, ptNAt? ss.cells k with
    | some (ea, wb), some (_, cw', ca, cv) =>
      if cw' = cw then
        some (((ss.applyWb wb).setReg64 rt (cv.zext cw)).advance, alignObl ss am ++ oblEq ea ca)
      else none
    | _, _ => none
  | .ldrS w cw rt am, .cell k =>
    if cw == .b128 then none else
    match symAddr ss am, ptNAt? ss.cells k with
    | some (ea, wb), some (_, cw', ca, cv) =>
      if cw' = cw then
        some (((ss.applyWb wb).setReg w rt (cv.sext cw)).advance, alignObl ss am ++ oblEq ea ca)
      else none
    | _, _ => none
  | .strN cw rt am, .cell k =>
    if cw == .b128 then none else
    match symAddr ss am, ptNMutAt? ss.cells k with
    | some (ea, wb), some (cw', ca, _) =>
      if cw' = cw then
        some (((ss.setCell k (.ptN cw false ca (mkTrunc cw (ss.readReg64 rt)))).applyWb wb).advance,
          alignObl ss am ++ oblEq ea ca)
      else none
    | _, _ => none
  | _, _ => none

section Soundness

variable {b : BitVec 64} {env : Env} {s0 : State}

open SState in
/-- One-step soundness of the symbolic checker. -/
theorem stepOp_sound {base : SExpr} {ss ss' : SState} {op : MOp} {h : Hint} {obl : List SProp}
    {m : Memory} {R : SepProp} (hbase : base.eval env = b)
    (hlen : ss.regs.length = 31) (hvval : VRegsValid ss.vregs)
    (hstep : stepOp base ss op h = some (ss', obl))
    (hobl : allHold env obl) (hm : m ⊨ cellsProp env ss.cells ∗ R) :
    ∃ m', op.exec (ss.toState b env s0 m) = ss'.toState b env s0 m' ∧
      (m' ⊨ cellsProp env ss'.cells ∗ R) ∧ ss'.regs.length = 31 ∧ VRegsValid ss'.vregs := by
  unfold stepOp at hstep
  split at hstep
  · -- LDR (64-bit)
    split at hstep
    · rename_i rt am k _ _ ea wb ro ca cv hA hC
      cases hstep
      rw [allHold_append] at hobl
      have hea := oblEq_sound hobl.2
      obtain ⟨hrd, hcan⟩ := cellsProp_load64 (pt64At?_some hC) hm
      refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, applyWb_length, hlen],
        by simpa using hvval⟩
      simp only [MOp.exec]
      rw [execLdr_x64 (alignObl_sound hobl.1) (symAddr_sound hA) (by rw [toState_mem, hea]; exact hcan),
        applyWb_sound ss hlen, toState_mem, hea, hrd,
        toState_writeReg _ (by rw [applyWb_length, hlen]), toState_advancePC]
    · cases hstep
  · -- STR (64-bit)
    split at hstep
    · rename_i rt am k _ _ ea wb ca cv hA hC
      cases hstep
      rw [allHold_append] at hobl
      have hea := oblEq_sound hobl.2
      obtain ⟨hst, hcan⟩ := cellsProp_store64 (ss.readReg64 rt) (pt64MutAt?_some hC) hm
      refine ⟨_, ?_, by simpa using hst, by simp [applyWb_length, hlen], by simpa using hvval⟩
      simp only [MOp.exec]
      rw [execStr_x64 (alignObl_sound hobl.1) (symAddr_sound hA) (by rw [toState_mem, hea]; exact hcan),
        toState_mem, hea, toState_readReg64, toState_setMem]
      rw [← toState_setCell ss k (.pt64 false ca (ss.readReg64 rt)),
        applyWb_sound _ (by exact hlen), toState_advancePC]
    · cases hstep
  · -- LDP (64-bit)
    split at hstep
    · rename_i rt1 rt2 am k1 k2 _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 hA hC1 hC2
      cases hstep
      rw [allHold_append, allHold_append] at hobl
      have hea1 := oblEq_sound hobl.1.2
      have hea2 := oblEq_sound hobl.2
      simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
      obtain ⟨hrd1, hcan1⟩ := cellsProp_load64 (pt64At?_some hC1) hm
      obtain ⟨hrd2, hcan2⟩ := cellsProp_load64 (pt64At?_some hC2) hm
      refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, applyWb_length, hlen],
        by simpa using hvval⟩
      simp only [MOp.exec]
      rw [execLdp_x64 (alignObl_sound hobl.1.1) (symAddr_sound hA)
          (by rw [toState_mem, hea1]; exact hcan1)
          (by rw [toState_mem, hea1, hea2]; exact hcan2),
        applyWb_sound ss hlen, toState_mem, hea1, hea2, hrd1, hrd2,
        toState_writeReg _ (by rw [applyWb_length, hlen]),
        toState_writeReg _ (by rw [setReg_length, applyWb_length, hlen]), toState_advancePC]
    · cases hstep
  · -- LDP (32-bit)
    split at hstep
    · rename_i rt1 rt2 am k1 k2 _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 hA hC1 hC2
      cases hstep
      rw [allHold_append, allHold_append] at hobl
      have hea1 := oblEq_sound hobl.1.2
      have hea2 := oblEq_sound hobl.2
      simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
      obtain ⟨hrd1, hcan1⟩ := cellsProp_loadN (ptNAt?_some hC1) hm
      obtain ⟨hrd2, hcan2⟩ := cellsProp_loadN (ptNAt?_some hC2) hm
      simp only [CW.read] at hrd1 hrd2
      refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, applyWb_length, hlen],
        by simpa using hvval⟩
      simp only [MOp.exec]
      rw [execLdp_w32 (alignObl_sound hobl.1.1) (symAddr_sound hA)
          (by rw [toState_mem, hea1]; exact hcan1)
          (by rw [toState_mem, hea1, hea2]; exact hcan2),
        applyWb_sound ss hlen, toState_mem, hea1, hea2, hrd1, hrd2,
        ← NVal.zext_eval, ← NVal.zext_eval,
        toState_writeReg64 _ (by rw [applyWb_length, hlen]),
        toState_writeReg64 _ (by rw [setReg64_length, applyWb_length, hlen]), toState_advancePC]
    · cases hstep
  · -- LDPSW (signed 32-bit pair to 64-bit)
    split at hstep
    · rename_i rt1 rt2 am k1 k2 _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 hA hC1 hC2
      cases hstep
      rw [allHold_append, allHold_append] at hobl
      have hea1 := oblEq_sound hobl.1.2
      have hea2 := oblEq_sound hobl.2
      simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
      obtain ⟨hrd1, hcan1⟩ := cellsProp_loadN (ptNAt?_some hC1) hm
      obtain ⟨hrd2, hcan2⟩ := cellsProp_loadN (ptNAt?_some hC2) hm
      simp only [CW.read] at hrd1 hrd2
      refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, applyWb_length, hlen],
        by simpa using hvval⟩
      simp only [MOp.exec]
      rw [execLdp_sw (alignObl_sound hobl.1.1) (symAddr_sound hA)
          (by rw [toState_mem, hea1]; exact hcan1)
          (by rw [toState_mem, hea1, hea2]; exact hcan2),
        applyWb_sound ss hlen, toState_mem, hea1, hea2, hrd1, hrd2,
        ← NVal.sext_eval, ← NVal.sext_eval,
        toState_writeReg64 _ (by rw [applyWb_length, hlen]),
        toState_writeReg64 _ (by rw [setReg64_length, applyWb_length, hlen]), toState_advancePC]
    · cases hstep
  · -- STP (64-bit)
    split at hstep
    · cases hstep
    · split at hstep
      · rename_i rt1 rt2 am k1 k2 hne _ _ _ ea wb ca1 cv1 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        have hk1 := pt64MutAt?_some hC1
        have hk2 := pt64MutAt?_some hC2
        obtain ⟨hst1, hcan1⟩ := cellsProp_store64 (ss.readReg64 rt1) hk1 hm
        obtain ⟨_, hcan2⟩ := cellsProp_store64 (ss.readReg64 rt2) hk2 hm
        have hk2' := (List.getElem?_set_ne (l := ss.cells) (a := Cell.pt64 false ca1 (ss.readReg64 rt1)) hne).trans hk2
        obtain ⟨hst2, _⟩ := cellsProp_store64 (ss.readReg64 rt2) hk2' hst1
        refine ⟨_, ?_, by simpa using hst2, by simp [applyWb_length, hlen], by simpa using hvval⟩
        simp only [MOp.exec]
        rw [execStp_x64 (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem, hea1]; exact hcan1)
            (by rw [toState_mem, hea1, hea2]; exact hcan2),
          toState_mem, hea1, hea2, toState_readReg64,
          toState_readReg64, toState_setMem]
        rw [← toState_setCell ss k1 (.pt64 false ca1 (ss.readReg64 rt1)),
          ← toState_setCell _ k2 (.pt64 false ca2 (ss.readReg64 rt2)),
          applyWb_sound _ (by exact hlen), toState_advancePC]
      · cases hstep
  · -- STP (32-bit)
    split at hstep
    · cases hstep
    · split at hstep
      · rename_i rt1 rt2 am k1 k2 hne _ _ _ ea wb ca1 cv1 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        have hk1 := ptNMutAt?_some hC1
        have hk2 := ptNMutAt?_some hC2
        obtain ⟨hst1, hcan1⟩ := cellsProp_storeN (w := .b32) (ss.readReg64 rt1) hk1 hm
        obtain ⟨_, hcan2⟩ := cellsProp_storeN (w := .b32) (ss.readReg64 rt2) hk2 hm
        have hk2' := (List.getElem?_set_ne (l := ss.cells)
          (a := Cell.ptN .b32 false ca1 (mkTrunc .b32 (ss.readReg64 rt1))) hne).trans hk2
        obtain ⟨hst2, _⟩ := cellsProp_storeN (w := .b32) (ss.readReg64 rt2) hk2' hst1
        simp only [CW.write, CW.bits] at hst2
        refine ⟨_, ?_, by simpa using hst2, by simp [applyWb_length, hlen], by simpa using hvval⟩
        simp only [MOp.exec]
        rw [execStp_w32 (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem, hea1]; exact hcan1)
            (by rw [toState_mem, hea1, hea2]; exact hcan2),
          toState_mem, hea1, hea2, toState_readReg64,
          toState_readReg64, toState_setMem]
        rw [← toState_setCell ss k1 (.ptN .b32 false ca1 (mkTrunc .b32 (ss.readReg64 rt1))),
          ← toState_setCell _ k2 (.ptN .b32 false ca2 (mkTrunc .b32 (ss.readReg64 rt2))),
          applyWb_sound _ (by exact hlen), toState_advancePC]
      · cases hstep
  · -- LDR Qt (128-bit cell)
    split at hstep
    · cases hstep
    · rename_i vt am k hvlen
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ ea wb ro ca cv hA hC
        cases hstep
        rw [allHold_append] at hobl
        have hea := oblEq_sound hobl.2
        obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
        refine ⟨m, ?_, by simpa using hm, by simp [applyWb_length, hlen],
          Or.inr (by simp [setVReg128_length, hv32])⟩
        simp only [MOp.exec]
        rw [execLdrSimdQ_eq (alignObl_sound hobl.1) (symAddr_sound hA)
            (by rw [toState_mem, hea]; exact hcan),
          applyWb_sound ss hlen, toState_mem, hea]
        have hrd' : m.read128 (ca.eval env) = cv.toVExpr.eval env := by
          rw [NVal.toVExpr_eval]; exact hrd
        rw [hrd', toState_writeVReg128 _ (by simp [hv32]), toState_advancePC]
      · cases hstep
  · -- LDR Qt (two adjacent 64-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt am k1 k2 hvlen
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        obtain ⟨hrd1, hcan1⟩ := cellsProp_load64 (pt64At?_some hC1) hm
        obtain ⟨hrd2, hcan2⟩ := cellsProp_load64 (pt64At?_some hC2) hm
        have hcan16 : m.canRead (ea.eval env) 16 = true :=
          canRead_16_of_8 (by rw [hea1]; exact hcan1) (by rw [hea1, hea2]; exact hcan2)
        refine ⟨m, ?_, by simpa using hm, by simp [applyWb_length, hlen],
          Or.inr (by simp [setVReg128_length, hv32])⟩
        simp only [MOp.exec]
        rw [execLdrSimdQ_eq (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem]; exact hcan16),
          applyWb_sound ss hlen, toState_mem]
        have hrd128 : m.read128 (ea.eval env) = (VExpr.pair64 cv2 cv1).eval env := by
          simp only [Memory.read128, VExpr.eval, hea1, hea2, hrd1, hrd2]
        rw [hrd128, toState_writeVReg128 _ (by simp [hv32]), toState_advancePC]
      · cases hstep
  · -- STR Qt (128-bit cell)
    split at hstep
    · cases hstep
    · rename_i vt am k hvlen
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ ea wb ca cv hA hC
        cases hstep
        rw [allHold_append] at hobl
        have hea := oblEq_sound hobl.2
        obtain ⟨hst, hcan⟩ := cellsProp_storeN_val (.v128 (ss.vreg vt.toNat)) (ptNMutAt?_some hC) hm
        simp only [CW.write, NVal.eval] at hst
        refine ⟨_, ?_, by simpa using hst, by simp [applyWb_length, hlen],
          Or.inr (by simp [hv32])⟩
        simp only [MOp.exec]
        rw [execStrSimdQ_eq (alignObl_sound hobl.1) (symAddr_sound hA)
            (by rw [toState_mem, hea]; exact hcan),
          toState_mem, hea, toState_readVReg128 _ hv32, toState_setMem]
        rw [← toState_setCell ss k (.ptN .b128 false ca (.v128 (ss.vreg vt.toNat))),
          applyWb_sound _ (by exact hlen), toState_advancePC]
        rfl
      · cases hstep
  · -- STR Qt (two adjacent 64-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt am k1 k2 hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
      obtain ⟨hvlen, hne⟩ := hcond
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ ea wb ca1 cv1 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        let ve := ss.vreg vt.toNat
        have hk1 := pt64MutAt?_some hC1
        have hk2 := pt64MutAt?_some hC2
        obtain ⟨hst1, hcan1⟩ := cellsProp_store64 ve.lo64 hk1 hm
        obtain ⟨_, hcan2⟩ := cellsProp_store64 ve.hi64 hk2 hm
        have hk2' := (List.getElem?_set_ne (l := ss.cells) (a := Cell.pt64 false ca1 ve.lo64) hne).trans hk2
        obtain ⟨hst2, _⟩ := cellsProp_store64 ve.hi64 hk2' hst1
        have hcan16 : m.canWrite (ea.eval env) 16 = true :=
          canWrite_16_of_8 (by rw [hea1]; exact hcan1) (by rw [hea1, hea2]; exact hcan2)
        refine ⟨_, ?_, by simpa [ve] using hst2, by simp [applyWb_length, hlen],
          Or.inr (by simp [hv32])⟩
        simp only [MOp.exec]
        rw [execStrSimdQ_eq (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem]; exact hcan16),
          toState_mem, toState_readVReg128 _ hv32, toState_setMem]
        have hwr : m.write128 (ea.eval env) (ve.eval env) =
            (m.write64 (ca1.eval env) (ve.lo64.eval env)).write64 (ca2.eval env) (ve.hi64.eval env) := by
          simp only [Memory.write128, hea1, hea2, VExpr.lo64_eval, VExpr.hi64_eval]
        rw [hwr, ← toState_setCell ss k1 (.pt64 false ca1 ve.lo64),
          ← toState_setCell _ k2 (.pt64 false ca2 ve.hi64),
          applyWb_sound _ (by exact hlen), toState_advancePC]
        rfl
      · cases hstep
  · -- LDP Qt1, Qt2 (two 128-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt1 vt2 am k1 k2 hvlen
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        obtain ⟨hrd1, hcan1⟩ := cellsProp_loadN (ptNAt?_some hC1) hm
        obtain ⟨hrd2, hcan2⟩ := cellsProp_loadN (ptNAt?_some hC2) hm
        refine ⟨m, ?_, by simpa using hm, by simp [applyWb_length, hlen],
          Or.inr (by simp [setVReg128_length, hv32])⟩
        simp only [MOp.exec]
        rw [execLdpSimdQ_eq (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem, hea1]; exact hcan1)
            (by rw [toState_mem, hea1, hea2]; exact hcan2),
          applyWb_sound ss hlen, toState_mem, hea1, hea2]
        have hrd1' : m.read128 (ca1.eval env) = cv1.toVExpr.eval env := by
          rw [NVal.toVExpr_eval]; exact hrd1
        have hrd2' : m.read128 (ca2.eval env) = cv2.toVExpr.eval env := by
          rw [NVal.toVExpr_eval]; exact hrd2
        rw [hrd1', hrd2', toState_writeVReg128 _ (by simp [hv32]),
          toState_writeVReg128 _ (by simp [setVReg128_length, hv32]), toState_advancePC]
      · cases hstep
  · -- LDP Qt1, Qt2 (four adjacent 64-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt1 vt2 am k1 k2 k3 k4 hvlen
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ _ _ ea wb ro1 ca1 cv1 ro2 ca2 cv2 ro3 ca3 cv3 ro4 ca4 cv4 hA hC1 hC2 hC3 hC4
        cases hstep
        rw [allHold_append, allHold_append, allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.1.1.2
        have hea2 := oblEq_sound hobl.1.1.2
        have hea3 := oblEq_sound hobl.1.2
        have hea4 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2 hea3 hea4
        obtain ⟨hrd1, hcan1⟩ := cellsProp_load64 (pt64At?_some hC1) hm
        obtain ⟨hrd2, hcan2⟩ := cellsProp_load64 (pt64At?_some hC2) hm
        obtain ⟨hrd3, hcan3⟩ := cellsProp_load64 (pt64At?_some hC3) hm
        obtain ⟨hrd4, hcan4⟩ := cellsProp_load64 (pt64At?_some hC4) hm
        have hstep24 : ea.eval env + 16#64 + 8#64 = ea.eval env + 24#64 := by bv_arith
        have hcan16a : m.canRead (ea.eval env) 16 = true :=
          canRead_16_of_8 (by rw [hea1]; exact hcan1) (by rw [hea1, hea2]; exact hcan2)
        have hcan16b : m.canRead (ea.eval env + 16#64) 16 = true :=
          canRead_16_of_8 (by rw [hea1, hea3]; exact hcan3)
            (by rw [hstep24, hea1, hea4]; exact hcan4)
        refine ⟨m, ?_, by simpa using hm, by simp [applyWb_length, hlen],
          Or.inr (by simp [setVReg128_length, hv32])⟩
        simp only [MOp.exec]
        rw [execLdpSimdQ_eq (alignObl_sound hobl.1.1.1.1) (symAddr_sound hA)
            (by rw [toState_mem]; exact hcan16a)
            (by rw [toState_mem]; exact hcan16b),
          applyWb_sound ss hlen, toState_mem]
        have hrd128a : m.read128 (ea.eval env) = (VExpr.pair64 cv2 cv1).eval env := by
          simp only [Memory.read128, VExpr.eval, hea1, hea2, hrd1, hrd2]
        have hrd128b : m.read128 (ea.eval env + 16#64) = (VExpr.pair64 cv4 cv3).eval env := by
          simp only [Memory.read128, VExpr.eval]
          rw [hstep24]
          simp only [hea1, hea3, hea4, hrd3, hrd4]
        rw [hrd128a, hrd128b, toState_writeVReg128 _ (by simp [hv32]),
          toState_writeVReg128 _ (by simp [setVReg128_length, hv32]), toState_advancePC]
      · cases hstep
  · -- STP Qt1, Qt2 (two 128-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt1 vt2 am k1 k2 hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
      obtain ⟨hvlen, hne⟩ := hcond
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ ea wb ca1 cv1 ca2 cv2 hA hC1 hC2
        cases hstep
        rw [allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.2
        have hea2 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2
        have hk1 := ptNMutAt?_some hC1
        have hk2 := ptNMutAt?_some hC2
        obtain ⟨hst1, hcan1⟩ := cellsProp_storeN_val (.v128 (ss.vreg vt1.toNat)) hk1 hm
        obtain ⟨_, hcan2⟩ := cellsProp_storeN_val (.v128 (ss.vreg vt2.toNat)) hk2 hm
        have hk2' := (List.getElem?_set_ne (l := ss.cells)
          (a := Cell.ptN .b128 false ca1 (.v128 (ss.vreg vt1.toNat))) hne).trans hk2
        obtain ⟨hst2, _⟩ := cellsProp_storeN_val (.v128 (ss.vreg vt2.toNat)) hk2' hst1
        simp only [CW.write, NVal.eval] at hst2
        refine ⟨_, ?_, by simpa using hst2, by simp [applyWb_length, hlen],
          Or.inr (by simp [hv32])⟩
        simp only [MOp.exec]
        rw [execStpSimdQ_eq (alignObl_sound hobl.1.1) (symAddr_sound hA)
            (by rw [toState_mem, hea1]; exact hcan1)
            (by rw [toState_mem, hea1, hea2]; exact hcan2),
          toState_mem, hea1, hea2, toState_readVReg128 _ hv32, toState_readVReg128 _ hv32,
          toState_setMem]
        rw [← toState_setCell ss k1 (.ptN .b128 false ca1 (.v128 (ss.vreg vt1.toNat))),
          ← toState_setCell _ k2 (.ptN .b128 false ca2 (.v128 (ss.vreg vt2.toNat))),
          applyWb_sound _ (by exact hlen), toState_advancePC]
        rfl
      · cases hstep
  · -- STP Qt1, Qt2 (four adjacent 64-bit cells)
    split at hstep
    · cases hstep
    · rename_i vt1 vt2 am k1 k2 k3 k4 hcond
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
      obtain ⟨⟨⟨⟨⟨⟨hvlen, hne12⟩, hne13⟩, hne14⟩, hne23⟩, hne24⟩, hne34⟩ := hcond
      have hv32 : ss.vregs.length = 32 := Classical.not_not.mp hvlen
      split at hstep
      · rename_i _ _ _ _ _ ea wb ca1 cv1 ca2 cv2 ca3 cv3 ca4 cv4 hA hC1 hC2 hC3 hC4
        cases hstep
        rw [allHold_append, allHold_append, allHold_append, allHold_append] at hobl
        have hea1 := oblEq_sound hobl.1.1.1.2
        have hea2 := oblEq_sound hobl.1.1.2
        have hea3 := oblEq_sound hobl.1.2
        have hea4 := oblEq_sound hobl.2
        simp only [mkAdd_eval, SExpr.eval, hea1] at hea2 hea3 hea4
        let ve1 := ss.vreg vt1.toNat
        let ve2 := ss.vreg vt2.toNat
        have hk1 := pt64MutAt?_some hC1
        have hk2 := pt64MutAt?_some hC2
        have hk3 := pt64MutAt?_some hC3
        have hk4 := pt64MutAt?_some hC4
        obtain ⟨hst1, hcan1⟩ := cellsProp_store64 ve1.lo64 hk1 hm
        obtain ⟨_, hcan2⟩ := cellsProp_store64 ve1.hi64 hk2 hm
        obtain ⟨_, hcan3⟩ := cellsProp_store64 ve2.lo64 hk3 hm
        obtain ⟨_, hcan4⟩ := cellsProp_store64 ve2.hi64 hk4 hm
        have hk2' := (List.getElem?_set_ne (l := ss.cells) (a := Cell.pt64 false ca1 ve1.lo64) hne12).trans hk2
        obtain ⟨hst2, _⟩ := cellsProp_store64 ve1.hi64 hk2' hst1
        have hk3' := (List.getElem?_set_ne (a := Cell.pt64 false ca2 ve1.hi64) hne23).trans
          ((List.getElem?_set_ne (l := ss.cells) (a := Cell.pt64 false ca1 ve1.lo64) hne13).trans hk3)
        obtain ⟨hst3, _⟩ := cellsProp_store64 ve2.lo64 hk3' hst2
        have hk4' := (List.getElem?_set_ne (a := Cell.pt64 false ca3 ve2.lo64) hne34).trans
          ((List.getElem?_set_ne (a := Cell.pt64 false ca2 ve1.hi64) hne24).trans
            ((List.getElem?_set_ne (l := ss.cells) (a := Cell.pt64 false ca1 ve1.lo64) hne14).trans hk4))
        obtain ⟨hst4, _⟩ := cellsProp_store64 ve2.hi64 hk4' hst3
        have hstep24 : ea.eval env + 16#64 + 8#64 = ea.eval env + 24#64 := by bv_arith
        have hcan16a : m.canWrite (ea.eval env) 16 = true :=
          canWrite_16_of_8 (by rw [hea1]; exact hcan1) (by rw [hea1, hea2]; exact hcan2)
        have hcan16b : m.canWrite (ea.eval env + 16#64) 16 = true :=
          canWrite_16_of_8 (by rw [hea1, hea3]; exact hcan3)
            (by rw [hstep24, hea1, hea4]; exact hcan4)
        refine ⟨_, ?_, by simpa [ve1, ve2] using hst4, by simp [applyWb_length, hlen],
          Or.inr (by simp [hv32])⟩
        simp only [MOp.exec]
        rw [execStpSimdQ_eq (alignObl_sound hobl.1.1.1.1) (symAddr_sound hA)
            (by rw [toState_mem]; exact hcan16a)
            (by rw [toState_mem]; exact hcan16b),
          toState_mem, toState_readVReg128 _ hv32, toState_readVReg128 _ hv32, toState_setMem]
        have hwr : (m.write128 (ea.eval env) (ve1.eval env)).write128 (ea.eval env + 16#64) (ve2.eval env) =
            (((m.write64 (ca1.eval env) (ve1.lo64.eval env)).write64 (ca2.eval env) (ve1.hi64.eval env)).write64
              (ca3.eval env) (ve2.lo64.eval env)).write64 (ca4.eval env) (ve2.hi64.eval env) := by
          rw [Memory.write128, Memory.write128, hstep24]
          simp only [hea1, hea2, hea3, hea4, VExpr.lo64_eval, VExpr.hi64_eval]
        rw [hwr, ← toState_setCell ss k1 (.pt64 false ca1 ve1.lo64),
          ← toState_setCell _ k2 (.pt64 false ca2 ve1.hi64),
          ← toState_setCell _ k3 (.pt64 false ca3 ve2.lo64),
          ← toState_setCell _ k4 (.pt64 false ca4 ve2.hi64),
          applyWb_sound _ (by exact hlen), toState_advancePC]
        rfl
      · cases hstep
  · -- ADD/SUB immediate
    rename_i w op rd rn imm12 shift12
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [execAddSubImm_eq, ← toState_advancePC]
    congr 1
    let imm := if shift12 then (imm12.zeroExtend 64) <<< 12 else imm12.zeroExtend 64
    show _ = ((ss.setReg w rd (mkAddSub w op (ss.readReg w rn) (.const imm))).toState
      b env s0 m).setPState ((mkFlags w op (ss.readReg w rn) (.const imm) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkAddSub_eval, mkFlags_denote, toState_readReg]
    rfl
  · -- ADD/SUB shifted register
    rename_i w op rd rn rm shift amount
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [execAddSubShift_eq, ← toState_advancePC]
    congr 1
    show _ = ((ss.setReg w rd (mkAddSub w op (ss.readReg w rn) (mkShiftVal w
      (ss.readReg w rm) shift amount))).toState
      b env s0 m).setPState ((mkFlags w op (ss.readReg w rn) (mkShiftVal w
      (ss.readReg w rm) shift amount) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkAddSub_eval, mkFlags_denote, mkShiftVal_eval, toState_readReg,
      toState_readReg]
    rfl
  · -- ADD/SUB extended register
    rename_i w op rd rn rm ext amount
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [execAddSubExt_eq, ← toState_advancePC]
    congr 1
    show _ = ((ss.setReg w rd (mkAddSub w op (ss.readReg w rn) (mkExtendVal w
      (ss.readReg64 rm) ext amount))).toState
      b env s0 m).setPState ((mkFlags w op (ss.readReg w rn) (mkExtendVal w
      (ss.readReg64 rm) ext amount) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkAddSub_eval, mkFlags_denote, mkExtendVal_eval, toState_readReg,
      toState_readReg64]
    rfl
  · -- logical immediate
    rename_i w op rd rn imm
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [execLogicalImm_eq, ← toState_advancePC]
    congr 1
    show _ = ((ss.setReg w rd (mkLogical w op (ss.readReg w rn) (.const imm))).toState
      b env s0 m).setPState ((mkLogicalFlags w op (ss.readReg w rn) (.const imm) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkLogical_eval, mkLogicalFlags_denote, toState_readReg]
    rfl
  · -- logical shifted register
    rename_i w op rd rn rm shift amount
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [execLogicalShift_eq, ← toState_advancePC]
    congr 1
    show _ = ((ss.setReg w rd (mkLogical w op (ss.readReg w rn) (mkShiftVal w
      (ss.readReg w rm) shift amount))).toState
      b env s0 m).setPState ((mkLogicalFlags w op (ss.readReg w rn) (mkShiftVal w
      (ss.readReg w rm) shift amount) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkLogical_eval, mkLogicalFlags_denote, mkShiftVal_eval,
      toState_readReg, toState_readReg]
    rfl
  · -- bitfield
    rename_i w op rd rn immr imms
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec, execBitfield]
    rw [toState_readReg, toState_readReg,
      show evalBitfield w op ((ss.readReg w rd).eval env) ((ss.readReg w rn).eval env) immr imms =
        (SExpr.bitfield w op (ss.readReg w rd) (ss.readReg w rn) immr imms).eval env from rfl,
      toState_writeReg _ hlen, toState_advancePC]
  · -- MOVZ
    rename_i w rd imm16 hw
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec, execMoveWide]
    rw [show (imm16.zeroExtend 64) <<< hw =
        (SExpr.const ((imm16.zeroExtend 64) <<< hw)).eval env from rfl,
      toState_writeReg _ hlen, toState_advancePC]
    rfl
  · -- MOVN
    rename_i w rd imm16 hw
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec, execMoveWide]
    rw [show ~~~((imm16.zeroExtend 64) <<< hw) =
        (SExpr.const (~~~((imm16.zeroExtend 64) <<< hw))).eval env from rfl,
      toState_writeReg _ hlen, toState_advancePC]
    rfl
  · -- MOVK
    rename_i w rd imm16 hw
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec, execMoveWide]
    rw [toState_readReg, ← mkMovk_eval env (ss.readReg w rd) imm16 hw,
      toState_writeReg _ hlen, toState_advancePC]
  · -- CSEL / CSINC / CSINV / CSNEG
    split at hstep
    · rename_i w op rd rn rm cond _ c hfc
      cases hstep
      refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
      simp only [MOp.exec, execCondSelect, toState_pstate, flagsCond?_sound hfc, toState_readReg]
      cases hc : c.eval env
      · simp only [Bool.false_eq_true, ite_false]
        cases op
        · rw [show (ss.readReg w rm).eval env =
                (mkIte c (ss.readReg w rn) (ss.readReg w rm)).eval env by simp [mkIte_eval, hc],
              toState_writeReg _ hlen, toState_advancePC]
        · rw [show ((ss.readReg w rm).eval env) + 1#64 =
                (mkIte c (ss.readReg w rn) (mkAdd (ss.readReg w rm) (.const 1#64))).eval env by
                simp [mkIte_eval, mkAdd_eval, SExpr.eval, hc],
              toState_writeReg _ hlen, toState_advancePC]
        · rw [show ~~~((ss.readReg w rm).eval env) =
                (mkIte c (ss.readReg w rn) (.xor (ss.readReg w rm) (.const 0xffffffffffffffff#64))).eval env by
                simp only [mkIte_eval, SExpr.eval, hc, Bool.false_eq_true, ite_false]; bv_bits,
              toState_writeReg _ hlen, toState_advancePC]
        · rw [show 0#64 - ((ss.readReg w rm).eval env) =
                (mkIte c (ss.readReg w rn) (mkNeg (ss.readReg w rm))).eval env by
                simp only [mkIte_eval, mkNeg_eval, hc, Bool.false_eq_true, ite_false,
                  BitVec.zero_sub],
              toState_writeReg _ hlen, toState_advancePC]
      · simp only [ite_true]
        rw [show (ss.readReg w rn).eval env =
              (mkIte c (ss.readReg w rn) (match op with
                | .CSEL => ss.readReg w rm
                | .CSINC => mkAdd (ss.readReg w rm) (.const 1#64)
                | .CSINV => .xor (ss.readReg w rm) (.const 0xffffffffffffffff#64)
                | .CSNEG => mkNeg (ss.readReg w rm))).eval env by simp [mkIte_eval, hc],
            toState_writeReg _ hlen, toState_advancePC]
    · cases hstep
  · -- DataProc1 (`RBIT`, `REV16`, `REV32`, `REV`, `CLZ`, `CLS`)
    rename_i w op rd rn
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    have hexec : execDataProc1 w op rd rn (ss.toState b env s0 m) =
        ((ss.toState b env s0 m).writeReg w rd
          ((SExpr.dataProc1 w op (ss.readReg w rn)).eval env)).advancePC := by
      simp only [execDataProc1, SExpr.eval, evalDataProc1Val, toState_readReg]
      rfl
    simp only [MOp.exec]
    rw [hexec, toState_writeReg _ hlen, toState_advancePC]
  · -- DataProc3 (`MADD`, `MSUB`, `SMADDL`, `SMSUBL`, `UMADDL`, `UMSUBL`, `SMULH`, `UMULH`)
    rename_i w op rd rn rm ra
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    have hexec : execDataProc3 w op rd rn rm ra (ss.toState b env s0 m) =
        ((ss.toState b env s0 m).writeReg w rd
          ((mkDataProc3 w op (ss.readReg64 rn) (ss.readReg64 rm) (ss.readReg64 ra)).eval env)).advancePC := by
      rw [mkDataProc3_eval]
      simp only [execDataProc3, evalDataProc3Val, State.readReg32, toState_readReg64]
      rfl
    simp only [MOp.exec]
    rw [hexec, toState_writeReg _ hlen, toState_advancePC]
  · -- B
    rename_i target
    cases hstep
    refine ⟨m, ?_, by simpa using hm, hlen, hvval⟩
    simp only [MOp.exec, toState_pc]
    rw [← SPc.addOff_denote]; rfl
  · -- B.cond
    split at hstep
    · rename_i cond target taken _ o ho
      cases hstep
      refine ⟨m, ?_, ?_, ?_, ?_⟩
      · simp only [MOp.exec, toState_pstate, condObl_sound ho hobl]
        cases taken
        · simp only [Bool.false_eq_true, ite_false]; exact toState_advancePC _
        · simp only [ite_true, toState_pc]; rw [← SPc.addOff_denote]; rfl
      · cases taken <;> simpa using hm
      · cases taken <;> simpa using hlen
      · cases taken <;> simpa using hvval
    · cases hstep
  · -- CBZ
    rename_i w rt target taken
    cases hstep
    refine ⟨m, ?_, ?_, ?_, ?_⟩
    · simp only [MOp.exec, toState_readReg]
      cases taken
      · have hne : (ss.readReg w rt).eval env ≠ 0#64 := hobl.1
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · simp_all
        · exact toState_advancePC _
      · have heq : (ss.readReg w rt).eval env = 0#64 := oblEq_sound hobl
        simp only [↓reduceIte]
        split
        · simp only [toState_pc]; rw [← SPc.addOff_denote]; rfl
        · simp_all
    · cases taken <;> simpa using hm
    · cases taken <;> simpa using hlen
    · cases taken <;> simpa using hvval
  · -- CBNZ
    rename_i w rt target taken
    cases hstep
    refine ⟨m, ?_, ?_, ?_, ?_⟩
    · simp only [MOp.exec, toState_readReg]
      cases taken
      · have heq : (ss.readReg w rt).eval env = 0#64 := oblEq_sound hobl
        simp only [Bool.false_eq_true, ↓reduceIte]
        split
        · simp_all
        · exact toState_advancePC _
      · have hne : (ss.readReg w rt).eval env ≠ 0#64 := hobl.1
        simp only [↓reduceIte]
        split
        · simp only [toState_pc]; rw [← SPc.addOff_denote]; rfl
        · simp_all
    · cases taken <;> simpa using hm
    · cases taken <;> simpa using hlen
    · cases taken <;> simpa using hvval
  · -- TBZ / TBNZ
    rename_i isNonZero rt bitPos target taken
    cases hstep
    have hbit := condToObl_sound (.bit (ss.readReg64 rt) bitPos) (if taken then isNonZero else !isNonZero) hobl
    simp only [SCond.eval] at hbit
    refine ⟨m, ?_, ?_, ?_, ?_⟩
    · simp only [MOp.exec, toState_readReg64, hbit]
      cases taken <;> cases isNonZero <;> simp [toState_pc, ← SPc.addOff_denote, toState_advancePC] <;> rfl
    · cases taken <;> simpa using hm
    · cases taken <;> simpa using hlen
    · cases taken <;> simpa using hvval
  · -- RET
    rename_i rn
    cases hstep
    refine ⟨m, ?_, by simpa using hm, hlen, hvval⟩
    simp only [MOp.exec, toState_readReg64]
    rfl
  · -- ADR
    split at hstep
    · rename_i rd target _ o hpc
      cases hstep
      refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
      simp only [MOp.exec, toState_pc, hpc, SPc.denote]
      rw [show (b + o) + target = (mkAdd base (.const (o + target))).eval env by
            rw [mkAdd_eval, hbase]; simp [SExpr.eval, BitVec.add_assoc],
        toState_writeReg64 _ hlen, toState_advancePC]
    · cases hstep
  · -- ADRP
    split at hstep
    · rename_i rd target _ o hpc
      cases hstep
      have hal : (splitOff base).1.eval env &&& 0xfff#64 = 0#64 := by
        have := oblEq_sound hobl
        simpa only [SExpr.eval] using this
      have hb : b = (splitOff base).1.eval env + (splitOff base).2 := by
        rw [← hbase]; exact splitOff_eval env base
      refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
      simp only [MOp.exec, toState_pc, hpc, SPc.denote]
      rw [show ((b + o) &&& 0xfffffffffffff000#64) + target =
          (mkAdd (splitOff base).1 (.const ((((splitOff base).2 + o) &&& 0xfffffffffffff000#64) +
            target))).eval env by
            rw [mkAdd_eval, hb, BitVec.add_assoc, adrp_page_add hal]
            simp only [SExpr.eval, BitVec.add_assoc],
        toState_writeReg64 _ hlen, toState_advancePC]
    · cases hstep
  · -- NOP / HINT / BARRIER / PRFM
    cases hstep
    refine ⟨m, ?_, by simpa using hm, hlen, hvval⟩
    exact toState_advancePC ss
  · -- MRS rt, TPIDR_EL0
    rename_i rt
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec, toState_tpidrEl0, toState_writeReg64 _ hlen, toState_advancePC]
  · -- MSR TPIDR_EL0, rt
    rename_i rt
    cases hstep
    refine ⟨m, ?_, by simpa using hm, hlen, hvval⟩
    simp only [MOp.exec, toState_readReg64, toState_setTpidr, toState_advancePC]
  · -- MRS rt, DCZID_EL0
    rename_i rt
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
    simp only [MOp.exec]
    rw [show 4#64 = (SExpr.const 4#64).eval env from rfl,
      toState_writeReg64 _ hlen, toState_advancePC]
    rfl
  · -- LDR (narrow zero-extending)
    split at hstep
    · cases hstep
    · split at hstep
      · rename_i w cw rt am k hif _ _ ea wb ro cw' ca cv hA hC
        have hcw128 : cw ≠ .b128 := by cases cw <;> simp at hif ⊢
        split at hstep
        · rename_i hcw
          subst hcw
          cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
          refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, applyWb_length, hlen],
            by simpa using hvval⟩
          simp only [MOp.exec]
          rw [execLdr_n (alignObl_sound hobl.1) (symAddr_sound hA) (by rw [toState_mem, hea]; exact hcan) hcw128,
            applyWb_sound ss hlen, toState_mem, hea, hrd, writeReg_zext _ _ _ _ _ hcw128, ← NVal.zext_eval,
            toState_writeReg64 _ (by rw [applyWb_length, hlen]), toState_advancePC]
        · cases hstep
      · cases hstep
  · -- LDRS (narrow sign-extending: LDRSW, LDRSB, LDRSH)
    split at hstep
    · cases hstep
    · split at hstep
      · rename_i w cw rt am k hif _ _ ea wb ro cw' ca cv hA hC
        have hcw128 : cw ≠ .b128 := by cases cw <;> simp at hif ⊢
        split at hstep
        · rename_i hcw
          subst hcw
          cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
          refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, applyWb_length, hlen],
            by simpa using hvval⟩
          simp only [MOp.exec]
          rw [execLdr_s (alignObl_sound hobl.1) (symAddr_sound hA) (by rw [toState_mem, hea]; exact hcan) hcw128,
            applyWb_sound ss hlen, toState_mem, hea, hrd, ← NVal.sext_eval,
            toState_writeReg _ (by rw [applyWb_length, hlen]), toState_advancePC]
        · cases hstep
      · cases hstep
  · -- STR (narrow)
    split at hstep
    · cases hstep
    · split at hstep
      · rename_i cw rt am k hif _ _ ea wb cw' ca cv hA hC
        have hcw128 : cw ≠ .b128 := by cases cw <;> simp at hif ⊢
        split at hstep
        · rename_i hcw
          subst hcw
          cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hst, hcan⟩ := cellsProp_storeN (ss.readReg64 rt) (ptNMutAt?_some hC) hm
          refine ⟨_, ?_, by simpa using hst, by simp [applyWb_length, hlen], by simpa using hvval⟩
          simp only [MOp.exec]
          rw [execStr_n (alignObl_sound hobl.1) (symAddr_sound hA) (by rw [toState_mem, hea]; exact hcan) hcw128,
            toState_mem, hea, toState_readReg64, toState_setMem]
          rw [← toState_setCell ss k (.ptN _ false ca (mkTrunc _ (ss.readReg64 rt))),
            applyWb_sound _ (by exact hlen), toState_advancePC]
        · cases hstep
      · cases hstep
  · cases hstep

end Soundness

/-! ## Relocation-Aware Symbolic Instructions (`SymInsn`) -/

/-- Block instruction entry: either an ordinary `Instr` or a relocated instruction (`ADRP`,
    `ADD :lo12:`, `LDR`/`STR :lo12:`) whose relocation target is a symbolic `SExpr` in `env`. -/
inductive SymInsn where
  | plain (i : Instr)
  | adrpSym (rd : Reg) (target : SExpr)
  | addLo12Sym (rd rn : Reg) (target : SExpr)
  | ldr64Lo12Sym (rt rn : Reg) (target : SExpr)
  | str64Lo12Sym (rt rn : Reg) (target : SExpr)
  | ldr32Lo12Sym (rt rn : Reg) (target : SExpr)
  | str32Lo12Sym (rt rn : Reg) (target : SExpr)
  | ldr16Lo12Sym (rt rn : Reg) (target : SExpr)
  | str16Lo12Sym (rt rn : Reg) (target : SExpr)
  | ldrbLo12Sym (rt rn : Reg) (target : SExpr)
  | strbLo12Sym (rt rn : Reg) (target : SExpr)

/-- Concrete `Instr` denoted by a `SymInsn` at `pc` in environment `env`. -/
def SymInsn.toInstr (env : Env) (pc : BitVec 64) : SymInsn → Instr
  | .plain i => i
  | .adrpSym rd target =>
    .adr true rd (Obj.pageOf (target.eval env) - Obj.pageOf pc)
  | .addLo12Sym rd rn target =>
    .addSubImm .W64 .ADD rd rn ((Obj.lo12Of (target.eval env)).truncate 12) false
  | .ldr64Lo12Sym rt rn target =>
    .ldr .W64 .X64 false rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .str64Lo12Sym rt rn target =>
    .str .X64 rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .ldr32Lo12Sym rt rn target =>
    .ldr .W32 .W32 false rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .str32Lo12Sym rt rn target =>
    .str .W32 rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .ldr16Lo12Sym rt rn target =>
    .ldr .W32 .H16 false rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .str16Lo12Sym rt rn target =>
    .str .H16 rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .ldrbLo12Sym rt rn target =>
    .ldr .W32 .B8 false rt (.Offset rn (Obj.lo12Of (target.eval env)))
  | .strbLo12Sym rt rn target =>
    .str .B8 rt (.Offset rn (Obj.lo12Of (target.eval env)))

/-- SP-alignment obligation for a base register `rn`. -/
def regAlignObl (ss : SState) (r : Reg) : List SProp :=
  match r with
  | .sp => oblAligned ss.sp
  | _ => []

/-- Symbolic execution of one `SymInsn` under advice `h`. -/
def stepSymInsn (base : SExpr) (ss : SState) (si : SymInsn) (h : Hint) :
    Option (SState × List SProp) :=
  match si, h with
  | .plain i, h =>
    match lower i with
    | some op => stepOp base ss op h
    | none => none
  | .adrpSym rd target, _ =>
    some ((ss.setReg64 rd (.pageOf target)).advance, [])
  | .addLo12Sym rd rn target, _ =>
    let x := ss.readReg .W64 rn
    let y := SExpr.lo12Of target
    some ({ ss.setReg .W64 rd (mkAddSub .W64 .ADD x y) with
            flags := mkFlags .W64 .ADD x y ss.flags }.advance, [])
  | .ldr64Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match pt64At? ss.cells k with
    | some (_, ca, cv) =>
      some ((ss.setReg .W64 rt cv).advance, regAlignObl ss rn ++ oblEq ea ca)
    | none => none
  | .str64Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match pt64MutAt? ss.cells k with
    | some (ca, _) =>
      some ((ss.setCell k (.pt64 false ca (ss.readReg64 rt))).advance,
        regAlignObl ss rn ++ oblEq ea ca)
    | none => none
  | .ldr32Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNAt? ss.cells k with
    | some (_, cw', ca, cv) =>
      if cw' = .b32 then
        some ((ss.setReg64 rt (cv.zext .b32)).advance, regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | .str32Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNMutAt? ss.cells k with
    | some (cw', ca, _) =>
      if cw' = .b32 then
        some ((ss.setCell k (.ptN .b32 false ca (mkTrunc .b32 (ss.readReg64 rt)))).advance,
          regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | .ldr16Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNAt? ss.cells k with
    | some (_, cw', ca, cv) =>
      if cw' = .b16 then
        some ((ss.setReg64 rt (cv.zext .b16)).advance, regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | .str16Lo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNMutAt? ss.cells k with
    | some (cw', ca, _) =>
      if cw' = .b16 then
        some ((ss.setCell k (.ptN .b16 false ca (mkTrunc .b16 (ss.readReg64 rt)))).advance,
          regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | .ldrbLo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNAt? ss.cells k with
    | some (_, cw', ca, cv) =>
      if cw' = .b8 then
        some ((ss.setReg64 rt (cv.zext .b8)).advance, regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | .strbLo12Sym rt rn target, .cell k =>
    let ea := mkAdd (ss.readReg64 rn) (.lo12Of target)
    match ptNMutAt? ss.cells k with
    | some (cw', ca, _) =>
      if cw' = .b8 then
        some ((ss.setCell k (.ptN .b8 false ca (mkTrunc .b8 (ss.readReg64 rt)))).advance,
          regAlignObl ss rn ++ oblEq ea ca)
      else none
    | none => none
  | _, _ => none

section SymInsnSoundness

variable {b : BitVec 64} {env : Env} {s0 : State} {m : Memory}

open SState in
theorem regAlignObl_sound {ss : SState} {rn : Reg} {off : BitVec 64}
    (h : allHold env (regAlignObl ss rn)) :
    checkAddrSPAligned (ss.toState b env s0 m) (.Offset rn off) = true := by
  have h' : allHold env (alignObl ss (.Offset rn off)) := by
    simpa [alignObl, regAlignObl, AddrMode.baseReg] using h
  exact alignObl_sound h'

open SState in
theorem evalAddrMode_lo12Sym (ss : SState) (rn : Reg) (target : SExpr) :
    evalAddrMode (ss.toState b env s0 m) (.Offset rn (Obj.lo12Of (target.eval env))) =
    ((mkAdd (ss.readReg64 rn) (.lo12Of target)).eval env, none) := by
  simp [evalAddrMode, mkAdd_eval, toState_readReg64, SExpr.eval]

open SState in
theorem stepSymInsn_sound {prog : Program} {base : SExpr} {ss ss' : SState} {si : SymInsn} {h : Hint}
    {obl : List SProp} {o : BitVec 64} {R : SepProp}
    (hbase : base.eval env = b) (hpc : ss.pc = .rel o)
    (hlen : ss.regs.length = 31) (hvval : VRegsValid ss.vregs)
    (hstep : stepSymInsn base ss si h = some (ss', obl))
    (hobl : allHold env obl) (hm : m ⊨ cellsProp env ss.cells ∗ R) :
    ∃ m', prog.evalInst (si.toInstr env (b + o)) (ss.toState b env s0 m) = ss'.toState b env s0 m' ∧
      (m' ⊨ cellsProp env ss'.cells ∗ R) ∧ ss'.regs.length = 31 ∧ VRegsValid ss'.vregs := by
  cases si with
  | plain i =>
    simp only [stepSymInsn] at hstep
    split at hstep
    · rename_i op hlow
      obtain ⟨m', hex, hm', hlen', hvval'⟩ :=
        stepOp_sound (b := b) (s0 := s0) hbase hlen hvval hstep hobl hm
      exact ⟨m', (lower_sound hlow _).trans hex, hm', hlen', hvval'⟩
    · cases hstep
  | adrpSym rd target =>
    simp only [stepSymInsn] at hstep
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
    rw [lower_sound (op := .adrp rd (Obj.pageOf (target.eval env) - Obj.pageOf (b + o))) rfl]
    simp only [MOp.exec, toState_pc, hpc, SPc.denote, Obj.adrp_pageOf_cancel]
    rw [show Obj.pageOf (target.eval env) = (SExpr.pageOf target).eval env from rfl,
      toState_writeReg64 _ hlen, toState_advancePC]
  | addLo12Sym rd rn target =>
    simp only [stepSymInsn] at hstep
    cases hstep
    refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
    rw [lower_sound (op := .addSubImm .W64 .ADD rd rn
      ((Obj.lo12Of (target.eval env)).truncate 12) false) rfl]
    simp only [MOp.exec]
    rw [execAddSubImm_eq, ← toState_advancePC]
    congr 1
    show _ = ((ss.setReg .W64 rd (mkAddSub .W64 .ADD (ss.readReg .W64 rn) (.lo12Of target))).toState
      b env s0 m).setPState ((mkFlags .W64 .ADD (ss.readReg .W64 rn) (.lo12Of target) ss.flags).denote
        env s0.pstate)
    rw [← toState_writeReg _ hlen, mkAddSub_eval, mkFlags_denote, toState_readReg]
    simp [Obj.zeroExtend_truncate_lo12Of, SExpr.eval]
  | ldr64Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i ro ca cv hC
        cases hstep
        rw [allHold_append] at hobl
        have hea := oblEq_sound hobl.2
        obtain ⟨hrd, hcan⟩ := cellsProp_load64 (pt64At?_some hC) hm
        refine ⟨m, ?_, by simpa using hm, by simp [setReg_length, hlen], by simpa using hvval⟩
        rw [lower_sound (op := .ldr .W64 .X64 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
        simp only [MOp.exec]
        rw [execLdr_x64 (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
            (by rw [toState_mem, hea]; exact hcan)]
        simp only [applyWriteback]
        rw [toState_mem, hea, hrd, toState_writeReg _ hlen, toState_advancePC]
      · cases hstep
  | str64Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i ca cv hC
        cases hstep
        rw [allHold_append] at hobl
        have hea := oblEq_sound hobl.2
        obtain ⟨hst, hcan⟩ := cellsProp_store64 (ss.readReg64 rt) (pt64MutAt?_some hC) hm
        refine ⟨_, ?_, by simpa using hst, by simp [hlen], by simpa using hvval⟩
        rw [lower_sound (op := .str .X64 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
        simp only [MOp.exec]
        rw [execStr_x64 (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
            (by rw [toState_mem, hea]; exact hcan)]
        simp only [applyWriteback]
        rw [toState_mem, hea, toState_readReg64, toState_setMem,
          ← toState_setCell ss k (.pt64 false ca (ss.readReg64 rt)), toState_advancePC]
      · cases hstep
  | ldr32Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i ro cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
          refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
          rw [lower_sound (op := .ldrN .W32 .b32 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execLdr_n (cw := .b32) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, hrd, writeReg_zext (cw := .b32) (hcw := by decide), ← NVal.zext_eval,
            toState_writeReg64 _ hlen, toState_advancePC]
        · cases hstep
      · cases hstep
  | str32Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hst, hcan⟩ := cellsProp_storeN (ss.readReg64 rt) (ptNMutAt?_some hC) hm
          refine ⟨_, ?_, by simpa using hst, by simp [hlen], by simpa using hvval⟩
          rw [lower_sound (op := .strN .b32 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execStr_n (cw := .b32) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, toState_readReg64, toState_setMem,
            ← toState_setCell ss k (.ptN .b32 false ca (mkTrunc .b32 (ss.readReg64 rt))), toState_advancePC]
        · cases hstep
      · cases hstep
  | ldr16Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i ro cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
          refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
          rw [lower_sound (op := .ldrN .W32 .b16 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execLdr_n (cw := .b16) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, hrd, writeReg_zext (cw := .b16) (hcw := by decide), ← NVal.zext_eval,
            toState_writeReg64 _ hlen, toState_advancePC]
        · cases hstep
      · cases hstep
  | str16Lo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hst, hcan⟩ := cellsProp_storeN (ss.readReg64 rt) (ptNMutAt?_some hC) hm
          refine ⟨_, ?_, by simpa using hst, by simp [hlen], by simpa using hvval⟩
          rw [lower_sound (op := .strN .b16 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execStr_n (cw := .b16) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, toState_readReg64, toState_setMem,
            ← toState_setCell ss k (.ptN .b16 false ca (mkTrunc .b16 (ss.readReg64 rt))), toState_advancePC]
        · cases hstep
      · cases hstep
  | ldrbLo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i ro cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hrd, hcan⟩ := cellsProp_loadN (ptNAt?_some hC) hm
          refine ⟨m, ?_, by simpa using hm, by simp [setReg64_length, hlen], by simpa using hvval⟩
          rw [lower_sound (op := .ldrN .W32 .b8 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execLdr_n (cw := .b8) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, hrd, writeReg_zext (cw := .b8) (hcw := by decide), ← NVal.zext_eval,
            toState_writeReg64 _ hlen, toState_advancePC]
        · cases hstep
      · cases hstep
  | strbLo12Sym rt rn target =>
    cases h <;> simp only [stepSymInsn] at hstep <;> try cases hstep
    case cell k =>
      split at hstep
      · rename_i cw' ca cv hC
        split at hstep
        · rename_i hcw; subst hcw; cases hstep
          rw [allHold_append] at hobl
          have hea := oblEq_sound hobl.2
          obtain ⟨hst, hcan⟩ := cellsProp_storeN (ss.readReg64 rt) (ptNMutAt?_some hC) hm
          refine ⟨_, ?_, by simpa using hst, by simp [hlen], by simpa using hvval⟩
          rw [lower_sound (op := .strN .b8 rt (.Offset rn (Obj.lo12Of (target.eval env)))) rfl]
          simp only [MOp.exec]
          rw [execStr_n (cw := .b8) (regAlignObl_sound hobl.1) (evalAddrMode_lo12Sym ss rn target)
              (by rw [toState_mem, hea]; exact hcan)]
          simp only [applyWriteback]
          rw [toState_mem, hea, toState_readReg64, toState_setMem,
            ← toState_setCell ss k (.ptN .b8 false ca (mkTrunc .b8 (ss.readReg64 rt))), toState_advancePC]
        · cases hstep
      · cases hstep

end SymInsnSoundness

end ProofLib.SymBlock
