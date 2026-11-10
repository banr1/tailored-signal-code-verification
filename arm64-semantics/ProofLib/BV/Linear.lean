/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.BV.Attr
import Arm64.Trusted.Spec.SepLogic

/-!
# Certified Linear Normal Form for `BitVec w`

Reflective decision procedure and normalizer (`bv_lin`, `bv_lin_norm`) for linear `BitVec w`
arithmetic (`+`, `-`, unary `-`, constant multiplication, left shift by a literal, and
`BitVec.ofNat w n` for linear `Nat` expressions `n`), treating non-linear subterms as opaque atoms.
`Lin.Expr` and `Lin.NExpr` normalize to `Lin.Poly` (`c + sum_i coeff_i * atom_i`), with equality and
disequality decided in the kernel by `Eq.refl true` via `Lin.eq_of_eqCheck` and `Lin.ne_of_neCheck`.
-/

namespace ProofLib.BV.Lin

@[expose] public section

def getD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: as, n + 1, d => getD as n d

/-! ## Reflected syntax -/

/-- Linear `Nat` expressions (argument of `BitVec.ofNat w`). -/
inductive NExpr where
  | atom (i : Nat)
  | lit (n : Nat)
  | add (a b : NExpr)
  | mul (a b : NExpr)
  deriving Inhabited, Repr

/-- Linear `BitVec w` expressions. -/
inductive Expr where
  | atom (i : Nat)
  | ofNat (n : NExpr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | neg (a : Expr)
  | mul (a b : Expr)
  | shl (a : Expr) (k : Nat)
  deriving Inhabited, Repr

def NExpr.denote (nctx : List Nat) : NExpr → Nat
  | .atom i => getD nctx i 0
  | .lit n => n
  | .add a b => a.denote nctx + b.denote nctx
  | .mul a b => a.denote nctx * b.denote nctx

def Expr.denote {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat) : Expr → BitVec w
  | .atom i => getD ctx i 0
  | .ofNat n => BitVec.ofNat w (n.denote nctx)
  | .add a b => a.denote ctx nctx + b.denote ctx nctx
  | .sub a b => a.denote ctx nctx - b.denote ctx nctx
  | .neg a => - a.denote ctx nctx
  | .mul a b => a.denote ctx nctx * b.denote ctx nctx
  | .shl a k => a.denote ctx nctx <<< k

/-! ## Normal form -/

@[inline] def intIsZero : Int → Bool
  | .ofNat n => Nat.beq n 0
  | .negSucc _ => false

theorem intIsZero_iff (c : Int) : intIsZero c = true ↔ c = 0 := by
  cases c <;> simp [intIsZero, Nat.beq_eq]

/-- Linear combination `c + sum coeff * atom(key)`. Terms are kept sorted by key with no
duplicates when built with `insertT`; soundness does not depend on this invariant. -/
structure Poly where
  c : Int
  ts : List (Nat × Int)
  deriving Inhabited, Repr, BEq

/-- Insert `(k, c)` into a sorted term list, merging and dropping zero coefficients. -/
def insertT (k : Nat) (c : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => cond (intIsZero c) [] [(k, c)]
  | (k', c') :: ts =>
    cond (Nat.blt k k') ((k, c) :: (k', c') :: ts)
      (cond (Nat.beq k k')
        (cond (intIsZero (c + c')) ts ((k, c + c') :: ts))
        ((k', c') :: insertT k c ts))

def addTs : List (Nat × Int) → List (Nat × Int) → List (Nat × Int)
  | [], ys => ys
  | (k, c) :: xs, ys => insertT k c (addTs xs ys)

def scaleTs (m : Int) : List (Nat × Int) → List (Nat × Int)
  | [] => []
  | (k, c) :: xs => (k, m * c) :: scaleTs m xs

def Poly.add (p q : Poly) : Poly := ⟨p.c + q.c, addTs p.ts q.ts⟩
def Poly.scale (m : Int) (p : Poly) : Poly :=
  cond (intIsZero m) ⟨0, []⟩ ⟨m * p.c, scaleTs m p.ts⟩
def Poly.neg (p : Poly) : Poly := p.scale (-1)

/-- Product, defined only if one side is constant. -/
def Poly.mul? : Poly → Poly → Option Poly
  | ⟨c, []⟩, q => some (q.scale c)
  | p, ⟨c, []⟩ => some (p.scale c)
  | _, _ => none

def NExpr.norm : NExpr → Option Poly
  | .atom i => some ⟨0, [(2 * i + 1, 1)]⟩
  | .lit n => some ⟨n, []⟩
  | .add a b =>
    match a.norm, b.norm with
    | some p, some q => some (p.add q)
    | _, _ => none
  | .mul a b =>
    match a.norm, b.norm with
    | some p, some q => p.mul? q
    | _, _ => none

def Expr.norm : Expr → Option Poly
  | .atom i => some ⟨0, [(2 * i, 1)]⟩
  | .ofNat n => n.norm
  | .add a b =>
    match a.norm, b.norm with
    | some p, some q => some (p.add q)
    | _, _ => none
  | .sub a b =>
    match a.norm, b.norm with
    | some p, some q => some (p.add q.neg)
    | _, _ => none
  | .neg a =>
    match a.norm with
    | some p => some p.neg
    | none => none
  | .mul a b =>
    match a.norm, b.norm with
    | some p, some q => p.mul? q
    | _, _ => none
  | .shl a k =>
    match a.norm with
    | some p => some (p.scale (Int.ofNat (2 ^ k)))
    | none => none

/-! ## Semantics of the normal form -/

def keyDenote {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat) (k : Nat) : BitVec w :=
  cond (Nat.beq (k % 2) 0) (getD ctx (k / 2) 0) (BitVec.ofNat w (getD nctx (k / 2) 0))

def denoteTs {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat) : List (Nat × Int) → BitVec w
  | [] => 0
  | (k, c) :: ts => keyDenote ctx nctx k * BitVec.ofInt w c + denoteTs ctx nctx ts

def Poly.denote {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat) (p : Poly) : BitVec w :=
  denoteTs ctx nctx p.ts + BitVec.ofInt w p.c

section Soundness
variable {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat)

theorem ofInt_zero' : BitVec.ofInt w 0 = 0 := by
  apply BitVec.eq_of_toNat_eq; simp

theorem insertT_denote (k : Nat) (c : Int) (ts : List (Nat × Int)) :
    denoteTs ctx nctx (insertT k c ts) =
      keyDenote ctx nctx k * BitVec.ofInt w c + denoteTs ctx nctx ts := by
  induction ts with
  | nil =>
    unfold insertT
    cases h : intIsZero c
    · simp [denoteTs]
    · rw [intIsZero_iff] at h; subst h; simp [denoteTs]
  | cons hd ts ih =>
    obtain ⟨k', c'⟩ := hd
    unfold insertT
    cases hlt : Nat.blt k k'
    · cases heq : Nat.beq k k'
      · simp only [Bool.cond_false, denoteTs, ih]; ac_rfl
      · rw [Nat.beq_eq] at heq; subst heq
        cases hz : intIsZero (c + c')
        · simp only [Bool.cond_false, Bool.cond_true, denoteTs, BitVec.ofInt_add]
          rw [BitVec.mul_add, BitVec.add_assoc]
        · rw [intIsZero_iff] at hz
          have : BitVec.ofInt w c + BitVec.ofInt w c' = 0 := by
            rw [← BitVec.ofInt_add, hz, ofInt_zero']
          simp only [Bool.cond_true, Bool.cond_false, denoteTs]
          rw [← BitVec.add_assoc, ← BitVec.mul_add, this]; simp
    · simp [denoteTs]

theorem addTs_denote (xs ys : List (Nat × Int)) :
    denoteTs ctx nctx (addTs xs ys) = denoteTs ctx nctx xs + denoteTs ctx nctx ys := by
  induction xs with
  | nil => simp [addTs, denoteTs]
  | cons hd xs ih =>
    obtain ⟨k, c⟩ := hd
    simp only [addTs, insertT_denote, ih, denoteTs, BitVec.add_assoc]

theorem scaleTs_denote (m : Int) (xs : List (Nat × Int)) :
    denoteTs ctx nctx (scaleTs m xs) = denoteTs ctx nctx xs * BitVec.ofInt w m := by
  induction xs with
  | nil => simp [scaleTs, denoteTs]
  | cons hd xs ih =>
    obtain ⟨k, c⟩ := hd
    simp only [scaleTs, denoteTs, ih, BitVec.ofInt_mul, BitVec.add_mul]
    rw [BitVec.mul_assoc, BitVec.mul_comm (BitVec.ofInt w c)]

theorem Poly.add_denote (p q : Poly) :
    (p.add q).denote ctx nctx = p.denote ctx nctx + q.denote ctx nctx := by
  simp only [Poly.add, Poly.denote, addTs_denote, BitVec.ofInt_add]; ac_rfl

theorem Poly.scale_denote (m : Int) (p : Poly) :
    (p.scale m).denote ctx nctx = p.denote ctx nctx * BitVec.ofInt w m := by
  unfold Poly.scale
  cases h : intIsZero m
  · simp only [Bool.cond_false, Poly.denote, scaleTs_denote, BitVec.ofInt_mul, BitVec.add_mul]
    rw [BitVec.mul_comm (BitVec.ofInt w m) (BitVec.ofInt w p.c)]
  · rw [intIsZero_iff] at h; subst h
    simp [Poly.denote, denoteTs]

theorem Poly.neg_denote (p : Poly) : p.neg.denote ctx nctx = - p.denote ctx nctx := by
  rw [Poly.neg, Poly.scale_denote]
  have : BitVec.ofInt w (-1) = -1 := by rw [BitVec.ofInt_neg]; rfl
  rw [this, BitVec.mul_neg]; simp

theorem Poly.mul?_denote (p q r : Poly) (h : p.mul? q = some r) :
    r.denote ctx nctx = p.denote ctx nctx * q.denote ctx nctx := by
  match p, q, h with
  | ⟨c, []⟩, q, h =>
    simp only [Poly.mul?, Option.some.injEq] at h; subst h
    rw [Poly.scale_denote, BitVec.mul_comm]; simp [Poly.denote, denoteTs]
  | ⟨c, _ :: _⟩, ⟨c', []⟩, h =>
    simp only [Poly.mul?, Option.some.injEq] at h; subst h
    rw [Poly.scale_denote]; simp [Poly.denote, denoteTs]

theorem NExpr.norm_sound (e : NExpr) (p : Poly) (h : e.norm = some p) :
    BitVec.ofNat w (e.denote nctx) = p.denote ctx nctx := by
  induction e generalizing p with
  | atom i =>
    simp only [NExpr.norm, Option.some.injEq] at h; subst h
    have h1 : Nat.beq ((2 * i + 1) % 2) 0 = false := by
      cases h : Nat.beq ((2 * i + 1) % 2) 0
      · rfl
      · rw [Nat.beq_eq] at h; omega
    have h2 : (2 * i + 1) / 2 = i := by omega
    simp only [NExpr.denote, Poly.denote, denoteTs, keyDenote, h1, h2, Bool.cond_false]
    simp
  | lit n =>
    simp only [NExpr.norm, Option.some.injEq] at h; subst h
    simp [NExpr.denote, Poly.denote, denoteTs]
  | add a b iha ihb =>
    simp only [NExpr.norm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [NExpr.denote, BitVec.ofNat_add, iha _ ‹_›, ihb _ ‹_›, Poly.add_denote]
  | mul a b iha ihb =>
    simp only [NExpr.norm] at h
    split at h
    · rw [NExpr.denote, BitVec.ofNat_mul, iha _ ‹_›, ihb _ ‹_›, Poly.mul?_denote _ _ _ _ _ h]
    · simp at h

theorem twoPow_eq_ofInt (k : Nat) : BitVec.twoPow w k = BitVec.ofInt w (Int.ofNat (2 ^ k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_twoPow, BitVec.toNat_ofInt]
  rw [Int.ofNat_eq_natCast, ← Int.natCast_emod, Int.toNat_natCast]

theorem Expr.norm_sound (e : Expr) (p : Poly) (h : e.norm = some p) :
    e.denote ctx nctx = p.denote ctx nctx := by
  induction e generalizing p with
  | atom i =>
    simp only [Expr.norm, Option.some.injEq] at h; subst h
    have h1 : Nat.beq ((2 * i) % 2) 0 = true := by rw [Nat.beq_eq]; omega
    have h2 : (2 * i) / 2 = i := by omega
    simp only [Expr.denote, Poly.denote, denoteTs, keyDenote, h1, h2, Bool.cond_true]
    simp
  | ofNat n => exact NExpr.norm_sound ctx nctx n p h
  | add a b iha ihb =>
    simp only [Expr.norm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [Expr.denote, iha _ ‹_›, ihb _ ‹_›, Poly.add_denote]
  | sub a b iha ihb =>
    simp only [Expr.norm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [Expr.denote, iha _ ‹_›, ihb _ ‹_›, Poly.add_denote, Poly.neg_denote,
      BitVec.sub_eq_add_neg]
  | neg a iha =>
    simp only [Expr.norm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [Expr.denote, iha _ ‹_›, Poly.neg_denote]
  | mul a b iha ihb =>
    simp only [Expr.norm] at h
    split at h
    · rw [Expr.denote, iha _ ‹_›, ihb _ ‹_›, Poly.mul?_denote _ _ _ _ _ h]
    · simp at h
  | shl a k iha =>
    simp only [Expr.norm] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rw [Expr.denote, iha _ ‹_›, Poly.scale_denote, BitVec.shiftLeft_eq_mul_twoPow,
      twoPow_eq_ofInt]

end Soundness

/-! ## Decision functions -/

/-- Check `c % m = 0` (`m = 0` checks `c = 0`). -/
@[inline] def zeroMod (m : Nat) (c : Int) : Bool := intIsZero (c % (m : Int))

def allZeroMod (m : Nat) : List (Nat × Int) → Bool
  | [] => true
  | (_, c) :: ts => zeroMod m c && allZeroMod m ts

/-- `a = b` holds modulo `m` by normal forms. -/
def eqCheck (m : Nat) (a b : Expr) : Bool :=
  match (Expr.sub a b).norm with
  | some p => zeroMod m p.c && allZeroMod m p.ts
  | none => false

/-- `a - b` normalizes to a constant that is non-zero modulo `m`. -/
def neCheck (m : Nat) (a b : Expr) : Bool :=
  match (Expr.sub a b).norm with
  | some p => !zeroMod m p.c && allZeroMod m p.ts
  | none => false

section Checks
variable {w : Nat} (ctx : List (BitVec w)) (nctx : List Nat)

theorem ofInt_eq_zero_of_zeroMod (m : Nat) (hm : m % 2 ^ w = 0) (c : Int)
    (h : zeroMod m c = true) : BitVec.ofInt w c = 0 := by
  rw [zeroMod, intIsZero_iff] at h
  apply BitVec.eq_of_toNat_eq
  have hd : ((2 ^ w : Nat) : Int) ∣ (m : Int) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hm)
  have h2 : c % ((2 ^ w : Nat) : Int) = 0 :=
    Int.emod_eq_zero_of_dvd (Int.dvd_trans hd (Int.dvd_of_emod_eq_zero h))
  simp only [BitVec.toNat_ofInt]
  rw [h2]; rfl

theorem denoteTs_eq_zero (m : Nat) (hm : m % 2 ^ w = 0) (ts : List (Nat × Int))
    (h : allZeroMod m ts = true) : denoteTs ctx nctx ts = 0 := by
  induction ts with
  | nil => rfl
  | cons hd ts ih =>
    obtain ⟨k, c⟩ := hd
    simp only [allZeroMod, Bool.and_eq_true] at h
    simp [denoteTs, ofInt_eq_zero_of_zeroMod m hm c h.1, ih h.2]

theorem eq_of_eqCheck (m : Nat) (hm : m % 2 ^ w = 0) (a b : Expr)
    (h : eqCheck m a b = true) : a.denote ctx nctx = b.denote ctx nctx := by
  unfold eqCheck at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true] at h
    have := Expr.norm_sound ctx nctx _ p hp
    rw [Poly.denote, denoteTs_eq_zero ctx nctx m hm _ h.2,
      ofInt_eq_zero_of_zeroMod m hm _ h.1, Expr.denote] at this
    have h5 := congrArg (· + b.denote ctx nctx) this
    simpa [BitVec.sub_add_cancel] using h5
  · simp at h

/-- Entry point for a literal width (`2^w` reduces to a literal in the kernel). -/
theorem eq_of_eqCheck_pow (a b : Expr) (h : eqCheck (2 ^ w) a b = true) :
    a.denote ctx nctx = b.denote ctx nctx :=
  eq_of_eqCheck ctx nctx _ (Nat.mod_self _) a b h

/-- Entry point for a symbolic width (exact `Int` coefficients). -/
theorem eq_of_eqCheck_zero (a b : Expr) (h : eqCheck 0 a b = true) :
    a.denote ctx nctx = b.denote ctx nctx :=
  eq_of_eqCheck ctx nctx 0 (Nat.zero_mod _) a b h

theorem ne_of_neCheck (a b : Expr) (h : neCheck (2 ^ w) a b = true) :
    a.denote ctx nctx ≠ b.denote ctx nctx := by
  unfold neCheck at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    intro heq
    have := Expr.norm_sound ctx nctx _ p hp
    rw [Poly.denote, denoteTs_eq_zero ctx nctx _ (Nat.mod_self _) _ h.2, Expr.denote, heq,
      BitVec.sub_self] at this
    simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_add] at this
    have h3 := congrArg BitVec.toNat this
    simp only [BitVec.toNat_zero, BitVec.toNat_ofInt] at h3
    have hpos : (0 : Int) < ((2 ^ w : Nat) : Int) := by
      have := Nat.two_pow_pos w; omega
    have hnn := Int.emod_nonneg p.c (Int.ne_of_gt hpos)
    have : p.c % ((2 ^ w : Nat) : Int) = 0 := by omega
    rw [zeroMod] at h
    have h4 : intIsZero (p.c % ((2 ^ w : Nat) : Int)) = true := (intIsZero_iff _).mpr this
    rw [h4] at h; exact absurd h.1 (by decide)
  · simp at h

end Checks

end

/-! ## Meta layer -/

public meta section
set_option compiler.relaxedMetaCheck true

open Lean Meta Elab Tactic

/-- Reification state: `BitVec` atoms and `Nat` atoms, compared up to instance-reducible defeq. -/
structure LinState where
  atoms : Array Lean.Expr := #[]
  natAtoms : Array Lean.Expr := #[]

abbrev LinM := StateRefT LinState MetaM

def LinM.run' {α : Type} (x : LinM α) : MetaM α := StateRefT'.run' x {}

private def findOrPush (arr : Array Lean.Expr) (e : Lean.Expr) : MetaM (Nat × Array Lean.Expr) := do
  for h : i in [:arr.size] do
    if arr[i] == e then return (i, arr)
  for h : i in [:arr.size] do
    if ← withNewMCtxDepth (withTransparency .instances (isDefEq arr[i] e)) then return (i, arr)
  return (arr.size, arr.push e)

def bvAtom (e : Lean.Expr) : LinM Nat := do
  let (i, arr) ← findOrPush (← get).atoms e
  modify fun s => { s with atoms := arr }
  return i

def natAtom (e : Lean.Expr) : LinM Nat := do
  let (i, arr) ← findOrPush (← get).natAtoms e
  modify fun s => { s with natAtoms := arr }
  return i

private def isBVBinInst (inst : Lean.Expr) (outer inner : Name) : Bool :=
  inst.isAppOfArity outer 2 && inst.appArg!.isAppOfArity inner 1

private def natLit? (e : Lean.Expr) : MetaM (Option Nat) := do
  if e.hasFVar || e.hasMVar then return none
  match ← (evalNat e).run with
  | some n => if n < 2 ^ 4096 then return some n else return none
  | none => return none

partial def reifyNat (e : Lean.Expr) : LinM NExpr := do
  if let some n ← natLit? e then return .lit n
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if i.isAppOfArity ``instHAdd 2 && i.appArg!.isConstOf ``instAddNat then return .add (← reifyNat a) (← reifyNat b)
  | HMul.hMul _ _ _ i a b =>
    if i.isAppOfArity ``instHMul 2 && i.appArg!.isConstOf ``instMulNat then
      let ra ← reifyNat a
      let rb ← reifyNat b
      if (NExpr.mul ra rb).norm.isSome then return .mul ra rb
  | Nat.succ a => return .add (← reifyNat a) (.lit 1)
  | _ => pure ()
  return .atom (← natAtom e)

partial def reify (e : Lean.Expr) : LinM Expr := do
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isBVBinInst i ``instHAdd ``BitVec.instAdd then return .add (← reify a) (← reify b)
  | HSub.hSub _ _ _ i a b =>
    if isBVBinInst i ``instHSub ``BitVec.instSub then return .sub (← reify a) (← reify b)
  | Neg.neg _ i a =>
    if i.isAppOfArity ``BitVec.instNeg 1 then return .neg (← reify a)
  | HMul.hMul _ _ _ i a b =>
    if isBVBinInst i ``instHMul ``BitVec.instMul then
      let ra ← reify a
      let rb ← reify b
      if (Expr.mul ra rb).norm.isSome then return .mul ra rb
  | HShiftLeft.hShiftLeft _ _ _ i a k =>
    if i.isAppOfArity ``BitVec.instHShiftLeftNat 1 then
      if let some k ← natLit? k then
        if k < 4096 then return .shl (← reify a) k
  | OfNat.ofNat _ n i =>
    if i.isAppOfArity ``BitVec.instOfNat 2 then
      if let some n := n.rawNatLit? then return .ofNat (.lit n)
  | BitVec.ofNat _ n => return .ofNat (← reifyNat n)
  | BitVec.ofFin w f =>
    if let some wv ← natLit? w then
      if let some (_, v, _) := f.app3? ``Fin.mk then
        if let some v ← natLit? v then
          if v < 2 ^ wv then return .ofNat (.lit v)
  | _ => pure ()
  return .atom (← bvAtom e)

def bvWidth? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let ty ← whnfR (← inferType e)
  match_expr ty with
  | BitVec w => return some w
  | _ => return none

def widthNat? (w : Lean.Expr) : MetaM (Option Nat) := do
  match ← natLit? w with
  | some n => if n ≤ 4096 then return some n else return none
  | none => return none

partial def nexprToLean : NExpr → Lean.Expr
  | .atom i => mkApp (mkConst ``NExpr.atom) (mkRawNatLit i)
  | .lit n => mkApp (mkConst ``NExpr.lit) (mkRawNatLit n)
  | .add a b => mkApp2 (mkConst ``NExpr.add) (nexprToLean a) (nexprToLean b)
  | .mul a b => mkApp2 (mkConst ``NExpr.mul) (nexprToLean a) (nexprToLean b)

partial def exprToLean : Expr → Lean.Expr
  | .atom i => mkApp (mkConst ``Expr.atom) (mkRawNatLit i)
  | .ofNat n => mkApp (mkConst ``Expr.ofNat) (nexprToLean n)
  | .add a b => mkApp2 (mkConst ``Expr.add) (exprToLean a) (exprToLean b)
  | .sub a b => mkApp2 (mkConst ``Expr.sub) (exprToLean a) (exprToLean b)
  | .neg a => mkApp (mkConst ``Expr.neg) (exprToLean a)
  | .mul a b => mkApp2 (mkConst ``Expr.mul) (exprToLean a) (exprToLean b)
  | .shl a k => mkApp2 (mkConst ``Expr.shl) (exprToLean a) (mkRawNatLit k)

def mkCtxs (w : Lean.Expr) : LinM (Lean.Expr × Lean.Expr) := do
  let s ← get
  let ctx ← mkListLit (mkApp (mkConst ``BitVec) w) s.atoms.toList
  let nctx ← mkListLit (mkConst ``Nat) s.natAtoms.toList
  return (ctx, nctx)

private def trueRefl : Lean.Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)

/-- Proof of `ea = eb` (`BitVec w`) from reified `ra` and `rb`, if `eqCheck` succeeds. -/
def proveEqCore (w ea eb : Lean.Expr) (ra rb : Expr) : LinM (Option Lean.Expr) := do
  let wn? ← widthNat? w
  let m := match wn? with | some n => 2 ^ n | none => 0
  unless eqCheck m ra rb do return none
  let (ctx, nctx) ← mkCtxs w
  let thm := if wn?.isSome then ``eq_of_eqCheck_pow else ``eq_of_eqCheck_zero
  let pf := mkApp6 (mkConst thm) w ctx nctx (exprToLean ra) (exprToLean rb) trueRefl
  return some (← mkExpectedTypeHint pf (← mkEq ea eb))

/-- Linear form of a `BitVec` term: width, constant, and `(atom, coeff)` list (coefficients
reduced mod `2^w` for a literal width, exact otherwise; zero coefficients dropped). `Nat` atoms
`n` are returned as `BitVec.ofNat w n`. -/
structure LinForm where
  width : Lean.Expr
  const : Int
  terms : Array (Lean.Expr × Int)

private def reduceCoeff (wn? : Option Nat) (c : Int) : Int :=
  match wn? with | some n => c % ((2 ^ n : Nat) : Int) | none => c

private def keyAtom (w : Lean.Expr) (k : Nat) : LinM Lean.Expr := do
  let s ← get
  if k % 2 == 0 then return s.atoms[k / 2]!
  else return mkApp2 (mkConst ``BitVec.ofNat) w s.natAtoms[k / 2]!

/-- Reify and normalize `e : BitVec w`. -/
def linearize (e : Lean.Expr) : LinM (Option LinForm) := do
  let some w ← bvWidth? e | return none
  let wn? ← widthNat? w
  let some p := (← reify e).norm | return none
  let mut terms := #[]
  for (k, c) in p.ts do
    let c := reduceCoeff wn? c
    if c != 0 then terms := terms.push (← keyAtom w k, c)
  return some { width := w, const := reduceCoeff wn? p.c, terms }

/-- Proof of `a = b`, or `none`. -/
def proveEq? (a b : Lean.Expr) : MetaM (Option Lean.Expr) := LinM.run' do
  let some w ← bvWidth? a | return none
  proveEqCore w a b (← reify a) (← reify b)

/-- Proof of `a != b` when `a - b` normalizes to a constant non-zero mod `2^w` (literal `w`
only), or `none`. -/
def proveNe? (a b : Lean.Expr) : MetaM (Option Lean.Expr) := LinM.run' do
  let some w ← bvWidth? a | return none
  let some n ← widthNat? w | return none
  let ra ← reify a
  let rb ← reify b
  unless neCheck (2 ^ n) ra rb do return none
  let (ctx, nctx) ← mkCtxs w
  let pf := mkApp6 (mkConst ``ne_of_neCheck) w ctx nctx (exprToLean ra) (exprToLean rb) trueRefl
  return some (← mkExpectedTypeHint pf (← mkAppM ``Ne #[a, b]))

/-- Construct `@OfNat.ofNat (BitVec w) c (BitVec.instOfNat w c)` with a raw literal `c`. -/
def mkBVLit (w : Lean.Expr) (c : Nat) : Lean.Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [0]) (mkApp (mkConst ``BitVec) w) (mkRawNatLit c)
    (mkApp2 (mkConst ``BitVec.instOfNat) w (mkRawNatLit c))

/-- If `a - b` normalizes to a constant `c` (`0 <= c < 2^w` for a literal width; `c >= 0` for a
symbolic width), return `c` and a proof of `a = b + (c : BitVec w)` where the numeral is
`mkBVLit w c`. -/
def diffConst? (a b : Lean.Expr) : MetaM (Option (Nat × Lean.Expr)) := LinM.run' do
  let some w ← bvWidth? a | return none
  let wn? ← widthNat? w
  let ra ← reify a
  let rb ← reify b
  let some p := (Expr.sub ra rb).norm | return none
  let m := match wn? with | some n => 2 ^ n | none => 0
  unless allZeroMod m p.ts do return none
  let c := reduceCoeff wn? p.c
  if c < 0 then return none
  let c := c.toNat
  let lit := mkBVLit w c
  let rhs ← mkAppM ``HAdd.hAdd #[b, lit]
  let some pf ← proveEqCore w a rhs ra (.add rb (.ofNat (.lit c))) | return none
  return some (c, pf)

/-! ## Canonical printing and `bv_lin` -/

private def bvMul (x y : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HMul.hMul #[x, y]
private def bvAdd (x y : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HAdd.hAdd #[x, y]
private def bvSub (x y : Lean.Expr) : MetaM Lean.Expr := mkAppM ``HSub.hSub #[x, y]
private def bvNeg (x : Lean.Expr) : MetaM Lean.Expr := mkAppM ``Neg.neg #[x]

private def signed (wn? : Option Nat) (c : Int) : Bool × Nat :=
  match wn? with
  | some n => let m : Nat := 2 ^ n; let c := (c % (m : Int)).toNat
    if 2 * c > m then (true, m - c) else (false, c)
  | none => if c < 0 then (true, c.natAbs) else (false, c.toNat)

/-- Canonical expression `t_1 ± t_2 ± ... ± k#w`, with atoms sorted by `Lean.Expr.lt`. -/
def canonical (w : Lean.Expr) (wn? : Option Nat) (p : Poly) : LinM Lean.Expr := do
  let mut ts : Array (Lean.Expr × Bool × Nat) := #[]
  for (k, c) in p.ts do
    let (neg, mag) := signed wn? c
    if mag != 0 then ts := ts.push (← keyAtom w k, neg, mag)
  ts := ts.qsort (fun x y => x.1.lt y.1)
  let term (a : Lean.Expr) (mag : Nat) : MetaM Lean.Expr :=
    if mag == 1 then pure a else bvMul a (mkBVLit w mag)
  let (cneg, cmag) := signed wn? p.c
  let mut acc : Option Lean.Expr := none
  for (a, neg, mag) in ts do
    let t ← term a mag
    acc ← match acc with
      | none => if neg then some <$> bvNeg t else pure (some t)
      | some x => some <$> (if neg then bvSub x t else bvAdd x t)
  match acc with
  | none =>
    let c := match wn? with
      | some n => (p.c % ((2 ^ n : Nat) : Int)).toNat
      | none => cmag
    if wn?.isNone && cneg then bvNeg (mkBVLit w c) else return mkBVLit w c
  | some x =>
    if cmag == 0 then return x
    if cneg then bvSub x (mkBVLit w cmag) else bvAdd x (mkBVLit w cmag)

/-- Canonical form of `e : BitVec w` with a proof `e = e'`, or `none` if `e` is an atom or
already canonical. -/
def normalize? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := LinM.run' do
  let some w ← bvWidth? e | return none
  let re ← reify e
  if let .atom _ := re then return none
  let some p := re.norm | return none
  let wn? ← widthNat? w
  let out ← canonical w wn? p
  if out == e then return none
  let some pf ← proveEqCore w e out re (← reify out) | return none
  return some (out, pf)

def linSimproc : Simp.Simproc := fun e => do
  match ← normalize? e with
  | some (e', pf) => return .done { expr := e', proof? := some pf }
  | none => return .continue

simproc [bv_lin_norm] bvLinAdd ((_ + _ : BitVec _)) := linSimproc
simproc [bv_lin_norm] bvLinSub ((_ - _ : BitVec _)) := linSimproc
simproc [bv_lin_norm] bvLinNeg ((- _ : BitVec _)) := linSimproc
simproc [bv_lin_norm] bvLinMul ((_ * _ : BitVec _)) := linSimproc
simproc [bv_lin_norm] bvLinShl ((_ <<< (_ : Nat) : BitVec _)) := linSimproc
simproc [bv_lin_norm] bvLinOfNat (BitVec.ofNat _ _) := linSimproc

private def goalShape? (ty : Lean.Expr) : MetaM (Option (Bool × Lean.Expr × Lean.Expr)) := do
  let ty ← instantiateMVars ty
  match_expr ty with
  | Eq _ a b => return some (true, a, b)
  | Ne _ a b => return some (false, a, b)
  | Not p =>
    match_expr p with
    | Eq _ a b => return some (false, a, b)
    | _ => return none
  | _ => return none

/-- When `true`, `bv_lin` falls back to rewriting non-cyclic local `BitVec` equality hypotheses
when the pure ring normalizer alone does not decide the goal. -/
register_option proofLib.bvLinAutoHyps : Bool := {
  defValue := true
  descr := "In `bv_lin`, automatically rewrite with non-cyclic local BitVec equality hypotheses when pure linear normalization does not decide the goal"
}

private def residue (a b : Lean.Expr) : MetaM MessageData := LinM.run' do
  let some w ← bvWidth? a | return m!"?"
  let some p := (Expr.sub (← reify a) (← reify b)).norm | return m!"?"
  return m!"{← canonical w (← widthNat? w) p}"

private def proveWithLocalEqs (g : MVarId) : MetaM Bool := g.withContext do
  let saved ← saveState
  try
    let mut gCur := g
    let mut anyRewritten := false
    let mut usedFVars : Std.HashMap FVarId Unit := {}
    for _ in [0 : 8] do
      let tgt ← instantiateMVars (← gCur.getType)
      let mut passChanged := false
      for decl in (← getLCtx) do
        if decl.isImplementationDetail || decl.isAuxDecl || usedFVars.contains decl.fvarId then
          continue
        let dty ← instantiateMVars decl.type
        match_expr dty with
        | Eq _ lhs rhs =>
          if (← bvWidth? lhs).isNone then continue
          if lhs == rhs then continue
          let dir? : Option Bool :=
            if (tgt.find? (· == lhs)).isSome && (rhs.find? (· == lhs)).isNone then
              some false
            else if (tgt.find? (· == rhs)).isSome && (lhs.find? (· == rhs)).isNone && rhs.isFVar then
              some true
            else
              none
          if let some symm := dir? then
            if let some r ← (try some <$> gCur.rewrite tgt decl.toExpr symm catch _ => pure none) then
              if r.mvarIds.isEmpty then
                gCur ← gCur.replaceTargetEq r.eNew r.eqProof
                usedFVars := usedFVars.insert decl.fvarId ()
                anyRewritten := true
                passChanged := true
                break
        | _ => continue
      if !passChanged then break
    if !anyRewritten then
      saved.restore
      return false
    let ty' ← instantiateMVars (← gCur.getType)
    let some (isEq, a', b') ← goalShape? ty' | do saved.restore; return false
    let pf? ← if isEq then proveEq? a' b' else proveNe? a' b'
    match pf? with
    | some pf =>
      gCur.assign (← mkExpectedTypeHint pf ty')
      return true
    | none =>
      saved.restore
      return false
  catch _ =>
    saved.restore
    return false

private def runBvLin (forceLocalEqs : Bool) (g : MVarId) : MetaM Unit := do
  let ty ← g.getType
  let some (isEq, a, b) ← goalShape? ty
    | throwError "bv_lin: goal is not `a = b`, `a ≠ b` or `¬ a = b`{indentExpr ty}"
  let some _ ← bvWidth? a | throwError "bv_lin: not a BitVec (in)equality{indentExpr ty}"
  let pf? ← if isEq then proveEq? a b else proveNe? a b
  match pf? with
  | some pf => g.assign (← mkExpectedTypeHint pf ty)
  | none =>
    if forceLocalEqs || proofLib.bvLinAutoHyps.get (← getOptions) then
      if ← proveWithLocalEqs g then
        return
    let res ← try residue a b catch _ => pure m!"?"
    throwError "bv_lin: linear normal form does not decide the goal; a - b normalizes to{indentD res}\nhint: bv_lin is a pure ring normalizer and ignores local hypotheses as well as bitwise/cast/comparison operations (which are treated as opaque atoms in the residue above); rewrite local equalities first (`rw [h]; bv_lin`) or use `bv_omega` / `bv_solve` / `bv_bits`"

/-- `bv_lin` closes `a = b`, `a != b`, and `not (a = b)` over `BitVec w` when the linear normal form
of `a - b` decides it (zero, or a non-zero constant), falling back to non-cyclic local `BitVec`
equality hypotheses when `proofLib.bvLinAutoHyps` is enabled. -/
elab "bv_lin" : tactic => liftMetaFinishingTactic (runBvLin false)

/-- `bv_lin*` rewrites with local `BitVec` equality hypotheses and closes the goal with `bv_lin`. -/
elab "bv_lin" "*" : tactic => liftMetaFinishingTactic (runBvLin true)

/-- `bv_lin [h1, h2, ...]` rewrites the goal with `h1, h2, ...` and closes it with `bv_lin`. -/
macro "bv_lin" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (try simp only [$hs,*]; bv_lin))

/-- `bv_auto` tries `bv_lin` first (including local equality rewriting), falling back to `bv_omega`
(and `bv_robdd` when `ProofLib.BV.ReflectROBDD` is imported). -/
syntax "bv_auto" : tactic
macro_rules
  | `(tactic| bv_auto) => `(tactic| first | bv_lin | bv_omega)

end

end ProofLib.BV.Lin
