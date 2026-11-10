/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Bit-Slicer and Witnessed ROBDD Decision Procedures

Pure-Lean kernel-reflective bitvector decision procedures closed via `Eq.refl true`:
`bv_slice` normalizes per-lane bitwise, shift, concatenation, and extraction goals via structural
`SBDD` trees (`checkSlice`, `prove_of_checkSlice`), and `bv_robdd` verifies interleaved LSB-to-MSB
ROBDD witnesses (`BinTree BDDNode`, `GateStep`) covering ripple-carry arithmetic, comparisons,
`AddWithCarry`, `ConditionHolds`, `ite`, and propositional hypotheses (`checkROBDD`,
`prove_of_checkROBDD`).
-/

namespace ProofLib.BV.ROBDD

@[expose] public section

/-! ## Structural primitives -/

/-- Structural list lookup with default, avoiding `Decidable` instances in kernel reduction. -/
def getD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | a :: _, 0, _ => a
  | _ :: as, n + 1, d => getD as n d

@[simp] theorem getD_nil {α : Type} (i : Nat) (d : α) : getD ([] : List α) i d = d := by
  cases i <;> rfl

@[simp] theorem getD_zero {α : Type} (a : α) (as : List α) (d : α) :
    getD (a :: as) 0 d = a := rfl

@[simp] theorem getD_succ {α : Type} (a : α) (as : List α) (n : Nat) (d : α) :
    getD (a :: as) (n + 1) d = getD as n d := rfl

theorem getD_of_ge {α : Type} : ∀ (xs : List α) (i : Nat) (d : α),
    xs.length ≤ i → getD xs i d = d
  | [], _, _, _ => getD_nil _ _
  | _ :: xs, i + 1, d, h => by
    simp only [List.length_cons] at h
    exact getD_of_ge xs i d (by omega)

/-- Radix-2 binary trie indexed by `Nat` bits (LSB at root) for $O(\log_2 N)$ structural lookup. -/
inductive BinTree (α : Type) where
  | empty
  | node (val : Option α) (left right : BinTree α)
  deriving Repr, Inhabited

/-- Structural $O(\log_2 i)$ optional lookup in a `BinTree`. Pattern-matching on `0` vs `i + 1`
forces `idx` to a `Nat` literal at every step during kernel reduction. -/
def BinTree.get? {α : Type} : BinTree α → Nat → Option α
  | .empty, _ => none
  | .node v _ _, 0 => v
  | .node _ l r, i + 1 =>
    cond (Nat.beq (Nat.land i 1) 0)
      (BinTree.get? l (Nat.shiftRight i 1))
      (BinTree.get? r (Nat.shiftRight i 1))

@[inline] def BinTree.get {α : Type} (d : α) (t : BinTree α) (idx : Nat) : α :=
  match t.get? idx with
  | some v => v
  | none => d

def BinTree.all {α : Type} (p : α → Bool) : BinTree α → Bool
  | .empty => true
  | .node none l r => BinTree.all p l && BinTree.all p r
  | .node (some x) l r => p x && BinTree.all p l && BinTree.all p r

theorem BinTree.all_get? {α : Type} (p : α → Bool) :
    ∀ (t : BinTree α) (idx : Nat) (x : α),
      BinTree.all p t = true → BinTree.get? t idx = some x → p x = true
  | .empty, _, _, _, hget => by cases hget
  | .node _ _ _, 0, x, hall, hget => by
    unfold BinTree.get? at hget
    subst hget
    simp only [BinTree.all, Bool.and_eq_true] at hall
    exact hall.1.1
  | .node v l r, i + 1, x, hall, hget => by
    unfold BinTree.get? at hget
    cases h1 : Nat.beq (Nat.land i 1) 0
    · rw [h1] at hget
      change BinTree.get? r (Nat.shiftRight i 1) = some x at hget
      cases v <;> simp only [BinTree.all, Bool.and_eq_true] at hall
      · exact BinTree.all_get? p r (Nat.shiftRight i 1) x hall.2 hget
      · exact BinTree.all_get? p r (Nat.shiftRight i 1) x hall.2 hget
    · rw [h1] at hget
      change BinTree.get? l (Nat.shiftRight i 1) = some x at hget
      cases v <;> simp only [BinTree.all, Bool.and_eq_true] at hall
      · exact BinTree.all_get? p l (Nat.shiftRight i 1) x hall.1 hget
      · exact BinTree.all_get? p l (Nat.shiftRight i 1) x hall.1.2 hget


/-! ## Symbolic Boolean backend (`SymBool`) and generic bit-blasting combinators -/

/-- Interface for symbolic Boolean representations (`SBDD` and `BinTree BDDNode` node IDs). -/
structure SymBool (α : Type) where
  fFalse : α
  fTrue  : α
  fVar   : Nat → α
  fNot   : α → Option α
  fAnd   : α → α → Option α
  fOr    : α → α → Option α
  fXor   : α → α → Option α

/-- Soundness contract for a `SymBool α` backend under bit-environment `benv : Nat → Bool`. -/
structure LawfulSymBool {α : Type} (B : SymBool α) (eval : α → Bool)
    (benv : Nat → Bool) (numVars : Nat) : Prop where
  eval_false : eval B.fFalse = false
  eval_true  : eval B.fTrue = true
  eval_var   : ∀ v, v < numVars → eval (B.fVar v) = benv v
  eval_not   : ∀ a u, B.fNot a = some u → eval u = !(eval a)
  eval_and   : ∀ a b u, B.fAnd a b = some u → eval u = (eval a && eval b)
  eval_or    : ∀ a b u, B.fOr a b = some u → eval u = (eval a || eval b)
  eval_xor   : ∀ a b u, B.fXor a b = some u → eval u = bne (eval a) (eval b)

/-- Symbolic `if c then t else e` built from `fAnd`, `fOr`, `fNot`: `(c && t) || (!c && e)`. -/
def symIte {α : Type} (B : SymBool α) (c t e : α) : Option α :=
  match B.fNot c, B.fAnd c t with
  | some nc, some ct =>
    match B.fAnd nc e with
    | some nce => B.fOr ct nce
    | none => none
  | _, _ => none

theorem symIte_sound {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars) (c t e u : α)
    (h : symIte B c t e = some u) :
    eval u = (if eval c then eval t else eval e) := by
  unfold symIte at h
  revert h
  cases hnc : B.fNot c <;> cases hct : B.fAnd c t <;> simp only
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · rename_i nc ct
    cases hnce : B.fAnd nc e <;> simp only
    · intro h; cases h
    · rename_i nce
      intro hor
      rw [hB.eval_or _ _ _ hor, hB.eval_and _ _ _ hct, hB.eval_and _ _ _ hnce, hB.eval_not _ _ hnc]
      cases eval c <;> simp

/-- Construct a list of `k` symbolic bits `[f start, f (start + 1), ..., f (start + k - 1)]`. -/
def mkBits {α : Type} (f : Nat → Option α) : Nat → Nat → Option (List α)
  | 0, _ => some []
  | k + 1, start =>
    match f start, mkBits f k (start + 1) with
    | some b, some bs => some (b :: bs)
    | _, _ => none

theorem mkBits_spec {α : Type} (f : Nat → Option α) (d : α) :
    ∀ (k start : Nat) (bs : List α),
      mkBits f k start = some bs →
      bs.length = k ∧
      ∀ i : Nat, i < k → ∃ b, f (start + i) = some b ∧ getD bs i d = b
  | 0, _, bs, h => by
    injection h with h'; subst h'
    exact ⟨rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  | k + 1, start, bs, h => by
    unfold mkBits at h
    revert h
    cases hf : f start <;> cases hrest : mkBits f k (start + 1) <;> simp only
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h
    · rename_i b rest
      intro h; injection h with h'; subst h'
      obtain ⟨hlen, hget⟩ := mkBits_spec f d k (start + 1) rest hrest
      refine ⟨by simp [hlen], fun i hi => ?_⟩
      cases i with
      | zero =>
        simp only [Nat.add_zero, getD_zero]
        exact ⟨b, hf, rfl⟩
      | succ j =>
        simp only [getD_succ]
        have hj : j < k := by omega
        obtain ⟨b', hb', hgd⟩ := hget j hj
        have hadd : start + 1 + j = start + (j + 1) := by omega
        rw [hadd] at hb'
        exact ⟨b', hb', hgd⟩

theorem mkBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    (w : Nat) (f : Nat → Option α) (target : BitVec w) (bs : List α)
    (hm : mkBits f w 0 = some bs)
    (hf : ∀ i b, i < w → f i = some b → eval b = target.getLsbD i) :
    bs.length = w ∧ ∀ i : Nat, eval (getD bs i B.fFalse) = target.getLsbD i := by
  obtain ⟨hlen, hspec⟩ := mkBits_spec f B.fFalse w 0 bs hm
  refine ⟨hlen, fun i => ?_⟩
  by_cases hi : i < w
  · obtain ⟨b, hfb, hgd⟩ := hspec i hi
    simp only [Nat.zero_add] at hfb
    rw [hgd, hf i b hi hfb]
  · rw [getD_of_ge bs i B.fFalse (by omega), hB.eval_false, BitVec.getLsbD_of_ge target i (by omega)]

@[inline] def headD {α : Type} (d : α) : List α → α
  | [] => d
  | x :: _ => x

@[inline] def tailD {α : Type} : List α → List α
  | [] => []
  | _ :: xs => xs

/-- Pattern-match on `as` once and pass `(head, tail)` to `k` as already-reduced constructor fields. -/
@[inline] def unconsD {α β : Type} (d : α) (as : List α) (k : α → List α → β) : β :=
  match as with
  | [] => k d []
  | a :: as' => k a as'

theorem unconsD_eq {α β : Type} (d : α) (as : List α) (k : α → List α → β) :
    unconsD d as k = k (headD d as) (tailD as) := by
  cases as <;> rfl

@[simp] theorem getD_zero_eq_headD {α : Type} (xs : List α) (d : α) :
    getD xs 0 d = headD d xs := by
  cases xs <;> rfl

@[simp] theorem getD_succ_eq_tailD {α : Type} (xs : List α) (i : Nat) (d : α) :
    getD xs (i + 1) d = getD (tailD xs) i d := by
  cases xs <;> rfl

private theorem shift_index {α : Type} (fx : Nat → α) (as : List α) (d : α) (start i : Nat)
    (hfx : ∀ j, fx (start + j) = getD as j d) :
    fx (start + 1 + i) = getD (tailD as) i d := by
  have hadd : start + 1 + i = start + (i + 1) := by omega
  rw [hadd, hfx (i + 1), getD_succ_eq_tailD]

/-- Linear $O(w)$ unary bit-list map across `k` bits (padding with `d`). -/
def mapBits {α : Type} (f : α → Option α) (d : α) : Nat → List α → Option (List α)
  | 0, _ => some []
  | k + 1, as =>
    unconsD d as (fun a as' =>
      match f a, mapBits f d k as' with
      | some b, some bs => some (b :: bs)
      | _, _ => none)

theorem mapBits_eq_mkBits {α : Type} (f : α → Option α) (d : α) :
    ∀ (k : Nat) (as : List α) (start : Nat) (fx : Nat → α),
      (∀ i, fx (start + i) = getD as i d) →
      mapBits f d k as = mkBits (fun i => f (fx i)) k start
  | 0, _, _, _, _ => rfl
  | k + 1, as, start, fx, hfx => by
    unfold mapBits mkBits
    rw [unconsD_eq]
    have h0 : fx start = headD d as := by
      have := hfx 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have ih := mapBits_eq_mkBits f d k (tailD as) (start + 1) fx (fun i => shift_index fx as d start i hfx)
    rw [h0, ih]

theorem mapBits_eq {α : Type} (f : α → Option α) (d : α) (w : Nat) (as : List α) :
    mapBits f d w as = mkBits (fun i => f (getD as i d)) w 0 :=
  mapBits_eq_mkBits f d w as 0 (fun i => getD as i d) (fun _ => by simp)

/-- Linear $O(w)$ binary bit-list zip across `k` bits (padding with `d`). -/
def zipBits {α : Type} (f : α → α → Option α) (d : α) : Nat → List α → List α → Option (List α)
  | 0, _, _ => some []
  | k + 1, as, bs =>
    unconsD d as (fun a as' =>
      unconsD d bs (fun b bs' =>
        match f a b, zipBits f d k as' bs' with
        | some c, some cs => some (c :: cs)
        | _, _ => none))

theorem zipBits_eq_mkBits {α : Type} (f : α → α → Option α) (d : α) :
    ∀ (k : Nat) (as bs : List α) (start : Nat) (fx fy : Nat → α),
      (∀ i, fx (start + i) = getD as i d) →
      (∀ i, fy (start + i) = getD bs i d) →
      zipBits f d k as bs = mkBits (fun i => f (fx i) (fy i)) k start
  | 0, _, _, _, _, _, _, _ => rfl
  | k + 1, as, bs, start, fx, fy, hfx, hfy => by
    unfold zipBits mkBits
    rw [unconsD_eq, unconsD_eq]
    have ha0 : fx start = headD d as := by
      have := hfx 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have hb0 : fy start = headD d bs := by
      have := hfy 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have ih := zipBits_eq_mkBits f d k (tailD as) (tailD bs) (start + 1) fx fy
      (fun i => shift_index fx as d start i hfx)
      (fun i => shift_index fy bs d start i hfy)
    rw [ha0, hb0, ih]

theorem zipBits_eq {α : Type} (f : α → α → Option α) (d : α) (w : Nat) (as bs : List α) :
    zipBits f d w as bs = mkBits (fun i => f (getD as i d) (getD bs i d)) w 0 :=
  zipBits_eq_mkBits f d w as bs 0 (fun i => getD as i d) (fun i => getD bs i d)
    (fun _ => by simp) (fun _ => by simp)

/-- Full adder on symbolic bits `x`, `y`, `cin`: returns `(sumBit, carryOut)`. -/
def fullAdder {α : Type} (B : SymBool α) (x y cin : α) : Option (α × α) :=
  match B.fXor x y with
  | none => none
  | some xy =>
    match B.fXor xy cin, B.fAnd x y, B.fAnd cin xy with
    | some s, some xyAnd, some cxyAnd =>
      match B.fOr xyAnd cxyAnd with
      | some cout => some (s, cout)
      | none => none
    | _, _, _ => none

private theorem bool_xor_assoc (a b c : Bool) : bne (bne a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bool_carry_eq_atLeastTwo (a b c : Bool) :
    ((a && b) || (c && bne a b)) = Bool.atLeastTwo a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem fullAdder_sound {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars) (x y cin s cout : α)
    (h : fullAdder B x y cin = some (s, cout)) :
    eval s = Bool.xor (eval x) (Bool.xor (eval y) (eval cin)) ∧
    eval cout = Bool.atLeastTwo (eval x) (eval y) (eval cin) := by
  unfold fullAdder at h
  revert h
  cases hxy : B.fXor x y <;> simp only
  · intro h; cases h
  · rename_i xy
    cases hs : B.fXor xy cin <;> cases h1 : B.fAnd x y <;> cases h2 : B.fAnd cin xy <;> simp only
    any_goals (intro h; cases h)
    rename_i s' xyAnd cxyAnd
    cases hcout : B.fOr xyAnd cxyAnd <;> simp only
    · intro h; cases h
    · rename_i cout'
      intro h; injection h with hp; injection hp with hs_eq hcout_eq; subst hs_eq hcout_eq
      rw [hB.eval_xor _ _ _ hs, hB.eval_xor _ _ _ hxy,
          hB.eval_or _ _ _ hcout, hB.eval_and _ _ _ h1, hB.eval_and _ _ _ h2, hB.eval_xor _ _ _ hxy]
      exact ⟨bool_xor_assoc _ _ _, bool_carry_eq_atLeastTwo _ _ _⟩

/-- Ripple-carry addition across `k` bit lanes starting at `start` with carry-in `cin`. -/
def rippleAddAux {α : Type} (B : SymBool α) (fx fy : Nat → α) :
    Nat → Nat → α → Option (List α × α)
  | 0, _, cin => some ([], cin)
  | k + 1, start, cin =>
    match fullAdder B (fx start) (fy start) cin with
    | none => none
    | some (s, cNext) =>
      match rippleAddAux B fx fy k (start + 1) cNext with
      | none => none
      | some (ss, cOut) => some (s :: ss, cOut)

theorem rippleAddAux_spec {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (c0 : Bool) (fx fy : Nat → α)
    (hfx : ∀ i, i < w → eval (fx i) = x.getLsbD i)
    (hfy : ∀ i, i < w → eval (fy i) = y.getLsbD i) :
    ∀ (k start : Nat) (cin : α) (ss : List α) (cOut : α),
      start + k ≤ w →
      eval cin = BitVec.carry start x y c0 →
      rippleAddAux B fx fy k start cin = some (ss, cOut) →
      ss.length = k ∧
      eval cOut = BitVec.carry (start + k) x y c0 ∧
      ∀ i, i < k → eval (getD ss i B.fFalse) =
        (x + y + BitVec.setWidth w (BitVec.ofBool c0)).getLsbD (start + i)
  | 0, start, cin, ss, cOut, _, hcin, h => by
    injection h with hp; injection hp with h1 h2; subst h1 h2
    refine ⟨rfl, ?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
    simp [hcin]
  | k + 1, start, cin, ss, cOut, hle, hcin, h => by
    unfold rippleAddAux at h
    revert h
    cases hfa : fullAdder B (fx start) (fy start) cin <;> simp only
    · intro h; cases h
    · rename_i p
      rcases p with ⟨s, cNext⟩
      cases hrest : rippleAddAux B fx fy k (start + 1) cNext <;> simp only
      · intro h; cases h
      · rename_i pr
        rcases pr with ⟨rest, cOut'⟩
        intro h; injection h with hp; injection hp with hss hc; subst hss hc
        have hstart : start < w := by omega
        obtain ⟨hs, hcNext⟩ := fullAdder_sound hB (fx start) (fy start) cin s cNext hfa
        rw [hfx start hstart, hfy start hstart, hcin] at hs hcNext
        rw [← BitVec.getLsbD_add_add_bool hstart x y c0] at hs
        rw [← BitVec.carry_succ start x y c0] at hcNext
        obtain ⟨hlen, hcOut, hbits⟩ :=
          rippleAddAux_spec hB x y c0 fx fy hfx hfy k (start + 1) cNext rest cOut' (by omega) hcNext hrest
        refine ⟨by simp [hlen], ?_, fun i hi => ?_⟩
        · have hadd : start + 1 + k = start + (k + 1) := by omega
          rw [← hadd, hcOut]
        · cases i with
          | zero =>
            simp only [Nat.add_zero, getD_zero]
            exact hs
          | succ j =>
            simp only [getD_succ]
            have hadd : start + 1 + j = start + (j + 1) := by omega
            rw [← hadd]
            exact hbits j (by omega)

theorem rippleAdd_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (c0 : Bool) (fx fy : Nat → α) (cin : α) (ss : List α) (cOut : α)
    (hfx : ∀ i, i < w → eval (fx i) = x.getLsbD i)
    (hfy : ∀ i, i < w → eval (fy i) = y.getLsbD i)
    (hcin : eval cin = c0)
    (h : rippleAddAux B fx fy w 0 cin = some (ss, cOut)) :
    (ss.length = w ∧ ∀ i : Nat, eval (getD ss i B.fFalse) =
      (x + y + BitVec.setWidth w (BitVec.ofBool c0)).getLsbD i) ∧
    eval cOut = BitVec.carry w x y c0 := by
  have hcin0 : eval cin = BitVec.carry 0 x y c0 := by rw [BitVec.carry_zero, hcin]
  obtain ⟨hlen, hcOut, hbits⟩ :=
    rippleAddAux_spec hB x y c0 fx fy hfx hfy w 0 cin ss cOut (by omega) hcin0 h
  simp only [Nat.zero_add] at hcOut hbits
  refine ⟨⟨hlen, fun i => ?_⟩, hcOut⟩
  by_cases hi : i < w
  · exact hbits i hi
  · rw [getD_of_ge ss i B.fFalse (by omega), hB.eval_false, BitVec.getLsbD_of_ge _ i (by omega)]

/-- Linear $O(w)$ ripple-carry addition directly over bit lists `as` and `bs`. -/
def rippleAddList {α : Type} (B : SymBool α) :
    Nat → List α → List α → α → Option (List α × α)
  | 0, _, _, cin => some ([], cin)
  | k + 1, as, bs, cin =>
    unconsD B.fFalse as (fun a as' =>
      unconsD B.fFalse bs (fun b bs' =>
        match fullAdder B a b cin with
        | none => none
        | some (s, cNext) =>
          match rippleAddList B k as' bs' cNext with
          | none => none
          | some (ss, cOut) => some (s :: ss, cOut)))

theorem rippleAddList_eq_aux {α : Type} (B : SymBool α) :
    ∀ (k : Nat) (as bs : List α) (start : Nat) (cin : α) (fx fy : Nat → α),
      (∀ i, fx (start + i) = getD as i B.fFalse) →
      (∀ i, fy (start + i) = getD bs i B.fFalse) →
      rippleAddList B k as bs cin = rippleAddAux B fx fy k start cin
  | 0, _, _, _, _, _, _, _, _ => rfl
  | k + 1, as, bs, start, cin, fx, fy, hfx, hfy => by
    unfold rippleAddList rippleAddAux
    rw [unconsD_eq, unconsD_eq]
    have ha0 : fx start = headD B.fFalse as := by
      have := hfx 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have hb0 : fy start = headD B.fFalse bs := by
      have := hfy 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    rw [ha0, hb0]
    cases fullAdder B (headD B.fFalse as) (headD B.fFalse bs) cin
    · rfl
    · rename_i p
      rcases p with ⟨s, cNext⟩
      dsimp only
      have ih := rippleAddList_eq_aux B k (tailD as) (tailD bs) (start + 1) cNext fx fy
        (fun i => shift_index fx as B.fFalse start i hfx)
        (fun i => shift_index fy bs B.fFalse start i hfy)
      rw [ih]

theorem rippleAddList_eq {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) (cin : α) :
    rippleAddList B w as bs cin =
      rippleAddAux B (fun i => getD as i B.fFalse) (fun i => getD bs i B.fFalse) w 0 cin :=
  rippleAddList_eq_aux B w as bs 0 cin _ _ (fun _ => by simp) (fun _ => by simp)

theorem rippleAddList_nil_left {α : Type} (B : SymBool α) (w : Nat) (bs : List α) (cin : α) :
    rippleAddList B w [] bs cin =
      rippleAddAux B (fun _ => B.fFalse) (fun i => getD bs i B.fFalse) w 0 cin :=
  rippleAddList_eq_aux B w [] bs 0 cin _ _ (fun _ => by simp [getD]) (fun _ => by simp)

/-- Bitwise equality check across `k` bit lanes starting at `start` with LSB-to-MSB accumulator `acc`. -/
def eqBitsAux {α : Type} (B : SymBool α) (fx fy : Nat → α) : Nat → Nat → α → Option α
  | 0, _, acc => some acc
  | k + 1, start, acc =>
    match B.fXor (fx start) (fy start) with
    | none => none
    | some diff =>
      match B.fNot diff with
      | none => none
      | some eqBit =>
        match B.fAnd acc eqBit with
        | none => none
        | some acc' => eqBitsAux B fx fy k (start + 1) acc'

theorem eqBitsAux_spec {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars) (fx fy : Nat → α) :
    ∀ (k start : Nat) (acc u : α),
      eqBitsAux B fx fy k start acc = some u →
      (eval u = true ↔ (eval acc = true ∧ ∀ i, i < k → eval (fx (start + i)) = eval (fy (start + i))))
  | 0, _, acc, u, h => by
    injection h with h'; subst h'
    simp
  | k + 1, start, acc, u, h => by
    unfold eqBitsAux at h
    revert h
    cases hdiff : B.fXor (fx start) (fy start) <;> simp only
    · intro h; cases h
    · rename_i diff
      cases heq : B.fNot diff <;> simp only
      · intro h; cases h
      · rename_i eqBit
        cases hand : B.fAnd acc eqBit <;> simp only
        · intro h; cases h
        · rename_i acc'
          intro hrest
          have ih := eqBitsAux_spec hB fx fy k (start + 1) acc' u hrest
          rw [ih, hB.eval_and _ _ _ hand, Bool.and_eq_true, hB.eval_not _ _ heq,
              hB.eval_xor _ _ _ hdiff]
          have hbit : ((!bne (eval (fx start)) (eval (fy start))) = true) ↔
              eval (fx start) = eval (fy start) := by
            cases eval (fx start) <;> cases eval (fy start) <;> decide
          rw [hbit]
          constructor
          · rintro ⟨⟨hacc, h0⟩, hsucc⟩
            refine ⟨hacc, fun i hi => ?_⟩
            cases i with
            | zero => simpa using h0
            | succ j =>
              have hadd : start + 1 + j = start + (j + 1) := by omega
              rw [← hadd]
              exact hsucc j (by omega)
          · rintro ⟨hacc, hall⟩
            refine ⟨⟨hacc, by simpa using hall 0 (by omega)⟩, fun j hj => ?_⟩
            have hadd : start + 1 + j = start + (j + 1) := by omega
            rw [hadd]
            exact hall (j + 1) (by omega)

theorem eqBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (fx fy : Nat → α) (u : α)
    (hfx : ∀ i, i < w → eval (fx i) = x.getLsbD i)
    (hfy : ∀ i, i < w → eval (fy i) = y.getLsbD i)
    (h : eqBitsAux B fx fy w 0 B.fTrue = some u) :
    eval u = (x == y) := by
  have hspec := eqBitsAux_spec hB fx fy w 0 B.fTrue u h
  apply Bool.eq_iff_iff.mpr
  simp only [hspec, hB.eval_true, true_and, beq_iff_eq]
  constructor
  · intro hall
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h1 := hall i hi
    simp only [Nat.zero_add] at h1
    rw [← hfx i hi, ← hfy i hi, h1]
  · intro heq i hi
    simp only [Nat.zero_add]
    rw [hfx i hi, hfy i hi, heq]

/-- Linear $O(w)$ tail-recursive bitwise equality check directly over bit lists `as` and `bs`. -/
def eqBitsListAux {α : Type} (B : SymBool α) : Nat → List α → List α → α → Option α
  | 0, _, _, acc => some acc
  | k + 1, as, bs, acc =>
    unconsD B.fFalse as (fun a as' =>
      unconsD B.fFalse bs (fun b bs' =>
        match B.fXor a b with
        | none => none
        | some diff =>
          match B.fNot diff with
          | none => none
          | some eqBit =>
            match B.fAnd acc eqBit with
            | none => none
            | some acc' => eqBitsListAux B k as' bs' acc'))

@[inline] def eqBitsList {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option α :=
  eqBitsListAux B w as bs B.fTrue

theorem eqBitsList_eq_aux {α : Type} (B : SymBool α) :
    ∀ (k : Nat) (as bs : List α) (start : Nat) (acc : α) (fx fy : Nat → α),
      (∀ i, fx (start + i) = getD as i B.fFalse) →
      (∀ i, fy (start + i) = getD bs i B.fFalse) →
      eqBitsListAux B k as bs acc = eqBitsAux B fx fy k start acc
  | 0, _, _, _, _, _, _, _, _ => rfl
  | k + 1, as, bs, start, acc, fx, fy, hfx, hfy => by
    unfold eqBitsListAux eqBitsAux
    rw [unconsD_eq, unconsD_eq]
    have ha0 : fx start = headD B.fFalse as := by
      have := hfx 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have hb0 : fy start = headD B.fFalse bs := by
      have := hfy 0; simp only [Nat.add_zero, getD_zero_eq_headD] at this; exact this
    have ih := fun acc' => eqBitsList_eq_aux B k (tailD as) (tailD bs) (start + 1) acc' fx fy
      (fun i => shift_index fx as B.fFalse start i hfx)
      (fun i => shift_index fy bs B.fFalse start i hfy)
    simp only [ha0, hb0, ih]

theorem eqBitsList_eq {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) :
    eqBitsList B w as bs =
      eqBitsAux B (fun i => getD as i B.fFalse) (fun i => getD bs i B.fFalse) w 0 B.fTrue :=
  eqBitsList_eq_aux B w as bs 0 B.fTrue _ _ (fun _ => by simp) (fun _ => by simp)

/-- Negate a bit list of width `w`. -/
def notBits {α : Type} (B : SymBool α) (w : Nat) (as : List α) : Option (List α) :=
  mapBits B.fNot B.fFalse w as

theorem notBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x : BitVec w) (as bs : List α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (h : notBits B w as = some bs) :
    bs.length = w ∧ ∀ i : Nat, eval (getD bs i B.fFalse) = (~~~x).getLsbD i := by
  unfold notBits at h
  rw [mapBits_eq] at h
  apply mkBits_valid hB w _ (~~~x) bs h
  intro i b hi hfb
  rw [hB.eval_not _ _ hfb, has i, BitVec.getLsbD_not, decide_eq_true hi, Bool.true_and]

private theorem setWidth_ofBool_false (w : Nat) :
    BitVec.setWidth w (BitVec.ofBool false) = 0#w := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem setWidth_ofBool_true (w : Nat) :
    BitVec.setWidth w (BitVec.ofBool true) = 1#w := by
  apply BitVec.eq_of_toNat_eq
  simp

private theorem add_not_add_one {w : Nat} (x y : BitVec w) :
    x + ~~~y + 1#w = x - y := by
  rw [BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]

private theorem zero_add_not_add_one {w : Nat} (x : BitVec w) :
    0#w + ~~~x + 1#w = -x := by
  rw [BitVec.zero_add, ← BitVec.neg_eq_not_add]

def addBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option (List α) :=
  match rippleAddList B w as bs B.fFalse with
  | some (ss, _) => some ss
  | none => none

theorem addBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs ss : List α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : addBits B w as bs = some ss) :
    ss.length = w ∧ ∀ i : Nat, eval (getD ss i B.fFalse) = (x + y).getLsbD i := by
  unfold addBits at h
  rw [rippleAddList_eq] at h
  revert h
  cases hra : rippleAddAux B (fun i => getD as i B.fFalse) (fun i => getD bs i B.fFalse) w 0 B.fFalse <;> simp only
  · intro h; cases h
  · rename_i p
    rcases p with ⟨ss', cOut⟩
    intro h; injection h with h'; subst h'
    obtain ⟨⟨hlen, hbits⟩, _⟩ :=
      rippleAdd_valid hB x y false _ _ B.fFalse ss' cOut (fun i _ => has i) (fun i _ => hbs i) hB.eval_false hra
    rw [setWidth_ofBool_false, BitVec.add_zero] at hbits
    exact ⟨hlen, hbits⟩

def subBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option (List α) :=
  match notBits B w bs with
  | none => none
  | some nbs =>
    match rippleAddList B w as nbs B.fTrue with
    | some (ss, _) => some ss
    | none => none

theorem subBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs ss : List α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : subBits B w as bs = some ss) :
    ss.length = w ∧ ∀ i : Nat, eval (getD ss i B.fFalse) = (x - y).getLsbD i := by
  unfold subBits at h
  revert h
  cases hnb : notBits B w bs <;> simp only
  · intro h; cases h
  · rename_i nbs
    rw [rippleAddList_eq]
    obtain ⟨_, hnbs⟩ := notBits_valid hB y bs nbs hbs hnb
    cases hra : rippleAddAux B (fun i => getD as i B.fFalse) (fun i => getD nbs i B.fFalse) w 0 B.fTrue <;> simp only
    · intro h; cases h
    · rename_i p
      rcases p with ⟨ss', cOut⟩
      intro h; injection h with h'; subst h'
      obtain ⟨⟨hlen, hbits⟩, _⟩ :=
        rippleAdd_valid hB x (~~~y) true _ _ B.fTrue ss' cOut (fun i _ => has i) (fun i _ => hnbs i) hB.eval_true hra
      rw [setWidth_ofBool_true, add_not_add_one] at hbits
      exact ⟨hlen, hbits⟩

def negBits {α : Type} (B : SymBool α) (w : Nat) (as : List α) : Option (List α) :=
  match notBits B w as with
  | none => none
  | some nas =>
    match rippleAddList B w [] nas B.fTrue with
    | some (ss, _) => some ss
    | none => none

theorem negBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x : BitVec w) (as ss : List α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (h : negBits B w as = some ss) :
    ss.length = w ∧ ∀ i : Nat, eval (getD ss i B.fFalse) = (-x).getLsbD i := by
  unfold negBits at h
  revert h
  cases hna : notBits B w as <;> simp only
  · intro h; cases h
  · rename_i nas
    rw [rippleAddList_nil_left]
    obtain ⟨_, hnas⟩ := notBits_valid hB x as nas has hna
    cases hra : rippleAddAux B (fun _ => B.fFalse) (fun i => getD nas i B.fFalse) w 0 B.fTrue <;> simp only
    · intro h; cases h
    · rename_i p
      rcases p with ⟨ss', cOut⟩
      intro h; injection h with h'; subst h'
      have hzero : ∀ i, i < w → eval B.fFalse = (0#w).getLsbD i := by
        intro i _; rw [hB.eval_false, BitVec.getLsbD_zero]
      obtain ⟨⟨hlen, hbits⟩, _⟩ :=
        rippleAdd_valid hB (0#w) (~~~x) true _ _ B.fTrue ss' cOut hzero (fun i _ => hnas i) hB.eval_true hra
      rw [setWidth_ofBool_true, zero_add_not_add_one] at hbits
      exact ⟨hlen, hbits⟩

/-- Symbolic `BitVec.ult x y` (`!(carry w x (~~~y) true)`). -/
def ultBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option α :=
  match notBits B w bs with
  | none => none
  | some nbs =>
    match rippleAddList B w as nbs B.fTrue with
    | some (_, cOut) => B.fNot cOut
    | none => none

theorem ultBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs : List α) (u : α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : ultBits B w as bs = some u) :
    eval u = BitVec.ult x y := by
  unfold ultBits at h
  revert h
  cases hnb : notBits B w bs <;> simp only
  · intro h; cases h
  · rename_i nbs
    rw [rippleAddList_eq]
    obtain ⟨_, hnbs⟩ := notBits_valid hB y bs nbs hbs hnb
    cases hra : rippleAddAux B (fun i => getD as i B.fFalse) (fun i => getD nbs i B.fFalse) w 0 B.fTrue <;> simp only
    · intro h; cases h
    · rename_i p
      rcases p with ⟨ss', cOut⟩
      intro hnot
      obtain ⟨_, hcOut⟩ :=
        rippleAdd_valid hB x (~~~y) true _ _ B.fTrue ss' cOut (fun i _ => has i) (fun i _ => hnbs i) hB.eval_true hra
      rw [hB.eval_not _ _ hnot, hcOut, BitVec.ult_eq_not_carry]

/-- Symbolic `BitVec.ule x y` (`!(BitVec.ult y x)`). -/
def uleBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option α :=
  match ultBits B w bs as with
  | some u => B.fNot u
  | none => none

theorem uleBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs : List α) (u : α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : uleBits B w as bs = some u) :
    eval u = BitVec.ule x y := by
  unfold uleBits at h
  revert h
  cases hult : ultBits B w bs as <;> simp only
  · intro h; cases h
  · rename_i u'
    intro hnot
    rw [hB.eval_not _ _ hnot, ultBits_valid hB y x bs as u' hbs has hult, BitVec.ule_eq_not_ult]

/-- Symbolic `BitVec.slt x y` (`(x.msb == y.msb).xor (carry w x (~~~y) true)`). -/
def sltBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option α :=
  match notBits B w bs with
  | none => none
  | some nbs =>
    match rippleAddList B w as nbs B.fTrue with
    | none => none
    | some (_, cOut) =>
      let msbA := getD as (w - 1) B.fFalse
      let msbB := getD bs (w - 1) B.fFalse
      match B.fXor msbA msbB with
      | none => none
      | some msbDiff =>
        match B.fNot msbDiff with
        | none => none
        | some msbEq => B.fXor msbEq cOut

private theorem bool_not_bne_eq_beq (a b : Bool) : (!bne a b) = (a == b) := by
  cases a <;> cases b <;> rfl

theorem sltBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs : List α) (u : α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : sltBits B w as bs = some u) :
    eval u = BitVec.slt x y := by
  unfold sltBits at h
  revert h
  cases hnb : notBits B w bs <;> simp only
  · intro h; cases h
  · rename_i nbs
    rw [rippleAddList_eq]
    obtain ⟨_, hnbs⟩ := notBits_valid hB y bs nbs hbs hnb
    cases hra : rippleAddAux B (fun i => getD as i B.fFalse) (fun i => getD nbs i B.fFalse) w 0 B.fTrue <;> simp only
    · intro h; cases h
    · rename_i p
      rcases p with ⟨ss', cOut⟩
      obtain ⟨_, hcOut⟩ :=
        rippleAdd_valid hB x (~~~y) true _ _ B.fTrue ss' cOut (fun i _ => has i) (fun i _ => hnbs i) hB.eval_true hra
      cases hdiff : B.fXor (getD as (w - 1) B.fFalse) (getD bs (w - 1) B.fFalse) <;> simp only
      · intro h; cases h
      · rename_i msbDiff
        cases heq : B.fNot msbDiff <;> simp only
        · intro h; cases h
        · rename_i msbEq
          intro hxor
          rw [hB.eval_xor _ _ _ hxor, hB.eval_not _ _ heq, hB.eval_xor _ _ _ hdiff,
              has (w - 1), hbs (w - 1), ← BitVec.msb_eq_getLsbD_last x, ← BitVec.msb_eq_getLsbD_last y,
              bool_not_bne_eq_beq, hcOut, BitVec.slt_eq_not_carry]

/-- Symbolic `BitVec.sle x y` (`!(BitVec.slt y x)`). -/
def sleBits {α : Type} (B : SymBool α) (w : Nat) (as bs : List α) : Option α :=
  match sltBits B w bs as with
  | some u => B.fNot u
  | none => none

theorem sleBits_valid {α : Type} {B : SymBool α} {eval : α → Bool} {benv : Nat → Bool} {numVars : Nat}
    (hB : LawfulSymBool B eval benv numVars)
    {w : Nat} (x y : BitVec w) (as bs : List α) (u : α)
    (has : ∀ i : Nat, eval (getD as i B.fFalse) = x.getLsbD i)
    (hbs : ∀ i : Nat, eval (getD bs i B.fFalse) = y.getLsbD i)
    (h : sleBits B w as bs = some u) :
    eval u = BitVec.sle x y := by
  unfold sleBits at h
  revert h
  cases hslt : sltBits B w bs as <;> simp only
  · intro h; cases h
  · rename_i u'
    intro hnot
    rw [hB.eval_not _ _ hnot, sltBits_valid hB y x bs as u' hbs has hslt, BitVec.sle_eq_not_slt]

/-! ## Reflected `BVExpr` and `BVGoal` grammar and generic bit-blaster -/

/-- Heterogeneous `BitVec` environment entry. -/
structure EnvEntry where
  w   : Nat
  val : BitVec w

/-- Variable environment for reflected `BitVec` and `Bool` atoms. -/
structure Env where
  vars  : List EnvEntry
  bvars : List Bool

def getEntry : List EnvEntry → Nat → EnvEntry
  | [], _ => ⟨0, 0#0⟩
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getEntry xs i

/-- Look up a `BitVec w` variable at `idx`. Uses `dite (e.w = w)` so `env.getBV w idx` is `rfl`
on well-typed variables, with `BitVec.setWidth w e.val` as a total fallback. -/
def Env.getBV (env : Env) (w : Nat) (idx : Nat) : BitVec w :=
  let e := getEntry env.vars idx
  if h : e.w = w then h ▸ e.val else BitVec.setWidth w e.val

def Env.getBool (env : Env) (idx : Nat) : Bool :=
  getD env.bvars idx false

theorem getLsbD_getBV (env : Env) (w idx i : Nat) (hi : i < w) :
    (env.getBV w idx).getLsbD i = (getEntry env.vars idx).val.getLsbD i := by
  unfold Env.getBV
  dsimp only
  split
  · rename_i h; cases h; rfl
  · simp [hi]

/-- Interleaved variable ID for a `Bool` variable `bidx` (even IDs `2 * bidx`). -/
@[inline] def boolVar (bidx : Nat) : Nat := 2 * bidx

/-- Interleaved LSB-to-MSB variable ID for bit `i` of `BitVec` variable `idx`
(odd IDs `2 * (i * stride + idx) + 1`).
Under this ordering, bit `0` of all variables comes first, then bit `1` of all variables, etc.,
giving ripple-carry adders and comparators $O(1)$ ROBDD cross-section width. -/
@[inline] def bitVar (stride idx i : Nat) : Nat := 2 * (i * stride + idx) + 1

/-- Bit-level assignment induced by `env : Env` and variable stride `stride : Nat`. -/
def envBits (env : Env) (stride : Nat) (v : Nat) : Bool :=
  if v % 2 == 0 then
    env.getBool (v / 2)
  else
    (getEntry env.vars ((v / 2) % stride)).val.getLsbD ((v / 2) / stride)

theorem envBits_boolVar (env : Env) (stride bidx : Nat) :
    envBits env stride (boolVar bidx) = env.getBool bidx := by
  have h1 : (2 * bidx) % 2 = 0 := by omega
  have h2 : (2 * bidx) / 2 = bidx := by omega
  simp [envBits, boolVar, h1, h2]

theorem envBits_bitVar (env : Env) (stride idx i : Nat) (h : idx < stride) :
    envBits env stride (bitVar stride idx i) = (getEntry env.vars idx).val.getLsbD i := by
  unfold envBits bitVar
  have hodd : (2 * (i * stride + idx) + 1) % 2 = 1 := by omega
  have hdiv2 : (2 * (i * stride + idx) + 1) / 2 = i * stride + idx := by omega
  have hmod : (i * stride + idx) % stride = idx := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  have hdiv : (i * stride + idx) / stride = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]
  rw [hodd, hdiv2, hmod, hdiv]
  rfl

/-- Semantic type of `BVExpr k`: `BitVec w` for `some w`, `Bool` for `none`. -/
@[reducible] def BVTy : Option Nat → Type
  | some w => BitVec w
  | none   => Bool

/-- Unified reflected expression grammar supporting both `BitVec w` (`BVExpr (some w)`)
and `Bool` (`BVExpr none`) subexpressions. -/
inductive BVExpr : Option Nat → Type where
  | var (w : Nat) (idx : Nat) : BVExpr (some w)
  | const (w : Nat) (val : Nat) : BVExpr (some w)
  | and {w : Nat} (a b : BVExpr (some w)) : BVExpr (some w)
  | or {w : Nat} (a b : BVExpr (some w)) : BVExpr (some w)
  | xor {w : Nat} (a b : BVExpr (some w)) : BVExpr (some w)
  | not {w : Nat} (a : BVExpr (some w)) : BVExpr (some w)
  | shl {w : Nat} (a : BVExpr (some w)) (k : Nat) : BVExpr (some w)
  | lshr {w : Nat} (a : BVExpr (some w)) (k : Nat) : BVExpr (some w)
  | ashr {w : Nat} (a : BVExpr (some w)) (k : Nat) : BVExpr (some w)
  | zext {w : Nat} (v : Nat) (a : BVExpr (some w)) : BVExpr (some v)
  | sext {w : Nat} (v : Nat) (a : BVExpr (some w)) : BVExpr (some v)
  | extract {w : Nat} (start len : Nat) (a : BVExpr (some w)) : BVExpr (some len)
  | append {wx wy : Nat} (a : BVExpr (some wx)) (b : BVExpr (some wy)) : BVExpr (some (wx + wy))
  | replicate {w : Nat} (n : Nat) (a : BVExpr (some w)) : BVExpr (some (w * n))
  | add {w : Nat} (a b : BVExpr (some w)) : BVExpr (some w)
  | sub {w : Nat} (a b : BVExpr (some w)) : BVExpr (some w)
  | neg {w : Nat} (a : BVExpr (some w)) : BVExpr (some w)
  | bvIte {w : Nat} (c : BVExpr none) (t e : BVExpr (some w)) : BVExpr (some w)
  | bconst (b : Bool) : BVExpr none
  | bvar (idx : Nat) : BVExpr none
  | getLsbD {w : Nat} (a : BVExpr (some w)) (i : Nat) : BVExpr none
  | msb {w : Nat} (a : BVExpr (some w)) : BVExpr none
  | beq {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | bne {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | ult {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | ule {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | slt {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | sle {w : Nat} (a b : BVExpr (some w)) : BVExpr none
  | bnot (p : BVExpr none) : BVExpr none
  | band (p q : BVExpr none) : BVExpr none
  | bor (p q : BVExpr none) : BVExpr none
  | bxor (p q : BVExpr none) : BVExpr none
  | bimp (p q : BVExpr none) : BVExpr none
  | biff (p q : BVExpr none) : BVExpr none
  | bite (c t e : BVExpr none) : BVExpr none

/-- Semantic denotation of `BVExpr k` in environment `env`. -/
def BVExpr.denote (env : Env) : {k : Option Nat} → BVExpr k → BVTy k
  | _, .var w idx => env.getBV w idx
  | _, .const w val => BitVec.ofNat w val
  | _, .and a b => a.denote env &&& b.denote env
  | _, .or a b => a.denote env ||| b.denote env
  | _, .xor a b => a.denote env ^^^ b.denote env
  | _, .not a => ~~~(a.denote env)
  | _, .shl a k => a.denote env <<< k
  | _, .lshr a k => a.denote env >>> k
  | _, .ashr a k => BitVec.sshiftRight (a.denote env) k
  | _, .zext v a => BitVec.zeroExtend v (a.denote env)
  | _, .sext v a => BitVec.signExtend v (a.denote env)
  | _, .extract start len a => BitVec.extractLsb' start len (a.denote env)
  | _, .append a b => a.denote env ++ b.denote env
  | _, .replicate n a => BitVec.replicate n (a.denote env)
  | _, .add a b => a.denote env + b.denote env
  | _, .sub a b => a.denote env - b.denote env
  | _, .neg a => -(a.denote env)
  | _, .bvIte c t e => if c.denote env = true then t.denote env else e.denote env
  | _, .bconst b => b
  | _, .bvar idx => env.getBool idx
  | _, .getLsbD a i => (a.denote env).getLsbD i
  | _, .msb a => (a.denote env).msb
  | _, .beq a b => (a.denote env == b.denote env)
  | _, .bne a b => (a.denote env != b.denote env)
  | _, .ult a b => BitVec.ult (a.denote env) (b.denote env)
  | _, .ule a b => BitVec.ule (a.denote env) (b.denote env)
  | _, .slt a b => BitVec.slt (a.denote env) (b.denote env)
  | _, .sle a b => BitVec.sle (a.denote env) (b.denote env)
  | _, .bnot p => !(p.denote env)
  | _, .band p q => (p.denote env && q.denote env)
  | _, .bor p q => (p.denote env || q.denote env)
  | _, .bxor p q => _root_.bne (p.denote env) (q.denote env)
  | _, .bimp p q => (!p.denote env || q.denote env)
  | _, .biff p q => (p.denote env == q.denote env)
  | _, .bite c t e => if c.denote env = true then t.denote env else e.denote env

/-- Symbolic result type for `compileBV`: `List α` of bits for `BitVec w`, `α` for `Bool`. -/
@[reducible] def SymRes (α : Type) : Option Nat → Type
  | some _ => List α
  | none   => α

/-- Generic bit-blasting compiler parameterized by any `SymBool α` backend. -/
def compileBV {α : Type} (B : SymBool α) (stride numVars : Nat) :
    {k : Option Nat} → BVExpr k → Option (SymRes α k)
  | _, .var w idx =>
    if Nat.blt idx stride then
      mkBits (fun i =>
        let v := bitVar stride idx i
        if Nat.blt v numVars then some (B.fVar v) else none) w 0
    else none
  | _, .const w val =>
    mkBits (fun i => some (cond (Nat.testBit val i) B.fTrue B.fFalse)) w 0
  | _, @BVExpr.and w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => zipBits B.fAnd B.fFalse w as bs
    | _, _ => none
  | _, @BVExpr.or w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => zipBits B.fOr B.fFalse w as bs
    | _, _ => none
  | _, @BVExpr.xor w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => zipBits B.fXor B.fFalse w as bs
    | _, _ => none
  | _, @BVExpr.not w a =>
    match compileBV B stride numVars a with
    | some as => notBits B w as
    | none => none
  | _, @BVExpr.shl w a k =>
    match compileBV B stride numVars a with
    | some as =>
      mkBits (fun i => some (if i < k then B.fFalse else getD as (i - k) B.fFalse)) w 0
    | none => none
  | _, @BVExpr.lshr w a k =>
    match compileBV B stride numVars a with
    | some as =>
      mkBits (fun i => some (getD as (k + i) B.fFalse)) w 0
    | none => none
  | _, @BVExpr.ashr w a k =>
    match compileBV B stride numVars a with
    | some as =>
      mkBits (fun i =>
        some (if k + i < w then getD as (k + i) B.fFalse else getD as (w - 1) B.fFalse)) w 0
    | none => none
  | _, @BVExpr.zext _ v a =>
    match compileBV B stride numVars a with
    | some as => mapBits some B.fFalse v as
    | none => none
  | _, @BVExpr.sext w v a =>
    match compileBV B stride numVars a with
    | some as =>
      mkBits (fun i =>
        some (if i < w then getD as i B.fFalse else getD as (w - 1) B.fFalse)) v 0
    | none => none
  | _, @BVExpr.extract _ start len a =>
    match compileBV B stride numVars a with
    | some as => mkBits (fun i => some (getD as (start + i) B.fFalse)) len 0
    | none => none
  | _, @BVExpr.append wx wy a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs =>
      mkBits (fun i =>
        some (if i < wy then getD bs i B.fFalse else getD as (i - wy) B.fFalse)) (wx + wy) 0
    | _, _ => none
  | _, @BVExpr.replicate w n a =>
    match compileBV B stride numVars a with
    | some as =>
      mkBits (fun i => some (getD as (i % w) B.fFalse)) (w * n) 0
    | none => none
  | _, @BVExpr.add w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => addBits B w as bs
    | _, _ => none
  | _, @BVExpr.sub w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => subBits B w as bs
    | _, _ => none
  | _, @BVExpr.neg w a =>
    match compileBV B stride numVars a with
    | some as => negBits B w as
    | none => none
  | _, @BVExpr.bvIte w c t e =>
    match compileBV B stride numVars c, compileBV B stride numVars t, compileBV B stride numVars e with
    | some uc, some ts, some es =>
      zipBits (symIte B uc) B.fFalse w ts es
    | _, _, _ => none
  | _, .bconst b => some (cond b B.fTrue B.fFalse)
  | _, .bvar idx =>
    let v := boolVar idx
    if Nat.blt v numVars then some (B.fVar v) else none
  | _, .getLsbD a i =>
    match compileBV B stride numVars a with
    | some as => some (getD as i B.fFalse)
    | none => none
  | _, @BVExpr.msb w a =>
    match compileBV B stride numVars a with
    | some as => some (getD as (w - 1) B.fFalse)
    | none => none
  | _, @BVExpr.beq w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => eqBitsList B w as bs
    | _, _ => none
  | _, @BVExpr.bne w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs =>
      match eqBitsList B w as bs with
      | some u => B.fNot u
      | none => none
    | _, _ => none
  | _, @BVExpr.ult w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => ultBits B w as bs
    | _, _ => none
  | _, @BVExpr.ule w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => uleBits B w as bs
    | _, _ => none
  | _, @BVExpr.slt w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => sltBits B w as bs
    | _, _ => none
  | _, @BVExpr.sle w a b =>
    match compileBV B stride numVars a, compileBV B stride numVars b with
    | some as, some bs => sleBits B w as bs
    | _, _ => none
  | _, .bnot p =>
    match compileBV B stride numVars p with
    | some up => B.fNot up
    | none => none
  | _, .band p q =>
    match compileBV B stride numVars p, compileBV B stride numVars q with
    | some up, some uq => B.fAnd up uq
    | _, _ => none
  | _, .bor p q =>
    match compileBV B stride numVars p, compileBV B stride numVars q with
    | some up, some uq => B.fOr up uq
    | _, _ => none
  | _, .bxor p q =>
    match compileBV B stride numVars p, compileBV B stride numVars q with
    | some up, some uq => B.fXor up uq
    | _, _ => none
  | _, .bimp p q =>
    match compileBV B stride numVars p, compileBV B stride numVars q with
    | some up, some uq =>
      match B.fNot up with
      | some nup => B.fOr nup uq
      | none => none
    | _, _ => none
  | _, .biff p q =>
    match compileBV B stride numVars p, compileBV B stride numVars q with
    | some up, some uq =>
      match B.fXor up uq with
      | some diff => B.fNot diff
      | none => none
    | _, _ => none
  | _, .bite c t e =>
    match compileBV B stride numVars c, compileBV B stride numVars t, compileBV B stride numVars e with
    | some uc, some ut, some ue => symIte B uc ut ue
    | _, _, _ => none

/-- Correctness invariant for `compileBV`: for `e : BVExpr (some w)`, `bs` has length `w` and bit
`i` evaluates to `(e.denote env).getLsbD i`; for `p : BVExpr none`, `u` evaluates to
`p.denote env`. -/
@[reducible] def ValidRes {α : Type} (B : SymBool α) (eval : α → Bool) (env : Env) :
    {k : Option Nat} → BVExpr k → SymRes α k → Prop
  | some w => fun e bs =>
    bs.length = w ∧ ∀ i : Nat, eval (getD bs i B.fFalse) = (e.denote env).getLsbD i
  | none => fun p u =>
    eval u = p.denote env

theorem compileBV_sound {α : Type} {B : SymBool α} {eval : α → Bool} {env : Env}
    {stride numVars : Nat}
    (hB : LawfulSymBool B eval (envBits env stride) numVars) :
    ∀ {k : Option Nat} (e : BVExpr k) (res : SymRes α k),
      compileBV B stride numVars e = some res →
      ValidRes B eval env e res := by
  intro k e
  induction e with
  | var w idx =>
    intro bs h
    unfold compileBV at h
    cases hidx : Nat.blt idx stride
    · rw [hidx] at h; cases h
    · rw [hidx] at h; dsimp only [ite_true] at h
      have hidx' : idx < stride := Nat.blt_eq.mp hidx
      apply mkBits_valid hB w _ (env.getBV w idx) bs h
      intro i b hi hfb
      cases hv : Nat.blt (bitVar stride idx i) numVars
      · rw [hv] at hfb; cases hfb
      · rw [hv] at hfb; injection hfb with hb; subst hb
        have hv' : bitVar stride idx i < numVars := Nat.blt_eq.mp hv
        rw [hB.eval_var _ hv', envBits_bitVar env stride idx i hidx', getLsbD_getBV env w idx i hi]
  | const w val =>
    intro bs h
    unfold compileBV at h
    apply mkBits_valid hB w _ (BitVec.ofNat w val) bs h
    intro i b hi hfb
    injection hfb with hb; subst hb
    rw [BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and]
    cases Nat.testBit val i <;> simp [hB.eval_true, hB.eval_false]
  | @and w a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    rw [zipBits_eq]
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    apply mkBits_valid hB w _ (a.denote env &&& b.denote env) cs h
    intro i u _ hu
    rw [hB.eval_and _ _ _ hu, has i, hbs i, BitVec.getLsbD_and]
  | @or w a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    rw [zipBits_eq]
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    apply mkBits_valid hB w _ (a.denote env ||| b.denote env) cs h
    intro i u _ hu
    rw [hB.eval_or _ _ _ hu, has i, hbs i, BitVec.getLsbD_or]
  | @xor w a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    rw [zipBits_eq]
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    apply mkBits_valid hB w _ (a.denote env ^^^ b.denote env) cs h
    intro i u _ hu
    rw [hB.eval_xor _ _ _ hu, has i, hbs i, BitVec.getLsbD_xor]
  | @not w a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      exact notBits_valid hB (a.denote env) as cs has h
  | @shl w a k iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB w _ (a.denote env <<< k) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      rw [BitVec.getLsbD_shiftLeft, decide_eq_true hi, Bool.true_and]
      by_cases hik : i < k
      · simp [hik, hB.eval_false]
      · simp [hik, has (i - k)]
  | @lshr w a k iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB w _ (a.denote env >>> k) cs h
      intro i u _ hu
      injection hu with hu'; subst hu'
      rw [has (k + i), BitVec.getLsbD_ushiftRight]
  | @ashr w a k iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB w _ (BitVec.sshiftRight (a.denote env) k) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      have hge : ¬ (w ≤ i) := by omega
      rw [BitVec.getLsbD_sshiftRight, decide_eq_false hge, Bool.not_false, Bool.true_and,
          BitVec.msb_eq_getLsbD_last]
      by_cases hki : k + i < w
      · simp [hki, has (k + i)]
      · simp [hki, has (w - 1)]
  | @zext w v a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      rw [mapBits_eq]
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB v _ (BitVec.zeroExtend v (a.denote env)) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      rw [has i, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  | @sext w v a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB v _ (BitVec.signExtend v (a.denote env)) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      rw [BitVec.getLsbD_signExtend, decide_eq_true hi, Bool.true_and, BitVec.msb_eq_getLsbD_last]
      by_cases hiw : i < w
      · simp [hiw, has i]
      · simp [hiw, has (w - 1)]
  | @extract w start len a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB len _ (BitVec.extractLsb' start len (a.denote env)) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      rw [has (start + i), BitVec.getLsbD_extractLsb', decide_eq_true hi, Bool.true_and]
  | @append wx wy a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    apply mkBits_valid hB (wx + wy) _ (a.denote env ++ b.denote env) cs h
    intro i u _ hu
    injection hu with hu'; subst hu'
    rw [BitVec.getLsbD_append]
    by_cases hiy : i < wy
    · simp [hiy, hbs i]
    · simp [hiy, has (i - wy)]
  | @replicate w n a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      apply mkBits_valid hB (w * n) _ (BitVec.replicate n (a.denote env)) cs h
      intro i u hi hu
      injection hu with hu'; subst hu'
      rw [has (i % w), BitVec.getLsbD_replicate, decide_eq_true hi, Bool.true_and]
  | @add w a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact addBits_valid hB (a.denote env) (b.denote env) as bs cs has hbs h
  | @sub w a b iha ihb =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact subBits_valid hB (a.denote env) (b.denote env) as bs cs has hbs h
  | @neg w a iha =>
    intro cs h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h
      obtain ⟨_, has⟩ := iha as ha
      exact negBits_valid hB (a.denote env) as cs has h
  | @bvIte w c t e ihc iht ihe =>
    intro cs h
    unfold compileBV at h
    revert h
    cases hc : compileBV B stride numVars c <;>
      cases ht : compileBV B stride numVars t <;>
      cases he : compileBV B stride numVars e <;> simp only
    any_goals (intro h; cases h)
    rename_i uc ts es
    rw [zipBits_eq]
    intro h
    have huc := ihc uc hc
    obtain ⟨_, hts⟩ := iht ts ht
    obtain ⟨_, hes⟩ := ihe es he
    apply mkBits_valid hB w _ (if c.denote env = true then t.denote env else e.denote env) cs h
    intro i u _ hu
    rw [symIte_sound hB uc (getD ts i B.fFalse) (getD es i B.fFalse) u hu, huc, hts i, hes i]
    cases c.denote env <;> rfl
  | bconst b =>
    intro u h
    injection h with hu; subst hu
    change eval (cond b B.fTrue B.fFalse) = b
    cases b <;> simp [hB.eval_true, hB.eval_false]
  | bvar idx =>
    intro u h
    unfold compileBV at h
    dsimp only at h
    cases hv : Nat.blt (boolVar idx) numVars
    · rw [hv] at h; cases h
    · rw [hv] at h; injection h with hu; subst hu
      have hv' : boolVar idx < numVars := Nat.blt_eq.mp hv
      change eval (B.fVar (boolVar idx)) = env.getBool idx
      rw [hB.eval_var _ hv', envBits_boolVar]
  | getLsbD a i iha =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h; injection h with hu; subst hu
      obtain ⟨_, has⟩ := iha as ha
      exact has i
  | @msb w a iha =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> simp only
    · intro h; cases h
    · rename_i as
      intro h; injection h with hu; subst hu
      obtain ⟨_, has⟩ := iha as ha
      dsimp only [ValidRes]
      rw [has (w - 1), ← BitVec.msb_eq_getLsbD_last]
      rfl
  | @beq w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    rw [eqBitsList_eq]
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact eqBits_valid hB (a.denote env) (b.denote env) _ _ u (fun i _ => has i) (fun i _ => hbs i) h
  | @bne w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    rw [eqBitsList_eq]
    cases heq : eqBitsAux B (fun i => getD as i B.fFalse) (fun i => getD bs i B.fFalse) w 0 B.fTrue <;> simp only
    · intro h; cases h
    · rename_i ueq
      intro hnot
      obtain ⟨_, has⟩ := iha as ha
      obtain ⟨_, hbs⟩ := ihb bs hb
      dsimp only [ValidRes]
      rw [hB.eval_not _ _ hnot,
          eqBits_valid hB (a.denote env) (b.denote env) _ _ ueq (fun i _ => has i) (fun i _ => hbs i) heq]
      rfl
  | @ult w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact ultBits_valid hB (a.denote env) (b.denote env) as bs u has hbs h
  | @ule w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact uleBits_valid hB (a.denote env) (b.denote env) as bs u has hbs h
  | @slt w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact sltBits_valid hB (a.denote env) (b.denote env) as bs u has hbs h
  | @sle w a b iha ihb =>
    intro u h
    unfold compileBV at h
    revert h
    cases ha : compileBV B stride numVars a <;> cases hb : compileBV B stride numVars b <;> simp only
    any_goals (intro h; cases h)
    rename_i as bs
    intro h
    obtain ⟨_, has⟩ := iha as ha
    obtain ⟨_, hbs⟩ := ihb bs hb
    exact sleBits_valid hB (a.denote env) (b.denote env) as bs u has hbs h
  | bnot p ihp =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> simp only
    · intro h; cases h
    · rename_i up
      intro hnot
      have ih1 : eval up = p.denote env := ihp up hp
      dsimp only [ValidRes]
      rw [hB.eval_not _ _ hnot, ih1]
      rfl
  | band p q ihp ihq =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> cases hq : compileBV B stride numVars q <;> simp only
    any_goals (intro h; cases h)
    rename_i up uq
    intro hand
    have ih1 : eval up = p.denote env := ihp up hp
    have ih2 : eval uq = q.denote env := ihq uq hq
    dsimp only [ValidRes]
    rw [hB.eval_and _ _ _ hand, ih1, ih2]
    rfl
  | bor p q ihp ihq =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> cases hq : compileBV B stride numVars q <;> simp only
    any_goals (intro h; cases h)
    rename_i up uq
    intro hor
    have ih1 : eval up = p.denote env := ihp up hp
    have ih2 : eval uq = q.denote env := ihq uq hq
    dsimp only [ValidRes]
    rw [hB.eval_or _ _ _ hor, ih1, ih2]
    rfl
  | bxor p q ihp ihq =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> cases hq : compileBV B stride numVars q <;> simp only
    any_goals (intro h; cases h)
    rename_i up uq
    intro hxor
    have ih1 : eval up = p.denote env := ihp up hp
    have ih2 : eval uq = q.denote env := ihq uq hq
    dsimp only [ValidRes]
    rw [hB.eval_xor _ _ _ hxor, ih1, ih2]
    rfl
  | bimp p q ihp ihq =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> cases hq : compileBV B stride numVars q <;> simp only
    any_goals (intro h; cases h)
    rename_i up uq
    cases hn : B.fNot up <;> simp only
    · intro h; cases h
    · rename_i nup
      intro hor
      have ih1 : eval up = p.denote env := ihp up hp
      have ih2 : eval uq = q.denote env := ihq uq hq
      dsimp only [ValidRes]
      rw [hB.eval_or _ _ _ hor, hB.eval_not _ _ hn, ih1, ih2]
      rfl
  | biff p q ihp ihq =>
    intro u h
    unfold compileBV at h
    revert h
    cases hp : compileBV B stride numVars p <;> cases hq : compileBV B stride numVars q <;> simp only
    any_goals (intro h; cases h)
    rename_i up uq
    cases hx : B.fXor up uq <;> simp only
    · intro h; cases h
    · rename_i diff
      intro hnot
      have ih1 : eval up = p.denote env := ihp up hp
      have ih2 : eval uq = q.denote env := ihq uq hq
      dsimp only [ValidRes]
      rw [hB.eval_not _ _ hnot, hB.eval_xor _ _ _ hx, ih1, ih2, bool_not_bne_eq_beq]
      rfl
  | bite c t e ihc iht ihe =>
    intro u h
    unfold compileBV at h
    revert h
    cases hc : compileBV B stride numVars c <;>
      cases ht : compileBV B stride numVars t <;>
      cases he : compileBV B stride numVars e <;> simp only
    any_goals (intro h; cases h)
    rename_i uc ut ue
    intro hite
    have ih1 : eval uc = c.denote env := ihc uc hc
    have ih2 : eval ut = t.denote env := iht ut ht
    have ih3 : eval ue = e.denote env := ihe ue he
    dsimp only [ValidRes, BVExpr.denote]
    rw [symIte_sound hB uc ut ue u hite, ih1, ih2, ih3]

/-- Reflected `Prop`-level goal syntax (`Spec`) whose `denote` matches user goals definitionally (`rfl`). -/
inductive BVGoal where
  | eq {w : Nat} (a b : BVExpr (some w))
  | ne {w : Nat} (a b : BVExpr (some w))
  | lt {w : Nat} (a b : BVExpr (some w))
  | le {w : Nat} (a b : BVExpr (some w))
  | boolEq (a b : BVExpr none)
  | boolNe (a b : BVExpr none)
  | top
  | bot
  | not (p : BVGoal)
  | and (p q : BVGoal)
  | or (p q : BVGoal)
  | imp (p q : BVGoal)
  | iff (p q : BVGoal)

/-- Direct `Prop` denotation of `BVGoal` (definitionally equal to the user's Lean goal). -/
def BVGoal.denote (env : Env) : BVGoal → Prop
  | .eq a b => a.denote env = b.denote env
  | .ne a b => a.denote env ≠ b.denote env
  | .lt a b => a.denote env < b.denote env
  | .le a b => a.denote env ≤ b.denote env
  | .boolEq a b => a.denote env = b.denote env
  | .boolNe a b => a.denote env ≠ b.denote env
  | .top => True
  | .bot => False
  | .not p => ¬(p.denote env)
  | .and p q => p.denote env ∧ q.denote env
  | .or p q => p.denote env ∨ q.denote env
  | .imp p q => p.denote env → q.denote env
  | .iff p q => (p.denote env ↔ q.denote env)

/-- Translate a `BVGoal` into a boolean `BVExpr none`. -/
def BVGoal.toBExpr : BVGoal → BVExpr none
  | .eq a b => .beq a b
  | .ne a b => .bnot (.beq a b)
  | .lt a b => .ult a b
  | .le a b => .ule a b
  | .boolEq a b => .biff a b
  | .boolNe a b => .bxor a b
  | .top => .bconst true
  | .bot => .bconst false
  | .not p => .bnot p.toBExpr
  | .and p q => .band p.toBExpr q.toBExpr
  | .or p q => .bor p.toBExpr q.toBExpr
  | .imp p q => .bimp p.toBExpr q.toBExpr
  | .iff p q => .biff p.toBExpr q.toBExpr

theorem BVGoal.denote_iff (env : Env) :
    ∀ (g : BVGoal), (g.toBExpr.denote env = true) ↔ g.denote env
  | .eq a b => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
  | .ne a b => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
  | .lt a b => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote, BitVec.ult_iff_lt]
  | .le a b => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote, BitVec.ule_iff_le]
  | .boolEq a b => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
  | .boolNe a b => by
    simp only [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
    cases a.denote env <;> cases b.denote env <;> decide
  | .top => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
  | .bot => by simp [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote]
  | .not p => by
    have ih := BVGoal.denote_iff env p
    simp only [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote, Bool.not_eq_true',
      ← Bool.not_eq_true, ih]
  | .and p q => by
    rw [show (BVGoal.and p q).toBExpr.denote env = (p.toBExpr.denote env && q.toBExpr.denote env) from rfl,
        Bool.and_eq_true, BVGoal.denote_iff env p, BVGoal.denote_iff env q]
    rfl
  | .or p q => by
    rw [show (BVGoal.or p q).toBExpr.denote env = (p.toBExpr.denote env || q.toBExpr.denote env) from rfl,
        Bool.or_eq_true, BVGoal.denote_iff env p, BVGoal.denote_iff env q]
    rfl
  | .imp p q => by
    have ihp := BVGoal.denote_iff env p
    have ihq := BVGoal.denote_iff env q
    simp only [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote, ← ihp, ← ihq]
    cases p.toBExpr.denote env <;> cases q.toBExpr.denote env <;> decide
  | .iff p q => by
    have ihp := BVGoal.denote_iff env p
    have ihq := BVGoal.denote_iff env q
    simp only [BVGoal.toBExpr, BVExpr.denote, BVGoal.denote, ← ihp, ← ihq]
    cases p.toBExpr.denote env <;> cases q.toBExpr.denote env <;> decide

/-! ## Per-lane structural ROBDD normalizer (`SBDD` and `bv_slice`) -/

/-- Basic Boolean gate operations used by `SBDD` and `BDDNode`. -/
inductive GateOp where
  | not
  | and
  | or
  | xor
  deriving Repr, Inhabited, BEq, DecidableEq

instance : LawfulBEq GateOp where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | cases h

@[inline] def GateOp.eval (op : GateOp) (a b : Bool) : Bool :=
  match op with
  | .not => !a
  | .and => a && b
  | .or  => a || b
  | .xor => bne a b

/-- Structural ROBDD tree for per-lane bit-slice normalization (`bv_slice`). -/
inductive SBDD where
  | leaf (b : Bool)
  | node (v : Nat) (lo hi : SBDD)
  deriving Repr, Inhabited

def SBDD.eval (benv : Nat → Bool) : SBDD → Bool
  | .leaf b => b
  | .node v lo hi => if benv v then SBDD.eval benv hi else SBDD.eval benv lo

def sbddEq : SBDD → SBDD → Bool
  | .leaf b1, .leaf b2 => b1 == b2
  | .node v1 l1 r1, .node v2 l2 r2 =>
    Nat.beq v1 v2 && sbddEq l1 l2 && sbddEq r1 r2
  | _, _ => false

theorem sbddEq_eq_true : ∀ (a b : SBDD), sbddEq a b = true → a = b
  | .leaf b1, .leaf b2, h => by
    simp only [sbddEq, beq_iff_eq] at h; subst h; rfl
  | .node v1 l1 r1, .node v2 l2 r2, h => by
    simp only [sbddEq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1.1, sbddEq_eq_true l1 l2 h.1.2, sbddEq_eq_true r1 r2 h.2]
  | .leaf _, .node _ _ _, h => by cases h
  | .node _ _ _, .leaf _, h => by cases h

/-- ROBDD reduction constructor: collapses `.node v lo hi` to `lo` when `lo == hi`. -/
@[inline] def mkSBDD (v : Nat) (lo hi : SBDD) : SBDD :=
  if sbddEq lo hi then lo else .node v lo hi

theorem eval_mkSBDD (benv : Nat → Bool) (v : Nat) (lo hi : SBDD) :
    SBDD.eval benv (mkSBDD v lo hi) =
      (if benv v then SBDD.eval benv hi else SBDD.eval benv lo) := by
  unfold mkSBDD
  cases h : sbddEq lo hi
  · rfl
  · rw [sbddEq_eq_true lo hi h]
    cases benv v <;> rfl

/-- Negate an `SBDD` in linear time. -/
def sbddNot : SBDD → SBDD
  | .leaf b => .leaf (!b)
  | .node v lo hi => .node v (sbddNot lo) (sbddNot hi)

theorem eval_sbddNot (benv : Nat → Bool) : ∀ (a : SBDD),
    SBDD.eval benv (sbddNot a) = !(SBDD.eval benv a)
  | .leaf _ => rfl
  | .node v lo hi => by
    simp only [sbddNot, SBDD.eval, eval_sbddNot benv lo, eval_sbddNot benv hi]
    cases benv v <;> rfl

/-- Terminal and idempotence base cases for `SBDD` gate application. -/
def sbddBaseOp (op : GateOp) (a b : SBDD) : Option SBDD :=
  match op with
  | .not => some (sbddNot a)
  | .and =>
    match a, b with
    | .leaf false, _ => some (.leaf false)
    | _, .leaf false => some (.leaf false)
    | .leaf true, _ => some b
    | _, .leaf true => some a
    | _, _ => if sbddEq a b then some a else none
  | .or =>
    match a, b with
    | .leaf true, _ => some (.leaf true)
    | _, .leaf true => some (.leaf true)
    | .leaf false, _ => some b
    | _, .leaf false => some a
    | _, _ => if sbddEq a b then some a else none
  | .xor =>
    match a, b with
    | .leaf false, _ => some b
    | _, .leaf false => some a
    | .leaf true, _ => some (sbddNot b)
    | _, .leaf true => some (sbddNot a)
    | _, _ => if sbddEq a b then some (.leaf false) else none

theorem sbddBaseOp_sound (benv : Nat → Bool) (op : GateOp) (a b res : SBDD)
    (h : sbddBaseOp op a b = some res) :
    SBDD.eval benv res = op.eval (SBDD.eval benv a) (SBDD.eval benv b) := by
  cases op <;> unfold sbddBaseOp at h
  · injection h with h'; subst h'
    exact eval_sbddNot benv a
  · cases a with
    | leaf ba =>
      cases ba
      · injection h with h'; subst h'; rfl
      · cases b with
        | leaf bb => cases bb <;> (injection h with h'; subst h'; rfl)
        | node vb lb rb => injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
    | node va la ra =>
      cases b with
      | leaf bb =>
        cases bb
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
      | node vb lb rb =>
        dsimp only at h
        cases heq : sbddEq (.node va la ra) (.node vb lb rb)
        · rw [heq] at h; cases h
        · rw [heq] at h; injection h with h'; subst h'
          rw [sbddEq_eq_true _ _ heq]; simp [GateOp.eval]
  · cases a with
    | leaf ba =>
      cases ba
      · cases b with
        | leaf bb => cases bb <;> (injection h with h'; subst h'; rfl)
        | node vb lb rb => injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
      · injection h with h'; subst h'; rfl
    | node va la ra =>
      cases b with
      | leaf bb =>
        cases bb
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
      | node vb lb rb =>
        dsimp only at h
        cases heq : sbddEq (.node va la ra) (.node vb lb rb)
        · rw [heq] at h; cases h
        · rw [heq] at h; injection h with h'; subst h'
          rw [sbddEq_eq_true _ _ heq]; simp [GateOp.eval]
  · cases a with
    | leaf ba =>
      cases ba
      · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
      · cases b with
        | leaf bb => cases bb <;> (injection h with h'; subst h'; rfl)
        | node vb lb rb => injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval, eval_sbddNot]
    | node va la ra =>
      cases b with
      | leaf bb =>
        cases bb
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval]
        · injection h with h'; subst h'; simp [GateOp.eval, SBDD.eval, eval_sbddNot]
      | node vb lb rb =>
        dsimp only at h
        cases heq : sbddEq (.node va la ra) (.node vb lb rb)
        · rw [heq] at h; cases h
        · rw [heq] at h; injection h with h'; subst h'
          rw [sbddEq_eq_true _ _ heq]; simp [GateOp.eval, SBDD.eval]

/-- Fuel-bounded structural ROBDD binary operator application. -/
def sbddApply (op : GateOp) : Nat → SBDD → SBDD → Option SBDD
  | 0, _, _ => none
  | fuel + 1, a, b =>
    match sbddBaseOp op a b with
    | some res => some res
    | none =>
      match a, b with
      | .node va loa hia, .node vb lob hib =>
        if Nat.beq va vb then
          match sbddApply op fuel loa lob, sbddApply op fuel hia hib with
          | some lo, some hi => some (mkSBDD va lo hi)
          | _, _ => none
        else if Nat.blt vb va then
          match sbddApply op fuel loa (.node vb lob hib), sbddApply op fuel hia (.node vb lob hib) with
          | some lo, some hi => some (mkSBDD va lo hi)
          | _, _ => none
        else
          match sbddApply op fuel (.node va loa hia) lob, sbddApply op fuel (.node va loa hia) hib with
          | some lo, some hi => some (mkSBDD vb lo hi)
          | _, _ => none
      | _, _ => none

theorem sbddApply_sound (benv : Nat → Bool) (op : GateOp) :
    ∀ (fuel : Nat) (a b res : SBDD),
      sbddApply op fuel a b = some res →
      SBDD.eval benv res = op.eval (SBDD.eval benv a) (SBDD.eval benv b)
  | 0, _, _, _, h => by cases h
  | fuel + 1, a, b, res, h => by
    unfold sbddApply at h
    cases hbase : sbddBaseOp op a b
    · rw [hbase] at h; dsimp only at h
      cases a with
      | leaf _ => cases h
      | node va loa hia =>
        cases b with
        | leaf _ => cases h
        | node vb lob hib =>
          dsimp only at h
          cases heq : Nat.beq va vb
          · cases hlt : Nat.blt vb va
            · cases hlo : sbddApply op fuel (.node va loa hia) lob
              · rw [heq, hlt, hlo] at h; cases h
              · rename_i lo
                cases hhi : sbddApply op fuel (.node va loa hia) hib
                · rw [heq, hlt, hlo, hhi] at h; cases h
                · rename_i hi
                  rw [heq, hlt, hlo, hhi] at h
                  injection h with h'; subst h'
                  rw [eval_mkSBDD,
                      sbddApply_sound benv op fuel (.node va loa hia) lob lo hlo,
                      sbddApply_sound benv op fuel (.node va loa hia) hib hi hhi]
                  simp only [SBDD.eval]
                  cases benv vb <;> rfl
            · cases hlo : sbddApply op fuel loa (.node vb lob hib)
              · rw [heq, hlt, hlo] at h; cases h
              · rename_i lo
                cases hhi : sbddApply op fuel hia (.node vb lob hib)
                · rw [heq, hlt, hlo, hhi] at h; cases h
                · rename_i hi
                  rw [heq, hlt, hlo, hhi] at h
                  injection h with h'; subst h'
                  rw [eval_mkSBDD,
                      sbddApply_sound benv op fuel loa (.node vb lob hib) lo hlo,
                      sbddApply_sound benv op fuel hia (.node vb lob hib) hi hhi]
                  simp only [SBDD.eval]
                  cases benv va <;> rfl
          · have hv : va = vb := Nat.beq_eq.mp heq
            subst hv
            cases hlo : sbddApply op fuel loa lob
            · rw [heq, hlo] at h; cases h
            · rename_i lo
              cases hhi : sbddApply op fuel hia hib
              · rw [heq, hlo, hhi] at h; cases h
              · rename_i hi
                rw [heq, hlo, hhi] at h
                injection h with h'; subst h'
                rw [eval_mkSBDD,
                    sbddApply_sound benv op fuel loa lob lo hlo,
                    sbddApply_sound benv op fuel hia hib hi hhi]
                simp only [SBDD.eval]
                cases benv va <;> rfl
    · rename_i res'
      rw [hbase] at h; injection h with h'; subst h'
      exact sbddBaseOp_sound benv op a b res' hbase

def sliceBackend (fuel : Nat) : SymBool SBDD where
  fFalse := .leaf false
  fTrue  := .leaf true
  fVar v := .node v (.leaf false) (.leaf true)
  fNot a := some (sbddNot a)
  fAnd a b := sbddApply .and fuel a b
  fOr  a b := sbddApply .or fuel a b
  fXor a b := sbddApply .xor fuel a b

theorem sliceBackend_lawful (benv : Nat → Bool) (fuel numVars : Nat) :
    LawfulSymBool (sliceBackend fuel) (SBDD.eval benv) benv numVars where
  eval_false := rfl
  eval_true  := rfl
  eval_var v _ := by simp [sliceBackend, SBDD.eval]
  eval_not a u h := by
    injection h with h'; subst h'
    exact eval_sbddNot benv a
  eval_and a b u h := sbddApply_sound benv .and fuel a b u h
  eval_or  a b u h := sbddApply_sound benv .or fuel a b u h
  eval_xor a b u h := sbddApply_sound benv .xor fuel a b u h

/-- Kernel checker for `bv_slice`: evaluates `g.toBExpr` using per-lane `SBDD`s and checks
whether the result reduces to `.leaf true`. -/
def checkSlice (fuel stride numVars : Nat) (g : BVGoal) : Bool :=
  match compileBV (sliceBackend fuel) stride numVars g.toBExpr with
  | some (.leaf true) => true
  | _ => false

/-- Soundness theorem for `bv_slice`, discharged in the kernel via `Eq.refl true`. -/
theorem prove_of_checkSlice (env : Env) (fuel stride numVars : Nat) (g : BVGoal)
    (h : checkSlice fuel stride numVars g = true) :
    g.denote env := by
  unfold checkSlice at h
  cases hc : compileBV (sliceBackend fuel) stride numVars g.toBExpr
  · rw [hc] at h; cases h
  · rename_i res
    cases res with
    | node _ _ _ => rw [hc] at h; cases h
    | leaf b =>
      cases b
      · rw [hc] at h; cases h
      · have hvalid :=
          compileBV_sound (sliceBackend_lawful (envBits env stride) fuel numVars) g.toBExpr (.leaf true) hc
        dsimp only [ValidRes, SBDD.eval] at hvalid
        exact (BVGoal.denote_iff env g).mp hvalid.symm

/-! ## Interleaved LSB-to-MSB witnessed ROBDD verifier (`BinTree BDDNode` and `bv_robdd`) -/

/-- Internal Shannon node `(var, lo, hi)` in the ROBDD DAG. Node IDs are partitioned into `0`
(`false`), `1` (`true`), `v + 2` for input variable `v < numVars`, and `numVars + 2 + i` for
compound node `i` in `dag : BinTree BDDNode`. -/
structure BDDNode where
  var : Nat
  lo  : Nat
  hi  : Nat
  deriving Repr, Inhabited

/-- Look up node `u` in `dag` (returning `⟨u - 2, 0, 1⟩` directly for variable nodes `2 ≤ u < numVars + 2`). -/
@[inline] def getNode (numVars : Nat) (dag : BinTree BDDNode) (u : Nat) : BDDNode :=
  if Nat.blt u (numVars + 2) then
    ⟨u - 2, 0, 1⟩
  else
    BinTree.get ⟨0, 0, 0⟩ dag (u - (numVars + 2))

/-- Evaluate ROBDD node `u` across variable levels `v - 1` down to `0` by structural recursion on `v`. -/
def evalAtLevel (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) : Nat → Nat → Bool
  | 0, u => Nat.beq u 1
  | v + 1, u =>
    if Nat.blt u 2 then
      Nat.beq u 1
    else
      match getNode numVars dag u with
      | ⟨nv, lo, hi⟩ =>
        if Nat.beq nv v then
          if benv v then evalAtLevel numVars dag benv v hi
          else evalAtLevel numVars dag benv v lo
        else
          evalAtLevel numVars dag benv v u

/-- Syntactic `0`-cofactor of node `u` at variable `v`. -/
@[inline] def cofactor0 (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat) : Nat :=
  if Nat.blt u 2 then u
  else
    match getNode numVars dag u with
    | ⟨nv, lo, _⟩ => if Nat.beq nv v then lo else u

/-- Syntactic `1`-cofactor of node `u` at variable `v`. -/
@[inline] def cofactor1 (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat) : Nat :=
  if Nat.blt u 2 then u
  else
    match getNode numVars dag u with
    | ⟨nv, _, hi⟩ => if Nat.beq nv v then hi else u

/-- Pass the syntactic `(0, 1)`-cofactors of `u` at `v` to `k` as already-reduced `Nat` literals
(extracted by matching `getNode numVars dag u` once and branching outside `k`). -/
@[inline] def withCofactors (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat)
    (k : Nat → Nat → Bool) : Bool :=
  if Nat.blt u 2 then
    k u u
  else
    match getNode numVars dag u with
    | ⟨nv, lo, hi⟩ =>
      if Nat.beq nv v then k lo hi else k u u

theorem withCofactors_eq (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat)
    (k : Nat → Nat → Bool) :
    withCofactors numVars dag v u k =
      k (cofactor0 numVars dag v u) (cofactor1 numVars dag v u) := by
  unfold withCofactors cofactor0 cofactor1
  cases Nat.blt u 2
  · dsimp only
    cases getNode numVars dag u
    dsimp only
    cases Nat.beq _ v <;> rfl
  · rfl

/-- Check that node `u` is either a leaf (`u < 2`) or has top variable `< v`. -/
@[inline] def topVarBelow (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat) : Bool :=
  Nat.blt u 2 ||
  match getNode numVars dag u with
  | ⟨nv, _, _⟩ => Nat.blt nv v

/-- Check that node `u` can be Shannon-expanded at variable `v < numVars`. -/
@[inline] def canExpandAt (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat) : Bool :=
  Nat.blt v numVars &&
  topVarBelow numVars dag (v + 1) u &&
  withCofactors numVars dag v u (fun u0 u1 =>
    topVarBelow numVars dag v u0 &&
    topVarBelow numVars dag v u1)

theorem evalAtLevel_lt_two (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool)
    (v u : Nat) (h : Nat.blt u 2 = true) :
    evalAtLevel numVars dag benv v u = Nat.beq u 1 := by
  cases v <;> simp [evalAtLevel, h]

theorem evalAtLevel_succ (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) (v u : Nat) :
    evalAtLevel numVars dag benv (v + 1) u =
      (if benv v then evalAtLevel numVars dag benv v (cofactor1 numVars dag v u)
       else evalAtLevel numVars dag benv v (cofactor0 numVars dag v u)) := by
  cases hlt : Nat.blt u 2
  · dsimp only [evalAtLevel, cofactor0, cofactor1]
    rw [hlt]
    cases getNode numVars dag u
    dsimp only
    cases Nat.beq _ v <;> cases benv v <;> rfl
  · have hc0 : cofactor0 numVars dag v u = u := by unfold cofactor0; simp [hlt]
    have hc1 : cofactor1 numVars dag v u = u := by unfold cofactor1; simp [hlt]
    rw [hc0, hc1, evalAtLevel_lt_two numVars dag benv v u hlt]
    dsimp only [evalAtLevel]
    rw [hlt]
    cases benv v <;> rfl

theorem evalAtLevel_add_of_topVarBelow (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool)
    (v : Nat) :
    ∀ (k u : Nat),
      topVarBelow numVars dag v u = true →
      evalAtLevel numVars dag benv (v + k) u = evalAtLevel numVars dag benv v u
  | 0, _, _ => by simp
  | k + 1, u, h => by
    have hadd : v + (k + 1) = (v + k) + 1 := by omega
    rw [hadd, evalAtLevel_succ]
    unfold topVarBelow at h
    cases hlt : Nat.blt u 2
    · rw [hlt, Bool.false_or] at h
      have hvar : (getNode numVars dag u).var < v := by
        cases hnd : getNode numVars dag u
        rw [hnd] at h
        exact Nat.blt_eq.mp h
      have hne : Nat.beq (getNode numVars dag u).var (v + k) = false :=
        Bool.eq_false_iff.mpr (by simp [Nat.beq_eq]; omega)
      have hc0 : cofactor0 numVars dag (v + k) u = u := by
        unfold cofactor0
        cases hnd : getNode numVars dag u
        rw [hnd] at hne
        simp [hlt, hne]
      have hc1 : cofactor1 numVars dag (v + k) u = u := by
        unfold cofactor1
        cases hnd : getNode numVars dag u
        rw [hnd] at hne
        simp [hlt, hne]
      rw [hc0, hc1]
      have ih := evalAtLevel_add_of_topVarBelow numVars dag benv v k u (by simp [topVarBelow, hlt, h])
      cases benv (v + k) <;> exact ih
    · have hc0 : cofactor0 numVars dag (v + k) u = u := by unfold cofactor0; simp [hlt]
      have hc1 : cofactor1 numVars dag (v + k) u = u := by unfold cofactor1; simp [hlt]
      rw [hc0, hc1]
      have ih := evalAtLevel_add_of_topVarBelow numVars dag benv v k u (by simp [topVarBelow, hlt])
      cases benv (v + k) <;> exact ih

/-- Top-level semantic evaluation of ROBDD node `u` across all `numVars` variables. -/
def evalBDD (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) (u : Nat) : Bool :=
  evalAtLevel numVars dag benv numVars u

@[simp] theorem evalBDD_false (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) :
    evalBDD numVars dag benv 0 = false :=
  evalAtLevel_lt_two numVars dag benv numVars 0 rfl

@[simp] theorem evalBDD_true (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) :
    evalBDD numVars dag benv 1 = true :=
  evalAtLevel_lt_two numVars dag benv numVars 1 rfl

theorem evalBDD_expand (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) (v u : Nat)
    (h : canExpandAt numVars dag v u = true) :
    evalBDD numVars dag benv u =
      (if benv v then evalBDD numVars dag benv (cofactor1 numVars dag v u)
       else evalBDD numVars dag benv (cofactor0 numVars dag v u)) := by
  unfold canExpandAt at h
  rw [withCofactors_eq] at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  rcases h with ⟨⟨hv, htop⟩, hc0, hc1⟩
  unfold evalBDD
  have hm1 : numVars = (v + 1) + (numVars - (v + 1)) := by omega
  have hm0 : numVars = v + (numVars - v) := by omega
  have h1 := evalAtLevel_add_of_topVarBelow numVars dag benv (v + 1) (numVars - (v + 1)) u htop
  rw [← hm1] at h1
  have h2 := evalAtLevel_add_of_topVarBelow numVars dag benv v (numVars - v) (cofactor0 numVars dag v u) hc0
  rw [← hm0] at h2
  have h3 := evalAtLevel_add_of_topVarBelow numVars dag benv v (numVars - v) (cofactor1 numVars dag v u) hc1
  rw [← hm0] at h3
  rw [h1, h2, h3, evalAtLevel_succ]

theorem evalBDD_var (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool) (v : Nat)
    (hv : v < numVars) :
    evalBDD numVars dag benv (v + 2) = benv v := by
  have hlt2 : Nat.blt (v + 2) 2 = false :=
    Bool.eq_false_iff.mpr (by simp [Nat.blt_eq])
  have hltN : Nat.blt (v + 2) (numVars + 2) = true := Nat.blt_eq.mpr (by omega)
  have hnd : getNode numVars dag (v + 2) = ⟨v, 0, 1⟩ := by
    unfold getNode; simp [hltN]
  have hc0 : cofactor0 numVars dag v (v + 2) = 0 := by
    unfold cofactor0; simp [hlt2, hnd]
  have hc1 : cofactor1 numVars dag v (v + 2) = 1 := by
    unfold cofactor1; simp [hlt2, hnd]
  have hexp : canExpandAt numVars dag v (v + 2) = true := by
    unfold canExpandAt
    rw [withCofactors_eq]
    unfold topVarBelow
    simp [hv, hlt2, hnd, hc0, hc1, Nat.blt_eq]
  rw [evalBDD_expand numVars dag benv v (v + 2) hexp, hc0, hc1, evalBDD_false, evalBDD_true]
  cases benv v <;> rfl

/-- Witnessed memo-table entry claiming `op(a, b) = u` by Shannon expansion on variable `v`. -/
structure GateStep where
  op : GateOp
  a  : Nat
  b  : Nat
  u  : Nat
  v  : Nat
  deriving Repr, Inhabited

/-- Deterministic 10-bit bucket index (`0..1023`) for `(op, a, b)` in `claims : BinTree (List GateStep)`. -/
@[inline] def hashGate (_op : GateOp) (a b : Nat) : Nat :=
  Nat.land (Nat.xor a (Nat.shiftLeft b 4)) 1023

def findInBucket (op : GateOp) (a b : Nat) : List GateStep → Option GateStep
  | [] => none
  | s :: rest =>
    if s.op == op && Nat.beq s.a a && Nat.beq s.b b then some s
    else findInBucket op a b rest

@[inline] def findGate (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) : Option GateStep :=
  findInBucket op a b (BinTree.get [] claims (hashGate op a b))

/-- Terminal/idempotent base cases for `GateOp` on ROBDD node IDs (`0 = false`, `1 = true`). -/
def applyBaseGate (op : GateOp) (a b : Nat) : Option Nat :=
  match op with
  | .not =>
    if Nat.beq a 0 then some 1
    else if Nat.beq a 1 then some 0
    else none
  | .and =>
    if Nat.beq a 0 || Nat.beq b 0 then some 0
    else if Nat.beq a 1 then some b
    else if Nat.beq b 1 then some a
    else if Nat.beq a b then some a
    else none
  | .or =>
    if Nat.beq a 1 || Nat.beq b 1 then some 1
    else if Nat.beq a 0 then some b
    else if Nat.beq b 0 then some a
    else if Nat.beq a b then some a
    else none
  | .xor =>
    if Nat.beq a 0 then some b
    else if Nat.beq b 0 then some a
    else if Nat.beq a 1 && Nat.beq b 1 then some 0
    else if Nat.beq a b then some 0
    else none

theorem applyBaseGate_sound (numVars : Nat) (dag : BinTree BDDNode) (benv : Nat → Bool)
    (op : GateOp) (a b u : Nat) (h : applyBaseGate op a b = some u) :
    evalBDD numVars dag benv u =
      op.eval (evalBDD numVars dag benv a) (evalBDD numVars dag benv b) := by
  cases op <;> unfold applyBaseGate at h
  · cases ha0 : Nat.beq a 0
    · rw [ha0] at h
      cases ha1 : Nat.beq a 1
      · rw [ha1] at h; cases h
      · rw [ha1] at h; injection h with hu; subst hu
        rw [Nat.beq_eq.mp ha1, evalBDD_false, evalBDD_true]; rfl
    · rw [ha0] at h; injection h with hu; subst hu
      rw [Nat.beq_eq.mp ha0, evalBDD_false, evalBDD_true]; rfl
  · cases ha0 : Nat.beq a 0
    · rw [ha0] at h
      cases hb0 : Nat.beq b 0
      · rw [hb0] at h
        cases ha1 : Nat.beq a 1
        · rw [ha1] at h
          cases hb1 : Nat.beq b 1
          · rw [hb1] at h
            cases hab : Nat.beq a b
            · rw [hab] at h; cases h
            · rw [hab] at h; injection h with hu; subst hu
              rw [Nat.beq_eq.mp hab]; simp [GateOp.eval]
          · rw [hb1] at h; injection h with hu; subst hu
            rw [Nat.beq_eq.mp hb1, evalBDD_true]; simp [GateOp.eval]
        · rw [ha1] at h; injection h with hu; subst hu
          rw [Nat.beq_eq.mp ha1, evalBDD_true]; simp [GateOp.eval]
      · rw [hb0] at h; injection h with hu; subst hu
        rw [Nat.beq_eq.mp hb0, evalBDD_false]; simp [GateOp.eval]
    · rw [ha0] at h; injection h with hu; subst hu
      rw [Nat.beq_eq.mp ha0, evalBDD_false]; rfl
  · cases ha1 : Nat.beq a 1
    · rw [ha1] at h
      cases hb1 : Nat.beq b 1
      · rw [hb1] at h
        cases ha0 : Nat.beq a 0
        · rw [ha0] at h
          cases hb0 : Nat.beq b 0
          · rw [hb0] at h
            cases hab : Nat.beq a b
            · rw [hab] at h; cases h
            · rw [hab] at h; injection h with hu; subst hu
              rw [Nat.beq_eq.mp hab]; simp [GateOp.eval]
          · rw [hb0] at h; injection h with hu; subst hu
            rw [Nat.beq_eq.mp hb0, evalBDD_false]; simp [GateOp.eval]
        · rw [ha0] at h; injection h with hu; subst hu
          rw [Nat.beq_eq.mp ha0, evalBDD_false]; simp [GateOp.eval]
      · rw [hb1] at h; injection h with hu; subst hu
        rw [Nat.beq_eq.mp hb1, evalBDD_true]; simp [GateOp.eval]
    · rw [ha1] at h; injection h with hu; subst hu
      rw [Nat.beq_eq.mp ha1, evalBDD_true]; rfl
  · cases ha0 : Nat.beq a 0
    · rw [ha0] at h
      cases hb0 : Nat.beq b 0
      · rw [hb0] at h
        cases ha1 : Nat.beq a 1
        · rw [ha1] at h
          cases hab : Nat.beq a b
          · rw [hab] at h; cases h
          · rw [hab] at h; injection h with hu; subst hu
            rw [Nat.beq_eq.mp hab, evalBDD_false]; simp [GateOp.eval]
        · rw [ha1] at h
          cases hb1 : Nat.beq b 1
          · rw [hb1] at h
            cases hab : Nat.beq a b
            · rw [hab] at h; cases h
            · rw [hab] at h; injection h with hu; subst hu
              rw [Nat.beq_eq.mp hab, evalBDD_false]; simp [GateOp.eval]
          · rw [hb1] at h; injection h with hu; subst hu
            rw [Nat.beq_eq.mp ha1, Nat.beq_eq.mp hb1, evalBDD_false, evalBDD_true]; rfl
      · rw [hb0] at h; injection h with hu; subst hu
        rw [Nat.beq_eq.mp hb0, evalBDD_false]; simp [GateOp.eval]
    · rw [ha0] at h; injection h with hu; subst hu
      rw [Nat.beq_eq.mp ha0, evalBDD_false]; simp [GateOp.eval]

/-- Verify a child cofactor claim `(op, a', b') = u'` below expansion variable `parentV`. -/
def checkChildGate (parentV : Nat) (claims : BinTree (List GateStep))
    (op : GateOp) (a' b' u' : Nat) : Bool :=
  match applyBaseGate op a' b' with
  | some uBase => Nat.beq uBase u'
  | none =>
    match findGate claims op a' b' with
    | some sc => Nat.beq sc.u u' && Nat.blt sc.v parentV
    | none => false

/-- Verify a single `GateStep` in `claims` by local Shannon cofactor expansion at `s.v`.
Uses `withCofactors` so that all six child cofactor node IDs `a0, a1, b0, b1, u0, u1` are passed
to `checkChildGate` as already-reduced `Nat` literals. -/
def checkGateStep (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep))
    (s : GateStep) : Bool :=
  canExpandAt numVars dag s.v s.a &&
  canExpandAt numVars dag s.v s.b &&
  canExpandAt numVars dag s.v s.u &&
  withCofactors numVars dag s.v s.a (fun a0 a1 =>
    withCofactors numVars dag s.v s.b (fun b0 b1 =>
      withCofactors numVars dag s.v s.u (fun u0 u1 =>
        checkChildGate s.v claims s.op a0 b0 u0 &&
        checkChildGate s.v claims s.op a1 b1 u1)))

def checkAllClaims (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep)) : Bool :=
  BinTree.all (fun bucket => bucket.all (checkGateStep numVars dag claims)) claims

/-- Apply `op` to ROBDD node IDs `a` and `b` using `applyBaseGate` or a verified lookup in `claims`. -/
def applyGate (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) : Option Nat :=
  match applyBaseGate op a b with
  | some u => some u
  | none =>
    match findGate claims op a b with
    | some s => some s.u
    | none => none

theorem findInBucket_mem_and_eq (p : GateStep → Bool) (op : GateOp) (a b : Nat) :
    ∀ (bucket : List GateStep) (s : GateStep),
      bucket.all p = true →
      findInBucket op a b bucket = some s →
      p s = true ∧ s.op = op ∧ s.a = a ∧ s.b = b
  | [], _, _, hfind => by cases hfind
  | hd :: tl, s, hall, hfind => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    unfold findInBucket at hfind
    cases hm : (hd.op == op && Nat.beq hd.a a && Nat.beq hd.b b)
    · rw [hm] at hfind
      exact findInBucket_mem_and_eq p op a b tl s hall.2 hfind
    · rw [hm] at hfind; injection hfind with hs; subst hs
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at hm
      exact ⟨hall.1, hm.1.1, hm.1.2, hm.2⟩

theorem findGate_valid (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep))
    (hall : checkAllClaims numVars dag claims = true)
    (op : GateOp) (a b : Nat) (s : GateStep)
    (hfind : findGate claims op a b = some s) :
    checkGateStep numVars dag claims s = true ∧ s.op = op ∧ s.a = a ∧ s.b = b := by
  unfold findGate BinTree.get at hfind
  cases hget : claims.get? (hashGate op a b)
  · rw [hget] at hfind; cases hfind
  · rename_i bucket
    rw [hget] at hfind
    have hbucket :=
      BinTree.all_get? (fun b : List GateStep => b.all (checkGateStep numVars dag claims))
        claims (hashGate op a b) bucket hall hget
    exact findInBucket_mem_and_eq (checkGateStep numVars dag claims) op a b bucket s hbucket hfind

theorem gateStep_sound (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep))
    (benv : Nat → Bool)
    (hall : checkAllClaims numVars dag claims = true) :
    ∀ (fuel : Nat) (s : GateStep),
      s.v < fuel →
      checkGateStep numVars dag claims s = true →
      evalBDD numVars dag benv s.u =
        s.op.eval (evalBDD numVars dag benv s.a) (evalBDD numVars dag benv s.b)
  | 0, s, hlt, _ => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, s, hlt, hstep => by
    unfold checkGateStep at hstep
    rw [withCofactors_eq, withCofactors_eq, withCofactors_eq] at hstep
    simp only [Bool.and_eq_true] at hstep
    rcases hstep with ⟨⟨⟨ha, hb⟩, hu⟩, hlo, hhi⟩
    have proveChild : ∀ (a' b' u' : Nat),
        checkChildGate s.v claims s.op a' b' u' = true →
        evalBDD numVars dag benv u' =
          s.op.eval (evalBDD numVars dag benv a') (evalBDD numVars dag benv b') := by
      intro a' b' u' hc
      unfold checkChildGate at hc
      cases hbase : applyBaseGate s.op a' b'
      · rw [hbase] at hc; dsimp only at hc
        cases hfg : findGate claims s.op a' b'
        · rw [hfg] at hc; cases hc
        · rename_i sc
          rw [hfg] at hc
          simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
          obtain ⟨hsc_step, hsc_op, hsc_a, hsc_b⟩ :=
            findGate_valid numVars dag claims hall s.op a' b' sc hfg
          have ih := gateStep_sound numVars dag claims benv hall fuel sc (by omega) hsc_step
          rw [hc.1, hsc_op, hsc_a, hsc_b] at ih
          exact ih
      · rename_i uBase
        rw [hbase] at hc
        have hu' : uBase = u' := Nat.beq_eq.mp hc
        subst hu'
        exact applyBaseGate_sound numVars dag benv s.op a' b' uBase hbase
    have h0 := proveChild (cofactor0 numVars dag s.v s.a) (cofactor0 numVars dag s.v s.b)
      (cofactor0 numVars dag s.v s.u) hlo
    have h1 := proveChild (cofactor1 numVars dag s.v s.a) (cofactor1 numVars dag s.v s.b)
      (cofactor1 numVars dag s.v s.u) hhi
    rw [evalBDD_expand numVars dag benv s.v s.u hu,
        evalBDD_expand numVars dag benv s.v s.a ha,
        evalBDD_expand numVars dag benv s.v s.b hb]
    cases benv s.v <;> simp [h0, h1]

theorem applyGate_sound (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep))
    (benv : Nat → Bool)
    (hall : checkAllClaims numVars dag claims = true)
    (op : GateOp) (a b u : Nat)
    (h : applyGate claims op a b = some u) :
    evalBDD numVars dag benv u =
      op.eval (evalBDD numVars dag benv a) (evalBDD numVars dag benv b) := by
  unfold applyGate at h
  cases hbase : applyBaseGate op a b
  · rw [hbase] at h; dsimp only at h
    cases hfg : findGate claims op a b
    · rw [hfg] at h; cases h
    · rename_i s
      rw [hfg] at h; injection h with hu; subst hu
      obtain ⟨hstep, hop, ha, hb⟩ := findGate_valid numVars dag claims hall op a b s hfg
      have hv : s.v < numVars := by
        unfold checkGateStep canExpandAt at hstep
        simp only [Bool.and_eq_true, Nat.blt_eq] at hstep
        exact hstep.1.1.1.1.1
      have hs := gateStep_sound numVars dag claims benv hall numVars s hv hstep
      rw [hop, ha, hb] at hs
      exact hs
  · rename_i uBase
    rw [hbase] at h; injection h with hu; subst hu
    exact applyBaseGate_sound numVars dag benv op a b uBase hbase

def robddBackend (claims : BinTree (List GateStep)) : SymBool Nat where
  fFalse := 0
  fTrue  := 1
  fVar v := v + 2
  fNot a := applyGate claims .not a 0
  fAnd a b := applyGate claims .and a b
  fOr  a b := applyGate claims .or a b
  fXor a b := applyGate claims .xor a b

theorem robddBackend_lawful (numVars : Nat) (dag : BinTree BDDNode) (claims : BinTree (List GateStep))
    (benv : Nat → Bool)
    (hall : checkAllClaims numVars dag claims = true) :
    LawfulSymBool (robddBackend claims) (evalBDD numVars dag benv) benv numVars where
  eval_false := evalBDD_false numVars dag benv
  eval_true  := evalBDD_true numVars dag benv
  eval_var v hv := evalBDD_var numVars dag benv v hv
  eval_not a u h := applyGate_sound numVars dag claims benv hall .not a 0 u h
  eval_and a b u h := applyGate_sound numVars dag claims benv hall .and a b u h
  eval_or  a b u h := applyGate_sound numVars dag claims benv hall .or a b u h
  eval_xor a b u h := applyGate_sound numVars dag claims benv hall .xor a b u h

/-- Direct `BinTree.rec` lookup avoiding `BinTree.brecOn` (`below` + `PProd`) in kernel reduction. -/
noncomputable def getRec? {α : Type} (t : BinTree α) : Nat → Option α :=
  BinTree.rec
    (motive := fun _ => Nat → Option α)
    (fun _ => none)
    (fun v _ _ ihL ihR idx =>
      Nat.casesOn idx v (fun i =>
        cond (Nat.beq (Nat.land i 1) 0)
          (ihL (Nat.shiftRight i 1))
          (ihR (Nat.shiftRight i 1))))
    t

theorem getRec?_eq {α : Type} (t : BinTree α) :
    ∀ idx : Nat, getRec? t idx = t.get? idx := by
  induction t with
  | empty => intro _; rfl
  | node v l r ihL ihR =>
    intro idx
    cases idx with
    | zero => rfl
    | succ i =>
      change (cond (Nat.beq (Nat.land i 1) 0) (getRec? l (Nat.shiftRight i 1)) (getRec? r (Nat.shiftRight i 1))) =
        (cond (Nat.beq (Nat.land i 1) 0) (l.get? (Nat.shiftRight i 1)) (r.get? (Nat.shiftRight i 1)))
      rw [ihL, ihR]

@[inline] noncomputable def getRec {α : Type} (d : α) (t : BinTree α) (idx : Nat) : α :=
  match getRec? t idx with
  | some v => v
  | none => d

theorem getRec_eq {α : Type} (d : α) (t : BinTree α) (idx : Nat) :
    getRec d t idx = BinTree.get d t idx := by
  unfold getRec BinTree.get
  rw [getRec?_eq]

noncomputable def allRec {α : Type} (p : α → Bool) (t : BinTree α) : Bool :=
  BinTree.rec
    (motive := fun _ => Bool)
    true
    (fun v _ _ ihL ihR =>
      match v with
      | none => ihL && ihR
      | some x => p x && ihL && ihR)
    t

theorem allRec_eq {α : Type} (p : α → Bool) (t : BinTree α) :
    allRec p t = t.all p := by
  induction t with
  | empty => rfl
  | node v l r ihL ihR =>
    cases v
    · change (allRec p l && allRec p r) = (l.all p && r.all p)
      rw [ihL, ihR]
    · rename_i x
      change (p x && allRec p l && allRec p r) = (p x && l.all p && r.all p)
      rw [ihL, ihR]

noncomputable def listAllRec {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => p x && ih) xs

theorem listAllRec_eq {α : Type} (p : α → Bool) (xs : List α) :
    listAllRec p xs = xs.all p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (p x && listAllRec p xs) = (p x && xs.all p)
    rw [ih]

@[inline] noncomputable def getNodeRec (numVars2 : Nat) (dag : BinTree BDDNode) (u : Nat) : BDDNode :=
  cond (Nat.blt u numVars2)
    ⟨u - 2, 0, 1⟩
    (getRec ⟨0, 0, 0⟩ dag (u - numVars2))

theorem getNodeRec_eq (numVars : Nat) (dag : BinTree BDDNode) (u : Nat) :
    getNodeRec (numVars + 2) dag u = getNode numVars dag u := by
  unfold getNodeRec getNode
  rw [getRec_eq]
  cases Nat.blt u (numVars + 2) <;> rfl

@[inline] noncomputable def topVarBelowRec (numVars2 : Nat) (dag : BinTree BDDNode) (v u : Nat) : Bool :=
  Nat.blt u 2 ||
  match getNodeRec numVars2 dag u with
  | ⟨nv, _, _⟩ => Nat.blt nv v

theorem topVarBelowRec_eq (numVars : Nat) (dag : BinTree BDDNode) (v u : Nat) :
    topVarBelowRec (numVars + 2) dag v u = topVarBelow numVars dag v u := by
  unfold topVarBelowRec topVarBelow
  rw [getNodeRec_eq]

/-- Verify once across `dag` that every internal `BDDNode ⟨nv, lo, hi⟩` has children strictly below `nv`. -/
noncomputable def checkDagOrdered (numVars : Nat) (dag : BinTree BDDNode) : Bool :=
  let numVars2 := numVars + 2
  allRec (fun nd =>
    match nd with
    | ⟨nv, lo, hi⟩ =>
      topVarBelowRec numVars2 dag nv lo &&
      topVarBelowRec numVars2 dag nv hi) dag

theorem getNode_children_ordered (numVars : Nat) (dag : BinTree BDDNode)
    (hdag : checkDagOrdered numVars dag = true) (u : Nat) :
    topVarBelow numVars dag (getNode numVars dag u).var (getNode numVars dag u).lo = true ∧
    topVarBelow numVars dag (getNode numVars dag u).var (getNode numVars dag u).hi = true := by
  unfold getNode
  cases hlt : Nat.blt u (numVars + 2)
  · unfold BinTree.get
    cases hget : dag.get? (u - (numVars + 2))
    · unfold topVarBelow; simp
    · rename_i nd
      unfold checkDagOrdered at hdag
      rw [allRec_eq] at hdag
      have hnd := BinTree.all_get? _ dag (u - (numVars + 2)) nd hdag hget
      rcases nd with ⟨nv, lo, hi⟩
      dsimp only at hnd ⊢
      rw [topVarBelowRec_eq, topVarBelowRec_eq, Bool.and_eq_true] at hnd
      exact hnd
  · unfold topVarBelow; simp

@[inline] noncomputable def expandAtOrdered (numVars2 : Nat) (dag : BinTree BDDNode) (v u : Nat)
    (k : Nat → Nat → Bool) : Bool :=
  cond (Nat.blt u 2)
    (k u u)
    (match getNodeRec numVars2 dag u with
     | ⟨nv, lo, hi⟩ =>
       cond (Nat.blt nv v)
         (k u u)
         (cond (Nat.beq nv v)
           (k lo hi)
           false))

theorem expandAtOrdered_eq (numVars : Nat) (dag : BinTree BDDNode)
    (hdag : checkDagOrdered numVars dag = true)
    (v u : Nat) (hv : Nat.blt v numVars = true) (k : Nat → Nat → Bool) :
    expandAtOrdered (numVars + 2) dag v u k =
      (canExpandAt numVars dag v u &&
       k (cofactor0 numVars dag v u) (cofactor1 numVars dag v u)) := by
  have hord := getNode_children_ordered numVars dag hdag u
  unfold expandAtOrdered canExpandAt
  rw [withCofactors_eq, getNodeRec_eq, hv, Bool.true_and]
  cases hlt2 : Nat.blt u 2
  · dsimp only [cond]
    unfold cofactor0 cofactor1 topVarBelow
    rw [hlt2, Bool.false_or]
    cases hnd : getNode numVars dag u with
    | mk nv lo hi =>
      rw [hnd] at hord
      dsimp only at hord ⊢
      cases hnv_lt : Nat.blt nv v
      · dsimp only [cond]
        cases hnv_eq : Nat.beq nv v
        · dsimp only [cond]
          have hlt_succ : Nat.blt nv (v + 1) = false := by
            apply Bool.eq_false_iff.mpr; intro hlt_s
            have h0 : nv < v + 1 := Nat.blt_eq.mp hlt_s
            have h1 : ¬ (nv < v) := by rw [← Nat.blt_eq, hnv_lt]; decide
            have h2 : ¬ (nv = v) := by rw [← Nat.beq_eq, hnv_eq]; decide
            omega
          rw [hlt_succ]; rfl
        · dsimp only [cond]
          have heq' : nv = v := Nat.beq_eq.mp hnv_eq
          subst heq'
          have hlt_succ : Nat.blt nv (nv + 1) = true := Nat.blt_eq.mpr (by omega)
          have h0 : topVarBelow numVars dag nv lo = true := hord.1
          have h1 : topVarBelow numVars dag nv hi = true := hord.2
          unfold topVarBelow at h0 h1
          simp [hlt_succ, h0, h1]
      · dsimp only [cond]
        have hnv' : nv < v := Nat.blt_eq.mp hnv_lt
        have hlt_succ : Nat.blt nv (v + 1) = true := Nat.blt_eq.mpr (by omega)
        have hne : Nat.beq nv v = false := Bool.eq_false_iff.mpr (by simp [Nat.beq_eq]; omega)
        simp [hnv_lt, hlt_succ, hne, hlt2, hnd]
  · unfold cofactor0 cofactor1 topVarBelow
    simp [hlt2]

@[inline] def GateOp.beq : GateOp → GateOp → Bool
  | .not, .not => true
  | .and, .and => true
  | .or,  .or  => true
  | .xor, .xor => true
  | _, _ => false

theorem GateOp.beq_eq (x y : GateOp) : GateOp.beq x y = (x == y) := by
  cases x <;> cases y <;> rfl

noncomputable def findInBucketRec (op : GateOp) (a b : Nat) (xs : List GateStep) : Option GateStep :=
  List.rec
    (motive := fun _ => Option GateStep)
    none
    (fun s _ ih =>
      match s with
      | ⟨op', a', b', _, _⟩ =>
        cond (Nat.beq a' a && Nat.beq b' b && GateOp.beq op' op)
          (some s)
          ih)
    xs

theorem findInBucketRec_eq (op : GateOp) (a b : Nat) (xs : List GateStep) :
    findInBucketRec op a b xs = findInBucket op a b xs := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨op', a', b', u', v'⟩
    change (cond (Nat.beq a' a && Nat.beq b' b && GateOp.beq op' op) (some ⟨op', a', b', u', v'⟩) (findInBucketRec op a b rest)) =
      (if (op' == op && Nat.beq a' a && Nat.beq b' b) = true then some ⟨op', a', b', u', v'⟩ else findInBucket op a b rest)
    rw [ih, GateOp.beq_eq]
    cases op' == op <;> cases Nat.beq a' a <;> cases Nat.beq b' b <;> rfl

@[inline] noncomputable def findGateRec (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) : Option GateStep :=
  findInBucketRec op a b (getRec [] claims (hashGate op a b))

theorem findGateRec_eq (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) :
    findGateRec claims op a b = findGate claims op a b := by
  unfold findGateRec findGate
  rw [getRec_eq, findInBucketRec_eq]

def applyBaseGateFast (op : GateOp) (a b : Nat) : Option Nat :=
  match op with
  | .not =>
    cond (Nat.beq a 0) (some 1)
      (cond (Nat.beq a 1) (some 0) none)
  | .and =>
    cond (Nat.beq a 0 || Nat.beq b 0) (some 0)
      (cond (Nat.beq a 1) (some b)
        (cond (Nat.beq b 1) (some a)
          (cond (Nat.beq a b) (some a) none)))
  | .or =>
    cond (Nat.beq a 1 || Nat.beq b 1) (some 1)
      (cond (Nat.beq a 0) (some b)
        (cond (Nat.beq b 0) (some a)
          (cond (Nat.beq a b) (some a) none)))
  | .xor =>
    cond (Nat.beq a 0) (some b)
      (cond (Nat.beq b 0) (some a)
        (cond (Nat.beq a 1 && Nat.beq b 1) (some 0)
          (cond (Nat.beq a b) (some 0) none)))

theorem applyBaseGateFast_eq (op : GateOp) (a b : Nat) :
    applyBaseGateFast op a b = applyBaseGate op a b := by
  cases op <;> unfold applyBaseGateFast applyBaseGate <;>
    cases Nat.beq a 0 <;> cases Nat.beq b 0 <;>
    cases Nat.beq a 1 <;> cases Nat.beq b 1 <;>
    cases Nat.beq a b <;> rfl

noncomputable def checkChildGateRec (parentV : Nat) (claims : BinTree (List GateStep))
    (op : GateOp) (a' b' u' : Nat) : Bool :=
  match applyBaseGateFast op a' b' with
  | some uBase => Nat.beq uBase u'
  | none =>
    match findGateRec claims op a' b' with
    | some ⟨_, _, _, u, v⟩ => Nat.beq u u' && Nat.blt v parentV
    | none => false

theorem checkChildGateRec_eq (parentV : Nat) (claims : BinTree (List GateStep))
    (op : GateOp) (a' b' u' : Nat) :
    checkChildGateRec parentV claims op a' b' u' =
      checkChildGate parentV claims op a' b' u' := by
  unfold checkChildGateRec checkChildGate
  rw [applyBaseGateFast_eq, findGateRec_eq]
  cases applyBaseGate op a' b'
  · cases findGate claims op a' b' with
    | none => rfl
    | some s => cases s; rfl
  · rfl

noncomputable def checkGateStepOrdered (numVars numVars2 : Nat) (dag : BinTree BDDNode)
    (claims : BinTree (List GateStep)) (s : GateStep) : Bool :=
  match s with
  | ⟨op, a, b, u, v⟩ =>
    Nat.blt v numVars &&
    expandAtOrdered numVars2 dag v a (fun a0 a1 =>
      expandAtOrdered numVars2 dag v b (fun b0 b1 =>
        expandAtOrdered numVars2 dag v u (fun u0 u1 =>
          checkChildGateRec v claims op a0 b0 u0 &&
          checkChildGateRec v claims op a1 b1 u1)))

theorem checkGateStepOrdered_eq (numVars : Nat) (dag : BinTree BDDNode)
    (claims : BinTree (List GateStep))
    (hdag : checkDagOrdered numVars dag = true) (s : GateStep) :
    checkGateStepOrdered numVars (numVars + 2) dag claims s =
      checkGateStep numVars dag claims s := by
  rcases s with ⟨op, a, b, u, v⟩
  unfold checkGateStepOrdered checkGateStep
  rw [withCofactors_eq, withCofactors_eq, withCofactors_eq]
  dsimp only
  by_cases hv : Nat.blt v numVars = true
  · rw [hv, Bool.true_and,
        expandAtOrdered_eq numVars dag hdag v a hv,
        expandAtOrdered_eq numVars dag hdag v b hv,
        expandAtOrdered_eq numVars dag hdag v u hv,
        checkChildGateRec_eq, checkChildGateRec_eq]
    cases canExpandAt numVars dag v a <;>
      cases canExpandAt numVars dag v b <;>
      cases canExpandAt numVars dag v u <;> rfl
  · have hv' : Nat.blt v numVars = false := Bool.eq_false_iff.mpr hv
    have ha : canExpandAt numVars dag v a = false := by unfold canExpandAt; simp [hv']
    simp [hv', ha]

noncomputable def checkAllClaimsOrdered (numVars : Nat) (dag : BinTree BDDNode)
    (claims : BinTree (List GateStep)) : Bool :=
  let numVars2 := numVars + 2
  checkDagOrdered numVars dag &&
  allRec (fun bucket => listAllRec (checkGateStepOrdered numVars numVars2 dag claims) bucket) claims

theorem checkAllClaimsOrdered_imp (numVars : Nat) (dag : BinTree BDDNode)
    (claims : BinTree (List GateStep))
    (h : checkAllClaimsOrdered numVars dag claims = true) :
    checkAllClaims numVars dag claims = true := by
  unfold checkAllClaimsOrdered at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hdag, hclaims⟩
  rw [allRec_eq] at hclaims
  have hstep : checkGateStepOrdered numVars (numVars + 2) dag claims =
      checkGateStep numVars dag claims := by
    funext s
    exact checkGateStepOrdered_eq numVars dag claims hdag s
  have hbucket : (fun bucket : List GateStep =>
      listAllRec (checkGateStepOrdered numVars (numVars + 2) dag claims) bucket) =
      (fun bucket : List GateStep => bucket.all (checkGateStep numVars dag claims)) := by
    funext bucket
    rw [listAllRec_eq, hstep]
  rw [hbucket] at hclaims
  exact hclaims

noncomputable def applyGateRec (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) : Option Nat :=
  match applyBaseGateFast op a b with
  | some u => some u
  | none =>
    match findGateRec claims op a b with
    | some ⟨_, _, _, u, _⟩ => some u
    | none => none

theorem applyGateRec_eq (claims : BinTree (List GateStep)) (op : GateOp) (a b : Nat) :
    applyGateRec claims op a b = applyGate claims op a b := by
  unfold applyGateRec applyGate
  rw [applyBaseGateFast_eq, findGateRec_eq]
  cases applyBaseGate op a b
  · cases findGate claims op a b with
    | none => rfl
    | some s => cases s; rfl
  · rfl

noncomputable def robddBackendRec (claims : BinTree (List GateStep)) : SymBool Nat where
  fFalse := 0
  fTrue  := 1
  fVar v := v + 2
  fNot a := applyGateRec claims .not a 0
  fAnd a b := applyGateRec claims .and a b
  fOr  a b := applyGateRec claims .or a b
  fXor a b := applyGateRec claims .xor a b

theorem robddBackendRec_eq (claims : BinTree (List GateStep)) :
    robddBackendRec claims = robddBackend claims := by
  unfold robddBackendRec robddBackend
  congr <;> funext _ <;> try funext _
  all_goals simp [applyGateRec_eq]

/-- Kernel checker for `bv_robdd`: verifies all witnessed `GateStep`s in `claims` and checks
that `g.toBExpr` evaluates to ROBDD node `1` (`true`). -/
noncomputable def checkROBDD (stride numVars : Nat) (dag : BinTree BDDNode)
    (claims : BinTree (List GateStep)) (g : BVGoal) : Bool :=
  checkAllClaimsOrdered numVars dag claims &&
  match compileBV (robddBackendRec claims) stride numVars g.toBExpr with
  | some u => Nat.beq u 1
  | none => false

/-- Soundness theorem for `bv_robdd`, discharged in the kernel via `Eq.refl true`. -/
theorem prove_of_checkROBDD (env : Env) (stride numVars : Nat)
    (dag : BinTree BDDNode) (claims : BinTree (List GateStep)) (g : BVGoal)
    (h : checkROBDD stride numVars dag claims g = true) :
    g.denote env := by
  unfold checkROBDD at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hallOrd, hcomp⟩
  have hall := checkAllClaimsOrdered_imp numVars dag claims hallOrd
  rw [robddBackendRec_eq] at hcomp
  revert hcomp
  cases hc : compileBV (robddBackend claims) stride numVars g.toBExpr <;> simp only
  · intro h; cases h
  · rename_i u
    intro hu1
    have hu : u = 1 := Nat.beq_eq.mp hu1
    subst hu
    have hvalid :=
      compileBV_sound (robddBackend_lawful numVars dag claims (envBits env stride) hall)
        g.toBExpr 1 hc
    dsimp only [ValidRes] at hvalid
    rw [evalBDD_true] at hvalid
    exact (BVGoal.denote_iff env g).mp hvalid.symm

end

/-! ## `MetaM` reifier, witnessed ROBDD builder, and tactics -/

public meta section
set_option compiler.relaxedMetaCheck true

/-- Return the first ripple-carry or arithmetic operator name in `BVExpr k`, if any, so `bv_slice`
can report when `bv_robdd` is required. -/
def BVExpr.firstArithOp? : {k : Option Nat} → BVExpr k → Option String
  | _, .var _ _ => none
  | _, .const _ _ => none
  | _, .and a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .or a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .xor a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .not a => a.firstArithOp?
  | _, .shl a _ => a.firstArithOp?
  | _, .lshr a _ => a.firstArithOp?
  | _, .ashr a _ => a.firstArithOp?
  | _, .zext _ a => a.firstArithOp?
  | _, .sext _ a => a.firstArithOp?
  | _, .extract _ _ a => a.firstArithOp?
  | _, .append a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .replicate _ a => a.firstArithOp?
  | _, .add _ _ => some "+"
  | _, .sub _ _ => some "-"
  | _, .neg (.const _ _) => none
  | _, .neg _ => some "neg"
  | _, .bvIte c t e => c.firstArithOp? <|> t.firstArithOp? <|> e.firstArithOp?
  | _, .bconst _ => none
  | _, .bvar _ => none
  | _, .getLsbD a _ => a.firstArithOp?
  | _, .msb a => a.firstArithOp?
  | _, .beq a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .bne a b => a.firstArithOp? <|> b.firstArithOp?
  | _, .ult _ _ => some "BitVec.ult"
  | _, .ule _ _ => some "BitVec.ule"
  | _, .slt _ _ => some "BitVec.slt"
  | _, .sle _ _ => some "BitVec.sle"
  | _, .bnot p => p.firstArithOp?
  | _, .band p q => p.firstArithOp? <|> q.firstArithOp?
  | _, .bor p q => p.firstArithOp? <|> q.firstArithOp?
  | _, .bxor p q => p.firstArithOp? <|> q.firstArithOp?
  | _, .bimp p q => p.firstArithOp? <|> q.firstArithOp?
  | _, .biff p q => p.firstArithOp? <|> q.firstArithOp?
  | _, .bite c t e => c.firstArithOp? <|> t.firstArithOp? <|> e.firstArithOp?

def BVGoal.firstArithOp? : BVGoal → Option String
  | .eq a b => a.firstArithOp? <|> b.firstArithOp?
  | .ne a b => a.firstArithOp? <|> b.firstArithOp?
  | .lt _ _ => some "<"
  | .le _ _ => some "≤"
  | .boolEq a b => a.firstArithOp? <|> b.firstArithOp?
  | .boolNe a b => a.firstArithOp? <|> b.firstArithOp?
  | .top => none
  | .bot => none
  | .not p => p.firstArithOp?
  | .and p q => p.firstArithOp? <|> q.firstArithOp?
  | .or p q => p.firstArithOp? <|> q.firstArithOp?
  | .imp p q => p.firstArithOp? <|> q.firstArithOp?
  | .iff p q => p.firstArithOp? <|> q.firstArithOp?

/-- Untrusted `MetaM` insertion into a `BinTree α` matching `BinTree.get?`. -/
partial def BinTree.insert {α : Type} (t : BinTree α) (idx : Nat) (x : α) : BinTree α :=
  match t, idx with
  | .empty, 0 => .node (some x) .empty .empty
  | .empty, i + 1 =>
    if (i &&& 1) == 0 then
      .node none (BinTree.insert .empty (i >>> 1) x) .empty
    else
      .node none .empty (BinTree.insert .empty (i >>> 1) x)
  | .node _ l r, 0 => .node (some x) l r
  | .node v l r, i + 1 =>
    if (i &&& 1) == 0 then
      .node v (BinTree.insert l (i >>> 1) x) r
    else
      .node v l (BinTree.insert r (i >>> 1) x)

instance : Hashable GateOp where
  hash
    | .not => 1
    | .and => 2
    | .or  => 3
    | .xor => 4

/-- `MetaM` ROBDD builder state for constructing `dag : BinTree BDDNode` and `claims : BinTree (List GateStep)`. -/
structure ROBDDBuilderState where
  numVars     : Nat
  nodes       : Array BDDNode := #[]
  uniqueTable : Std.HashMap (Nat × Nat × Nat) Nat := {}
  memoTable   : Std.HashMap (GateOp × Nat × Nat) GateStep := {}
  claimsList  : Array GateStep := #[]

namespace ROBDDBuilderState

@[inline] def init (numVars : Nat) : ROBDDBuilderState :=
  { numVars }

@[inline] def getNode (st : ROBDDBuilderState) (u : Nat) : BDDNode :=
  if u < 2 then ⟨0, 0, 0⟩
  else if u < st.numVars + 2 then ⟨u - 2, 0, 1⟩
  else st.nodes.getD (u - (st.numVars + 2)) ⟨0, 0, 0⟩

@[inline] def cofactor0 (st : ROBDDBuilderState) (v u : Nat) : Nat :=
  if u < 2 then u
  else
    let nd := st.getNode u
    if nd.var == v then nd.lo else u

@[inline] def cofactor1 (st : ROBDDBuilderState) (v u : Nat) : Nat :=
  if u < 2 then u
  else
    let nd := st.getNode u
    if nd.var == v then nd.hi else u

end ROBDDBuilderState

/-- Allocate or reuse a canonical reduced ROBDD node for `(v, lo, hi)`. -/
def mkNodeBuilder (v lo hi : Nat) : StateM ROBDDBuilderState Nat := do
  if lo == hi then
    return lo
  else if lo == 0 && hi == 1 then
    return v + 2
  else
    let st ← get
    let key := (v, lo, hi)
    if let some u := st.uniqueTable[key]? then
      return u
    else
      let u := st.numVars + 2 + st.nodes.size
      set { st with
        nodes := st.nodes.push ⟨v, lo, hi⟩
        uniqueTable := st.uniqueTable.insert key u }
      return u

/-- Apply `op` to ROBDD node IDs `a` and `b`, recording non-base steps in `claimsList`. -/
partial def applyGateBuilder (op : GateOp) (a b : Nat) : StateM ROBDDBuilderState Nat := do
  let b := match op with | .not => 0 | _ => b
  if let some u := applyBaseGate op a b then
    return u
  else
    let st ← get
    let key := (op, a, b)
    if let some step := st.memoTable[key]? then
      return step.u
    else
      let va := (st.getNode a).var
      let vb := (st.getNode b).var
      let v :=
        if a < 2 then vb
        else if b < 2 then va
        else Nat.max va vb
      let a0 := st.cofactor0 v a
      let b0 := st.cofactor0 v b
      let a1 := st.cofactor1 v a
      let b1 := st.cofactor1 v b
      let lo ← applyGateBuilder op a0 b0
      let hi ← applyGateBuilder op a1 b1
      let u ← mkNodeBuilder v lo hi
      let step : GateStep := ⟨op, a, b, u, v⟩
      modify fun s => { s with
        memoTable := s.memoTable.insert key step
        claimsList := s.claimsList.push step }
      return u

def simIte (c t e : Nat) : StateM ROBDDBuilderState Nat := do
  let ct ← applyGateBuilder .and c t
  let nc ← applyGateBuilder .not c 0
  let nce ← applyGateBuilder .and nc e
  applyGateBuilder .or ct nce

def simMkBits (f : Nat → StateM ROBDDBuilderState Nat) : Nat → Nat → StateM ROBDDBuilderState (List Nat)
  | 0, _ => return []
  | k + 1, start => do
    let b ← f start
    let bs ← simMkBits f k (start + 1)
    return b :: bs

def simFullAdder (x y cin : Nat) : StateM ROBDDBuilderState (Nat × Nat) := do
  let xy ← applyGateBuilder .xor x y
  let s ← applyGateBuilder .xor xy cin
  let xyAnd ← applyGateBuilder .and x y
  let cxyAnd ← applyGateBuilder .and cin xy
  let cout ← applyGateBuilder .or xyAnd cxyAnd
  return (s, cout)

def simRippleAddAux (fx fy : Nat → Nat) : Nat → Nat → Nat → StateM ROBDDBuilderState (List Nat × Nat)
  | 0, _, cin => return ([], cin)
  | k + 1, start, cin => do
    let (s, cNext) ← simFullAdder (fx start) (fy start) cin
    let (ss, cOut) ← simRippleAddAux fx fy k (start + 1) cNext
    return (s :: ss, cOut)

def simEqBitsAux (fx fy : Nat → Nat) : Nat → Nat → Nat → StateM ROBDDBuilderState Nat
  | 0, _, acc => return acc
  | k + 1, start, acc => do
    let diff ← applyGateBuilder .xor (fx start) (fy start)
    let eqBit ← applyGateBuilder .not diff 0
    let acc' ← applyGateBuilder .and acc eqBit
    simEqBitsAux fx fy k (start + 1) acc'

def simNotBits (w : Nat) (as : List Nat) : StateM ROBDDBuilderState (List Nat) :=
  simMkBits (fun i => applyGateBuilder .not (getD as i 0) 0) w 0

def simUltBits (w : Nat) (as bs : List Nat) : StateM ROBDDBuilderState Nat := do
  let nbs ← simNotBits w bs
  let (_, cOut) ← simRippleAddAux (fun i => getD as i 0) (fun i => getD nbs i 0) w 0 1
  applyGateBuilder .not cOut 0

def simSltBits (w : Nat) (as bs : List Nat) : StateM ROBDDBuilderState Nat := do
  let nbs ← simNotBits w bs
  let (_, cOut) ← simRippleAddAux (fun i => getD as i 0) (fun i => getD nbs i 0) w 0 1
  let msbA := getD as (w - 1) 0
  let msbB := getD bs (w - 1) 0
  let msbDiff ← applyGateBuilder .xor msbA msbB
  let msbEq ← applyGateBuilder .not msbDiff 0
  applyGateBuilder .xor msbEq cOut

/-- Direct ROBDD node compiler in `StateM ROBDDBuilderState` executing the exact gate sequence of `compileBV`. -/
def simCompileBV (stride : Nat) : {k : Option Nat} → BVExpr k → StateM ROBDDBuilderState (SymRes Nat k)
  | _, .var w idx =>
    simMkBits (fun i => return (bitVar stride idx i + 2)) w 0
  | _, .const w val =>
    simMkBits (fun i => return (cond (Nat.testBit val i) 1 0)) w 0
  | _, @BVExpr.and w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simMkBits (fun i => applyGateBuilder .and (getD as i 0) (getD bs i 0)) w 0
  | _, @BVExpr.or w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simMkBits (fun i => applyGateBuilder .or (getD as i 0) (getD bs i 0)) w 0
  | _, @BVExpr.xor w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simMkBits (fun i => applyGateBuilder .xor (getD as i 0) (getD bs i 0)) w 0
  | _, @BVExpr.not w a => do
    let as ← simCompileBV stride a
    simNotBits w as
  | _, @BVExpr.shl w a k => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (if i < k then 0 else getD as (i - k) 0)) w 0
  | _, @BVExpr.lshr w a k => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (getD as (k + i) 0)) w 0
  | _, @BVExpr.ashr w a k => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (if k + i < w then getD as (k + i) 0 else getD as (w - 1) 0)) w 0
  | _, @BVExpr.zext _ v a => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (getD as i 0)) v 0
  | _, @BVExpr.sext w v a => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (if w == 0 then 0 else if i < w then getD as i 0 else getD as (w - 1) 0)) v 0
  | _, @BVExpr.extract _ start len a => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (getD as (start + i) 0)) len 0
  | _, @BVExpr.append wx wy a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simMkBits (fun i => return (if i < wy then getD bs i 0 else getD as (i - wy) 0)) (wx + wy) 0
  | _, @BVExpr.replicate w n a => do
    let as ← simCompileBV stride a
    simMkBits (fun i => return (if w == 0 then 0 else getD as (i % w) 0)) (w * n) 0
  | _, @BVExpr.add w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    let (ss, _) ← simRippleAddAux (fun i => getD as i 0) (fun i => getD bs i 0) w 0 0
    return ss
  | _, @BVExpr.sub w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    let nbs ← simNotBits w bs
    let (ss, _) ← simRippleAddAux (fun i => getD as i 0) (fun i => getD nbs i 0) w 0 1
    return ss
  | _, @BVExpr.neg w a => do
    let as ← simCompileBV stride a
    let nas ← simNotBits w as
    let (ss, _) ← simRippleAddAux (fun _ => 0) (fun i => getD nas i 0) w 0 1
    return ss
  | _, @BVExpr.bvIte w c t e => do
    let uc ← simCompileBV stride c
    let ts ← simCompileBV stride t
    let es ← simCompileBV stride e
    simMkBits (fun i => simIte uc (getD ts i 0) (getD es i 0)) w 0
  | _, .bconst b => return (cond b 1 0)
  | _, .bvar idx => return (boolVar idx + 2)
  | _, .getLsbD a i => do
    let as ← simCompileBV stride a
    return (getD as i 0)
  | _, @BVExpr.msb w a => do
    let as ← simCompileBV stride a
    return (getD as (w - 1) 0)
  | _, @BVExpr.beq w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simEqBitsAux (fun i => getD as i 0) (fun i => getD bs i 0) w 0 1
  | _, @BVExpr.bne w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    let ueq ← simEqBitsAux (fun i => getD as i 0) (fun i => getD bs i 0) w 0 1
    applyGateBuilder .not ueq 0
  | _, @BVExpr.ult w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simUltBits w as bs
  | _, @BVExpr.ule w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    let gt ← simUltBits w bs as
    applyGateBuilder .not gt 0
  | _, @BVExpr.slt w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    simSltBits w as bs
  | _, @BVExpr.sle w a b => do
    let as ← simCompileBV stride a
    let bs ← simCompileBV stride b
    let gt ← simSltBits w bs as
    applyGateBuilder .not gt 0
  | _, .bnot p => do
    let up ← simCompileBV stride p
    applyGateBuilder .not up 0
  | _, .band p q => do
    let up ← simCompileBV stride p
    let uq ← simCompileBV stride q
    applyGateBuilder .and up uq
  | _, .bor p q => do
    let up ← simCompileBV stride p
    let uq ← simCompileBV stride q
    applyGateBuilder .or up uq
  | _, .bxor p q => do
    let up ← simCompileBV stride p
    let uq ← simCompileBV stride q
    applyGateBuilder .xor up uq
  | _, .bimp p q => do
    let up ← simCompileBV stride p
    let uq ← simCompileBV stride q
    let nup ← applyGateBuilder .not up 0
    applyGateBuilder .or nup uq
  | _, .biff p q => do
    let up ← simCompileBV stride p
    let uq ← simCompileBV stride q
    let diff ← applyGateBuilder .xor up uq
    applyGateBuilder .not diff 0
  | _, .bite c t e => do
    let uc ← simCompileBV stride c
    let ut ← simCompileBV stride t
    let ue ← simCompileBV stride e
    simIte uc ut ue

/-- Build `dag : BinTree BDDNode` and `claims : BinTree (List GateStep)` from `ROBDDBuilderState`. -/
def finalizeWitness (st : ROBDDBuilderState) : BinTree BDDNode × BinTree (List GateStep) := Id.run do
  let mut dag : BinTree BDDNode := .empty
  for i in [0 : st.nodes.size] do
    dag := dag.insert i st.nodes[i]!
  let mut buckets : Std.HashMap Nat (List GateStep) := {}
  for step in st.claimsList do
    let h := hashGate step.op step.a step.b
    let cur := buckets.getD h []
    buckets := buckets.insert h (step :: cur)
  let mut claims : BinTree (List GateStep) := .empty
  for (h, bucket) in buckets.toList do
    claims := claims.insert h bucket.reverse
  return (dag, claims)

open Lean Meta Elab Tactic

def listToExpr {α : Type} (ty : Expr) (elemToExpr : α → Expr) (xs : List α) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) ty (elemToExpr x) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

def optionToExpr {α : Type} (ty : Expr) (elemToExpr : α → Expr) : Option α → Expr
  | none => mkApp (mkConst ``Option.none [0]) ty
  | some x => mkApp2 (mkConst ``Option.some [0]) ty (elemToExpr x)

def binTreeToExpr {α : Type} (ty : Expr) (elemToExpr : α → Expr) : BinTree α → Expr
  | .empty => mkApp (mkConst ``BinTree.empty) ty
  | .node v l r =>
    mkApp4 (mkConst ``BinTree.node) ty
      (optionToExpr ty elemToExpr v)
      (binTreeToExpr ty elemToExpr l)
      (binTreeToExpr ty elemToExpr r)

def bddNodeToExpr (nd : BDDNode) : Expr :=
  mkApp3 (mkConst ``BDDNode.mk) (toExpr nd.var) (toExpr nd.lo) (toExpr nd.hi)

def gateOpToExpr : GateOp → Expr
  | .not => mkConst ``GateOp.not
  | .and => mkConst ``GateOp.and
  | .or  => mkConst ``GateOp.or
  | .xor => mkConst ``GateOp.xor

def gateStepToExpr (s : GateStep) : Expr :=
  mkApp5 (mkConst ``GateStep.mk)
    (gateOpToExpr s.op) (toExpr s.a) (toExpr s.b) (toExpr s.u) (toExpr s.v)

def envToExpr (bvAtoms : Array (Nat × Expr)) (boolAtoms : Array Expr) : Expr :=
  let varsExpr := listToExpr (mkConst ``EnvEntry)
    (fun (w, e) => mkApp2 (mkConst ``EnvEntry.mk) (toExpr w) e) bvAtoms.toList
  let boolsExpr := listToExpr (mkConst ``Bool) id boolAtoms.toList
  mkApp2 (mkConst ``Env.mk) varsExpr boolsExpr

/-- Serialize a `BVExpr k` into a Lean `Expr` without `Eq.rec` casts. -/
def bvExprToExpr : {k : Option Nat} → BVExpr k → Expr
  | _, .var w idx => mkApp2 (mkConst ``BVExpr.var) (toExpr w) (toExpr idx)
  | _, .const w val => mkApp2 (mkConst ``BVExpr.const) (toExpr w) (toExpr val)
  | _, @BVExpr.and w a b => mkApp3 (mkConst ``BVExpr.and) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.or w a b => mkApp3 (mkConst ``BVExpr.or) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.xor w a b => mkApp3 (mkConst ``BVExpr.xor) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.not w a => mkApp2 (mkConst ``BVExpr.not) (toExpr w) (bvExprToExpr a)
  | _, @BVExpr.shl w a k => mkApp3 (mkConst ``BVExpr.shl) (toExpr w) (bvExprToExpr a) (toExpr k)
  | _, @BVExpr.lshr w a k => mkApp3 (mkConst ``BVExpr.lshr) (toExpr w) (bvExprToExpr a) (toExpr k)
  | _, @BVExpr.ashr w a k => mkApp3 (mkConst ``BVExpr.ashr) (toExpr w) (bvExprToExpr a) (toExpr k)
  | _, @BVExpr.zext w v a => mkApp3 (mkConst ``BVExpr.zext) (toExpr w) (toExpr v) (bvExprToExpr a)
  | _, @BVExpr.sext w v a => mkApp3 (mkConst ``BVExpr.sext) (toExpr w) (toExpr v) (bvExprToExpr a)
  | _, @BVExpr.extract w start len a =>
    mkApp4 (mkConst ``BVExpr.extract) (toExpr w) (toExpr start) (toExpr len) (bvExprToExpr a)
  | _, @BVExpr.append wx wy a b =>
    mkApp4 (mkConst ``BVExpr.append) (toExpr wx) (toExpr wy) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.replicate w n a =>
    mkApp3 (mkConst ``BVExpr.replicate) (toExpr w) (toExpr n) (bvExprToExpr a)
  | _, @BVExpr.add w a b => mkApp3 (mkConst ``BVExpr.add) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.sub w a b => mkApp3 (mkConst ``BVExpr.sub) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.neg w a => mkApp2 (mkConst ``BVExpr.neg) (toExpr w) (bvExprToExpr a)
  | _, @BVExpr.bvIte w c t e =>
    mkApp4 (mkConst ``BVExpr.bvIte) (toExpr w) (bvExprToExpr c) (bvExprToExpr t) (bvExprToExpr e)
  | _, .bconst b => mkApp (mkConst ``BVExpr.bconst) (toExpr b)
  | _, .bvar idx => mkApp (mkConst ``BVExpr.bvar) (toExpr idx)
  | _, @BVExpr.getLsbD w a i => mkApp3 (mkConst ``BVExpr.getLsbD) (toExpr w) (bvExprToExpr a) (toExpr i)
  | _, @BVExpr.msb w a => mkApp2 (mkConst ``BVExpr.msb) (toExpr w) (bvExprToExpr a)
  | _, @BVExpr.beq w a b => mkApp3 (mkConst ``BVExpr.beq) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.bne w a b => mkApp3 (mkConst ``BVExpr.bne) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.ult w a b => mkApp3 (mkConst ``BVExpr.ult) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.ule w a b => mkApp3 (mkConst ``BVExpr.ule) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.slt w a b => mkApp3 (mkConst ``BVExpr.slt) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, @BVExpr.sle w a b => mkApp3 (mkConst ``BVExpr.sle) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | _, .bnot p => mkApp (mkConst ``BVExpr.bnot) (bvExprToExpr p)
  | _, .band p q => mkApp2 (mkConst ``BVExpr.band) (bvExprToExpr p) (bvExprToExpr q)
  | _, .bor p q => mkApp2 (mkConst ``BVExpr.bor) (bvExprToExpr p) (bvExprToExpr q)
  | _, .bxor p q => mkApp2 (mkConst ``BVExpr.bxor) (bvExprToExpr p) (bvExprToExpr q)
  | _, .bimp p q => mkApp2 (mkConst ``BVExpr.bimp) (bvExprToExpr p) (bvExprToExpr q)
  | _, .biff p q => mkApp2 (mkConst ``BVExpr.biff) (bvExprToExpr p) (bvExprToExpr q)
  | _, .bite c t e => mkApp3 (mkConst ``BVExpr.bite) (bvExprToExpr c) (bvExprToExpr t) (bvExprToExpr e)

def bvGoalToExpr : BVGoal → Expr
  | @BVGoal.eq w a b => mkApp3 (mkConst ``BVGoal.eq) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | @BVGoal.ne w a b => mkApp3 (mkConst ``BVGoal.ne) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | @BVGoal.lt w a b => mkApp3 (mkConst ``BVGoal.lt) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | @BVGoal.le w a b => mkApp3 (mkConst ``BVGoal.le) (toExpr w) (bvExprToExpr a) (bvExprToExpr b)
  | .boolEq a b => mkApp2 (mkConst ``BVGoal.boolEq) (bvExprToExpr a) (bvExprToExpr b)
  | .boolNe a b => mkApp2 (mkConst ``BVGoal.boolNe) (bvExprToExpr a) (bvExprToExpr b)
  | .top => mkConst ``BVGoal.top
  | .bot => mkConst ``BVGoal.bot
  | .not p => mkApp (mkConst ``BVGoal.not) (bvGoalToExpr p)
  | .and p q => mkApp2 (mkConst ``BVGoal.and) (bvGoalToExpr p) (bvGoalToExpr q)
  | .or p q => mkApp2 (mkConst ``BVGoal.or) (bvGoalToExpr p) (bvGoalToExpr q)
  | .imp p q => mkApp2 (mkConst ``BVGoal.imp) (bvGoalToExpr p) (bvGoalToExpr q)
  | .iff p q => mkApp2 (mkConst ``BVGoal.iff) (bvGoalToExpr p) (bvGoalToExpr q)

structure ReifyState where
  bvAtoms          : Array (Nat × Expr) := #[]
  boolAtoms        : Array Expr := #[]
  unsupportedTerms : Array (String × Expr) := #[]

abbrev ReifyM := StateRefT ReifyState MetaM

/-- Check if a constant name is a transparent ARM64 / BitVec wrapper that should be unfolded during reification. -/
def isTransparentWrapper (n : Name) : Bool :=
  match n with
  | .str _ s =>
    s == "AddWithCarry64" || s == "AddWithCarry32" ||
    s == "subsPState64" || s == "addsPState64" ||
    s == "subsPState32" || s == "addsPState32" ||
    s == "ConditionHolds"
  | _ => false

/-- Normalize an `Expr` before reification by unfolding transparent wrappers (`AddWithCarry64`,
`ConditionHolds`, `subsPState64`, etc.) and reducing projections, `let`-bindings,
and constant-condition `ite`s. -/
partial def normWrapper (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).consumeMData
  match e with
  | .letE _ _ v b _ =>
    normWrapper (b.instantiate1 v)
  | .proj typeName idx structExpr =>
    let s' ← normWrapper structExpr
    let e' := Expr.proj typeName idx s'
    let eWhnf ← whnfCore e'
    if eWhnf != e' then normWrapper eWhnf else return e'
  | _ =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    if fn.isLambda then
      return (← normWrapper (fn.beta args))
    if let .const n _ := fn then
      if isTransparentWrapper n then
        if let some u ← unfoldDefinition? e then
          let uWhnf ← whnfCore u
          return (← normWrapper uWhnf)
      if n == ``ite && args.size == 5 then
        let condProp ← normWrapper args[1]!
        if condProp.isAppOfArity ``Eq 3 then
          let lhs ← normWrapper (condProp.getArg! 1)
          let rhs ← normWrapper (condProp.getArg! 2)
          if lhs.isConstOf ``Bool.true && rhs.isConstOf ``Bool.true then
            return (← normWrapper args[3]!)
          if lhs.isConstOf ``Bool.false && rhs.isConstOf ``Bool.true then
            return (← normWrapper args[4]!)
      let isProjFn :=
        n == ``Prod.fst || n == ``Prod.snd ||
        (match n with | .str _ s => s == "n" || s == "z" || s == "c" || s == "v" | _ => false)
      if isProjFn then
        let args' ← args.mapM normWrapper
        let e' := mkAppN fn args'
        let eWhnf ← whnfCore e'
        if eWhnf != e' then return (← normWrapper eWhnf)
        if let some u ← unfoldDefinition? e' then
          let uWhnf ← whnfCore u
          if uWhnf != e' then return (← normWrapper uWhnf)
    return e

partial def evalNatExpr? (e : Expr) : MetaM (Option Nat) := do
  let e := (← instantiateMVars e).consumeMData
  if let some n := e.rawNatLit? then return some n
  if let some n := e.nat? then return some n
  let eWhnf ← whnf e
  if let some n := eWhnf.rawNatLit? then return some n
  if let some n := eWhnf.nat? then return some n
  return none

def getBitVecWidth? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnf ty
  if ty.isAppOfArity ``BitVec 1 then
    evalNatExpr? (ty.getArg! 0)
  else
    return none

/-- Extract a constant `BitVec` literal value `val` if `e` is `OfNat.ofNat val` or `BitVec.ofNat w val`. -/
def getBVConstVal? (e : Expr) : MetaM (Option Nat) := do
  let e := e.consumeMData
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if fn.isConstOf ``OfNat.ofNat && args.size >= 2 then
    evalNatExpr? args[1]!
  else if fn.isConstOf ``BitVec.ofNat && args.size >= 2 then
    evalNatExpr? args[1]!
  else
    return none

/-- Extract a constant shift amount `k : Nat` from either a `Nat` literal or a constant `BitVec` literal. -/
def getShiftConst? (e : Expr) : MetaM (Option Nat) := do
  if let some k ← evalNatExpr? e then
    return some k
  let ty ← inferType e
  if let some w ← getBitVecWidth? ty then
    if let some val ← getBVConstVal? e then
      return some (val % (2 ^ w))
  return none

/-! ### Power-of-two multiplication preprocessing -/

theorem mul_ofNat_two_pow_eq_shl {w : Nat} (x : BitVec w) (k : Nat) :
    x * BitVec.ofNat w (2 ^ k) = x <<< k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem ofNat_two_pow_mul_eq_shl {w : Nat} (x : BitVec w) (k : Nat) :
    BitVec.ofNat w (2 ^ k) * x = x <<< k := by
  rw [BitVec.mul_comm]; exact mul_ofNat_two_pow_eq_shl x k

theorem mul_eq_shl_of_eq_two_pow {w : Nat} (x c : BitVec w) (k : Nat)
    (h : c = BitVec.ofNat w (2 ^ k)) : x * c = x <<< k := by
  subst h; exact mul_ofNat_two_pow_eq_shl x k

theorem mul_eq_shl_of_eq_two_pow' {w : Nat} (x c : BitVec w) (k : Nat)
    (h : c = BitVec.ofNat w (2 ^ k)) : c * x = x <<< k := by
  subst h; exact ofNat_two_pow_mul_eq_shl x k

def bvPow2Log? (e : Expr) : MetaM (Option Nat) := do
  let some v ← getBVConstVal? e | return none
  if v == 0 then return none
  let k := Nat.log2 v
  if 2 ^ k == v then return some k else return none

def mulPow2Step? (w x c : Expr) (left : Bool) : MetaM (Option Simp.Step) := do
  let some k ← bvPow2Log? c | return none
  let thm := if left then ``mul_eq_shl_of_eq_two_pow' else ``mul_eq_shl_of_eq_two_pow
  let pfPartial := mkAppN (mkConst thm) #[w, x, c, mkNatLit k]
  let .forallE _ hTy _ _ ← whnf (← inferType pfPartial) | return none
  let some (_, _, rhsC) := hTy.eq? | return none
  unless ← withTransparency .default (isDefEq c rhsC) do return none
  let pf := mkApp pfPartial (← mkEqRefl c)
  let some (_, _, rhs) := (← inferType pf).eq? | return none
  return some (.done { expr := rhs, proof? := some pf })

/-- Rewrite `x * 2^k` and `2^k * x` (with one non-literal operand) to `x <<< k`. -/
simproc_decl bvMulPow2 ((_ : BitVec _) * (_ : BitVec _)) := fun e => do
  let e := e.consumeMData
  unless e.isAppOfArity ``HMul.hMul 6 do return .continue
  let a := e.appFn!.appArg!
  let b := e.appArg!
  let ty ← whnfR (← inferType e)
  unless ty.isAppOfArity ``BitVec 1 do return .continue
  let w := ty.appArg!
  let aLit := (← getBVConstVal? a).isSome
  let bLit := (← getBVConstVal? b).isSome
  if aLit && bLit then return .continue
  if bLit then
    if let some s ← mulPow2Step? w a b false then return s
  if aLit then
    if let some s ← mulPow2Step? w b a true then return s
  return .continue

/-- Rewrite power-of-two literal multiplications in the target and `Prop` hypotheses to constant
left shifts (`bvMulPow2`), returning `none` if the goal closes. -/
def preprocessMulPow2 (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let hasMul (e : Expr) : Bool := (e.find? fun s => s.isAppOfArity ``HMul.hMul 6).isSome
  let tgt ← instantiateMVars (← g.getType)
  let mut fvars : Array FVarId := #[]
  for d in (← getLCtx) do
    if !d.isImplementationDetail then
      let ty ← instantiateMVars d.type
      if hasMul ty then
        if ← isProp ty then
          fvars := fvars.push d.fvarId
  if !hasMul tgt && fvars.isEmpty then return some g
  let ctx ← Simp.mkContext (config := { failIfUnchanged := false }) (simpTheorems := #[])
    (congrTheorems := ← getSimpCongrTheorems)
  let s ← ({} : Simp.Simprocs).add ``bvMulPow2 (post := true)
  let (r, _) ← simpGoal g ctx #[s] (simplifyTarget := hasMul tgt) (fvarIdsToSimp := fvars)
  return r.map (·.2)

def internBVAtom (w : Nat) (e : Expr) : ReifyM (BVExpr (some w)) := do
  let st ← get
  for i in [0 : st.bvAtoms.size] do
    let (w', e') := st.bvAtoms[i]!
    if w == w' && (← isDefEq e e') then
      return .var w i
  let idx := st.bvAtoms.size
  set { st with bvAtoms := st.bvAtoms.push (w, e) }
  return .var w idx

def internBoolAtom (e : Expr) : ReifyM (BVExpr none) := do
  let st ← get
  for i in [0 : st.boolAtoms.size] do
    if ← isDefEq e st.boolAtoms[i]! then
      return .bvar i
  let idx := st.boolAtoms.size
  set { st with boolAtoms := st.boolAtoms.push e }
  return .bvar idx

def recordUnsupported (opName : String) (e : Expr) : ReifyM Unit := do
  modify fun st => { st with unsupportedTerms := st.unsupportedTerms.push (opName, e) }

mutual

partial def reifyBV (w : Nat) (e : Expr) : ReifyM (BVExpr (some w)) := do
  let e ← normWrapper e
  if let some val ← getBVConstVal? e then
    return .const w val
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let .const n _ := fn then
    if (n == ``HAnd.hAnd && args.size == 6) || (n == ``BitVec.and && args.size == 3) then
      let a ← reifyBV w args[args.size - 2]!
      let b ← reifyBV w args[args.size - 1]!
      return .and a b
    if (n == ``HOr.hOr && args.size == 6) || (n == ``BitVec.or && args.size == 3) then
      let a ← reifyBV w args[args.size - 2]!
      let b ← reifyBV w args[args.size - 1]!
      return .or a b
    if (n == ``HXor.hXor && args.size == 6) || (n == ``BitVec.xor && args.size == 3) then
      let a ← reifyBV w args[args.size - 2]!
      let b ← reifyBV w args[args.size - 1]!
      return .xor a b
    if (n == ``Complement.complement && args.size == 3) || (n == ``BitVec.not && args.size == 2) then
      let a ← reifyBV w args[args.size - 1]!
      return .not a
    if (n == ``HAdd.hAdd && args.size == 6) || (n == ``BitVec.add && args.size == 3) then
      let a ← reifyBV w args[args.size - 2]!
      let b ← reifyBV w args[args.size - 1]!
      return .add a b
    if (n == ``HSub.hSub && args.size == 6) || (n == ``BitVec.sub && args.size == 3) then
      let a ← reifyBV w args[args.size - 2]!
      let b ← reifyBV w args[args.size - 1]!
      return .sub a b
    if (n == ``Neg.neg && args.size == 3) || (n == ``BitVec.neg && args.size == 2) then
      let a ← reifyBV w args[args.size - 1]!
      return .neg a
    if (n == ``HShiftLeft.hShiftLeft && args.size == 6) || (n == ``BitVec.shiftLeft && args.size == 3) then
      let aArg := args[args.size - 2]!
      let kArg := args[args.size - 1]!
      if let some k ← getShiftConst? kArg then
        let a ← reifyBV w aArg
        return .shl a k
      else
        recordUnsupported "variable <<< (non-constant shift)" e
        return (← internBVAtom w e)
    if (n == ``HShiftRight.hShiftRight && args.size == 6) || (n == ``BitVec.ushiftRight && args.size == 3) then
      let aArg := args[args.size - 2]!
      let kArg := args[args.size - 1]!
      if let some k ← getShiftConst? kArg then
        let a ← reifyBV w aArg
        return .lshr a k
      else
        recordUnsupported "variable >>> (non-constant shift)" e
        return (← internBVAtom w e)
    if n == ``BitVec.sshiftRight && args.size == 3 then
      let aArg := args[1]!
      let kArg := args[2]!
      if let some k ← getShiftConst? kArg then
        let a ← reifyBV w aArg
        return .ashr a k
      else
        recordUnsupported "variable sshiftRight (non-constant shift)" e
        return (← internBVAtom w e)
    if (n == ``BitVec.zeroExtend || n == ``BitVec.truncate || n == ``BitVec.setWidth) && args.size == 3 then
      if let some wIn ← evalNatExpr? args[0]! then
        let a ← reifyBV wIn args[2]!
        return .zext w a
    if n == ``BitVec.signExtend && args.size == 3 then
      if let some wIn ← evalNatExpr? args[0]! then
        let a ← reifyBV wIn args[2]!
        return .sext w a
    if n == ``BitVec.extractLsb' && args.size == 4 then
      if let some wIn ← evalNatExpr? args[0]! then
        if let some start ← evalNatExpr? args[1]! then
          if let some len ← evalNatExpr? args[2]! then
            if h : len = w then
              let a ← reifyBV wIn args[3]!
              return h ▸ BVExpr.extract start len a
    if n == ``BitVec.extractLsb && args.size == 4 then
      if let some wIn ← evalNatExpr? args[0]! then
        if let some hi ← evalNatExpr? args[1]! then
          if let some lo ← evalNatExpr? args[2]! then
            let len := hi - lo + 1
            if h : len = w then
              let a ← reifyBV wIn args[3]!
              return h ▸ BVExpr.extract lo len a
    if (n == ``HAppend.hAppend && args.size == 6) || (n == ``BitVec.append && args.size == 4) then
      let aArg := args[args.size - 2]!
      let bArg := args[args.size - 1]!
      let tyA ← inferType aArg
      let tyB ← inferType bArg
      if let some wx ← getBitVecWidth? tyA then
        if let some wy ← getBitVecWidth? tyB then
          if h : wx + wy = w then
            let a ← reifyBV wx aArg
            let b ← reifyBV wy bArg
            return h ▸ BVExpr.append a b
    if n == ``BitVec.replicate && args.size == 3 then
      if let some wIn ← evalNatExpr? args[0]! then
        if let some rep ← evalNatExpr? args[1]! then
          if h : wIn * rep = w then
            let a ← reifyBV wIn args[2]!
            return h ▸ BVExpr.replicate rep a
    if n == ``ite && args.size == 5 then
      let condProp ← normWrapper args[1]!
      if condProp.isAppOfArity ``Eq 3 then
        let eqTy ← whnf (condProp.getArg! 0)
        if eqTy.isConstOf ``Bool then
          let lhs := condProp.getArg! 1
          let rhs ← normWrapper (condProp.getArg! 2)
          if rhs.isConstOf ``Bool.true then
            let c ← reifyBool lhs
            let t ← reifyBV w args[3]!
            let f ← reifyBV w args[4]!
            return .bvIte c t f
    if n == ``HMul.hMul || n == ``BitVec.mul then
      recordUnsupported "* (BitVec multiplication)" e
      return (← internBVAtom w e)
    if n == ``HDiv.hDiv || n == ``BitVec.udiv || n == ``BitVec.sdiv then
      recordUnsupported "/ (BitVec division)" e
      return (← internBVAtom w e)
    if n == ``HMod.hMod || n == ``BitVec.umod || n == ``BitVec.srem || n == ``BitVec.smod then
      recordUnsupported "% (BitVec modulo/remainder)" e
      return (← internBVAtom w e)
  internBVAtom w e

partial def reifyBool (e : Expr) : ReifyM (BVExpr none) := do
  let e ← normWrapper e
  if e.isConstOf ``Bool.true then return .bconst true
  if e.isConstOf ``Bool.false then return .bconst false
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let .const n _ := fn then
    if n == ``Bool.not && args.size == 1 then
      return .bnot (← reifyBool args[0]!)
    if n == ``Bool.and && args.size == 2 then
      return .band (← reifyBool args[0]!) (← reifyBool args[1]!)
    if n == ``Bool.or && args.size == 2 then
      return .bor (← reifyBool args[0]!) (← reifyBool args[1]!)
    if n == ``Bool.xor && args.size == 2 then
      return .bxor (← reifyBool args[0]!) (← reifyBool args[1]!)
    if n == ``BitVec.getLsbD && args.size == 3 then
      if let some w ← evalNatExpr? args[0]! then
        if let some idx ← evalNatExpr? args[2]! then
          let a ← reifyBV w args[1]!
          return .getLsbD a idx
    if n == ``BitVec.msb && args.size == 2 then
      if let some w ← evalNatExpr? args[0]! then
        let a ← reifyBV w args[1]!
        return .msb a
    if n == ``BitVec.ult && args.size == 3 then
      if let some w ← evalNatExpr? args[0]! then
        return .ult (← reifyBV w args[1]!) (← reifyBV w args[2]!)
    if n == ``BitVec.ule && args.size == 3 then
      if let some w ← evalNatExpr? args[0]! then
        return .ule (← reifyBV w args[1]!) (← reifyBV w args[2]!)
    if n == ``BitVec.slt && args.size == 3 then
      if let some w ← evalNatExpr? args[0]! then
        return .slt (← reifyBV w args[1]!) (← reifyBV w args[2]!)
    if n == ``BitVec.sle && args.size == 3 then
      if let some w ← evalNatExpr? args[0]! then
        return .sle (← reifyBV w args[1]!) (← reifyBV w args[2]!)
    if n == ``BEq.beq && args.size == 4 then
      let ty ← whnf args[0]!
      if let some w ← getBitVecWidth? ty then
        return .beq (← reifyBV w args[2]!) (← reifyBV w args[3]!)
      if ty.isConstOf ``Bool then
        return .biff (← reifyBool args[2]!) (← reifyBool args[3]!)
    if n == ``bne && args.size == 4 then
      let ty ← whnf args[0]!
      if let some w ← getBitVecWidth? ty then
        return .bne (← reifyBV w args[2]!) (← reifyBV w args[3]!)
      if ty.isConstOf ``Bool then
        return .bxor (← reifyBool args[2]!) (← reifyBool args[3]!)
    if n == ``ite && args.size == 5 then
      let condProp ← normWrapper args[1]!
      if condProp.isAppOfArity ``Eq 3 then
        let eqTy ← whnf (condProp.getArg! 0)
        if eqTy.isConstOf ``Bool then
          let lhs := condProp.getArg! 1
          let rhs ← normWrapper (condProp.getArg! 2)
          if rhs.isConstOf ``Bool.true then
            return .bite (← reifyBool lhs) (← reifyBool args[3]!) (← reifyBool args[4]!)
  internBoolAtom e

end

partial def reifyGoal? (e : Expr) : ReifyM (Option BVGoal) := do
  let e ← normWrapper e
  if e.isConstOf ``True then return some .top
  if e.isConstOf ``False then return some .bot
  if let .forallE _ dom body _ := e then
    if !body.hasLooseBVars then
      if (← isProp dom) && (← isProp body) then
        if let some p ← reifyGoal? dom then
          if let some q ← reifyGoal? body then
            return some (.imp p q)
  let fn := e.getAppFn.consumeMData
  let args := e.getAppArgs
  if let .const n _ := fn then
    if n == ``Not && args.size == 1 then
      if let some p ← reifyGoal? args[0]! then
        return some (.not p)
    if n == ``And && args.size == 2 then
      if let some p ← reifyGoal? args[0]! then
        if let some q ← reifyGoal? args[1]! then
          return some (.and p q)
    if n == ``Or && args.size == 2 then
      if let some p ← reifyGoal? args[0]! then
        if let some q ← reifyGoal? args[1]! then
          return some (.or p q)
    if n == ``Iff && args.size == 2 then
      if let some p ← reifyGoal? args[0]! then
        if let some q ← reifyGoal? args[1]! then
          return some (.iff p q)
    if n == ``Eq && args.size == 3 then
      let ty ← whnf args[0]!
      if let some w ← getBitVecWidth? ty then
        let a ← reifyBV w args[1]!
        let b ← reifyBV w args[2]!
        return some (.eq a b)
      if ty.isConstOf ``Bool then
        let a ← reifyBool args[1]!
        let b ← reifyBool args[2]!
        return some (.boolEq a b)
    if n == ``Ne && args.size == 3 then
      let ty ← whnf args[0]!
      if let some w ← getBitVecWidth? ty then
        let a ← reifyBV w args[1]!
        let b ← reifyBV w args[2]!
        return some (.ne a b)
      if ty.isConstOf ``Bool then
        let a ← reifyBool args[1]!
        let b ← reifyBool args[2]!
        return some (.boolNe a b)
    if n == ``LT.lt && args.size == 4 then
      if let some w ← getBitVecWidth? args[0]! then
        return some (.lt (← reifyBV w args[2]!) (← reifyBV w args[3]!))
    if n == ``LE.le && args.size == 4 then
      if let some w ← getBitVecWidth? args[0]! then
        return some (.le (← reifyBV w args[2]!) (← reifyBV w args[3]!))
    if n == ``GT.gt && args.size == 4 then
      if let some w ← getBitVecWidth? args[0]! then
        return some (.lt (← reifyBV w args[3]!) (← reifyBV w args[2]!))
    if n == ``GE.ge && args.size == 4 then
      if let some w ← getBitVecWidth? args[0]! then
        return some (.le (← reifyBV w args[3]!) (← reifyBV w args[2]!))
  return none

def formatUnsupportedNote (st : ReifyState) : MessageData :=
  if st.unsupportedTerms.isEmpty then
    m!""
  else
    let items := st.unsupportedTerms.toList.map fun (op, e) => m!"'{op}' in ({e})"
    m!"\nNote: unsupported subterms were abstracted as atomic variables: {MessageData.joinSep items m!", "}"

/-- Collect the target `BVGoal` and any reifiable local context hypotheses, introducing leading
dependent `∀` binders while leaving `Prop` implications for `BVGoal.imp`. -/
def reifyGoalWithHyps (g : MVarId) : MetaM (MVarId × BVGoal × Array Expr × ReifyState) := do
  let mut g := g
  while true do
    let t ← g.getType
    if let .forallE _ dom body _ := t then
      if body.hasLooseBVars || !(← isProp dom) then
        let (_, g') ← g.intro1P
        g := g'
      else
        break
    else
      break
  g.withContext do
    let target ← g.getType
    let (gTargetOpt, st0) ← (reifyGoal? target).run {}
    let some gTarget := gTargetOpt
      | throwError "goal is outside the supported BitVec/Bool propositional grammar:\n  {target}"
    let mut st := st0
    let mut hyps : Array (Expr × BVGoal) := #[]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        if ← isProp decl.type then
          let (ghOpt, st') ← (reifyGoal? decl.type).run st
          if let some gh := ghOpt then
            st := st'
            hyps := hyps.push (decl.toExpr, gh)
    let gFull := hyps.foldr (fun (_, gh) acc => BVGoal.imp gh acc) gTarget
    return (g, gFull, hyps.map (·.1), st)

def computeDimensions (st : ReifyState) : Nat × Nat :=
  let stride := Nat.max st.bvAtoms.size 1
  let maxW := st.bvAtoms.foldl (fun acc (w, _) => Nat.max acc w) 0
  let numVars := Nat.max (2 * maxW * stride) (2 * st.boolAtoms.size)
  (stride, numVars)

def toHexLit (val w : Nat) : String :=
  s!"0x{String.ofList (Nat.toDigits 16 val)}#{w}"

/-- Walk `builderSt` from `rootNode` (`!= 1`) to terminal `0` and reconstruct up to 6 `BitVec` or
`Bool` atom assignments as a diagnostic counterexample witness. -/
def formatCounterexampleNote (stride : Nat) (st : ReifyState) (rootNode : Nat)
    (builderSt : ROBDDBuilderState) : MessageData :=
  if rootNode == 1 then
    m!""
  else Id.run do
    let mut trueVars : Std.HashMap Nat Unit := {}
    let mut u := rootNode
    let mut fuel := builderSt.numVars + 2
    while u > 1 && fuel > 0 do
      fuel := fuel - 1
      let nd := builderSt.getNode u
      if nd.lo != 1 then
        u := nd.lo
      else
        trueVars := trueVars.insert nd.var ()
        u := nd.hi
    let mut items : Array MessageData := #[]
    let maxItems := 6
    for idx in [0 : st.bvAtoms.size] do
      if items.size < maxItems then
        let (w, expr) := st.bvAtoms[idx]!
        let mut val : Nat := 0
        for i in [0 : w] do
          if trueVars.contains (bitVar stride idx i) then
            val := val + (1 <<< i)
        items := items.push m!"{expr} = {toHexLit val w}"
    for bidx in [0 : st.boolAtoms.size] do
      if items.size < maxItems then
        let expr := st.boolAtoms[bidx]!
        let bval := trueVars.contains (boolVar bidx)
        items := items.push m!"{expr} = {bval}"
    let totalAtoms := st.bvAtoms.size + st.boolAtoms.size
    let moreSuffix :=
      if totalAtoms > maxItems then m!", … (+{totalAtoms - maxItems} more)" else m!""
    let witnessLine :=
      if items.isEmpty then m!""
      else m!"\ncounterexample witness: {MessageData.joinSep items.toList m!", "}{moreSuffix}"
    return m!"{witnessLine}\nhint: if these atoms are constrained by local hypotheses, rewrite or substitute them before calling `bv_robdd` / `bv_slice`, or use `bv_solve`"

def elabBVSlice : TacticM Unit := do
  let g ← getMainGoal
  let some g ← preprocessMulPow2 g | replaceMainGoal []
  let (g, gFull, hypFVars, st) ← reifyGoalWithHyps g
  if let some arithOp := gFull.firstArithOp? then
    throwError "bv_slice: operator '{arithOp}' requires ripple-carry reasoning and is outside the Tier 1 pure bit-slice grammar; use 'bv_robdd' instead"
  let (stride, numVars) := computeDimensions st
  let fuel := numVars + 2
  if !checkSlice fuel stride numVars gFull then
    let (rootNode, builderSt) := (simCompileBV stride gFull.toBExpr).run (ROBDDBuilderState.init numVars)
    throwError "bv_slice failed: goal is not a bit-slice tautology{formatUnsupportedNote st}{formatCounterexampleNote stride st rootNode builderSt}"
  g.withContext do
    let envExpr := envToExpr st.bvAtoms st.boolAtoms
    let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let pfFull := mkAppN (mkConst ``prove_of_checkSlice)
      #[envExpr, toExpr fuel, toExpr stride, toExpr numVars, bvGoalToExpr gFull, reflTrue]
    let pf := mkAppN pfFull hypFVars
    g.assign pf

def elabBVROBDD : TacticM Unit := do
  let g ← getMainGoal
  let some g ← preprocessMulPow2 g | replaceMainGoal []
  let (g, gFull, hypFVars, st) ← reifyGoalWithHyps g
  let (stride, numVars) := computeDimensions st
  let (rootNode, builderSt) := (simCompileBV stride gFull.toBExpr).run (ROBDDBuilderState.init numVars)
  if rootNode != 1 then
    throwError "bv_robdd failed: goal is not a tautology (ROBDD reduced to node {rootNode} ≠ 1){formatUnsupportedNote st}{formatCounterexampleNote stride st rootNode builderSt}"
  let (dag, claims) := finalizeWitness builderSt
  g.withContext do
    let envExpr := envToExpr st.bvAtoms st.boolAtoms
    let dagExpr := binTreeToExpr (mkConst ``BDDNode) bddNodeToExpr dag
    let claimsExpr := binTreeToExpr (mkApp (mkConst ``List [0]) (mkConst ``GateStep))
      (listToExpr (mkConst ``GateStep) gateStepToExpr) claims
    let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let pfFull := mkAppN (mkConst ``prove_of_checkROBDD)
      #[envExpr, toExpr stride, toExpr numVars, dagExpr, claimsExpr, bvGoalToExpr gFull, reflTrue]
    let pf := mkAppN pfFull hypFVars
    g.assign pf

/-- Kernel-reflective per-lane bit-slicer (`Eq.refl true`) for bitwise operations, constant shifts,
`++`, `extractLsb'`, `zeroExtend`, `signExtend`, `replicate`, `getLsbD`, and `msb`. -/
elab "bv_slice" : tactic => elabBVSlice

/-- Kernel-reflective witnessed ROBDD decision procedure (`Eq.refl true`) supporting the bit-slice
grammar together with ripple-carry `+`, `-`, `neg`, `<`, `≤`, `ult`, `ule`, `slt`, `sle`, `ite`,
`AddWithCarry64`/`32`, `ConditionHolds`, and propositional hypotheses. -/
elab "bv_robdd" : tactic => elabBVROBDD

end

end ProofLib.BV.ROBDD
