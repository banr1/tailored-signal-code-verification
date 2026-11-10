/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64

/-!
# Radix-Tree Primitives, Register Files, and Cache-Line Memory Core

Defines closure-free data structures and strict WHNF-forcing combinators for kernel-evaluated
ARM64 execution:
- `BinTree α`: a low-bit-first (`k % 2`) path-compressed binary radix tree with $O(d)$ lookup and
  update.
- `FastRegs`: depth-5 (`32`-slot) GPR and SIMD register files proved extensionally equal to
  `Arm64.RegFile` and `Arm64.VRegFile`.
- `Line64` and depth-58 `BinTree Line64`: 64-byte cache lines with line-batched cell writes
  (`setCellsAt`) and lazy 64-byte uniform region loads (`loadRegionFast`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemAux

open Arm64

/-!
CPS value-forcing combinators (`withForced*`) match values to constructor WHNF before passing them
to `k` so lazy thunks do not accumulate across multi-step kernel reduction.
-/

@[inline] def withForcedNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

@[simp] theorem withForcedNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    withForcedNat n k = k n := by
  cases n <;> rfl

@[inline] def withForcedBool {α : Type} (b : Bool) (k : Bool → α) : α :=
  match b with
  | false => k false
  | true => k true

@[simp] theorem withForcedBool_eq {α : Type} (b : Bool) (k : Bool → α) :
    withForcedBool b k = k b := by
  cases b <;> rfl

/-- Reconstruct `v` from `v.toNat` in WHNF so `Fin.isLt` proof terms do not accumulate. -/
@[inline] def withForcedBV {w : Nat} {α : Type} (v : BitVec w) (k : BitVec w → α) : α :=
  match v.toNat with
  | 0 => k 0#w
  | m + 1 => k (BitVec.ofNat w (Nat.succ m))

private theorem bv_clean_app {w : Nat} {α : Type} (v : BitVec w) (k : BitVec w → α) :
    (match v.toNat with | 0 => k 0#w | m + 1 => k (BitVec.ofNat w (Nat.succ m))) = k v := by
  cases ht : v.toNat with
  | zero => rw [show v = 0#w from BitVec.eq_of_toNat_eq (by simp [ht])]
  | succ m =>
    rw [show v = BitVec.ofNat w (Nat.succ m) from
      BitVec.eq_of_toNat_eq (by simp [ht, Nat.mod_eq_of_lt (ht ▸ v.isLt)])]

@[simp] theorem withForcedBV_eq {w : Nat} {α : Type} (v : BitVec w) (k : BitVec w → α) :
    withForcedBV v k = k v := bv_clean_app v k

@[inline] def withForcedPerm {α : Type} (p : Perm) (k : Perm → α) : α :=
  withForcedBool p.r fun r =>
  withForcedBool p.w fun w =>
  withForcedBool p.x fun x =>
  withForcedBool p.lazyFree fun lf =>
  withForcedBool p.anon fun an =>
    k ⟨r, w, x, lf, an⟩

@[simp] theorem withForcedPerm_eq {α : Type} (p : Perm) (k : Perm → α) :
    withForcedPerm p k = k p := by
  rcases p with ⟨_ | _, _ | _, _ | _, _ | _, _ | _⟩ <;> rfl

@[inline] def withForcedPermOpt {α : Type} (p : Option Perm) (k : Option Perm → α) : α :=
  match p with
  | none => k none
  | some q => withForcedPerm q fun q' => k (some q')

@[simp] theorem withForcedPermOpt_eq {α : Type} (p : Option Perm) (k : Option Perm → α) :
    withForcedPermOpt p k = k p := by
  cases p with
  | none => rfl
  | some q => simp [withForcedPermOpt]

@[inline] def withForcedPState {α : Type} (ps : PState) (k : PState → α) : α :=
  withForcedBool ps.n fun n =>
  withForcedBool ps.z fun z =>
  withForcedBool ps.c fun c =>
  withForcedBool ps.v fun v =>
    k ⟨n, z, c, v⟩

@[simp] theorem withForcedPState_eq {α : Type} (ps : PState) (k : PState → α) :
    withForcedPState ps k = k ps := by
  rcases ps with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- Map `ps` to one of the 16 ground `PState` constants without CPS closures. -/
def canonPState (ps : PState) : PState :=
  match ps.n, ps.z, ps.c, ps.v with
  | false, false, false, false => ⟨false, false, false, false⟩ | false, false, false, true => ⟨false, false, false, true⟩
  | false, false, true,  false => ⟨false, false, true,  false⟩ | false, false, true,  true => ⟨false, false, true,  true⟩
  | false, true,  false, false => ⟨false, true,  false, false⟩ | false, true,  false, true => ⟨false, true,  false, true⟩
  | false, true,  true,  false => ⟨false, true,  true,  false⟩ | false, true,  true,  true => ⟨false, true,  true,  true⟩
  | true,  false, false, false => ⟨true,  false, false, false⟩ | true,  false, false, true => ⟨true,  false, false, true⟩
  | true,  false, true,  false => ⟨true,  false, true,  false⟩ | true,  false, true,  true => ⟨true,  false, true,  true⟩
  | true,  true,  false, false => ⟨true,  true,  false, false⟩ | true,  true,  false, true => ⟨true,  true,  false, true⟩
  | true,  true,  true,  false => ⟨true,  true,  true,  false⟩ | true,  true,  true,  true => ⟨true,  true,  true,  true⟩

@[simp] theorem canonPState_eq (ps : PState) : canonPState ps = ps := by
  rcases ps with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- Memory cell entry `(perm?, byte)` as in `Arm64.Memory.cells`. -/
abbrev Cell := Option Perm × BitVec 8

@[inline] def withForcedCell {α : Type} (c : Cell) (k : Cell → α) : α :=
  withForcedPermOpt c.1 fun p =>
  withForcedBV c.2 fun b =>
    k (p, b)

@[simp] theorem withForcedCell_eq {α : Type} (c : Cell) (k : Cell → α) :
    withForcedCell c k = k c := by
  rcases c with ⟨p, b⟩
  simp [withForcedCell]

@[inline] def withForcedExecStatus {α : Type} (st : ExecStatus) (k : ExecStatus → α) : α :=
  match st with
  | .Running => k .Running
  | .Halted => k .Halted
  | .Exited code => withForcedBV code fun c => k (.Exited c)
  | .Signaled sig => withForcedBV sig fun s => k (.Signaled s)
  | .Panicked => k .Panicked
  | .OutOfMemory => k .OutOfMemory
  | .Exception msg => k (.Exception msg)

@[simp] theorem withForcedExecStatus_eq {α : Type} (st : ExecStatus) (k : ExecStatus → α) :
    withForcedExecStatus st k = k st := by
  cases st <;> simp [withForcedExecStatus]

def withForcedListSpine {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k => withForcedListSpine xs fun xs' => k (x :: xs')

@[simp] theorem withForcedListSpine_eq {α β : Type} (xs : List α) (k : List α → β) :
    withForcedListSpine xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => exact ih (fun xs' => k (x :: xs'))

def withForcedIvList {β : Type} : List (Nat × Nat) → (List (Nat × Nat) → β) → β
  | [], k => k []
  | (lo, hi) :: xs, k =>
    withForcedNat lo fun lo' =>
    withForcedNat hi fun hi' =>
    withForcedIvList xs fun xs' =>
      k ((lo', hi') :: xs')

@[simp] theorem withForcedIvList_eq {β : Type} (xs : List (Nat × Nat)) (k : List (Nat × Nat) → β) :
    withForcedIvList xs k = k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨lo, hi⟩
    simp only [withForcedIvList, withForcedNat_eq]
    exact ih (fun xs' => k ((lo, hi) :: xs'))

/-- Low-bit-first path-compressed binary radix tree: `k % 2` selects the left (`0`) or right (`1`)
child, and `.twig kj v` stores a singleton key-value pair at any depth. -/
inductive BinTree (α : Type) where
  | empty  : BinTree α
  | twig   : Nat → α → BinTree α
  | branch : BinTree α → BinTree α → BinTree α
  deriving DecidableEq, Repr, Inhabited

@[inline] def withForcedBinTree {α β : Type} (t : BinTree α) (k : BinTree α → β) : β :=
  match t with
  | .empty => k .empty
  | .twig j v => k (.twig j v)
  | .branch lo hi => k (.branch lo hi)

@[simp] theorem withForcedBinTree_eq {α β : Type} (t : BinTree α) (k : BinTree α → β) :
    withForcedBinTree t k = k t := by
  cases t <;> rfl

@[inline] def mkTwig {α : Type} (k : Nat) (v : α) : BinTree α :=
  match k with
  | 0 => .twig 0 v
  | m + 1 => .twig (Nat.succ m) v

@[simp] theorem mkTwig_eq {α : Type} (k : Nat) (v : α) : mkTwig k v = .twig k v := by
  cases k <;> rfl

@[inline] def mkBranchL {α : Type} (c hi : BinTree α) : BinTree α :=
  match c with
  | .empty => .branch .empty hi
  | .twig j u => .branch (.twig j u) hi
  | .branch a b => .branch (.branch a b) hi

@[simp] theorem mkBranchL_eq {α : Type} (c hi : BinTree α) : mkBranchL c hi = .branch c hi := by
  cases c <;> rfl

@[inline] def mkBranchR {α : Type} (lo c : BinTree α) : BinTree α :=
  match c with
  | .empty => .branch lo .empty
  | .twig j u => .branch lo (.twig j u)
  | .branch a b => .branch lo (.branch a b)

@[simp] theorem mkBranchR_eq {α : Type} (lo c : BinTree α) : mkBranchR lo c = .branch lo c := by
  cases c <;> rfl

/-- `btGet d tr k` looks up key `k` in `tr` up to depth `d`. -/
def btGet {α : Type} : Nat → BinTree α → Nat → Option α
  | _, .empty, _ => none
  | _, .twig kj v, k => if Nat.beq k kj then some v else none
  | 0, .branch _ _, _ => none
  | d + 1, .branch lo hi, k =>
    if Nat.beq (Nat.mod k 2) 0 then btGet d lo (Nat.div k 2) else btGet d hi (Nat.div k 2)

/-- `btSet d tr k v` updates key `k` to `v` in `tr` at depth `d`. -/
def btSet {α : Type} : Nat → BinTree α → Nat → α → BinTree α
  | 0, _, k, v => mkTwig k v
  | _ + 1, .empty, k, v => mkTwig k v
  | d + 1, .twig kj u, k, v =>
    if Nat.beq k kj then .twig kj v
    else if Nat.beq (Nat.mod kj 2) 0 then
      if Nat.beq (Nat.mod k 2) 0 then
        mkBranchL (btSet d (mkTwig (Nat.div kj 2) u) (Nat.div k 2) v) .empty
      else
        .branch (mkTwig (Nat.div kj 2) u) (mkTwig (Nat.div k 2) v)
    else
      if Nat.beq (Nat.mod k 2) 0 then
        .branch (mkTwig (Nat.div k 2) v) (mkTwig (Nat.div kj 2) u)
      else
        mkBranchR .empty (btSet d (mkTwig (Nat.div kj 2) u) (Nat.div k 2) v)
  | d + 1, .branch lo hi, k, v =>
    if Nat.beq (Nat.mod k 2) 0 then
      mkBranchL (btSet d lo (Nat.div k 2) v) hi
    else
      mkBranchR lo (btSet d hi (Nat.div k 2) v)

@[simp] theorem btGet_empty {α : Type} (d k : Nat) :
    btGet d (.empty : BinTree α) k = none := by
  cases d <;> rfl

@[simp] theorem btGet_twig {α : Type} (d kj k : Nat) (v : α) :
    btGet d (.twig kj v) k = if Nat.beq k kj then some v else none := by
  cases d <;> rfl

private theorem nat_beq_self (k : Nat) : Nat.beq k k = true :=
  Nat.beq_eq.mpr rfl

private theorem nat_beq_iff_div_mod (a b : Nat) :
    Nat.beq a b = (Nat.beq (Nat.mod a 2) (Nat.mod b 2) && Nat.beq (Nat.div a 2) (Nat.div b 2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Nat.beq_eq]
  have : a.mod 2 = a % 2 := rfl
  have : b.mod 2 = b % 2 := rfl
  have : a.div 2 = a / 2 := rfl
  have : b.div 2 = b / 2 := rfl
  omega

private def btChildren {α : Type} : BinTree α → BinTree α × BinTree α
  | .empty => (.empty, .empty)
  | .twig kj u =>
    if Nat.beq (Nat.mod kj 2) 0 then (.twig (Nat.div kj 2) u, .empty)
    else (.empty, .twig (Nat.div kj 2) u)
  | .branch lo hi => (lo, hi)

private theorem btGet_succ {α : Type} (d : Nat) (tr : BinTree α) (j : Nat) :
    btGet (d + 1) tr j =
      if Nat.beq (Nat.mod j 2) 0 then btGet d (btChildren tr).1 (Nat.div j 2)
      else btGet d (btChildren tr).2 (Nat.div j 2) := by
  cases tr with
  | empty =>
    cases Nat.beq (Nat.mod j 2) 0 <;> simp [btGet, btChildren]
  | branch lo hi =>
    simp [btGet, btChildren]
  | twig kj u =>
    simp only [btGet, btChildren]
    rw [nat_beq_iff_div_mod j kj]
    cases hj : Nat.beq (Nat.mod j 2) 0 <;> cases hk : Nat.beq (Nat.mod kj 2) 0
    · have hmod_eq : Nat.mod j 2 = Nat.mod kj 2 := by
        have h1 : j % 2 ≠ 0 := fun h => by
          have hb : Nat.beq (Nat.mod j 2) 0 = true := Nat.beq_eq.mpr h
          rw [hb] at hj; cases hj
        have h2 : kj % 2 ≠ 0 := fun h => by
          have hb : Nat.beq (Nat.mod kj 2) 0 = true := Nat.beq_eq.mpr h
          rw [hb] at hk; cases hk
        change j % 2 = kj % 2; omega
      simp [hmod_eq]
    · have hne : Nat.beq (Nat.mod j 2) (Nat.mod kj 2) = false := by
        apply Bool.eq_false_iff.mpr; intro heq
        have h1 := Nat.beq_eq.mp hk; have h2 := Nat.beq_eq.mp heq
        rw [h1] at h2; rw [Nat.beq_eq.mpr h2] at hj; cases hj
      simp [hne]
    · have hne : Nat.beq (Nat.mod j 2) (Nat.mod kj 2) = false := by
        apply Bool.eq_false_iff.mpr; intro heq
        have h1 := Nat.beq_eq.mp hj; have h2 := Nat.beq_eq.mp heq
        rw [h1] at h2; rw [Nat.beq_eq.mpr h2.symm] at hk; cases hk
      simp [hne]
    · have hmod_eq : Nat.mod j 2 = Nat.mod kj 2 := by
        rw [Nat.beq_eq.mp hj, Nat.beq_eq.mp hk]
      simp [hmod_eq]

private theorem btGet_btSet_succ {α : Type} (d : Nat) (tr : BinTree α) (k : Nat) (v : α) (j : Nat) :
    btGet (d + 1) (btSet (d + 1) tr k v) j =
      if Nat.beq (Nat.mod j 2) 0 then
        btGet d (if Nat.beq (Nat.mod k 2) 0 then btSet d (btChildren tr).1 (Nat.div k 2) v
                 else (btChildren tr).1) (Nat.div j 2)
      else
        btGet d (if Nat.beq (Nat.mod k 2) 0 then (btChildren tr).2
                 else btSet d (btChildren tr).2 (Nat.div k 2) v) (Nat.div j 2) := by
  have hbr (lo hi : BinTree α) :
      btGet (d + 1) (.branch lo hi) j =
        if Nat.beq (Nat.mod j 2) 0 then btGet d lo (Nat.div j 2)
        else btGet d hi (Nat.div j 2) := by
    simp [btGet]
  have htw (c : BinTree α × BinTree α)
      (hc : c = if Nat.beq (Nat.mod k 2) 0 then (.twig (Nat.div k 2) v, .empty)
                else (.empty, .twig (Nat.div k 2) v)) :
      btGet (d + 1) (.twig k v) j =
        if Nat.beq (Nat.mod j 2) 0 then btGet d c.1 (Nat.div j 2)
        else btGet d c.2 (Nat.div j 2) := by
    rw [btGet_succ d (.twig k v) j, btChildren, ← hc]
  cases tr with
  | empty =>
    simp only [btSet, mkTwig_eq, btChildren]
    cases hk : Nat.beq (Nat.mod k 2) 0
    · exact htw (.empty, btSet d .empty (Nat.div k 2) v) (by cases d <;> simp [hk, btSet])
    · exact htw (btSet d .empty (Nat.div k 2) v, .empty) (by cases d <;> simp [hk, btSet])
  | branch lo hi =>
    simp only [btSet, btChildren, mkBranchL_eq, mkBranchR_eq]
    cases hk : Nat.beq (Nat.mod k 2) 0 <;> simp [hbr]
  | twig kj u =>
    simp only [btSet, btChildren]
    cases hkkj : Nat.beq k kj
    · simp only [Bool.false_eq_true, ↓reduceIte, mkTwig_eq, mkBranchL_eq, mkBranchR_eq]
      cases hkj : Nat.beq (Nat.mod kj 2) 0 <;> cases hk : Nat.beq (Nat.mod k 2) 0
      · simp [hbr]
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hbr]; cases d <;> simp [btSet, mkTwig_eq]
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hbr]; cases d <;> simp [btSet, mkTwig_eq]
      · simp [hbr]
    · have heq : k = kj := Nat.beq_eq.mp hkkj
      subst heq
      simp only [↓reduceIte]
      cases hk : Nat.beq (Nat.mod k 2) 0
      · exact htw (.empty, btSet d (.twig (Nat.div k 2) u) (Nat.div k 2) v)
          (by cases d <;> simp [hk, btSet])
      · exact htw (btSet d (.twig (Nat.div k 2) u) (Nat.div k 2) v, .empty)
          (by cases d <;> simp [hk, btSet])

theorem btGet_btSet_same' {α : Type} (d k : Nat) (tr : BinTree α) (v : α) :
    btGet d (btSet d tr k v) k = some v := by
  induction d generalizing tr k with
  | zero => simp [btSet]
  | succ d ih =>
    rw [btGet_btSet_succ]
    cases hk : Nat.beq (Nat.mod k 2) 0 <;> simp [ih]

theorem btGet_btSet_same {α : Type} (d k : Nat) (tr : BinTree α) (v : α) (_hk : k < 2 ^ d) :
    btGet d (btSet d tr k v) k = some v :=
  btGet_btSet_same' d k tr v

theorem btGet_btSet_ne {α : Type} (d k j : Nat) (tr : BinTree α) (v : α)
    (hk : k < 2 ^ d) (hj : j < 2 ^ d) (hne : k ≠ j) :
    btGet d (btSet d tr k v) j = btGet d tr j := by
  induction d generalizing tr k j with
  | zero => omega
  | succ d ih =>
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by omega
    have hk' : Nat.div k 2 < 2 ^ d := by change k / 2 < 2 ^ d; omega
    have hj' : Nat.div j 2 < 2 ^ d := by change j / 2 < 2 ^ d; omega
    rw [btGet_btSet_succ, btGet_succ d tr j]
    cases hk0 : Nat.beq (Nat.mod k 2) 0 <;> cases hj0 : Nat.beq (Nat.mod j 2) 0
    · have hdiv : Nat.div k 2 ≠ Nat.div j 2 := by
        have h1 : k % 2 ≠ 0 := fun h => by
          have hb : Nat.beq (Nat.mod k 2) 0 = true := Nat.beq_eq.mpr h
          rw [hb] at hk0; cases hk0
        have h2 : j % 2 ≠ 0 := fun h => by
          have hb : Nat.beq (Nat.mod j 2) 0 = true := Nat.beq_eq.mpr h
          rw [hb] at hj0; cases hj0
        change k / 2 ≠ j / 2; omega
      simp [ih (Nat.div k 2) (Nat.div j 2) (btChildren tr).2 hk' hj' hdiv]
    · simp
    · simp
    · have hdiv : Nat.div k 2 ≠ Nat.div j 2 := by
        have h1 : k % 2 = 0 := Nat.beq_eq.mp hk0
        have h2 : j % 2 = 0 := Nat.beq_eq.mp hj0
        change k / 2 ≠ j / 2; omega
      simp [ih (Nat.div k 2) (Nat.div j 2) (btChildren tr).1 hk' hj' hdiv]

theorem btGet_btSet_btSet_same_key {α : Type} (d k j : Nat) (tr : BinTree α) (v1 v2 : α)
    (hk : k < 2 ^ d) (hj : j < 2 ^ d) :
    btGet d (btSet d (btSet d tr k v1) k v2) j = btGet d (btSet d tr k v2) j := by
  by_cases h : k = j
  · subst h
    rw [btGet_btSet_same d k _ v2 hk, btGet_btSet_same d k _ v2 hk]
  · rw [btGet_btSet_ne d k j _ v2 hk hj h, btGet_btSet_ne d k j _ v1 hk hj h,
      btGet_btSet_ne d k j _ v2 hk hj h]

/-- Depth-5 (`32`-slot) GPR and SIMD register files backed by `BinTree`. -/
structure FastRegs where
  gprs  : BinTree (BitVec 64) := .empty
  vregs : BinTree (BitVec 128) := .empty
  deriving DecidableEq, Repr, Inhabited

@[inline] def withForcedFastRegs {α : Type} (fr : FastRegs) (k : FastRegs → α) : α :=
  match fr with
  | ⟨gprs, vregs⟩ => k ⟨gprs, vregs⟩

@[simp] theorem withForcedFastRegs_eq {α : Type} (fr : FastRegs) (k : FastRegs → α) :
    withForcedFastRegs fr k = k fr := by
  cases fr; rfl

namespace FastRegs

def empty : FastRegs := ⟨.empty, .empty⟩

@[inline] def btSetCleanBV {w : Nat} (d : Nat) (tr : BinTree (BitVec w)) (k : Nat)
    (val : BitVec w) : BinTree (BitVec w) :=
  match val.toNat with
  | 0 => btSet d tr k 0#w
  | m + 1 => btSet d tr k (BitVec.ofNat w (Nat.succ m))

@[simp] theorem btSetCleanBV_eq {w : Nat} (d : Nat) (tr : BinTree (BitVec w)) (k : Nat)
    (val : BitVec w) : btSetCleanBV d tr k val = btSet d tr k val :=
  bv_clean_app val (btSet d tr k)

@[inline] def mkFastRegsG (g : BinTree (BitVec 64)) (v : BinTree (BitVec 128)) : FastRegs :=
  match g with
  | .empty => ⟨.empty, v⟩
  | .twig j u => ⟨.twig j u, v⟩
  | .branch a b => ⟨.branch a b, v⟩

@[simp] theorem mkFastRegsG_eq (g : BinTree (BitVec 64)) (v : BinTree (BitVec 128)) :
    mkFastRegsG g v = ⟨g, v⟩ := by cases g <;> rfl

@[inline] def mkFastRegsV (g : BinTree (BitVec 64)) (v : BinTree (BitVec 128)) : FastRegs :=
  match v with
  | .empty => ⟨g, .empty⟩
  | .twig j u => ⟨g, .twig j u⟩
  | .branch a b => ⟨g, .branch a b⟩

@[simp] theorem mkFastRegsV_eq (g : BinTree (BitVec 64)) (v : BinTree (BitVec 128)) :
    mkFastRegsV g v = ⟨g, v⟩ := by cases v <;> rfl

def readGpr (fr : FastRegs) (idx : BitVec 5) : BitVec 64 :=
  (btGet 5 fr.gprs idx.toNat).getD 0#64

def writeGpr (fr : FastRegs) (idx : BitVec 5) (val : BitVec 64) : FastRegs :=
  match fr with
  | ⟨gprs, vregs⟩ => mkFastRegsG (btSetCleanBV 5 gprs idx.toNat val) vregs

def readVReg (fr : FastRegs) (idx : BitVec 5) : BitVec 128 :=
  (btGet 5 fr.vregs idx.toNat).getD 0#128

def writeVReg (fr : FastRegs) (idx : BitVec 5) (val : BitVec 128) : FastRegs :=
  match fr with
  | ⟨gprs, vregs⟩ => mkFastRegsV gprs (btSetCleanBV 5 vregs idx.toNat val)

def Agrees (fr : FastRegs) (rf : RegFile) (vf : VRegFile) : Prop :=
  (∀ i : BitVec 5, fr.readGpr i = rf.read i) ∧
  (∀ i : BitVec 5, fr.readVReg i = vf.read i)

theorem empty_agrees : FastRegs.empty.Agrees RegFile.empty VRegFile.empty := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem readGpr_eq {fr : FastRegs} {rf : RegFile} {vf : VRegFile}
    (h : fr.Agrees rf vf) (idx : BitVec 5) :
    fr.readGpr idx = rf.read idx :=
  h.1 idx

theorem readVReg_eq {fr : FastRegs} {rf : RegFile} {vf : VRegFile}
    (h : fr.Agrees rf vf) (idx : BitVec 5) :
    fr.readVReg idx = vf.read idx :=
  h.2 idx

theorem writeGpr_agrees {fr : FastRegs} {rf : RegFile} {vf : VRegFile}
    (h : fr.Agrees rf vf) (idx : BitVec 5) (val : BitVec 64) :
    (fr.writeGpr idx val).Agrees (rf.write idx val) vf := by
  rcases fr with ⟨gprs, vregs⟩
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [writeGpr, mkFastRegsG_eq, btSetCleanBV_eq, readGpr, RegFile.write, RegFile.read]
    by_cases heq : i = idx
    · subst heq
      simp only [↓reduceIte, btGet_btSet_same', Option.getD_some]
    · have hne : idx.toNat ≠ i.toNat := fun hn => heq (BitVec.eq_of_toNat_eq hn.symm)
      simp only [heq, ↓reduceIte]
      rw [btGet_btSet_ne 5 idx.toNat i.toNat gprs val idx.isLt i.isLt hne]
      exact h.1 i
  · simp only [writeGpr, mkFastRegsG_eq, btSetCleanBV_eq, readVReg]
    exact h.2 i

theorem writeVReg_agrees {fr : FastRegs} {rf : RegFile} {vf : VRegFile}
    (h : fr.Agrees rf vf) (idx : BitVec 5) (val : BitVec 128) :
    (fr.writeVReg idx val).Agrees rf (vf.write idx val) := by
  rcases fr with ⟨gprs, vregs⟩
  refine ⟨fun i => ?_, fun i => ?_⟩
  · simp only [writeVReg, mkFastRegsV_eq, btSetCleanBV_eq, readGpr]
    exact h.1 i
  · simp only [writeVReg, mkFastRegsV_eq, btSetCleanBV_eq, readVReg, VRegFile.write, VRegFile.read]
    by_cases heq : i = idx
    · subst heq
      simp only [↓reduceIte, btGet_btSet_same', Option.getD_some]
    · have hne : idx.toNat ≠ i.toNat := fun hn => heq (BitVec.eq_of_toNat_eq hn.symm)
      simp only [heq, ↓reduceIte]
      rw [btGet_btSet_ne 5 idx.toNat i.toNat vregs val idx.isLt i.isLt hne]
      exact h.2 i

end FastRegs

/-- 64-byte (`2 ^ 6`) cache line indexed by `addr % 64` at depth `6`. -/
abbrev Line64 := BinTree Cell

@[inline] def setCleanBV8 (ln : Line64) (lo : Nat) (p : Option Perm) (b : BitVec 8) : Line64 :=
  match b.toNat with
  | 0 => btSet 6 ln lo (p, 0#8)
  | m + 1 => btSet 6 ln lo (p, BitVec.ofNat 8 (Nat.succ m))

@[simp] theorem setCleanBV8_eq (ln : Line64) (lo : Nat) (p : Option Perm) (b : BitVec 8) :
    setCleanBV8 ln lo p b = btSet 6 ln lo (p, b) :=
  bv_clean_app b (fun x => btSet 6 ln lo (p, x))

/-- Strict closure-free cell update in `Line64` at byte offset `lo < 64`. -/
def btSet6Cell (ln : Line64) (lo : Nat) (p : Option Perm) (b : BitVec 8) : Line64 :=
  match ln with
  | .empty => match p with | none => setCleanBV8 .empty lo none b | some q => setCleanBV8 .empty lo (some q) b
  | .twig j u => match p with | none => setCleanBV8 (.twig j u) lo none b | some q => setCleanBV8 (.twig j u) lo (some q) b
  | .branch x y => match p with | none => setCleanBV8 (.branch x y) lo none b | some q => setCleanBV8 (.branch x y) lo (some q) b

@[simp] theorem btSet6Cell_eq (ln : Line64) (lo : Nat) (p : Option Perm) (b : BitVec 8) :
    btSet6Cell ln lo p b = btSet 6 ln lo (p, b) := by
  cases ln <;> cases p <;> simp [btSet6Cell]

/-- Strict closure-free cache-line update in `lines` at line index `hi < 2 ^ 58`. -/
def btSet58Line (lines : BinTree Line64) (hi : Nat) (ln : Line64) : BinTree Line64 :=
  match ln with
  | .empty => btSet 58 lines hi .empty
  | .twig j u => btSet 58 lines hi (.twig j u)
  | .branch x y => btSet 58 lines hi (.branch x y)

@[simp] theorem btSet58Line_eq (lines : BinTree Line64) (hi : Nat) (ln : Line64) :
    btSet58Line lines hi ln = btSet 58 lines hi ln := by
  cases ln <;> rfl

@[inline] def lineByteCanRead (sb top addr : Nat) (ln : Line64) (lo : Nat) : Bool :=
  match btGet 6 ln lo with
  | some (some p, _) => p.r && !p.lazyFree
  | some (none, _) => false
  | none => Nat.ble sb addr && Nat.blt addr top

@[inline] def lineByteCanWrite (sb top addr : Nat) (ln : Line64) (lo : Nat) : Bool :=
  match btGet 6 ln lo with
  | some (some p, _) => p.w && !p.x
  | some (none, _) => false
  | none => Nat.ble sb addr && Nat.blt addr top

def lineCanReadAux (sb top : Nat) (ln : Line64) (addr lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    lineByteCanRead sb top addr ln lo &&
      lineCanReadAux sb top ln (Nat.add addr 1) (Nat.add lo 1) n

def lineCanWriteAux (sb top : Nat) (ln : Line64) (addr lo : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    lineByteCanWrite sb top addr ln lo &&
      lineCanWriteAux sb top ln (Nat.add addr 1) (Nat.add lo 1) n

@[inline] def lineCellWritePerm (sb top addr : Nat) (ln : Line64) (lo : Nat) : Option Perm :=
  match btGet 6 ln lo with
  | some (some p, _) =>
    if !p.lazyFree then some p
    else match p with | ⟨r, w, x, _, an⟩ => some ⟨r, w, x, false, an⟩
  | some (none, _) => none
  | none =>
    if Nat.ble sb addr && Nat.blt addr top then some Perm.rw else none

@[inline] def writeLineByte (sb top addr : Nat) (ln : Line64) (lo : Nat) (b : BitVec 8) : Line64 :=
  btSet6Cell ln lo (lineCellWritePerm sb top addr ln lo) b

/-- Look up cell at `addr < 2 ^ 64` via line `addr / 64` and byte offset `addr % 64`. -/
def rawCellAt (lines : BinTree Line64) (addr : Nat) : Option Cell :=
  match btGet 58 lines (addr / 64) with
  | some line => btGet 6 line (addr % 64)
  | none => none

def setRawCell (lines : BinTree Line64) (addr : Nat) (c : Cell) : BinTree Line64 :=
  withForcedCell c fun cf =>
    let hi := addr / 64
    let lo := addr % 64
    let oldLine := (btGet 58 lines hi).getD .empty
    withForcedBinTree (btSet 6 oldLine lo cf) fun newLine =>
      btSet 58 lines hi newLine

theorem div64_lt_2pow58 {addr : Nat} (h : addr < 2 ^ 64) : addr / 64 < 2 ^ 58 := by
  omega

theorem mod64_lt_2pow6 (addr : Nat) : addr % 64 < 2 ^ 6 := by
  omega

theorem rawCellAt_setRawCell_same (lines : BinTree Line64) {addr : Nat} (c : Cell) :
    rawCellAt (setRawCell lines addr c) addr = some c := by
  simp only [setRawCell, withForcedCell_eq, withForcedBinTree_eq, rawCellAt, btGet_btSet_same']

theorem rawCellAt_setRawCell_ne (lines : BinTree Line64) {addr addr' : Nat} (c : Cell)
    (h1 : addr < 2 ^ 64) (h2 : addr' < 2 ^ 64) (hne : addr' ≠ addr) :
    rawCellAt (setRawCell lines addr c) addr' = rawCellAt lines addr' := by
  simp only [setRawCell, withForcedCell_eq, withForcedBinTree_eq, rawCellAt]
  by_cases hhi : addr / 64 = addr' / 64
  · rw [← hhi, btGet_btSet_same']
    dsimp only
    have hlo : addr % 64 ≠ addr' % 64 := by omega
    rw [btGet_btSet_ne 6 (addr % 64) (addr' % 64) _ c (mod64_lt_2pow6 addr) (mod64_lt_2pow6 addr') hlo]
    cases btGet 58 lines (addr / 64) <;> rfl
  · rw [btGet_btSet_ne 58 (addr / 64) (addr' / 64) lines _
      (div64_lt_2pow58 h1) (div64_lt_2pow58 h2) hhi]

/-- Reference 1-by-1 cell writer over `[addr, addr + cs.length)` (capped at `2 ^ 64`). -/
def foldSetRawCell (lines : BinTree Line64) (addr : Nat) : List Cell → BinTree Line64
  | [] => lines
  | c :: cs =>
    if addr < 2 ^ 64 then
      foldSetRawCell (setRawCell lines addr c) (addr + 1) cs
    else
      lines

/-- Write consecutive cells: buffer updates to `(curHi, curLine)` within a 64-byte cache line and
commit via `btSet58Line` only when `addr / 64` changes. -/
def flushAndSetCells (lines : BinTree Line64) (curHi : Nat) (curLine : Line64)
    (addr : Nat) : List Cell → BinTree Line64
  | [] => btSet58Line lines curHi curLine
  | (p, b) :: cs =>
    if Nat.blt addr (2 ^ 64) then
      let hi := addr / 64
      let lo := addr % 64
      if hi == curHi then
        flushAndSetCells lines curHi (btSet6Cell curLine lo p b) (addr + 1) cs
      else
        match btSet58Line lines curHi curLine with
        | .empty => flushAndSetCells .empty hi (btSet6Cell .empty lo p b) (addr + 1) cs
        | .twig j u => flushAndSetCells (.twig j u) hi (btSet6Cell ((btGet 58 (.twig j u) hi).getD .empty) lo p b) (addr + 1) cs
        | .branch x y => flushAndSetCells (.branch x y) hi (btSet6Cell ((btGet 58 (.branch x y) hi).getD .empty) lo p b) (addr + 1) cs
    else
      btSet58Line lines curHi curLine

/-- Write contiguous cells `cs` at `addr`, batched by 64-byte cache line. -/
def setCellsAt (lines : BinTree Line64) (addr : Nat) (cs : List Cell) : BinTree Line64 :=
  match cs with
  | [] => lines
  | (p, b) :: rest =>
    if Nat.blt addr (2 ^ 64) then
      let hi := addr / 64
      let curLine := (btGet 58 lines hi).getD .empty
      flushAndSetCells lines hi (btSet6Cell curLine (addr % 64) p b) (addr + 1) rest
    else
      lines

/-- Extensional equality of two depth-58 `Line64` trees across all 64-bit addresses. -/
def LinesEq (l1 l2 : BinTree Line64) : Prop :=
  ∀ a : Nat, a < 2 ^ 64 → rawCellAt l1 a = rawCellAt l2 a

theorem linesEq_setRawCell {l1 l2 : BinTree Line64} (h : LinesEq l1 l2)
    {addr : Nat} (hadr : addr < 2 ^ 64) (c : Cell) :
    LinesEq (setRawCell l1 addr c) (setRawCell l2 addr c) := by
  intro a ha
  by_cases heq : a = addr
  · subst heq; rw [rawCellAt_setRawCell_same, rawCellAt_setRawCell_same]
  · rw [rawCellAt_setRawCell_ne l1 c hadr ha heq, rawCellAt_setRawCell_ne l2 c hadr ha heq, h a ha]

theorem linesEq_foldSetRawCell {l1 l2 : BinTree Line64} (h : LinesEq l1 l2)
    (addr : Nat) (cs : List Cell) :
    LinesEq (foldSetRawCell l1 addr cs) (foldSetRawCell l2 addr cs) := by
  induction cs generalizing l1 l2 addr with
  | nil => exact h
  | cons c cs ih =>
    simp only [foldSetRawCell]
    split
    · rename_i hadr; exact ih (linesEq_setRawCell h hadr c) (addr + 1)
    · exact h

theorem linesEq_flushAndSetCells (lines : BinTree Line64) (curHi : Nat) (curLine : Line64)
    (hhi : curHi < 2 ^ 58) (addr : Nat) (cs : List Cell) :
    LinesEq (flushAndSetCells lines curHi curLine addr cs)
      (foldSetRawCell (btSet 58 lines curHi curLine) addr cs) := by
  induction cs generalizing lines curHi curLine addr with
  | nil => intro _ _; simp [flushAndSetCells, foldSetRawCell]
  | cons c cs ih =>
    rcases c with ⟨p, b⟩
    simp only [flushAndSetCells, foldSetRawCell, btSet6Cell_eq, btSet58Line_eq]
    by_cases hadr : addr < 2 ^ 64
    · have hblt : Nat.blt addr (2 ^ 64) = true := Nat.blt_eq.mpr hadr
      simp only [hadr, hblt, ↓reduceIte]
      have hhi' : addr / 64 < 2 ^ 58 := div64_lt_2pow58 hadr
      by_cases heq : (addr / 64 == curHi) = true
      · simp only [heq, ↓reduceIte]
        have hcur_eq : addr / 64 = curHi := beq_iff_eq.mp heq
        have hstep := ih lines curHi (btSet 6 curLine (addr % 64) (p, b)) hhi (addr + 1)
        have hbase : LinesEq (btSet 58 lines curHi (btSet 6 curLine (addr % 64) (p, b)))
            (setRawCell (btSet 58 lines curHi curLine) addr (p, b)) := by
          intro a ha
          simp only [setRawCell, withForcedCell_eq, withForcedBinTree_eq, hcur_eq,
            btGet_btSet_same', Option.getD_some, rawCellAt]
          congr 1
          exact (btGet_btSet_btSet_same_key 58 curHi (a / 64) lines curLine _
            hhi (div64_lt_2pow58 ha)).symm
        exact fun a ha => (hstep a ha).trans (linesEq_foldSetRawCell hbase (addr + 1) cs a ha)
      · simp only [Bool.not_eq_true] at heq
        simp only [heq, Bool.false_eq_true, ↓reduceIte, setRawCell, withForcedCell_eq,
          withForcedBinTree_eq]
        have hbt (t : BinTree Line64) :
            (match t with
             | .empty => flushAndSetCells .empty (addr / 64) (btSet 6 .empty (addr % 64) (p, b)) (addr + 1) cs
             | .twig j u => flushAndSetCells (.twig j u) (addr / 64) (btSet 6 ((btGet 58 (.twig j u) (addr / 64)).getD .empty) (addr % 64) (p, b)) (addr + 1) cs
             | .branch x y => flushAndSetCells (.branch x y) (addr / 64) (btSet 6 ((btGet 58 (.branch x y) (addr / 64)).getD .empty) (addr % 64) (p, b)) (addr + 1) cs) =
              flushAndSetCells t (addr / 64) (btSet 6 ((btGet 58 t (addr / 64)).getD .empty) (addr % 64) (p, b)) (addr + 1) cs := by cases t <;> rfl
        rw [hbt]
        exact ih (btSet 58 lines curHi curLine) (addr / 64) _ hhi' (addr + 1)
    · have hblt : Nat.blt addr (2 ^ 64) = false := Bool.eq_false_iff.mpr (fun hb => hadr (Nat.blt_eq.mp hb))
      simp only [hadr, hblt, Bool.false_eq_true, ↓reduceIte]
      intro _ _; rfl

theorem linesEq_setCellsAt (lines : BinTree Line64) (addr : Nat) (cs : List Cell) :
    LinesEq (setCellsAt lines addr cs) (foldSetRawCell lines addr cs) := by
  cases cs with
  | nil => intro _ _; rfl
  | cons c rest =>
    rcases c with ⟨p, b⟩
    simp only [setCellsAt, foldSetRawCell, btSet6Cell_eq]
    by_cases hadr : addr < 2 ^ 64
    · have hblt : Nat.blt addr (2 ^ 64) = true := Nat.blt_eq.mpr hadr
      simp only [hadr, hblt, ↓reduceIte, setRawCell, withForcedCell_eq, withForcedBinTree_eq]
      exact linesEq_flushAndSetCells lines (addr / 64) _ (div64_lt_2pow58 hadr) (addr + 1) rest
    · have hblt : Nat.blt addr (2 ^ 64) = false := Bool.eq_false_iff.mpr (fun hb => hadr (Nat.blt_eq.mp hb))
      simp only [hadr, hblt, Bool.false_eq_true, ↓reduceIte]
      intro _ _; rfl

theorem rawCellAt_foldSetRawCell_noWrap (lines : BinTree Line64) (addr : Nat) (cs : List Cell)
    (hwrap : addr + cs.length ≤ 2 ^ 64) (a : Nat) (ha : a < 2 ^ 64) :
    rawCellAt (foldSetRawCell lines addr cs) a =
      if h : addr ≤ a ∧ a < addr + cs.length then
        some (cs[a - addr]'(by omega))
      else
        rawCellAt lines a := by
  induction cs generalizing lines addr with
  | nil =>
    simp only [foldSetRawCell, List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | cons c cs ih =>
    simp only [List.length_cons] at hwrap ⊢
    have hadr : addr < 2 ^ 64 := by omega
    simp only [foldSetRawCell, hadr, ↓reduceIte]
    rw [ih (setRawCell lines addr c) (addr + 1) (by omega)]
    split <;> split
    · have hidx : a - addr = (a - (addr + 1)) + 1 := by omega
      simp only [hidx, List.getElem_cons_succ]
    · omega
    · rename_i h1 h2
      have heq : a = addr := by omega
      subst heq
      simp only [Nat.sub_self, List.getElem_cons_zero, rawCellAt_setRawCell_same]
    · rename_i h1 h2
      have hne : a ≠ addr := by omega
      exact rawCellAt_setRawCell_ne lines c hadr ha hne

theorem sub_lt_iff_range {base a : BitVec 64} {len : Nat}
    (hwrap : base.toNat + len ≤ 2 ^ 64) :
    (a - base).toNat < len ↔ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + len) := by
  simp only [BitVec.toNat_sub]
  have ha := a.isLt
  have hb := base.isLt
  by_cases hle : base.toNat ≤ a.toNat
  · have hmod : (2 ^ 64 - base.toNat + a.toNat) % 2 ^ 64 = a.toNat - base.toNat := by
      have heq : 2 ^ 64 - base.toNat + a.toNat = 2 ^ 64 + (a.toNat - base.toNat) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    omega
  · have hmod : (2 ^ 64 - base.toNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - base.toNat + a.toNat :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

theorem toNat_sub_succ_base {a base : BitVec 64} (hne : a ≠ base) :
    (a - base).toNat = (a - (base + 1#64)).toNat + 1 := by
  have ha := a.isLt
  have hb := base.isLt
  have hneNat : a.toNat ≠ base.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  simp only [BitVec.toNat_sub, BitVec.toNat_add]
  have h1 : (1#64).toNat = 1 := rfl
  rw [h1]
  by_cases htop : base.toNat + 1 = 2 ^ 64
  · rw [htop, Nat.mod_self]
    have hmod1 : (2 ^ 64 - base.toNat + a.toNat) % 2 ^ 64 = 1 + a.toNat := by
      have heq : 2 ^ 64 - base.toNat + a.toNat = 1 + a.toNat := by omega
      rw [heq]
      exact Nat.mod_eq_of_lt (by omega)
    have hmod2 : (2 ^ 64 - 0 + a.toNat) % 2 ^ 64 = a.toNat := by
      rw [Nat.sub_zero, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
    rw [hmod1, hmod2]
    omega
  · have hb1 : (base.toNat + 1) % 2 ^ 64 = base.toNat + 1 := Nat.mod_eq_of_lt (by omega)
    rw [hb1]
    by_cases hlt : base.toNat < a.toNat
    · have hm1 : (2 ^ 64 - base.toNat + a.toNat) % 2 ^ 64 = a.toNat - base.toNat := by
        have heq : 2 ^ 64 - base.toNat + a.toNat = 2 ^ 64 + (a.toNat - base.toNat) := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hm2 : (2 ^ 64 - (base.toNat + 1) + a.toNat) % 2 ^ 64 = a.toNat - (base.toNat + 1) := by
        have heq : 2 ^ 64 - (base.toNat + 1) + a.toNat = 2 ^ 64 + (a.toNat - (base.toNat + 1)) := by omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hm1, hm2]
      omega
    · have hm1 : (2 ^ 64 - base.toNat + a.toNat) % 2 ^ 64 = 2 ^ 64 - base.toNat + a.toNat :=
        Nat.mod_eq_of_lt (by omega)
      have hm2 : (2 ^ 64 - (base.toNat + 1) + a.toNat) % 2 ^ 64 = 2 ^ 64 - (base.toNat + 1) + a.toNat :=
        Nat.mod_eq_of_lt (by omega)
      rw [hm1, hm2]
      omega

theorem memory_writeBytes_cells_noWrap (m : Memory) (base : BitVec 64) (bs : List (BitVec 8))
    (hwrap : base.toNat + bs.length ≤ 2 ^ 64) (a : BitVec 64) :
    (m.writeBytes base bs).cells a =
      if h : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + bs.length then
        some (match m.rawPerm a with
              | some p => some { p with lazyFree := false }
              | none => none, bs[a.toNat - base.toNat]'(by omega))
      else
        m.cells a := by
  induction bs generalizing m base with
  | nil =>
    simp only [Memory.writeBytes, List.length_nil, Nat.add_zero]
    by_cases hrng : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat
    · omega
    · rw [dite_eq_right_of_eq_false (eq_false hrng)]
  | cons b rest ih =>
    simp only [List.length_cons] at hwrap
    simp only [Memory.writeBytes]
    cases rest with
    | nil =>
      simp only [Memory.writeBytes, Memory.write8]
      by_cases heq : a = base
      · subst heq
        have hrng : a.toNat ≤ a.toNat ∧ a.toNat < a.toNat + [b].length := by simp
        rw [dite_eq_left_of_eq_true (eq_true hrng)]
        simp only [↓reduceIte, Nat.sub_self, List.getElem_cons_zero]
        rcases m.rawPerm a with _ | _ <;> rfl
      · have hne : a.toNat ≠ base.toNat := fun hn => heq (BitVec.eq_of_toNat_eq hn)
        have hrng : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + [b].length) := by
          simp only [List.length_cons, List.length_nil]; omega
        rw [dite_eq_right_of_eq_false (eq_false hrng)]
        simp only [heq, ↓reduceIte]
    | cons b2 rest2 =>
      have hlen2 : (b2 :: rest2).length = rest2.length + 1 := rfl
      have hlen3 : (b :: b2 :: rest2).length = rest2.length + 2 := rfl
      have hwrap' : base.toNat + (rest2.length + 2) ≤ 2 ^ 64 := by
        simp only [List.length_cons] at hwrap; omega
      have hb1 : (base + 1#64).toNat = base.toNat + 1 := by
        rw [BitVec.toNat_add]
        change (base.toNat + 1) % 2 ^ 64 = base.toNat + 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [ih (m.write8 base b) (base + 1#64) (by rw [hb1, hlen2]; omega)]
      by_cases h1 : (base + 1#64).toNat ≤ a.toNat ∧ a.toNat < (base + 1#64).toNat + (b2 :: rest2).length
      · have h2 : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + (b :: b2 :: rest2).length := by
          rw [hb1, hlen2] at h1; rw [hlen3]; omega
        rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)]
        have hne : a ≠ base := fun heq => by subst heq; omega
        have hrp : (m.write8 base b).rawPerm a = m.rawPerm a := by
          simp [Memory.rawPerm, Memory.write8, hne]
        rw [hrp]
        congr 1; congr 1
        have hidx : a.toNat - base.toNat = (a.toNat - (base + 1#64).toNat) + 1 := by omega
        exact (List.getElem_cons_succ b (b2 :: rest2) (a.toNat - (base + 1#64).toNat)
          (by rw [hb1, hlen2] at h1; rw [hlen3]; omega)).symm.trans (by simp only [← hidx])
      · rw [dite_eq_right_of_eq_false (eq_false h1)]
        by_cases heq : a = base
        · subst heq
          have h2 : a.toNat ≤ a.toNat ∧ a.toNat < a.toNat + (b :: b2 :: rest2).length := by
            rw [hlen3]; omega
          rw [dite_eq_left_of_eq_true (eq_true h2)]
          simp only [Memory.write8, ↓reduceIte, Nat.sub_self, List.getElem_cons_zero]
          rcases m.rawPerm a with _ | _ <;> rfl
        · have hne : a.toNat ≠ base.toNat := fun hn => heq (BitVec.eq_of_toNat_eq hn)
          have h2 : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + (b :: b2 :: rest2).length) := by
            rw [hb1, hlen2] at h1; rw [hlen3]; omega
          rw [dite_eq_right_of_eq_false (eq_false h2)]
          simp only [Memory.write8, heq, ↓reduceIte]

@[inline] def tail1Byte : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | _ :: s => s

private theorem tail1Byte_eq (bs : List (BitVec 8)) : tail1Byte bs = bs.drop 1 := by
  cases bs <;> rfl

def drop8Bytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte bs)))))))

private theorem drop8Bytes_eq_drop (bs : List (BitVec 8)) : drop8Bytes bs = bs.drop 8 := by
  simp [drop8Bytes, tail1Byte_eq, List.drop_drop]

/-- Closure-free `bs.drop 63`, kept irreducible so `loadUniform64` checks 64-byte availability in WHNF. -/
def drop63Bytes (bs : List (BitVec 8)) : List (BitVec 8) :=
  let s56 := drop8Bytes (drop8Bytes (drop8Bytes (drop8Bytes (drop8Bytes (drop8Bytes (drop8Bytes bs))))))
  tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte (tail1Byte s56))))))

theorem drop63Bytes_eq_drop (bs : List (BitVec 8)) : drop63Bytes bs = bs.drop 63 := by
  simp [drop63Bytes, drop8Bytes_eq_drop, tail1Byte_eq, List.drop_drop]

attribute [local irreducible] drop63Bytes

/-- Lazily build a 64-byte `Line64` of uniform permission `cp` (reduced only when line `hi` is read). -/
def buildLazyLineAux (cp : Option Perm) : Nat → Nat → Line64 → List (BitVec 8) → Line64
  | 0, _, ln, _ => ln
  | _ + 1, _, ln, [] => ln
  | k + 1, lo, ln, b :: rest =>
    buildLazyLineAux cp k (Nat.add lo 1) (btSet6Cell ln lo cp b) rest

private theorem btGet_buildLazyLineAux (cp : Option Perm) :
    ∀ (k lo : Nat) (ln : Line64) (bs : List (BitVec 8))
      (_hlo : lo + k ≤ 64) (_hlen : k ≤ bs.length) (j : Nat) (_hj : j < 64),
        btGet 6 (buildLazyLineAux cp k lo ln bs) j =
          if h : lo ≤ j ∧ j < lo + k then some (cp, bs[j - lo]'(by omega))
          else btGet 6 ln j
  | 0, lo, ln, bs, _, _, j, _ => by
    simp only [buildLazyLineAux, Nat.add_zero]
    split
    · omega
    · rfl
  | k + 1, lo, ln, [], _, hlen, _, _ => absurd hlen (Nat.not_succ_le_zero _)
  | k + 1, lo, ln, b :: rest, hlo, hlen, j, hj => by
    simp only [List.length_cons] at hlen
    have hadd : Nat.add lo 1 = lo + 1 := rfl
    simp only [buildLazyLineAux, btSet6Cell_eq, hadd]
    rw [btGet_buildLazyLineAux cp k (lo + 1) (btSet 6 ln lo (cp, b)) rest (by omega) (by omega) j hj]
    by_cases h1 : lo + 1 ≤ j ∧ j < lo + 1 + k
    · have h2 : lo ≤ j ∧ j < lo + (k + 1) := by omega
      rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)]
      have hsub : j - lo = (j - (lo + 1)) + 1 := by omega
      simp only [hsub, List.getElem_cons_succ]
    · rw [dite_eq_right_of_eq_false (eq_false h1)]
      by_cases heq : j = lo
      · subst heq
        have h2 : j ≤ j ∧ j < j + (k + 1) := by omega
        rw [dite_eq_left_of_eq_true (eq_true h2)]
        simp [btGet_btSet_same']
      · have h2 : ¬ (lo ≤ j ∧ j < lo + (k + 1)) := by omega
        rw [dite_eq_right_of_eq_false (eq_false h2)]
        exact btGet_btSet_ne 6 lo j ln (cp, b) (by omega) hj (Ne.symm heq)

/-- Output of `loadUniform64`: updated `lines`, number of 64-byte lines `loaded`, and unconsumed `rest`. -/
structure UniformLoadRes where
  lines  : BinTree Line64
  loaded : Nat
  rest   : List (BitVec 8)

/-- Tail-recursively load up to `q` aligned 64-byte uniform cache lines from line index `hi`. -/
def loadUniform64 (cp : Option Perm) :
    Nat → Nat → Nat → BinTree Line64 → List (BitVec 8) → UniformLoadRes
  | 0, _, loaded, lines, bs => ⟨lines, loaded, bs⟩
  | q + 1, hi, loaded, lines, bs =>
    match drop63Bytes bs with
    | [] => ⟨lines, loaded, bs⟩
    | _ :: rest =>
      let lazyLn := buildLazyLineAux cp 64 0 .empty bs
      let hi' := Nat.add hi 1
      match Nat.add loaded 1 with
      | 0 => ⟨lines, 0, rest⟩
      | m + 1 =>
        match btSet 58 lines hi lazyLn with
        | .empty => loadUniform64 cp q hi' (Nat.succ m) .empty rest
        | .twig j u => loadUniform64 cp q hi' (Nat.succ m) (.twig j u) rest
        | .branch x y => loadUniform64 cp q hi' (Nat.succ m) (.branch x y) rest

theorem foldSetRawCell_append (lines : BinTree Line64) (addr : Nat) (cs1 cs2 : List Cell)
    (hwrap : addr + cs1.length ≤ 2 ^ 64) :
    foldSetRawCell lines addr (cs1 ++ cs2) =
      foldSetRawCell (foldSetRawCell lines addr cs1) (addr + cs1.length) cs2 := by
  induction cs1 generalizing lines addr with
  | nil => simp [foldSetRawCell]
  | cons c cs1 ih =>
    simp only [List.length_cons] at hwrap ⊢
    have hadr : addr < 2 ^ 64 := by omega
    simp only [List.cons_append, foldSetRawCell, hadr, ↓reduceIte]
    rw [ih (setRawCell lines addr c) (addr + 1) (by omega)]
    have hadd : addr + 1 + cs1.length = addr + (cs1.length + 1) := by omega
    rw [hadd]

private theorem linesEq_btSet_lazyLine64 (cp : Option Perm) (lines : BinTree Line64) (hi : Nat)
    (bs : List (BitVec 8)) (hhi : (hi + 1) * 64 ≤ 2 ^ 64) (hbs : 64 ≤ bs.length) :
    LinesEq (btSet 58 lines hi (buildLazyLineAux cp 64 0 .empty bs))
      (foldSetRawCell lines (hi * 64) ((bs.take 64).map (fun b => (cp, b)))) := by
  intro a ha
  have hlen : ((bs.take 64).map (fun b => (cp, b))).length = 64 := by
    rw [List.length_map, List.length_take]; omega
  rw [rawCellAt_foldSetRawCell_noWrap lines (hi * 64) _ (by rw [hlen]; omega) a ha]
  dsimp only [rawCellAt]
  by_cases hdiv : a / 64 = hi
  · have hrng : hi * 64 ≤ a ∧ a < hi * 64 + ((bs.take 64).map (fun b => (cp, b))).length := by
      rw [hlen]; omega
    rw [dite_eq_left_of_eq_true (eq_true hrng), hdiv, btGet_btSet_same']
    dsimp only
    rw [btGet_buildLazyLineAux cp 64 0 .empty bs (by omega) hbs (a % 64) (mod64_lt_2pow6 a)]
    have hlo : 0 ≤ a % 64 ∧ a % 64 < 0 + 64 := ⟨Nat.zero_le _, mod64_lt_2pow6 a⟩
    rw [dite_eq_left_of_eq_true (eq_true hlo)]
    have hidx : a % 64 - 0 = a - hi * 64 := by omega
    simp [hidx]
  · have hrng : ¬ (hi * 64 ≤ a ∧ a < hi * 64 + ((bs.take 64).map (fun b => (cp, b))).length) := by
      rw [hlen]; omega
    rw [dite_eq_right_of_eq_false (eq_false hrng),
      btGet_btSet_ne 58 hi (a / 64) lines _ (by omega) (div64_lt_2pow58 ha) (Ne.symm hdiv)]

theorem loadUniform64_spec (cp : Option Perm) :
    ∀ (q hi loaded : Nat) (lines : BinTree Line64) (bs : List (BitVec 8)),
      (hi + q) * 64 ≤ 2 ^ 64 →
      ∃ m : Nat,
        m ≤ q ∧ m * 64 ≤ bs.length ∧
        (loadUniform64 cp q hi loaded lines bs).loaded = loaded + m ∧
        (loadUniform64 cp q hi loaded lines bs).rest = bs.drop (m * 64) ∧
        LinesEq (loadUniform64 cp q hi loaded lines bs).lines
          (foldSetRawCell lines (hi * 64) ((bs.take (m * 64)).map (fun b => (cp, b))))
  | 0, hi, loaded, lines, bs, _ => by
    refine ⟨0, Nat.le_refl 0, Nat.zero_le _, by simp [loadUniform64], by simp [loadUniform64], ?_⟩
    intro a _; simp [loadUniform64, foldSetRawCell]
  | q + 1, hi, loaded, lines, bs, hwrap => by
    unfold loadUniform64
    cases hd : drop63Bytes bs with
    | nil =>
      refine ⟨0, Nat.zero_le _, Nat.zero_le _, by simp, by simp, ?_⟩
      intro a _; simp [foldSetRawCell]
    | cons b63 rest =>
      have hdrop63 : bs.drop 63 = b63 :: rest := by rw [← drop63Bytes_eq_drop, hd]
      have hbs64 : 64 ≤ bs.length := by
        have hlen := congrArg List.length hdrop63
        simp only [List.length_drop, List.length_cons] at hlen; omega
      have hrest_eq : rest = bs.drop 64 := by
        have h64 : (64 : Nat) = 63 + 1 := rfl
        rw [h64, ← List.drop_drop, hdrop63]; rfl
      dsimp only
      have hbt (t : BinTree Line64) :
          (match t with
           | .empty => loadUniform64 cp q (hi + 1) (loaded + 1) .empty rest
           | .twig j u => loadUniform64 cp q (hi + 1) (loaded + 1) (.twig j u) rest
           | .branch x y => loadUniform64 cp q (hi + 1) (loaded + 1) (.branch x y) rest) =
            loadUniform64 cp q (hi + 1) (loaded + 1) t rest := by cases t <;> rfl
      rw [hbt]
      have hhi64 : (hi + 1) * 64 ≤ 2 ^ 64 := by
        have : (hi + 1) * 64 + q * 64 = (hi + (q + 1)) * 64 := by
          rw [Nat.add_mul, Nat.add_mul]; omega
        omega
      have hhiq64 : (hi + 1 + q) * 64 ≤ 2 ^ 64 := by
        have : hi + 1 + q = hi + (q + 1) := by omega
        rw [this]; exact hwrap
      let lines1 := btSet 58 lines hi (buildLazyLineAux cp 64 0 .empty bs)
      have hl1 : LinesEq lines1 (foldSetRawCell lines (hi * 64) ((bs.take 64).map (fun b => (cp, b)))) :=
        linesEq_btSet_lazyLine64 cp lines hi bs hhi64 hbs64
      obtain ⟨m', hm'_le, hm'_len, hld, hrst, hleq⟩ :=
        loadUniform64_spec cp q (hi + 1) (loaded + 1) lines1 rest hhiq64
      dsimp only [lines1] at hld hrst hleq
      refine ⟨m' + 1, by omega, by rw [hrest_eq, List.length_drop] at hm'_len; omega,
        by omega, ?_, ?_⟩
      · rw [hrst, hrest_eq, List.drop_drop]
        congr 1; omega
      · intro a ha
        rw [hleq a ha, linesEq_foldSetRawCell hl1 ((hi + 1) * 64) _ a ha]
        have htake : bs.take ((m' + 1) * 64) = bs.take 64 ++ rest.take (m' * 64) := by
          have hmul : (m' + 1) * 64 = 64 + m' * 64 := by omega
          rw [hmul, hrest_eq, List.take_add]
        have hlen64 : ((bs.take 64).map (fun b => (cp, b))).length = 64 := by
          rw [List.length_map, List.length_take]; omega
        have haddr : hi * 64 + ((bs.take 64).map (fun b => (cp, b))).length = (hi + 1) * 64 := by
          rw [hlen64]; omega
        rw [htake, List.map_append, foldSetRawCell_append lines (hi * 64) _ _ (by rw [hlen64]; omega),
          haddr]

/-- Convert region bytes to `Cell` entries with `anon := false` on the first `nonAnonLen` bytes. -/
def regionToCells (perm : Perm) (nonAnonLen : Nat) : Nat → List (BitVec 8) → List Cell
  | _, [] => []
  | i, b :: bs =>
    let p : Perm := { perm with lazyFree := false, anon := if Nat.blt i nonAnonLen then false else perm.anon }
    (some p, b) :: regionToCells perm nonAnonLen (i + 1) bs

theorem regionToCells_length (perm : Perm) (nonAnonLen : Nat) :
    ∀ (i : Nat) (bs : List (BitVec 8)), (regionToCells perm nonAnonLen i bs).length = bs.length
  | _, [] => rfl
  | i, _ :: bs => by
    simp only [regionToCells, List.length_cons, regionToCells_length perm nonAnonLen (i + 1) bs]

theorem regionToCells_getElem (perm : Perm) (nonAnonLen : Nat) :
    ∀ (i : Nat) (bs : List (BitVec 8)) (k : Nat) (hk : k < bs.length),
      (regionToCells perm nonAnonLen i bs)[k]'(by rw [regionToCells_length]; exact hk) =
        (some { perm with lazyFree := false, anon := if i + k < nonAnonLen then false else perm.anon }, bs[k]'hk)
  | _, [], _, hk => absurd hk (Nat.not_lt_zero _)
  | i, _ :: bs, k, hk => by
    simp only [List.length_cons] at hk
    cases k with
    | zero =>
      simp only [regionToCells, List.getElem_cons_zero, Nat.add_zero]
      by_cases hlt : i < nonAnonLen <;> simp [Nat.blt_eq, hlt]
    | succ j =>
      simp only [regionToCells, List.getElem_cons_succ]
      have hrec := regionToCells_getElem perm nonAnonLen (i + 1) bs j (by omega)
      have hadd : i + 1 + j = i + (j + 1) := by omega
      simpa only [hadd] using hrec

private theorem regionToCells_split_nonAnon (perm : Perm) (nonAnonLen : Nat) :
    ∀ (k i : Nat) (bs : List (BitVec 8)),
      i + k ≤ nonAnonLen → k ≤ bs.length →
      regionToCells perm nonAnonLen i bs =
        (bs.take k).map (fun b => (some { perm with lazyFree := false, anon := false }, b)) ++
          regionToCells perm nonAnonLen (i + k) (bs.drop k)
  | 0, i, bs, _, _ => by simp
  | _ + 1, _, [], _, hlen => absurd hlen (Nat.not_succ_le_zero _)
  | k + 1, i, b :: bs, hi, hlen => by
    simp only [List.length_cons] at hlen
    have hilt : Nat.blt i nonAnonLen = true := Nat.blt_eq.mpr (by omega)
    simp only [regionToCells, hilt, ↓reduceIte, List.take_succ_cons,
      List.map_cons, List.drop_succ_cons, List.cons_append]
    rw [regionToCells_split_nonAnon perm nonAnonLen k (i + 1) bs (by omega) (by omega)]
    have hadd : i + 1 + k = i + (k + 1) := by omega
    rw [hadd]

/-- Load a region `(start, nonAnonLen, perm, bytes)` via `loadUniform64` on a 64-byte-aligned
`nonAnonLen` prefix and `setCellsAt` on the remainder. -/
def loadRegionFast (lines : BinTree Line64) (start nonAnonLen : Nat) (perm : Perm)
    (bytes : List (BitVec 8)) : BinTree Line64 :=
  let q := Nat.div nonAnonLen 64
  if Nat.beq (Nat.mod start 64) 0 && Nat.ble (start + q * 64) (2 ^ 64) then
    let cp : Option Perm := some { perm with lazyFree := false, anon := false }
    match loadUniform64 cp q (Nat.div start 64) 0 lines bytes with
    | ⟨lines1, loaded, rest⟩ =>
      setCellsAt lines1 (start + loaded * 64)
        (regionToCells perm nonAnonLen (loaded * 64) rest)
  else
    setCellsAt lines start (regionToCells perm nonAnonLen 0 bytes)

theorem linesEq_loadRegionFast (lines : BinTree Line64) (start nonAnonLen : Nat) (perm : Perm)
    (bytes : List (BitVec 8)) :
    LinesEq (loadRegionFast lines start nonAnonLen perm bytes)
      (foldSetRawCell lines start (regionToCells perm nonAnonLen 0 bytes)) := by
  unfold loadRegionFast
  have hd1 : Nat.div nonAnonLen 64 = nonAnonLen / 64 := rfl
  have hd2 : Nat.div start 64 = start / 64 := rfl
  have hm1 : Nat.mod start 64 = start % 64 := rfl
  dsimp only
  rw [hd1, hd2, hm1]
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
    rcases hcond with ⟨halign, hwrap⟩
    let cp : Option Perm := some { perm with lazyFree := false, anon := false }
    have hhi_wrap : (start / 64 + nonAnonLen / 64) * 64 ≤ 2 ^ 64 := by omega
    obtain ⟨m, hm_le, hm_len, hld, hrst, hleq⟩ :=
      loadUniform64_spec cp (nonAnonLen / 64) (start / 64) 0 lines bytes hhi_wrap
    have hstart_eq : start / 64 * 64 = start := by omega
    rw [hstart_eq] at hleq
    cases hres : loadUniform64 cp (nonAnonLen / 64) (start / 64) 0 lines bytes with
    | mk lines1 loaded rest =>
      rw [hres] at hld hrst hleq
      dsimp only at hld hrst hleq ⊢
      rw [Nat.zero_add] at hld
      subst loaded rest
      intro a ha
      rw [linesEq_setCellsAt lines1 (start + m * 64) _ a ha,
        linesEq_foldSetRawCell hleq (start + m * 64) _ a ha]
      have hsplit := regionToCells_split_nonAnon perm nonAnonLen (m * 64) 0 bytes
        (by omega) hm_len
      rw [Nat.zero_add] at hsplit
      have hmap_len : ((bytes.take (m * 64)).map (fun b => (cp, b))).length = m * 64 := by
        rw [List.length_map, List.length_take]; omega
      rw [hsplit, foldSetRawCell_append lines start _ _ (by rw [hmap_len]; omega),
        hmap_len]
  · exact linesEq_setCellsAt lines start _

end Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
