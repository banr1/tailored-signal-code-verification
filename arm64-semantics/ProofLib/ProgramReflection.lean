/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.PrologueFrame
public import ProofLib.BV.Arith
public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflection for Concrete Programs

Proof-by-reflection primitives that discharge instruction fetches and symbol-table lookups on
concrete `Arm64.Program` values in $O(\log N)$ or linear kernel time:
- `WordTree` (`word_tree_of%`, `fetch_of_wordTree`, `sliceBytesChecked`): balanced binary trees of
  4-byte little-endian words sharing `BitVec 8` `Expr` nodes with `<prog>.code` so byte-image
  equality checks by pointer equality in the kernel and per-offset instruction decoding runs in
  $O(\log N)$ steps;
- `List Char` table reflection (`sym_chars_of%`, `stub_chars_of%`, `assoc_chars_of%`,
  `isStrictSorted`, `fnOff_of_allFresh`, `fnOff_of_stub`): pre-encoded codepoint-list keys and
  strict-sortedness checks reducing symbol and extern-stub lookups to indexed list access;
- `rfl_kernel` for direct kernel definitional-equality proofs and `fnEntryExt` for symbol-entry
  metadata registration.
-/

namespace ProofLib.ProgramReflection

open Arm64

@[expose] public section

open Lean Elab Tactic Meta in
/-- Assign `@Eq.refl _ lhs` directly to the main equality goal so the kernel checks definitional
    equality once without interpreted `Meta.isDefEq` WHNF reduction or `@[_refl_lemma]` overhead. -/
scoped elab "rfl_kernel" : tactic => do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "rfl_kernel: expected equality goal"
  g.assign (← mkEqRefl lhs)
  replaceMainGoal []

/-! ## `WordTree` Reflection for `Program.fetch` -/

/-- Balanced binary tree of 4-byte little-endian instruction words. -/
inductive WordTree where
  | empty : WordTree
  | leaf (b0 b1 b2 b3 : BitVec 8) : WordTree
  | node (leftWords : Nat) (left right : WordTree) : WordTree

/-- Flatten a `WordTree` onto an accumulator byte list in $O(N)$ steps without `++`. -/
def WordTree.toBytesAux : WordTree → List (BitVec 8) → List (BitVec 8)
  | .empty, acc => acc
  | .leaf b0 b1 b2 b3, acc => b0 :: b1 :: b2 :: b3 :: acc
  | .node _ l r, acc => l.toBytesAux (r.toBytesAux acc)

/-- Flatten a `WordTree` to its list of bytes. -/
def WordTree.toBytes (t : WordTree) : List (BitVec 8) :=
  t.toBytesAux []

/-- Alias for `WordTree` used when referring to concrete code trees (`code_call_off%`). -/
abbrev CodeTree := WordTree

/-- Construct a single-word `WordTree` leaf from a 32-bit little-endian instruction word. -/
def WordTree.ofWord (w : BitVec 32) : WordTree :=
  .leaf (w.extractLsb' 0 8) (w.extractLsb' 8 8) (w.extractLsb' 16 8) (w.extractLsb' 24 8)

/-- Build a balanced `WordTree` (`CodeTree`) from a slice `[lo, hi)` of `words`. -/
def WordTree.ofWordsSlice (words : Array (BitVec 32)) : Nat → Nat → Nat → WordTree
  | 0, _, _ => .empty
  | fuel + 1, lo, hi =>
    let len := hi - lo
    if len == 0 then .empty
    else if len == 1 then
      match words[lo]? with
      | some w => WordTree.ofWord w
      | none => .empty
    else
      let half := len / 2
      let mid := lo + half
      .node half (WordTree.ofWordsSlice words fuel lo mid) (WordTree.ofWordsSlice words fuel mid hi)

/-- Build a balanced `WordTree` (`CodeTree`) from an `Array (BitVec 32)`. -/
def WordTree.ofWordsArray (words : Array (BitVec 32)) : WordTree :=
  WordTree.ofWordsSlice words (words.size + 1) 0 words.size

/-- Build a balanced `WordTree` (`CodeTree`) from a `List (BitVec 32)`. -/
def WordTree.ofWords (words : List (BitVec 32)) : WordTree :=
  WordTree.ofWordsArray words.toArray

/-- Flatten a `WordTree` onto an accumulator list of 32-bit instruction words in $O(N)$ steps. -/
def WordTree.toWordsAux : WordTree → List (BitVec 32) → List (BitVec 32)
  | .empty, acc => acc
  | .leaf b0 b1 b2 b3, acc => (b3 ++ b2 ++ b1 ++ b0) :: acc
  | .node _ l r, acc => l.toWordsAux (r.toWordsAux acc)

/-- Flatten a `WordTree` (`CodeTree`) to its list of 32-bit instruction words. -/
def WordTree.toWords (t : WordTree) : List (BitVec 32) :=
  t.toWordsAux []

/-- Verify in a single $O(N)$ bottom-up pass that every `node lw l r` annotation `lw` equals
    the number of 4-byte words in `l`, returning the total number of words in the tree. -/
def WordTree.checkSize? : WordTree → Option Nat
  | .empty => some 0
  | .leaf _ _ _ _ => some 1
  | .node lw l r =>
    match l.checkSize?, r.checkSize? with
    | some nl, some nr => if lw == nl then some (nl + nr) else none
    | _, _ => none

/-- Look up the $j$-th 4-byte word in a `WordTree` in $O(\log N)$ steps. -/
def WordTree.getQuad? : WordTree → Nat → Option (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)
  | .empty, _ => none
  | .leaf b0 b1 b2 b3, 0 => some (b0, b1, b2, b3)
  | .leaf _ _ _ _, _ + 1 => none
  | .node lw l r, j => if j < lw then l.getQuad? j else r.getQuad? (j - lw)

private theorem WordTree.drop_all_toBytesAux :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)),
      t.checkSize? = some n →
      (t.toBytesAux acc).drop (4 * n) = acc
  | .empty, _, acc, h => by
    simp only [checkSize?, Option.some.injEq] at h
    subst h
    rfl
  | .leaf _ _ _ _, _, acc, h => by
    simp only [checkSize?, Option.some.injEq] at h
    subst h
    rfl
  | .node lw l r, _, acc, h => by
    simp only [checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h
    subst h
    have hadd : 4 * (nl + nr) = 4 * nl + 4 * nr := Nat.mul_add 4 nl nr
    rw [toBytesAux, hadd, ← List.drop_drop,
        drop_all_toBytesAux l (r.toBytesAux acc) hl,
        drop_all_toBytesAux r acc hr]

private theorem WordTree.getQuad?_drop_toBytesAux {b0 b1 b2 b3 : BitVec 8} :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (j : Nat),
      t.checkSize? = some n →
      t.getQuad? j = some (b0, b1, b2, b3) →
      ∃ rest, (t.toBytesAux acc).drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest
  | .empty, _, _, _, _, hget => by simp [getQuad?] at hget
  | .leaf b0' b1' b2' b3', _, acc, 0, _, hget => by
    simp only [getQuad?, Option.some.injEq, Prod.mk.injEq] at hget
    rcases hget with ⟨rfl, rfl, ⟨rfl, rfl⟩⟩
    exact ⟨acc, rfl⟩
  | .leaf _ _ _ _, _, _, _ + 1, _, hget => by simp [getQuad?] at hget
  | .node lw l r, _, acc, j, hsz, hget => by
    simp only [checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    simp only [getQuad?] at hget
    split at hget
    · exact getQuad?_drop_toBytesAux l (r.toBytesAux acc) j hl hget
    · rename_i hnotlt
      have hj : 4 * j = 4 * lw + 4 * (j - lw) := by omega
      rw [toBytesAux, hj, ← List.drop_drop, drop_all_toBytesAux l (r.toBytesAux acc) hl]
      exact getQuad?_drop_toBytesAux r acc (j - lw) hr hget

/-- The bytes of `t` from offset `4 * j` start with the quad that `getQuad? j` returns. -/
theorem WordTree.toBytes_drop_of_getQuad? {t : WordTree} {n j : Nat} {b0 b1 b2 b3 : BitVec 8}
    (hsz : t.checkSize? = some n) (hget : t.getQuad? j = some (b0, b1, b2, b3)) :
    ∃ rest, t.toBytes.drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest :=
  WordTree.getQuad?_drop_toBytesAux t [] j hsz hget

/-- Fetch and decode the 32-bit instruction at code offset `off` from a `WordTree` in
    $O(\log N)$ steps (`none` for an unaligned `off`). -/
def WordTree.fetchDecodeAt (t : WordTree) (off : Nat) : Option Instr :=
  match t.getQuad? (off / 4) with
  | some (b0, b1, b2, b3) =>
    if off == 4 * (off / 4) then decode (b3 ++ b2 ++ b1 ++ b0) else none
  | none => none

private theorem findSome?_eq_none_of_forall {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = none) → l.findSome? f = none
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.findSome?_cons, h x (List.mem_cons_self ..)]
    exact findSome?_eq_none_of_forall fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- No hook is found when neither `externs` nor `overrides` define any hook. -/
theorem hookAtOff?_eq_none_of_isNone {prog : Program}
    (h_ext : ∀ sym, (prog.externs sym).isNone = true)
    (h_ovr : ∀ sym, (prog.overrides sym).isNone = true) (k : Nat) :
    prog.hookAtOff? k = none := by
  have e1 : (prog.stubs.findSome? fun (n, o) => if o == k then prog.externs n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (h_ext n)]
  have e2 : (prog.symbols.findSome? fun (n, o) => if o == k then prog.overrides n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (h_ovr n)]
  unfold Program.hookAtOff?
  rw [e1, e2]
  rfl

/-- Check that all extern stubs in `stubs` have offset `≥ textEnd`. -/
def noStubBefore (textEnd : Nat) : List (String × Nat) → Bool
  | [] => true
  | (_, o) :: rest => if Nat.ble textEnd o then noStubBefore textEnd rest else false

private theorem findSome?_stubs_eq_none_of_noStubBefore {textEnd k : Nat} (hk : k < textEnd)
    (ext : String → Option (State → State)) :
    ∀ {stubs : List (String × Nat)},
      noStubBefore textEnd stubs = true →
      (stubs.findSome? fun (n, o) => if o == k then ext n else none) = none
  | [], _ => rfl
  | (_, o) :: rest, h => by
    simp only [noStubBefore] at h
    split at h <;> try contradiction
    rename_i hle
    have hne : (o == k) = false :=
      beq_eq_false_iff_ne.mpr (by have := Nat.le_of_ble_eq_true hle; omega)
    simp only [List.findSome?_cons, hne, Bool.false_eq_true, ↓reduceIte]
    exact findSome?_stubs_eq_none_of_noStubBefore hk ext h

/-- When all stubs lie at offsets `≥ textEnd` (`noStubBefore textEnd prog.stubs = true`) and
    `overrides` is empty, no hook sits at any offset `k < textEnd`, regardless of `prog.externs`. -/
theorem hookAtOff?_eq_none_of_noStubBefore {prog : Program} {textEnd k : Nat}
    (h_stubs : noStubBefore textEnd prog.stubs = true)
    (h_ovr : ∀ sym, (prog.overrides sym).isNone = true)
    (hk : k < textEnd) :
    prog.hookAtOff? k = none := by
  have e1 := findSome?_stubs_eq_none_of_noStubBefore hk prog.externs h_stubs
  have e2 : (prog.symbols.findSome? fun (n, o) => if o == k then prog.overrides n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (h_ovr n)]
  unfold Program.hookAtOff?
  rw [e1, e2]
  rfl

/-- Soundness of `WordTree.fetchDecodeAt`: any instruction decoded from a well-formed `WordTree`
    for `prog.code` at offset `off` is fetched by `prog.fetch` at `prog.base + off` when no hook
    has its entry point at `off`. -/
theorem fetch_of_wordTree {prog : Program} {t : WordTree} (n : Nat)
    (hcode : prog.code = t.toBytes)
    (hwf : t.checkSize? = some n)
    {off : Nat} {inst : Instr}
    (h : t.fetchDecodeAt off = some inst)
    (hoff : off < 2 ^ 64 := by decide)
    (hhook : prog.hookAtOff? off = none := by
      exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _) :
    prog.fetch (prog.base + BitVec.ofNat 64 off) = some inst := by
  simp only [WordTree.fetchDecodeAt] at h
  split at h <;> try contradiction
  rename_i b0 b1 b2 b3 hget
  split at h <;> try contradiction
  rename_i hoff_eq
  have hoff4 : off = 4 * (off / 4) := beq_iff_eq.mp hoff_eq
  rcases WordTree.getQuad?_drop_toBytesAux t [] (off / 4) hwf hget with ⟨rest, hdrop⟩
  have hsub : (prog.base + BitVec.ofNat 64 off - prog.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
  unfold Program.fetch Program.externAt?
  rw [hsub, hhook]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Program.readWordOff]
  rw [hcode, WordTree.toBytes, hoff4, hdrop]
  have hal : ¬(4 * (off / 4) % 4 ≠ 0) := by omega
  simp only [hal, ↓reduceIte]
  exact h


end

public meta section

open Lean Meta in
/-- Unfold `e` to weak-head normal form, zeta-reducing any `let` chunks, and return the elements
    of the resulting `List.cons` spine without touching the element `Expr`s. -/
partial def listElemsWhnf (e : Expr) : MetaM (Array Expr) := do
  let mut elems : Array Expr := #[]
  let mut cur := e
  for _ in [0 : 100000000] do
    while cur.isLet do
      cur := cur.letBody!.instantiate1 cur.letValue!
    if !cur.isAppOfArity ``List.cons 3 then
      cur ← withTransparency .all (whnf cur)
    if cur.isAppOfArity ``List.cons 3 then
      elems := elems.push (cur.getArg! 1)
      cur := cur.getArg! 2
    else
      break
  return elems

open Lean Elab Term Meta in
/-- Build a balanced `WordTree` from `<prog>.code` at elaboration time, unfolding `<prog>`
    (e.g. `Program.mk`, `Program.ofImage`, or an `Obj.Image` constant) by `whnf`, unwrapping
    `Expr.letE` chunks from list literals and reusing the exact `BitVec 8` `Expr` nodes so
    `<prog>.code = <tree>.toBytes` checks by pointer equality in the kernel. -/
scoped elab "word_tree_of% " progId:ident : term => do
  let c ← realizeGlobalConstNoOverload progId
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Program.code) (Lean.mkConst c))
  let leafFn := Lean.mkConst ``WordTree.leaf
  let nodeFn := Lean.mkConst ``WordTree.node
  let emptyTree := Lean.mkConst ``WordTree.empty
  let rec build (fuel : Nat) (lo hi : Nat) : TermElabM Expr := do
    match fuel with
    | 0 => return emptyTree
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then
        return emptyTree
      else if len == 1 then
        let baseIdx := 4 * lo
        return mkApp4 leafFn (elems[baseIdx]!) (elems[baseIdx + 1]!) (elems[baseIdx + 2]!) (elems[baseIdx + 3]!)
      else
        let half := len / 2
        let mid := lo + half
        let l ← build fuel' lo mid
        let r ← build fuel' mid hi
        return mkApp3 nodeFn (mkRawNatLit half) l r
  build 64 0 (elems.size / 4)

end

@[expose] public section

/-! ## `List Char` Symbol-Table Reflection for `Program.fnOff` -/

/-- Structural `Bool` equality on `List Nat` using primitive kernel `Nat.beq`. -/
def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | n₁ :: ns₁, n₂ :: ns₂ => if Nat.beq n₁ n₂ then natListBeq ns₁ ns₂ else false
  | _, _ => false

private theorem natListBeq_eq_false : ∀ {l₁ l₂ : List Nat}, natListBeq l₁ l₂ = false → l₁ ≠ l₂
  | [], [], h => by contradiction
  | _ :: _, [], _ => nofun
  | [], _ :: _, _ => nofun
  | n₁ :: ns₁, n₂ :: ns₂, h => by
    simp only [natListBeq] at h
    split at h
    · intro hcons
      injection hcons with _ htail
      exact natListBeq_eq_false h htail
    · rename_i hne
      intro hcons
      injection hcons with hhead _
      subst hhead
      exact absurd (Nat.beq_eq.mpr rfl) hne

/-- Precompute `(length, codepoints)` for a `List Char` symbol key once in $O(|s|)$ so pairwise
    freshness checks compare cached lengths first and never re-evaluate `Char.val.toNat`. -/
def encodeCharKey (cs : List Char) : Nat × List Nat :=
  let ns := cs.map (fun c => c.val.toNat)
  (ns.length, ns)

/-- Fast equality check on pre-encoded `(length, codepoints)` keys: checks length equality first. -/
def natEntryBeq (e₁ e₂ : Nat × List Nat) : Bool :=
  if Nat.beq e₁.1 e₂.1 then natListBeq e₁.2 e₂.2 else false

private theorem natEntryBeq_eq_false {e₁ e₂ : Nat × List Nat} (h : natEntryBeq e₁ e₂ = false) :
    e₁ ≠ e₂ := by
  simp only [natEntryBeq] at h
  split at h
  · intro heq
    exact natListBeq_eq_false h (congrArg Prod.snd heq)
  · rename_i hlen
    intro heq
    exact absurd (Nat.beq_eq.mpr (congrArg Prod.fst heq)) hlen

private theorem string_beq_of_natEntryBeq_false {l₁ l₂ : List Char}
    (h : natEntryBeq (encodeCharKey l₁) (encodeCharKey l₂) = false) :
    (String.ofList l₁ == String.ofList l₂) = false :=
  beq_eq_false_iff_ne.mpr (mt String.ofList_inj.mp (mt (congrArg encodeCharKey) (natEntryBeq_eq_false h)))

/-- Map a reflected `List Char` symbol table back to `List (String × Nat)`. -/
def toStringSymbols : List (List Char × Nat) → List (String × Nat)
  | [] => []
  | (cs, addr) :: rest => (String.ofList cs, addr) :: toStringSymbols rest

/-- Pre-encode all symbol keys in $O(M)$ before pairwise freshness checking. -/
def prepareCharSymbols : List (List Char × Nat) → List (Nat × List Nat)
  | [] => []
  | (cs, _) :: rest => encodeCharKey cs :: prepareCharSymbols rest

/-- Check that `e` does not appear in the remaining pre-encoded symbol list. -/
def natEntryFresh (e : Nat × List Nat) : List (Nat × List Nat) → Bool
  | [] => true
  | e' :: r => if natEntryBeq e e' then false else natEntryFresh e r

/-- Check that all pre-encoded symbol keys are pairwise distinct. -/
def allFreshEntries : List (Nat × List Nat) → Bool
  | [] => true
  | e :: rest => if natEntryFresh e rest then allFreshEntries rest else false

/-- Check that all symbol keys in a reflected symbol table are pairwise distinct. -/
def allFreshCharSymbols (syms : List (List Char × Nat)) : Bool :=
  allFreshEntries (prepareCharSymbols syms)

private theorem natEntryFresh_getElem {cs₀ : List Char} :
    ∀ (tl : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs₀) (prepareCharSymbols tl) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        tl[k]? = some (cs, addr) → natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs) = false
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl', hfresh, k, _, _, hk => by
    simp only [prepareCharSymbols, natEntryFresh] at hfresh
    split at hfresh
    · contradiction
    · rename_i hne01
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact Bool.eq_false_of_ne_true hne01
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact natEntryFresh_getElem tl' hfresh k' hk

private theorem findSymbol_of_allFresh :
    ∀ (syms : List (List Char × Nat)),
      allFreshEntries (prepareCharSymbols syms) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        syms[k]? = some (cs, addr) →
        (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) = some (String.ofList cs, addr)
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharSymbols, allFreshEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        simp only [toStringSymbols, List.find?, beq_self_eq_true]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [toStringSymbols, List.find?]
        rw [string_beq_of_natEntryBeq_false (natEntryFresh_getElem tl hfresh k' hk)]
        exact findSymbol_of_allFresh tl h k' hk
    · contradiction

private theorem toStringSymbols_getElem? :
    ∀ (syms : List (List Char × Nat)) (k : Nat) {name : String} {addr : Nat},
      (toStringSymbols syms)[k]? = some (name, addr) →
      ∃ cs, syms[k]? = some (cs, addr) ∧ name = String.ofList cs
  | [], _, _, _, hk => by simp [toStringSymbols] at hk
  | (cs₀, _) :: _, 0, _, _, hk => by
    simp only [toStringSymbols, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
    rcases hk with ⟨rfl, rfl⟩
    exact ⟨cs₀, rfl, rfl⟩
  | (_, _) :: tl, k + 1, _, _, hk => by
    simp only [toStringSymbols, List.getElem?_cons_succ] at hk
    exact toStringSymbols_getElem? tl k hk

/-- Soundness of symbol-table reflection: if `prog.symbols = toStringSymbols syms` and all keys in
    `syms` are pairwise distinct (`allFreshCharSymbols syms = true`), then `prog.fnOff name = off`
    follows from $O(k)$ list indexing `prog.symbols[k]? = some (name, off)`. -/
theorem fnOff_of_allFresh {prog : Program} (syms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols syms)
    (hfresh : allFreshCharSymbols syms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : prog.symbols[k]? = some (name, off)) :
    prog.fnOff name = off := by
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? syms k hk with ⟨cs, hk_cs, rfl⟩
  simp only [Program.fnOff, Program.findSymbol?, hsyms,
             findSymbol_of_allFresh syms hfresh k hk_cs, Option.orElse, Option.map, Option.getD]


private theorem findSymbol_none_of_fresh {cs : List Char} :
    ∀ (syms : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs) (prepareCharSymbols syms) = true →
      (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) = none
  | [], _ => rfl
  | (cs₀, _) :: tl, h => by
    simp only [prepareCharSymbols, natEntryFresh] at h
    split at h
    · contradiction
    · rename_i hne
      have hbeq : (String.ofList cs₀ == String.ofList cs) = false :=
        beq_eq_false_iff_ne.mpr
          (Ne.symm (mt String.ofList_inj.mp (mt (congrArg encodeCharKey) (natEntryBeq_eq_false (Bool.eq_false_of_ne_true hne)))))
      simp only [toStringSymbols, List.find?, hbeq]
      exact findSymbol_none_of_fresh tl h

/-- Check that every pre-encoded entry in `stubEntries` is absent from `symEntries`. -/
def allDisjointEntries : List (Nat × List Nat) → List (Nat × List Nat) → Bool
  | [], _ => true
  | e :: rest, symEntries =>
    if natEntryFresh e symEntries then allDisjointEntries rest symEntries else false

/-- Check that all keys in `stubSyms` are pairwise distinct and disjoint from `syms`. -/
def wfStubCharSymbols (stubSyms syms : List (List Char × Nat)) : Bool :=
  let stubEntries := prepareCharSymbols stubSyms
  let symEntries := prepareCharSymbols syms
  if allFreshEntries stubEntries then allDisjointEntries stubEntries symEntries else false

private theorem natEntryFresh_of_allDisjoint {symEntries : List (Nat × List Nat)} :
    ∀ (stubSyms : List (List Char × Nat)),
      allDisjointEntries (prepareCharSymbols stubSyms) symEntries = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        stubSyms[k]? = some (cs, addr) →
        natEntryFresh (encodeCharKey cs) symEntries = true
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharSymbols, allDisjointEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact hfresh
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact natEntryFresh_of_allDisjoint tl h k' hk
    · contradiction

/-- Soundness of symbol-table reflection for extern stubs: if `name` is at index `k` in
    `prog.stubs` with offset `off`, and the stub keys are pairwise distinct and disjoint from the
    symbol keys (`wfStubCharSymbols stubSyms syms = true`), then `prog.fnOff name = off`. -/
theorem fnOff_of_stub {prog : Program}
    (syms stubSyms : List (List Char × Nat))
    (hsyms : prog.symbols = toStringSymbols syms)
    (hstubs : prog.stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms syms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : prog.stubs[k]? = some (name, off)) :
    prog.fnOff name = off := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  rw [hstubs] at hk
  rcases toStringSymbols_getElem? stubSyms k hk with ⟨cs, hk_cs, rfl⟩
  have hdisj := natEntryFresh_of_allDisjoint stubSyms hwf k hk_cs
  simp only [Program.fnOff, Program.findSymbol?, hsyms, hstubs,
             findSymbol_none_of_fresh syms hdisj,
             findSymbol_of_allFresh stubSyms hfresh_st k hk_cs,
             Option.orElse, Option.map, Option.getD]

private theorem filterSymbol_nil_of_fresh {cs : List Char} :
    ∀ (syms : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs) (prepareCharSymbols syms) = true →
      (toStringSymbols syms).filter (fun p => p.1 == String.ofList cs) = []
  | [], _ => rfl
  | (cs₀, _) :: tl, h => by
    simp only [prepareCharSymbols, natEntryFresh] at h
    split at h
    · contradiction
    · rename_i hne
      have hbeq : (String.ofList cs₀ == String.ofList cs) = false :=
        beq_eq_false_iff_ne.mpr
          (Ne.symm (mt String.ofList_inj.mp (mt (congrArg encodeCharKey)
            (natEntryBeq_eq_false (Bool.eq_false_of_ne_true hne)))))
      simp only [toStringSymbols, List.filter, hbeq]
      exact filterSymbol_nil_of_fresh tl h

private theorem filterSymbol_of_allFresh :
    ∀ (syms : List (List Char × Nat)),
      allFreshEntries (prepareCharSymbols syms) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        syms[k]? = some (cs, addr) →
        (toStringSymbols syms).filter (fun p => p.1 == String.ofList cs) =
          [(String.ofList cs, addr)]
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharSymbols, allFreshEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        simp only [toStringSymbols, List.filter, beq_self_eq_true,
          filterSymbol_nil_of_fresh tl hfresh]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [toStringSymbols, List.filter]
        rw [string_beq_of_natEntryBeq_false (natEntryFresh_getElem tl hfresh k' hk)]
        exact filterSymbol_of_allFresh tl h k' hk
    · contradiction

private theorem any_eq_false_of_find?_eq_none {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.find? p = none → xs.any p = false
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.find?] at h
    cases hx : p x
    · rw [hx] at h
      simp only [List.any_cons, hx, Bool.false_or]
      exact any_eq_false_of_find?_eq_none p rest h
    · rw [hx] at h; nomatch h

private theorem any_eq_true_of_find?_eq_some {α : Type} (p : α → Bool) {y : α} :
    ∀ (xs : List α), xs.find? p = some y → xs.any p = true
  | [], h => nomatch h
  | x :: rest, h => by
    simp only [List.find?] at h
    cases hx : p x
    · rw [hx] at h
      simp only [List.any_cons, hx, Bool.false_or]
      exact any_eq_true_of_find?_eq_some p rest h
    · simp only [List.any_cons, hx, Bool.true_or]

private theorem findStub_none_of_allDisjoint {cs : List Char} {addr : Nat}
    {charSyms : List (List Char × Nat)} (k : Nat) (hk : charSyms[k]? = some (cs, addr)) :
    ∀ (stubSyms : List (List Char × Nat)),
      allDisjointEntries (prepareCharSymbols stubSyms) (prepareCharSymbols charSyms) = true →
      (toStringSymbols stubSyms).find? (fun p => p.1 == String.ofList cs) = none
  | [], _ => rfl
  | (cs₀, _) :: tl, h => by
    simp only [prepareCharSymbols, allDisjointEntries] at h
    split at h
    · rename_i hfresh
      simp only [toStringSymbols, List.find?,
        string_beq_of_natEntryBeq_false (natEntryFresh_getElem charSyms hfresh k hk)]
      exact findStub_none_of_allDisjoint k hk tl h
    · contradiction

/-- If `syms = toStringSymbols charSyms`, `allFreshCharSymbols charSyms = true`, and
    `syms[k]? = some (name, off)`, then `Obj.lookup name syms = some off`. -/
theorem lookup_of_allFresh {syms : List (String × Nat)} (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    Obj.lookup name syms = some off := by
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? charSyms k hk with ⟨cs, hk_cs, rfl⟩
  simp only [Obj.lookup, hsyms, findSymbol_of_allFresh charSyms hfresh k hk_cs, Option.map]

/-- If `syms = toStringSymbols charSyms`, `allFreshCharSymbols charSyms = true`, and
    `syms[k]? = some (name, off)`, then `Obj.lookupUnique name syms = some off`. -/
theorem lookupUnique_of_allFresh {syms : List (String × Nat)} (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    Obj.lookupUnique name syms = some off := by
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? charSyms k hk with ⟨cs, hk_cs, rfl⟩
  simp only [Obj.lookupUnique, hsyms, filterSymbol_of_allFresh charSyms hfresh k hk_cs]

/-- If `syms = toStringSymbols charSyms`, `allFreshCharSymbols charSyms = true`, and
    `syms[k]? = some (name, off)`, then `syms.filter (·.1 == name) = [(name, off)]`. -/
theorem filter_of_allFresh {syms : List (String × Nat)} (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    syms.filter (·.1 == name) = [(name, off)] := by
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? charSyms k hk with ⟨cs, hk_cs, rfl⟩
  rw [hsyms]
  exact filterSymbol_of_allFresh charSyms hfresh k hk_cs

/-- If `syms = toStringSymbols charSyms`, `allFreshCharSymbols charSyms = true`, and
    `syms[k]? = some (name, off)`, then `(syms.filter (·.1 == name)).length = 1`. -/
theorem filter_length_of_allFresh {syms : List (String × Nat)} (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    (syms.filter (·.1 == name)).length = 1 := by
  rw [filter_of_allFresh charSyms hsyms hfresh k hk]; rfl

/-- If `syms = toStringSymbols charSyms`, `allFreshCharSymbols charSyms = true`, and
    `syms[k]? = some (name, off)`, then `syms.any (·.1 == name) = true`. -/
theorem any_of_allFresh {syms : List (String × Nat)} (charSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hfresh : allFreshCharSymbols charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    syms.any (·.1 == name) = true := by
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? charSyms k hk with ⟨cs, hk_cs, rfl⟩
  rw [hsyms]
  exact any_eq_true_of_find?_eq_some _ _ (findSymbol_of_allFresh charSyms hfresh k hk_cs)

/-- If `stubs = toStringSymbols stubSyms`, `wfStubCharSymbols stubSyms charSyms = true`, and
    `stubs[k]? = some (name, off)`, then `Obj.lookup name stubs = some off`. -/
theorem lookup_stub_of_wf {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    Obj.lookup name stubs = some off := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  exact lookup_of_allFresh stubSyms hstubs hfresh_st k hk

/-- If `stubs = toStringSymbols stubSyms`, `wfStubCharSymbols stubSyms charSyms = true`, and
    `stubs[k]? = some (name, off)`, then `Obj.lookupUnique name stubs = some off`. -/
theorem lookupUnique_stub_of_wf {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    Obj.lookupUnique name stubs = some off := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  exact lookupUnique_of_allFresh stubSyms hstubs hfresh_st k hk

/-- If `stubs = toStringSymbols stubSyms`, `wfStubCharSymbols stubSyms charSyms = true`, and
    `stubs[k]? = some (name, off)`, then `(stubs.filter (·.1 == name)).length = 1`. -/
theorem filter_length_stub_of_wf {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    (stubs.filter (·.1 == name)).length = 1 := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  exact filter_length_of_allFresh stubSyms hstubs hfresh_st k hk

/-- If `stubs = toStringSymbols stubSyms`, `wfStubCharSymbols stubSyms charSyms = true`, and
    `stubs[k]? = some (name, off)`, then `stubs.any (·.1 == name) = true`. -/
theorem any_stub_of_wf {stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    stubs.any (·.1 == name) = true := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  exact any_of_allFresh stubSyms hstubs hfresh_st k hk

/-- If `name` is at index `k` in `stubs` and `wfStubCharSymbols stubSyms charSyms = true`,
    then `Obj.lookup name syms = none`. -/
theorem lookup_symbols_none_of_stub {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    Obj.lookup name syms = none := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rw [hstubs] at hk
  rcases toStringSymbols_getElem? stubSyms k hk with ⟨cs, hk_cs, rfl⟩
  have hdisj := natEntryFresh_of_allDisjoint stubSyms hwf k hk_cs
  simp only [Obj.lookup, hsyms, findSymbol_none_of_fresh charSyms hdisj, Option.map]

/-- If `name` is at index `k` in `stubs` and `wfStubCharSymbols stubSyms charSyms = true`,
    then `syms.any (·.1 == name) = false`. -/
theorem any_symbols_false_of_stub {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : stubs[k]? = some (name, off)) :
    syms.any (·.1 == name) = false := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rw [hstubs] at hk
  rcases toStringSymbols_getElem? stubSyms k hk with ⟨cs, hk_cs, rfl⟩
  have hdisj := natEntryFresh_of_allDisjoint stubSyms hwf k hk_cs
  rw [hsyms]
  exact any_eq_false_of_find?_eq_none _ _ (findSymbol_none_of_fresh charSyms hdisj)

/-- If `name` is at index `k` in `syms` and `wfStubCharSymbols stubSyms charSyms = true`,
    then `stubs.any (·.1 == name) = false`. -/
theorem any_stubs_false_of_symbol {syms stubs : List (String × Nat)}
    (charSyms stubSyms : List (List Char × Nat))
    (hsyms : syms = toStringSymbols charSyms)
    (hstubs : stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms charSyms = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : syms[k]? = some (name, off)) :
    stubs.any (·.1 == name) = false := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rw [hsyms] at hk
  rcases toStringSymbols_getElem? charSyms k hk with ⟨cs, hk_cs, rfl⟩
  rw [hstubs]
  exact any_eq_false_of_find?_eq_none _ _ (findStub_none_of_allDisjoint k hk_cs stubSyms hwf)

open Lean Elab Term Meta in
/-- Build the `List Char` expression (`List.cons (Char.ofNat n) ...`) for `s : String`. -/
meta def mkStrCharsExpr (s : String) : Expr :=
  let cs := s.toList
  let c := Lean.mkConst ``Char
  let charOfNat := Lean.mkConst ``Char.ofNat
  let consFn := Lean.mkApp (Lean.mkConst ``List.cons [Lean.Level.zero]) c
  let nilExpr := Lean.mkApp (Lean.mkConst ``List.nil [Lean.Level.zero]) c
  cs.foldr (fun ch acc =>
    Lean.mkApp2 consFn (Lean.mkApp charOfNat (Lean.mkRawNatLit ch.toNat)) acc) nilExpr

open Lean Elab Term Meta in
/-- `str_chars% "s"` (or `str_chars% symConst`): the `List Char` literal of `s`. -/
elab "str_chars% " s:term:arg : term => do
  let strVal ← match s.raw.isStrLit? with
    | some str => pure str
    | none =>
      let e ← elabTerm s (some (Lean.mkConst ``String))
      let e ← instantiateMVars e
      if let .lit (.strVal str) := e then pure str
      else if let .lit (.strVal str) := (← withTransparency .all (whnf e)) then pure str
      else throwError "str_chars%: expected string literal or constant, got {e}"
  return mkStrCharsExpr strVal

end

public meta section

open Lean Elab Term Meta in
private def elabSymCharsOfField (progId : Ident) (field : Name) : TermElabM Expr := do
  let c ← realizeGlobalConstNoOverload progId
  let entries ← listElemsWhnf (mkApp (Lean.mkConst field) (Lean.mkConst c))
  let mut pairs : Array (Expr × Expr) := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    unless pairExpr.isAppOfArity ``Prod.mk 4 do
      throwError "expected `Prod.mk` entry in symbol table, got {pairExpr}"
    let strExpr := pairExpr.getArg! 2
    let offExpr := pairExpr.getArg! 3
    let some s ← (do
        if let .lit (.strVal s) := strExpr then pure (some s)
        else if let .lit (.strVal s) := (← withTransparency .all (whnf strExpr)) then pure (some s)
        else pure none)
      | throwError "expected string literal in symbol table, got {strExpr}"
    pairs := pairs.push (toExpr s.toList, offExpr)
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let natType := Lean.mkConst ``Nat
  let prodType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType natType
  let prodMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType natType
  let nilExpr := mkApp (Lean.mkConst ``List.nil [Level.zero]) prodType
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) prodType
  let mut acc := nilExpr
  for i in [0 : pairs.size] do
    let (csExpr, offExpr) := pairs[pairs.size - 1 - i]!
    acc := mkApp2 consFn (mkApp2 prodMk csExpr offExpr) acc
  return acc

/-- Build the reflected `List (List Char × Nat)` symbol table from `<prog>.symbols` at
    elaboration time, matching the kernel's `string_lit_to_constructor` representation. -/
scoped elab "sym_chars_of% " progId:ident : term => elabSymCharsOfField progId ``Program.symbols

/-- Build the reflected `List (List Char × Nat)` extern-stub table from `<prog>.stubs` at
    elaboration time. -/
scoped elab "stub_chars_of% " progId:ident : term => elabSymCharsOfField progId ``Program.stubs

end

@[expose] public section

/-! ## Stub Offset Reflection for `Program.hookAtOff?` -/

/-- Check that offset `o` does not appear in the remaining stub list. -/
def offsetFresh (o : Nat) : List (String × Nat) → Bool
  | [] => true
  | (_, o') :: rest => if Nat.beq o o' then false else offsetFresh o rest

/-- Check that all stub offsets in `stubs` are pairwise distinct. -/
def allFreshOffsets : List (String × Nat) → Bool
  | [] => true
  | (_, o) :: rest => if offsetFresh o rest then allFreshOffsets rest else false

private theorem findSome?_stubs_eq_none_of_offsetFresh {off : Nat}
    (ext : String → Option (State → State)) :
    ∀ {stubs : List (String × Nat)},
      offsetFresh off stubs = true →
      (stubs.findSome? fun (n, o) => if o == off then ext n else none) = none
  | [], _ => rfl
  | (_, o) :: rest, h => by
    simp only [offsetFresh] at h
    split at h <;> try contradiction
    rename_i hne
    have hbeq : (o == off) = false :=
      beq_eq_false_iff_ne.mpr (Ne.symm (mt Nat.beq_eq.mpr hne))
    simp only [List.findSome?_cons, hbeq, Bool.false_eq_true, ↓reduceIte]
    exact findSome?_stubs_eq_none_of_offsetFresh ext h

private theorem offsetFresh_getElem {o₀ : Nat} :
    ∀ (tl : List (String × Nat)),
      offsetFresh o₀ tl = true →
      ∀ (k : Nat) {name : String} {off : Nat},
        tl[k]? = some (name, off) → (o₀ == off) = false
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl', hfresh, k, _, _, hk => by
    simp only [offsetFresh] at hfresh
    split at hfresh
    · contradiction
    · rename_i hne
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact beq_eq_false_iff_ne.mpr (mt Nat.beq_eq.mpr hne)
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact offsetFresh_getElem tl' hfresh k' hk

private theorem findSome?_stubs_of_allFreshOffsets (ext : String → Option (State → State)) :
    ∀ (stubs : List (String × Nat)),
      allFreshOffsets stubs = true →
      ∀ (k : Nat) {name : String} {off : Nat},
        stubs[k]? = some (name, off) →
        (stubs.findSome? fun (n, o) => if o == off then ext n else none) = ext name
  | [], _, _, _, _, hk => by simp at hk
  | (n₀, _) :: tl, h, k, _, _, hk => by
    simp only [allFreshOffsets] at h
    split at h <;> try contradiction
    rename_i hfresh
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
      rcases hk with ⟨rfl, rfl⟩
      simp only [List.findSome?_cons, beq_self_eq_true, ↓reduceIte]
      cases ext n₀ with
      | none => exact findSome?_stubs_eq_none_of_offsetFresh ext hfresh
      | some _ => rfl
    | succ k' =>
      simp only [List.getElem?_cons_succ] at hk
      simp only [List.findSome?_cons, offsetFresh_getElem tl hfresh k' hk,
        Bool.false_eq_true, ↓reduceIte]
      exact findSome?_stubs_of_allFreshOffsets ext tl h k' hk

/-- Soundness of stub-offset reflection for `Program.hookAtOff?`: if all stub offsets in
    `prog.stubs` are pairwise distinct (`allFreshOffsets prog.stubs = true`), `overrides` is
    empty, and `prog.stubs[k]? = some (name, off)`, then `prog.hookAtOff? off = prog.externs name`. -/
theorem hookAtOff?_of_stub {prog : Program}
    (hfresh : allFreshOffsets prog.stubs = true)
    (hovr : ∀ sym, (prog.overrides sym).isNone = true)
    (k : Nat) {name : String} {off : Nat}
    (hk : prog.stubs[k]? = some (name, off)) :
    prog.hookAtOff? off = prog.externs name := by
  have e1 := findSome?_stubs_of_allFreshOffsets prog.externs prog.stubs hfresh k hk
  have e2 : (prog.symbols.findSome? fun (n, o) => if o == off then prog.overrides n else none) = none :=
    findSome?_eq_none_of_forall fun ⟨n, _⟩ _ => by
      simp [Option.isNone_iff_eq_none.mp (hovr n)]
  unfold Program.hookAtOff?
  rw [e1, e2, Option.or_none]

/-! ## `List Char` Association-List Reflection -/

/-- Map a reflected `List Char` association list back to `List (String × α)`. -/
def toStringAssoc {α : Type} : List (List Char × α) → List (String × α)
  | [] => []
  | (cs, v) :: rest => (String.ofList cs, v) :: toStringAssoc rest

/-- Pre-encode all keys in `List (List Char × α)` before pairwise freshness checking. -/
def prepareCharAssoc {α : Type} : List (List Char × α) → List (Nat × List Nat)
  | [] => []
  | (cs, _) :: rest => encodeCharKey cs :: prepareCharAssoc rest

/-- Check that all keys in a reflected association list are pairwise distinct. -/
def allFreshCharAssoc {α : Type} (syms : List (List Char × α)) : Bool :=
  allFreshEntries (prepareCharAssoc syms)

private theorem natEntryFresh_getElem_assoc {α : Type} {cs₀ : List Char} :
    ∀ (tl : List (List Char × α)),
      natEntryFresh (encodeCharKey cs₀) (prepareCharAssoc tl) = true →
      ∀ (k : Nat) {cs : List Char} {v : α},
        tl[k]? = some (cs, v) → natEntryBeq (encodeCharKey cs₀) (encodeCharKey cs) = false
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl', hfresh, k, _, _, hk => by
    simp only [prepareCharAssoc, natEntryFresh] at hfresh
    split at hfresh
    · contradiction
    · rename_i hne01
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        exact Bool.eq_false_of_ne_true hne01
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        exact natEntryFresh_getElem_assoc tl' hfresh k' hk

theorem findAssoc_of_allFresh {α : Type} :
    ∀ (syms : List (List Char × α)),
      allFreshEntries (prepareCharAssoc syms) = true →
      ∀ (k : Nat) {cs : List Char} {v : α},
        syms[k]? = some (cs, v) →
        (toStringAssoc syms).find? (fun p => p.1 == String.ofList cs) = some (String.ofList cs, v)
  | [], _, _, _, _, hk => by simp at hk
  | (_, _) :: tl, h, k, _, _, hk => by
    simp only [prepareCharAssoc, allFreshEntries] at h
    split at h
    · rename_i hfresh
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        rcases hk with ⟨rfl, rfl⟩
        simp only [toStringAssoc, List.find?, beq_self_eq_true]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [toStringAssoc, List.find?]
        rw [string_beq_of_natEntryBeq_false (natEntryFresh_getElem_assoc tl hfresh k' hk)]
        exact findAssoc_of_allFresh tl h k' hk
    · contradiction


/-! ## Linear $O(N)$ Strict-Sorted Symbol Freshness -/

/-- Strict lexicographic order on codepoint lists using primitive `Nat.beq` and `Nat.blt`. -/
def natListLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if Nat.beq a b then natListLt as bs else Nat.blt a b

/-- Strict lexicographic order on `List Char` codepoints using primitive kernel `Nat.beq` / `Nat.blt`
    (matches UTF-8 byte order `as_bytes().cmp`). -/
def charListLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if Nat.beq a.val.toNat b.val.toNat then charListLt as bs
    else Nat.blt a.val.toNat b.val.toNat

/-- `true` iff adjacent elements are strictly `lt`-increasing. -/
def strictChain {α : Type} (lt : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => if lt a b then strictChain lt (b :: rest) else false

/-- Linear `O(N)` check that a reflected `(List Char × α)` table is strictly sorted in canonical
    `charListLt` (UTF-8 byte) order (`N - 1` adjacent kernel comparisons). -/
def isStrictSorted {α : Type} (syms : List (List Char × α)) : Bool :=
  strictChain (fun a b => charListLt a.1 b.1) syms

private theorem if_true_eq {α : Type} (t e : α) : (if true = true then t else e) = t := rfl
private theorem if_false_eq {α : Type} (t e : α) : (if false = true then t else e) = e := rfl

private theorem beq_eq_false_of_ne {a b : Nat} (h : a ≠ b) : a.beq b = false := by
  cases hb : a.beq b with
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
  | false => rfl

theorem natListLt_irrefl : ∀ l : List Nat, natListLt l l = false
  | [] => rfl
  | a :: as => by
    change (if Nat.beq a a = true then natListLt as as else Nat.blt a a) = false
    rw [Nat.beq_refl, if_true_eq, natListLt_irrefl as]

theorem natListLt_trans : ∀ {l₁ l₂ l₃ : List Nat},
    natListLt l₁ l₂ = true → natListLt l₂ l₃ = true → natListLt l₁ l₃ = true
  | [], [], _, h₁, _ => nomatch h₁
  | [], _ :: _, [], _, h₂ => nomatch h₂
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h₁, _ => nomatch h₁
  | _ :: _, _ :: _, [], _, h₂ => nomatch h₂
  | a :: as, b :: bs, c :: cs, h₁, h₂ => by
    change (if Nat.beq a b = true then natListLt as bs else Nat.blt a b) = true at h₁
    change (if Nat.beq b c = true then natListLt bs cs else Nat.blt b c) = true at h₂
    change (if Nat.beq a c = true then natListLt as cs else Nat.blt a c) = true
    cases hab : Nat.beq a b <;> cases hbc : Nat.beq b c
    · rw [hab, if_false_eq, Nat.blt_eq] at h₁
      rw [hbc, if_false_eq, Nat.blt_eq] at h₂
      have hlt : a < c := Nat.lt_trans h₁ h₂
      rw [beq_eq_false_of_ne (Nat.ne_of_lt hlt), if_false_eq, Nat.blt_eq]
      exact hlt
    · rw [hab, if_false_eq] at h₁
      have hab' : a ≠ b := Nat.ne_of_beq_eq_false hab
      have hbc_eq : b = c := Nat.eq_of_beq_eq_true hbc
      rw [beq_eq_false_of_ne (hbc_eq ▸ hab'), if_false_eq]
      exact hbc_eq ▸ h₁
    · rw [hbc, if_false_eq] at h₂
      have hbc' : b ≠ c := Nat.ne_of_beq_eq_false hbc
      have hab_eq : a = b := Nat.eq_of_beq_eq_true hab
      rw [beq_eq_false_of_ne (hab_eq ▸ hbc'), if_false_eq]
      exact hab_eq ▸ h₂
    · rw [hab, if_true_eq] at h₁
      rw [hbc, if_true_eq] at h₂
      have hac : a = c := (Nat.eq_of_beq_eq_true hab).trans (Nat.eq_of_beq_eq_true hbc)
      rw [hac, Nat.beq_refl, if_true_eq]
      exact natListLt_trans h₁ h₂

theorem charListLt_eq_natListLt : ∀ (cs₁ cs₂ : List Char),
    charListLt cs₁ cs₂ = natListLt (cs₁.map (fun c => c.val.toNat)) (cs₂.map (fun c => c.val.toNat))
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    change (if Nat.beq a.val.toNat b.val.toNat = true then charListLt as bs else Nat.blt a.val.toNat b.val.toNat) =
      (if Nat.beq a.val.toNat b.val.toNat = true then natListLt (as.map (fun c => c.val.toNat)) (bs.map (fun c => c.val.toNat)) else Nat.blt a.val.toNat b.val.toNat)
    rw [charListLt_eq_natListLt as bs]

theorem charListLt_irrefl (cs : List Char) : charListLt cs cs = false := by
  rw [charListLt_eq_natListLt, natListLt_irrefl]

theorem charListLt_trans {cs₁ cs₂ cs₃ : List Char}
    (h₁ : charListLt cs₁ cs₂ = true) (h₂ : charListLt cs₂ cs₃ = true) :
    charListLt cs₁ cs₃ = true := by
  rw [charListLt_eq_natListLt] at h₁ h₂ ⊢
  exact natListLt_trans h₁ h₂

theorem strictChain_pairwise {α : Type} (lt : α → α → Bool)
    (htrans : ∀ {a b c : α}, lt a b = true → lt b c = true → lt a c = true) :
    ∀ l : List α, strictChain lt l = true → l.Pairwise (fun a b => lt a b = true)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  | a :: b :: rest, h => by
    change (if lt a b = true then strictChain lt (b :: rest) else false) = true at h
    cases hab : lt a b with
    | false => rw [hab, if_false_eq] at h; nomatch h
    | true =>
      rw [hab, if_true_eq] at h
      have ih := strictChain_pairwise lt htrans (b :: rest) h
      refine List.Pairwise.cons (fun c hc => ?_) ih
      cases hc with
      | head => exact hab
      | tail _ hmem =>
        cases ih with
        | cons hrel _ => exact htrans hab (hrel c hmem)

/-- A strictly sorted reflected table has pairwise distinct `List Char` keys. -/
theorem pairwise_ne_of_strictSorted {α : Type} {syms : List (List Char × α)}
    (h : isStrictSorted syms = true) : syms.Pairwise (fun a b => a.1 ≠ b.1) :=
  (strictChain_pairwise (fun (a b : List Char × α) => charListLt a.1 b.1)
    (fun h₁ h₂ => charListLt_trans h₁ h₂) syms h).imp fun {a b} hlt heq => by
    rw [heq, charListLt_irrefl] at hlt
    exact Bool.false_ne_true hlt

private theorem natListBeq_eq_true : ∀ {l₁ l₂ : List Nat}, natListBeq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | n₁ :: ns₁, n₂ :: ns₂, h => by
    change (if Nat.beq n₁ n₂ = true then natListBeq ns₁ ns₂ else false) = true at h
    cases hn : Nat.beq n₁ n₂ with
    | false => rw [hn, if_false_eq] at h; nomatch h
    | true =>
      rw [hn, if_true_eq] at h
      rw [Nat.eq_of_beq_eq_true hn, natListBeq_eq_true h]

private theorem natEntryBeq_eq_true {e₁ e₂ : Nat × List Nat} (h : natEntryBeq e₁ e₂ = true) :
    e₁ = e₂ := by
  change (if Nat.beq e₁.1 e₂.1 = true then natListBeq e₁.2 e₂.2 else false) = true at h
  cases hlen : Nat.beq e₁.1 e₂.1 with
  | false => rw [hlen, if_false_eq] at h; nomatch h
  | true =>
    rw [hlen, if_true_eq] at h
    exact Prod.ext (Nat.eq_of_beq_eq_true hlen) (natListBeq_eq_true h)

private theorem char_map_toNat_inj :
    ∀ {l₁ l₂ : List Char},
      l₁.map (fun c => c.val.toNat) = l₂.map (fun c => c.val.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | c₁ :: cs₁, c₂ :: cs₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases h with ⟨hhd, htl⟩
    have hc : c₁ = c₂ := by
      cases c₁; cases c₂
      simp only [Char.mk.injEq, ← UInt32.toNat_inj]
      exact hhd
    rw [hc, char_map_toNat_inj htl]

/-- `String.ofList` equality (`==`) agrees with `natEntryBeq` on `encodeCharKey`. -/
theorem string_beq_eq_natEntryBeq (l₁ l₂ : List Char) :
    (String.ofList l₁ == String.ofList l₂) = natEntryBeq (encodeCharKey l₁) (encodeCharKey l₂) := by
  cases hb : natEntryBeq (encodeCharKey l₁) (encodeCharKey l₂) with
  | false => exact string_beq_of_natEntryBeq_false hb
  | true =>
    have heq := char_map_toNat_inj (congrArg Prod.snd (natEntryBeq_eq_true hb))
    subst heq
    exact beq_self_eq_true _

private theorem natEntryFresh_of_forall {e : Nat × List Nat} :
    ∀ rest : List (Nat × List Nat), (∀ e' ∈ rest, e ≠ e') → natEntryFresh e rest = true
  | [], _ => rfl
  | e' :: rest, h => by
    have hne : natEntryBeq e e' = false := by
      cases hb : natEntryBeq e e' with
      | true => exact absurd (natEntryBeq_eq_true hb) (h e' (List.Mem.head _))
      | false => rfl
    change (if natEntryBeq e e' = true then false else natEntryFresh e rest) = true
    rw [hne, if_false_eq]
    exact natEntryFresh_of_forall rest fun e'' h'' => h e'' (List.Mem.tail _ h'')

theorem allFreshEntries_of_pairwise :
    ∀ l : List (Nat × List Nat), l.Pairwise (fun a b => a ≠ b) → allFreshEntries l = true
  | [], _ => rfl
  | e :: rest, List.Pairwise.cons hfresh hrest => by
    change (if natEntryFresh e rest = true then allFreshEntries rest else false) = true
    rw [natEntryFresh_of_forall rest hfresh, if_true_eq]
    exact allFreshEntries_of_pairwise rest hrest

private theorem prepareCharAssoc_pairwise_of_strictSorted {α : Type} :
    ∀ {syms : List (List Char × α)},
      syms.Pairwise (fun a b => charListLt a.1 b.1 = true) →
      (prepareCharAssoc syms).Pairwise (fun a b => a ≠ b)
  | [], _ => List.Pairwise.nil
  | (cs, _) :: rest, List.Pairwise.cons hrel hrest => by
    refine List.Pairwise.cons ?_ (prepareCharAssoc_pairwise_of_strictSorted hrest)
    have hall : ∀ (r : List (List Char × α)),
        (∀ p ∈ r, charListLt cs p.1 = true) →
        ∀ e ∈ prepareCharAssoc r, encodeCharKey cs ≠ e := by
      intro r hr
      induction r with
      | nil => intro _ hm; nomatch hm
      | cons p tl ih =>
        intro e hm
        cases hm with
        | head =>
          have hlt := hr p (List.Mem.head _)
          rw [charListLt_eq_natListLt] at hlt
          intro heq
          have h2 : cs.map (fun c => c.val.toNat) = p.1.map (fun c => c.val.toNat) :=
            congrArg Prod.snd heq
          rw [h2, natListLt_irrefl] at hlt
          exact Bool.false_ne_true hlt
        | tail _ htl =>
          exact ih (fun q hq => hr q (List.Mem.tail _ hq)) e htl
    exact hall rest hrel

private theorem prepareCharSymbols_eq_prepareCharAssoc :
    ∀ (syms : List (List Char × Nat)), prepareCharSymbols syms = prepareCharAssoc syms
  | [] => rfl
  | _ :: rest => congrArg _ (prepareCharSymbols_eq_prepareCharAssoc rest)

/-- Prove `allFreshCharAssoc syms = true` in $N - 1$ adjacent kernel comparisons
    (`isStrictSorted syms = true`) instead of $\binom{N}{2}$. -/
theorem allFreshCharAssoc_of_strictSorted {α : Type} {syms : List (List Char × α)}
    (h : isStrictSorted syms = true) : allFreshCharAssoc syms = true :=
  allFreshEntries_of_pairwise (prepareCharAssoc syms)
    (prepareCharAssoc_pairwise_of_strictSorted
      (strictChain_pairwise (fun (a b : List Char × α) => charListLt a.1 b.1)
        (fun h₁ h₂ => charListLt_trans h₁ h₂) syms h))

/-- Prove `allFreshCharSymbols syms = true` in $N - 1$ adjacent kernel comparisons
    (`isStrictSorted syms = true`) instead of $\binom{N}{2}$. -/
theorem allFreshCharSymbols_of_strictSorted {syms : List (List Char × Nat)}
    (h : isStrictSorted syms = true) : allFreshCharSymbols syms = true := by
  unfold allFreshCharSymbols
  rw [prepareCharSymbols_eq_prepareCharAssoc]
  exact allFreshCharAssoc_of_strictSorted h


/-- Extract `4 * cnt` bytes starting at 4-byte word index `widx` from a `WordTree` onto `acc`
    in $O(\log N + \text{cnt})$ steps without `List.drop` on the flat byte list. -/
def WordTree.sliceBytesAux : WordTree → Nat → Nat → List (BitVec 8) → List (BitVec 8)
  | .empty, _, _, acc => acc
  | .leaf b0 b1 b2 b3, widx, cnt, acc =>
    if widx == 0 && cnt > 0 then b0 :: b1 :: b2 :: b3 :: acc else acc
  | .node lw l r, widx, cnt, acc =>
    if cnt == 0 then acc
    else if widx + cnt ≤ lw then
      WordTree.sliceBytesAux l widx cnt acc
    else if lw ≤ widx then
      WordTree.sliceBytesAux r (widx - lw) cnt acc
    else
      let leftCnt := lw - widx
      WordTree.sliceBytesAux l widx leftCnt (WordTree.sliceBytesAux r 0 (cnt - leftCnt) acc)

/-- Extract `span` bytes starting at byte offset `off` from `t : WordTree` of `n` words when
    `off` and `span` are 4-byte aligned and `off + span ≤ 4 * n`. -/
def WordTree.sliceBytesChecked (t : WordTree) (n off span : Nat) : Option (List (BitVec 8)) :=
  if off % 4 == 0 && span % 4 == 0 then
    let widx := off / 4
    let cnt := span / 4
    if widx + cnt ≤ n then
      some (WordTree.sliceBytesAux t widx cnt [])
    else none
  else none

private theorem WordTree.toBytesAux_eq_append :
    ∀ (t : WordTree) (acc : List (BitVec 8)),
      t.toBytesAux acc = t.toBytesAux [] ++ acc
  | .empty, _ => rfl
  | .leaf _ _ _ _, _ => rfl
  | .node _ l r, acc => by
    simp only [WordTree.toBytesAux]
    rw [toBytesAux_eq_append l (r.toBytesAux acc),
        toBytesAux_eq_append r acc, toBytesAux_eq_append l (r.toBytesAux []),
        List.append_assoc]

/-- Total byte length of a `WordTree` (`4` bytes per leaf). -/
def WordTree.byteLen : WordTree → Nat
  | .empty => 0
  | .leaf _ _ _ _ => 4
  | .node _ l r => l.byteLen + r.byteLen

private theorem WordTree.length_toBytesAux (t : WordTree) (acc : List (BitVec 8)) :
    (t.toBytesAux acc).length = t.byteLen + acc.length := by
  induction t generalizing acc with
  | empty => simp [WordTree.toBytesAux, WordTree.byteLen]
  | leaf _ _ _ _ => simp [WordTree.toBytesAux, WordTree.byteLen]; omega
  | node _ l r ihl ihr =>
    simp only [WordTree.toBytesAux, WordTree.byteLen, ihl, ihr]
    omega

/-- The flattened byte list of a `WordTree` has length `t.byteLen`. -/
@[simp] theorem WordTree.length_toBytes (t : WordTree) :
    t.toBytes.length = t.byteLen := by
  simpa [WordTree.toBytes] using WordTree.length_toBytesAux t []

theorem WordTree.length_toBytesAux_nil :
    ∀ (t : WordTree) {n : Nat},
      t.checkSize? = some n →
      (t.toBytesAux []).length = 4 * n
  | .empty, _, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .leaf _ _ _ _, _, h => by
    simp only [WordTree.checkSize?, Option.some.injEq] at h; subst h; rfl
  | .node lw l r, _, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    rw [WordTree.toBytesAux, toBytesAux_eq_append l, List.length_append,
        length_toBytesAux_nil l hl, length_toBytesAux_nil r hr]
    omega

/-- If `t.checkSize? = some n`, then `t.toBytes.length = 4 * n`. -/
theorem WordTree.length_toBytes_of_checkSize? {t : WordTree} {n : Nat}
    (h : t.checkSize? = some n) :
    t.toBytes.length = 4 * n :=
  WordTree.length_toBytesAux_nil t h

private theorem WordTree.sliceBytesAux_eq :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (widx cnt : Nat),
      t.checkSize? = some n →
      widx + cnt ≤ n →
      ((t.toBytesAux []).drop (4 * widx)).take (4 * cnt) ++ acc =
        WordTree.sliceBytesAux t widx cnt acc
  | .empty, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?, Option.some.injEq] at hsz; subst hsz
    have hw : widx = 0 := by omega
    have hc : cnt = 0 := by omega
    subst hw; subst hc; rfl
  | .leaf b0 b1 b2 b3, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?, Option.some.injEq] at hsz; subst hsz
    rcases (by omega : cnt = 0 ∨ (widx = 0 ∧ cnt = 1)) with rfl | ⟨rfl, rfl⟩
    · simp [WordTree.sliceBytesAux]
    · rfl
  | .node lw l r, _, acc, widx, cnt, hsz, hle => by
    simp only [WordTree.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    simp only [Option.some.injEq] at hsz; subst hsz
    have hlen_l := length_toBytesAux_nil l hl
    have hlen_r := length_toBytesAux_nil r hr
    simp only [WordTree.sliceBytesAux]
    by_cases hcnt0 : cnt = 0
    · subst hcnt0; simp
    · have hcnt_beq : (cnt == 0) = false := beq_eq_false_iff_ne.mpr hcnt0
      simp only [hcnt_beq, Bool.false_eq_true, ↓reduceIte]
      rw [WordTree.toBytesAux, toBytesAux_eq_append l (r.toBytesAux [])]
      split
      · rename_i hleft
        have h1 : 4 * widx ≤ (l.toBytesAux []).length := by omega
        have h2 : 4 * cnt ≤ ((l.toBytesAux []).drop (4 * widx)).length := by
          rw [List.length_drop]; omega
        rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
        exact sliceBytesAux_eq l acc widx cnt hl hleft
      · rename_i hnotleft
        split
        · rename_i hright
          have h1 : (l.toBytesAux []).length ≤ 4 * widx := by omega
          have hdrop_l : (l.toBytesAux []).drop (4 * widx) = [] :=
            List.drop_eq_nil_of_le h1
          have hsub : 4 * widx - (l.toBytesAux []).length = 4 * (widx - lw) := by omega
          rw [List.drop_append, hdrop_l, List.nil_append, hsub]
          exact sliceBytesAux_eq r acc (widx - lw) cnt hr (by omega)
        · rename_i hnotright
          have h1 : 4 * widx ≤ (l.toBytesAux []).length := by omega
          have hrem : ((l.toBytesAux []).drop (4 * widx)).length = 4 * (lw - widx) := by
            rw [List.length_drop]; omega
          rw [List.drop_append_of_le_length h1, List.take_append, hrem]
          have htake_l : ((l.toBytesAux []).drop (4 * widx)).take (4 * cnt) =
              ((l.toBytesAux []).drop (4 * widx)).take (4 * (lw - widx)) := by
            rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          have hsub : 4 * cnt - 4 * (lw - widx) = 4 * (cnt - (lw - widx)) := by omega
          rw [htake_l, hsub, List.append_assoc,
              ← (show ((r.toBytesAux []).drop (4 * 0)).take (4 * (cnt - (lw - widx))) ++ acc = _ from
                sliceBytesAux_eq r acc 0 (cnt - (lw - widx)) hr (by omega)),
              List.drop_zero]
          exact sliceBytesAux_eq l _ widx (lw - widx) hl (by omega)

/-- If `WordTree.sliceBytesChecked t n off span = some bs`, then `(t.toBytes.drop off).take span = bs`. -/
theorem WordTree.sliceBytesChecked_eq {t : WordTree} {n off span : Nat} {bs : List (BitVec 8)}
    (hwf : t.checkSize? = some n)
    (hs : WordTree.sliceBytesChecked t n off span = some bs) :
    ((t.toBytes.drop off).take span) = bs := by
  simp only [WordTree.sliceBytesChecked] at hs
  split at hs <;> try contradiction
  rename_i hal
  split at hs <;> try contradiction
  rename_i hle
  simp only [Option.some.injEq] at hs
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hal
  rcases hal with ⟨hal_off, hal_span⟩
  have hoff : off = 4 * (off / 4) := by omega
  have hspan : span = 4 * (span / 4) := by omega
  have h := WordTree.sliceBytesAux_eq t [] (off / 4) (span / 4) hwf hle
  rw [List.append_nil] at h
  rw [WordTree.toBytes, hoff, hspan, h, hs]

/-- If `WordTree.sliceBytesChecked t n off span = some bs`, then `off` and `span` are 4-byte aligned
    and `off + span ≤ 4 * n`. -/
theorem WordTree.sliceBytesChecked_bounds {t : WordTree} {n off span : Nat} {bs : List (BitVec 8)}
    (hs : WordTree.sliceBytesChecked t n off span = some bs) :
    off % 4 = 0 ∧ span % 4 = 0 ∧ off + span ≤ 4 * n := by
  simp only [WordTree.sliceBytesChecked] at hs
  split at hs <;> try contradiction
  rename_i hal
  split at hs <;> try contradiction
  rename_i hle
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hal
  rcases hal with ⟨hal_off, hal_span⟩
  exact ⟨hal_off, hal_span, by omega⟩

end

public meta section

open Lean Elab Term Meta in
/-- Reflect a `List (String × α)` constant `<listId>` (such as `<c>_funcTable`) into
    `List (List Char × α)` at elaboration time, reusing the value `Expr`s so
    `<listId> = toStringAssoc <chars>` checks in the kernel. -/
scoped elab "assoc_chars_of% " listId:ident : term => do
  let c ← realizeGlobalConstNoOverload listId
  let listExpr := Lean.mkConst c
  let listTy ← whnf (← inferType listExpr)
  unless listTy.isAppOfArity ``List 1 do
    throwError "assoc_chars_of%: expected `List` constant, got type {listTy}"
  let elemTy ← whnf (listTy.getArg! 0)
  unless elemTy.isAppOfArity ``Prod 2 do
    throwError "assoc_chars_of%: expected `List (String × α)`, got element type {elemTy}"
  let valTy := elemTy.getArg! 1
  let entries ← listElemsWhnf listExpr
  let mut pairs : Array (Expr × Expr) := #[]
  for pairExpr in entries do
    let pairExpr ← if pairExpr.isAppOfArity ``Prod.mk 4 then pure pairExpr
      else withTransparency .all (whnf pairExpr)
    unless pairExpr.isAppOfArity ``Prod.mk 4 do
      throwError "assoc_chars_of%: expected `Prod.mk` entry, got {pairExpr}"
    let strExpr := pairExpr.getArg! 2
    let valExpr := pairExpr.getArg! 3
    let some s ← (do
        if let .lit (.strVal s) := strExpr then pure (some s)
        else if let .lit (.strVal s) := (← withTransparency .all (whnf strExpr)) then pure (some s)
        else pure none)
      | throwError "assoc_chars_of%: expected string literal key, got {strExpr}"
    pairs := pairs.push (toExpr s.toList, valExpr)
  let charListType := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Char)
  let prodType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) charListType valTy
  let prodMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) charListType valTy
  let nilExpr := mkApp (Lean.mkConst ``List.nil [Level.zero]) prodType
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) prodType
  let mut acc := nilExpr
  for i in [0 : pairs.size] do
    let (csExpr, valExpr) := pairs[pairs.size - 1 - i]!
    acc := mkApp2 consFn (mkApp2 prodMk csExpr valExpr) acc
  return acc

/-! ## Symbol-Entry Registry (`fnEntryExt`) -/

/-- Per-function metadata stored in `fnEntryExt` for `wp_entry` and `wp_init_fn`. -/
structure FnEntryInfo where
  /-- Function symbol name (as used in `Program.fnAddr`). -/
  sym : String
  /-- Fully qualified constant name of the canonical `Program` (`<ns>.<c>`). -/
  codeConst : Lean.Name
  /-- Prefix for decode/fetch lemmas (`<target_ns>.<prog_name>`). -/
  decPrefix : Lean.Name
  /-- Fully qualified constant name of `<ns>.<c>_fnOff_0x<off>`. -/
  fnOffLemma : Lean.Name
  /-- Canonical byte offset of the function entry from `base`. -/
  off : Nat
  /-- Function size in bytes. -/
  sizeBytes : Nat
  /-- Prologue stack frame size in bytes (if statically inferred). -/
  frameBytes? : Option Nat := none
  /-- `true` for a placed library program `P : (a : A) → Program` (registered by
      `gen_placed_fnOffs`): `fnOffLemma` then takes `P`'s parameter, and instruction fetches come
      from the global `P_rebase_fetch_0x<off>` lemmas, so `wp_entry` emits no `code_fetches`. -/
  placed : Bool := false
  deriving Inhabited, Repr, BEq

/-- Persistent environment extension storing `FnEntryInfo` records across imported target modules. -/
initialize fnEntryExt : Lean.SimplePersistentEnvExtension FnEntryInfo (Array FnEntryInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

/-- Look up `FnEntryInfo` by symbol name `sym`, optionally restricted to `codeConst?`. -/
def lookupFnEntry? (env : Lean.Environment) (sym : String) (codeConst? : Option Lean.Name := none) :
    Option FnEntryInfo :=
  let entries := fnEntryExt.getState env
  entries.findRev? fun info =>
    info.sym == sym &&
    match codeConst? with
    | some c => info.codeConst == c
    | none => true

/-- Look up `FnEntryInfo` by canonical `codeConst` and byte offset `off`. -/
def lookupFnEntryByOff? (env : Lean.Environment) (codeConst : Lean.Name) (off : Nat) :
    Option FnEntryInfo :=
  let entries := fnEntryExt.getState env
  entries.findRev? fun info =>
    info.codeConst == codeConst && info.off == off

open Lean Elab Command in
/-- Register a function entry in `fnEntryExt` for `wp_entry` / `wp_init_fn`. -/
scoped syntax "register_fn_entry " str ppSpace ident ppSpace ident ppSpace ident ppSpace num ppSpace num (ppSpace num)? : command

open Lean Elab Command in
elab_rules : command
  | `(command| register_fn_entry $sym:str $codeId:ident $decId:ident $fnOffId:ident $off:num $sz:num $[$fb?:num]?) => do
    let env ← getEnv
    let currNs ← getCurrNamespace
    let resolveConstOrId (id : Ident) : Name :=
      let n := id.getId
      if env.contains n then n
      else if env.contains (currNs ++ n) then currNs ++ n
      else n
    let resolvePrefixOrId (id : Ident) : Name :=
      let n := id.getId
      if n.isAtomic && !currNs.isAnonymous then currNs ++ n else n
    let info : FnEntryInfo := {
      sym := sym.getString
      codeConst := resolveConstOrId codeId
      decPrefix := resolvePrefixOrId decId
      fnOffLemma := resolveConstOrId fnOffId
      off := off.getNat
      sizeBytes := sz.getNat
      frameBytes? := fb?.map (·.getNat)
    }
    modifyEnv fun env => fnEntryExt.addEntry env info

end

end ProofLib.ProgramReflection
