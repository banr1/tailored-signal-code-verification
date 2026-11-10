/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib.ProgramReflection -- shake: keep
public meta import Aesop.BuiltinRules
public import Aesop.BuiltinRules
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.Simps
public meta import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
public meta import Mathlib.Tactic.ToDual
public import ProofLib.Lemmas
public import Arm64.Legacy.Object.LinkedImage
import LibsignalBinary.Proofs.CodeLayout
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core
import GeneratedLean.LibsignalSessionObj

/-!
# Relocation and well-formedness witnesses for `libsignalSessionImage`

Pure relocation helpers and reflection witnesses for the 5-object `libsignalSessionImage`
(`libsignal_protocol`, `libsignal_session`, `libsignal_core`, `bytes`, `libsignal_e2e`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.ImageWitness

open Arm64 ProofLib ProofLib.ProgramReflection Lean Meta Elab Term

set_option maxRecDepth 2000000

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, k + 1 => listGet? xs k

theorem listGet?_eq_getElem? {α : Type} :
    ∀ (xs : List α) (k : Nat), listGet? xs k = xs[k]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => listGet?_eq_getElem? xs k

private theorem natListBeq_eq_false' : ∀ {l₁ l₂ : List Nat}, natListBeq l₁ l₂ = false → l₁ ≠ l₂
  | [], [], h => by contradiction
  | _ :: _, [], _ => nofun
  | [], _ :: _, _ => nofun
  | _ :: ns₁, _ :: ns₂, h => by
    simp only [natListBeq] at h
    split at h
    · intro hcons
      injection hcons with _ htail
      exact natListBeq_eq_false' h htail
    · rename_i hne
      intro hcons
      injection hcons with hhead _
      subst hhead
      exact absurd (Nat.beq_eq.mpr rfl) hne

private theorem natEntryBeq_eq_false' {e₁ e₂ : Nat × List Nat} (h : natEntryBeq e₁ e₂ = false) :
    e₁ ≠ e₂ := by
  simp only [natEntryBeq] at h
  split at h
  · intro heq
    exact natListBeq_eq_false' h (congrArg Prod.snd heq)
  · rename_i hlen
    intro heq
    exact absurd (Nat.beq_eq.mpr (congrArg Prod.fst heq)) hlen

private theorem string_beq_of_natEntryBeq_false' {l₁ l₂ : List Char}
    (h : natEntryBeq (encodeCharKey l₁) (encodeCharKey l₂) = false) :
    (String.ofList l₁ == String.ofList l₂) = false :=
  beq_eq_false_iff_ne.mpr
    (mt String.ofList_inj.mp (mt (congrArg encodeCharKey) (natEntryBeq_eq_false' h)))

private theorem natEntryFresh_getElem' {cs₀ : List Char} :
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
        exact natEntryFresh_getElem' tl' hfresh k' hk

private theorem find_and_filter_none_of_fresh {cs : List Char} :
    ∀ (syms : List (List Char × Nat)),
      natEntryFresh (encodeCharKey cs) (prepareCharSymbols syms) = true →
      (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) = none ∧
      (toStringSymbols syms).filter (fun p => p.1 == String.ofList cs) = []
  | [], _ => ⟨rfl, rfl⟩
  | (cs₀, _) :: tl, h => by
    simp only [prepareCharSymbols, natEntryFresh] at h
    split at h
    · contradiction
    · rename_i hne
      have hbeq : (String.ofList cs₀ == String.ofList cs) = false :=
        beq_eq_false_iff_ne.mpr (Ne.symm (mt String.ofList_inj.mp
          (mt (congrArg encodeCharKey) (natEntryBeq_eq_false' (Bool.eq_false_of_ne_true hne)))))
      simp only [toStringSymbols, List.find?, List.filter, hbeq]
      exact find_and_filter_none_of_fresh tl h

private theorem find_and_filter_of_allFresh :
    ∀ (syms : List (List Char × Nat)),
      allFreshEntries (prepareCharSymbols syms) = true →
      ∀ (k : Nat) {cs : List Char} {addr : Nat},
        syms[k]? = some (cs, addr) →
        (toStringSymbols syms).find? (fun p => p.1 == String.ofList cs) =
          some (String.ofList cs, addr) ∧
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
        simp only [toStringSymbols, List.find?, List.filter, beq_self_eq_true,
          (find_and_filter_none_of_fresh tl hfresh).2, and_self]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        simp only [toStringSymbols, List.find?, List.filter,
          string_beq_of_natEntryBeq_false' (natEntryFresh_getElem' tl hfresh k' hk)]
        exact find_and_filter_of_allFresh tl h k' hk
    · contradiction

private theorem toStringSymbols_getElem?' :
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
    exact toStringSymbols_getElem?' tl k hk

theorem lookup_and_unique_of_allFresh {syms : List (List Char × Nat)} {xs : List (String × Nat)}
    (hxs : xs = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    {k : Nat} {name : String} {off : Nat} (hk : xs[k]? = some (name, off)) :
    Obj.lookup name xs = some off ∧
    xs.filter (fun p => p.1 == name) = [(name, off)] := by
  rw [hxs] at hk ⊢
  rcases toStringSymbols_getElem?' syms k hk with ⟨cs, hk_cs, rfl⟩
  obtain ⟨hfind, hfilt⟩ := find_and_filter_of_allFresh syms hfresh k hk_cs
  exact ⟨by simp [Obj.lookup, hfind], hfilt⟩

theorem filter_sublist_eq_singleton {α : Type} {name : String}
    {pre mid post : List (String × α)} {v : α}
    (h : (pre ++ mid ++ post).filter (fun p => p.1 == name) = [(name, v)])
    (hmem : (name, v) ∈ mid) :
    mid.filter (fun p => p.1 == name) = [(name, v)] := by
  rw [List.filter_append, List.filter_append] at h
  have hmem_f : (name, v) ∈ mid.filter (fun p => p.1 == name) :=
    List.mem_filter.mpr ⟨hmem, beq_self_eq_true name⟩
  cases hpre : pre.filter (fun p => p.1 == name) with
  | nil =>
    rw [hpre, List.nil_append] at h
    cases hmid : mid.filter (fun p => p.1 == name) with
    | nil => simp [hmid] at hmem_f
    | cons a tl =>
      rw [hmid, List.cons_append] at h
      injection h with ha htl
      have htl_nil : tl = [] := (List.append_eq_nil_iff.mp htl).1
      subst ha; subst htl_nil; rfl
  | cons a tl =>
    rw [hpre, List.cons_append, List.cons_append] at h
    injection h with _ htl
    have hmid_nil : mid.filter (fun p => p.1 == name) = [] :=
      (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp htl).1).2
    simp [hmid_nil] at hmem_f

theorem lookupUnique_of_filter_sublist {α : Type} {name : String}
    {pre mid post : List (String × α)} {v : α}
    (h : (pre ++ mid ++ post).filter (fun p => p.1 == name) = [(name, v)])
    (hmem : (name, v) ∈ mid) :
    Obj.lookupUnique name mid = some v := by
  simp [Obj.lookupUnique, filter_sublist_eq_singleton h hmem]

private theorem natEntryFresh_of_allDisjoint' {symEntries : List (Nat × List Nat)} :
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
        exact natEntryFresh_of_allDisjoint' tl h k' hk
    · contradiction

theorem resolveSym_of_sym {li : Obj.LinkedImage} {syms : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    {k : Nat} {name : String} {off : Nat} (hk : li.symbols[k]? = some (name, off)) :
    li.resolveSym name = some off := by
  have hl := (lookup_and_unique_of_allFresh hsyms hfresh hk).1
  simp [Obj.LinkedImage.resolveSym, hl]

theorem resolveSym_of_stub {li : Obj.LinkedImage}
    {syms stubSyms : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols syms)
    (hstubs : li.stubs = toStringSymbols stubSyms)
    (hwf : wfStubCharSymbols stubSyms syms = true)
    {k : Nat} {name : String} {off : Nat} (hk : li.stubs[k]? = some (name, off)) :
    li.resolveSym name = some off := by
  simp only [wfStubCharSymbols] at hwf
  split at hwf <;> try contradiction
  rename_i hfresh_st
  rw [hstubs] at hk
  rcases toStringSymbols_getElem?' stubSyms k hk with ⟨cs, hk_cs, rfl⟩
  have hdisj := natEntryFresh_of_allDisjoint' stubSyms hwf k hk_cs
  have hnone := (find_and_filter_none_of_fresh syms hdisj).1
  have hsome := (find_and_filter_of_allFresh stubSyms hfresh_st k hk_cs).1
  simp [Obj.LinkedImage.resolveSym, Obj.lookup, hsyms, hstubs, hnone, hsome]

private theorem WordTree.toBytesAux_eq_append' :
    ∀ (t : WordTree) (acc : List (BitVec 8)),
      t.toBytesAux acc = t.toBytesAux [] ++ acc
  | .empty, _ => rfl
  | .leaf _ _ _ _, _ => rfl
  | .node _ l r, acc => by
    simp only [WordTree.toBytesAux]
    rw [toBytesAux_eq_append' l (r.toBytesAux acc),
        toBytesAux_eq_append' r acc, toBytesAux_eq_append' l (r.toBytesAux []),
        List.append_assoc]

theorem WordTree.length_toBytesAux_nil' :
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
    rw [WordTree.toBytesAux, toBytesAux_eq_append' l, List.length_append,
        length_toBytesAux_nil' l hl, length_toBytesAux_nil' r hr]
    omega

private theorem WordTree.sliceBytesAux_eq' :
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
    have hlen_l := length_toBytesAux_nil' l hl
    have hlen_r := length_toBytesAux_nil' r hr
    simp only [WordTree.sliceBytesAux]
    by_cases hcnt0 : cnt = 0
    · subst hcnt0; simp
    · have hcnt_beq : (cnt == 0) = false := beq_eq_false_iff_ne.mpr hcnt0
      simp only [hcnt_beq, Bool.false_eq_true, ↓reduceIte]
      rw [WordTree.toBytesAux, toBytesAux_eq_append' l (r.toBytesAux [])]
      split
      · rename_i hleft
        have h1 : 4 * widx ≤ (l.toBytesAux []).length := by omega
        have h2 : 4 * cnt ≤ ((l.toBytesAux []).drop (4 * widx)).length := by
          rw [List.length_drop]; omega
        rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
        exact sliceBytesAux_eq' l acc widx cnt hl hleft
      · rename_i hnotleft
        split
        · rename_i hright
          have h1 : (l.toBytesAux []).length ≤ 4 * widx := by omega
          have hdrop_l : (l.toBytesAux []).drop (4 * widx) = [] :=
            List.drop_eq_nil_of_le h1
          have hsub : 4 * widx - (l.toBytesAux []).length = 4 * (widx - lw) := by omega
          rw [List.drop_append, hdrop_l, List.nil_append, hsub]
          exact sliceBytesAux_eq' r acc (widx - lw) cnt hr (by omega)
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
                sliceBytesAux_eq' r acc 0 (cnt - (lw - widx)) hr (by omega)),
              List.drop_zero]
          exact sliceBytesAux_eq' l _ widx (lw - widx) hl (by omega)

theorem sliceBytesChecked_eq' {t : WordTree} {n off span : Nat} {bs : List (BitVec 8)}
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
  have h := WordTree.sliceBytesAux_eq' t [] (off / 4) (span / 4) hwf hle
  rw [List.append_nil] at h
  rw [WordTree.toBytes, hoff, hspan, h, hs]

theorem stubs_all_of_noStubBefore {textEnd off len : Nat} (hle : off + len ≤ textEnd) :
    ∀ {stubs : List (String × Nat)},
      noStubBefore textEnd stubs = true →
      (stubs.all fun (_, s) => !(decide (off ≤ s) && decide (s < off + len))) = true
  | [], _ => rfl
  | (_, s) :: rest, h => by
    simp only [noStubBefore] at h
    split at h <;> try contradiction
    rename_i hble
    have hs : textEnd ≤ s := Nat.le_of_ble_eq_true hble
    have hnot : (!(decide (off ≤ s) && decide (s < off + len))) = true := by
      simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    simp only [List.all_cons, hnot, Bool.true_and]
    exact stubs_all_of_noStubBefore hle h

structure CallWitness where
  roff : Nat
  isSym : Bool
  kTarget : Nat
  targetOff : Nat
  deriving Repr

structure CallFnWitness where
  kSym : Nat
  off : Nat
  calls : List CallWitness
  deriving Repr

structure FnWitness where
  kSym : Nat
  off : Nat
  deriving Repr

private meta def strLitVal (e : Expr) : MetaM String := do
  let some s ← (do
      if let .lit (.strVal s) := e then pure (some s)
      else if let .lit (.strVal s) := (← withTransparency .all (whnf e)) then pure (some s)
      else pure none)
    | throwError "expected string literal, got {e}"
  return s

private meta def natLitVal (e : Expr) : MetaM Nat := do
  let e ← withTransparency .all (whnf e)
  if let some n := e.rawNatLit? then return n
  if let some n := e.nat? then return n
  throwError "expected nat literal, got {e}"

private meta def mkListExpr (elemTy : Expr) (elems : Array Expr) : Expr := Id.run do
  let nilExpr := mkApp (Lean.mkConst ``List.nil [Level.zero]) elemTy
  let consFn := mkApp (Lean.mkConst ``List.cons [Level.zero]) elemTy
  let mut acc := nilExpr
  for i in [0 : elems.size] do
    acc := mkApp2 consFn elems[elems.size - 1 - i]! acc
  return acc

elab "build_witness% " imgId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let syms ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.symbols) (Lean.mkConst c))
  let mut symMap : Std.HashMap String (Nat × Nat) := {}
  for i in [0 : syms.size] do
    let e ← if syms[i]!.isAppOfArity ``Prod.mk 4 then pure syms[i]! else withTransparency .all (whnf syms[i]!)
    let s ← strLitVal (e.getArg! 2)
    let off ← natLitVal (e.getArg! 3)
    if !symMap.contains s then symMap := symMap.insert s (i, off)
  let stubs ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.stubs) (Lean.mkConst c))
  let mut stubMap : Std.HashMap String (Nat × Nat) := {}
  for i in [0 : stubs.size] do
    let e ← if stubs[i]!.isAppOfArity ``Prod.mk 4 then pure stubs[i]! else withTransparency .all (whnf stubs[i]!)
    let s ← strLitVal (e.getArg! 2)
    let off ← natLitVal (e.getArg! 3)
    if !stubMap.contains s then stubMap := stubMap.insert s (i, off)
  let objs ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.objects) (Lean.mkConst c))
  let fwTy := Lean.mkConst ``FnWitness
  let fwMk := Lean.mkConst ``FnWitness.mk
  let cwTy := Lean.mkConst ``CallWitness
  let cwMk := Lean.mkConst ``CallWitness.mk
  let cfwTy := Lean.mkConst ``CallFnWitness
  let cfwMk := Lean.mkConst ``CallFnWitness.mk
  let fwListTy := mkApp (Lean.mkConst ``List [Level.zero]) fwTy
  let cfwListTy := mkApp (Lean.mkConst ``List [Level.zero]) cfwTy
  let pairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) fwListTy cfwListTy
  let pairMk := mkApp2 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) fwListTy cfwListTy
  let mut objExprs : Array Expr := #[]
  for o in objs do
    let fns ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.ObjectInfo.fns) o)
    let mut fwExprs : Array Expr := #[]
    for fnEntry in fns do
      let fnEntry ← if fnEntry.isAppOfArity ``Prod.mk 4 then pure fnEntry else withTransparency .all (whnf fnEntry)
      let fnName ← strLitVal (fnEntry.getArg! 2)
      let (kSym, off) := symMap.getD fnName (0, 0)
      fwExprs := fwExprs.push (mkApp2 fwMk (mkRawNatLit kSym) (mkRawNatLit off))
    let callFns ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.ObjectInfo.callFns) o)
    let mut cfwExprs : Array Expr := #[]
    for cfEntry in callFns do
      let cfEntry ← if cfEntry.isAppOfArity ``Prod.mk 4 then pure cfEntry else withTransparency .all (whnf cfEntry)
      let fnName ← strLitVal (cfEntry.getArg! 2)
      let (kSym, off) := symMap.getD fnName (0, 0)
      let rhs ← if (cfEntry.getArg! 3).isAppOfArity ``Prod.mk 4 then pure (cfEntry.getArg! 3) else withTransparency .all (whnf (cfEntry.getArg! 3))
      let calls ← listElemsWhnf (rhs.getArg! 3)
      let mut cwExprs : Array Expr := #[]
      for cEntry in calls do
        let cEntry ← if cEntry.isAppOfArity ``Prod.mk 4 then pure cEntry else withTransparency .all (whnf cEntry)
        let roff ← natLitVal (cEntry.getArg! 2)
        let symName ← strLitVal (cEntry.getArg! 3)
        let (isSym, kTarget, targetOff) := match symMap[symName]? with
          | some (idx, toff) => (true, idx, toff)
          | none =>
            let (idx, toff) := stubMap.getD symName (0, 0)
            (false, idx, toff)
        cwExprs := cwExprs.push (mkApp4 cwMk (mkRawNatLit roff) (toExpr isSym) (mkRawNatLit kTarget) (mkRawNatLit targetOff))
      cfwExprs := cfwExprs.push (mkApp3 cfwMk (mkRawNatLit kSym) (mkRawNatLit off) (mkListExpr cwTy cwExprs))
    objExprs := objExprs.push (mkApp2 pairMk (mkListExpr fwTy fwExprs) (mkListExpr cfwTy cfwExprs))
  return mkListExpr pairTy objExprs

def checkCallWordsCW (off j : Nat) :
    List (BitVec 8) → List (BitVec 8) → List CallWitness → Bool
  | b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: c2 :: c3 :: cs, cws =>
    let w := [b0, b1, b2, b3]
    let actual := [c0, c1, c2, c3]
    let expected := match cws.find? (fun cw => cw.roff == 4 * j) with
      | some cw => Obj.patchBranchBytes w (off + 4 * j) cw.targetOff
      | none => w
    actual == expected && checkCallWordsCW off (j + 1) bs cs cws
  | [], [], _ => true
  | _, _, _ => false

theorem drop_four_cons {α : Type} (x0 x1 x2 x3 : α) (xs : List α) (k : Nat) :
    (x0 :: x1 :: x2 :: x3 :: xs).drop (4 * (k + 1)) = xs.drop (4 * k) := by
  have h : 4 * (k + 1) = 4 * k + 4 := by omega
  rw [h]; rfl

theorem checkCallWordsCW_get (off : Nat) (cws : List CallWitness) :
    ∀ (bs cs : List (BitVec 8)) (j₀ k : Nat),
      checkCallWordsCW off j₀ bs cs cws = true →
      k < bs.length / 4 →
      ((cs.drop (4 * k)).take 4 ==
        let w := (bs.drop (4 * k)).take 4
        match cws.find? (fun cw => cw.roff == 4 * (j₀ + k)) with
        | some cw => Obj.patchBranchBytes w (off + 4 * (j₀ + k)) cw.targetOff
        | none => w) = true
  | [], _, _, _, _, hk => by simp at hk
  | [_], _, _, _, _, hk => by simp at hk
  | [_, _], _, _, _, _, hk => by simp at hk
  | [_, _, _], _, _, _, _, hk => by simp at hk
  | b0 :: b1 :: b2 :: b3 :: bs, c0 :: c1 :: c2 :: c3 :: cs, j₀, k, h, hk => by
    simp only [checkCallWordsCW, Bool.and_eq_true] at h
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.drop_zero, List.take]
      exact h.1
    | succ k' =>
      have hk' : k' < bs.length / 4 := by
        simp only [List.length_cons] at hk; omega
      rw [drop_four_cons b0 b1 b2 b3 bs k', drop_four_cons c0 c1 c2 c3 cs k',
          show j₀ + (k' + 1) = (j₀ + 1) + k' by omega]
      exact checkCallWordsCW_get off cws bs cs (j₀ + 1) k' h.2 hk'
  | _ :: _ :: _ :: _ :: _, [], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_, _], _, _, h, _ => by simp [checkCallWordsCW] at h
  | _ :: _ :: _ :: _ :: _, [_, _, _], _, _, h, _ => by simp [checkCallWordsCW] at h

theorem drop_take_four_of_slice {code cs : List (BitVec 8)} {off len j : Nat}
    (hslice : (code.drop off).take len = cs) (hj : j < len / 4) :
    (cs.drop (4 * j)).take 4 = (code.drop (off + 4 * j)).take 4 := by
  rw [← hslice, List.drop_take, List.drop_drop, List.take_take,
      Nat.min_eq_left (by omega)]

def checkCallsRanges (off : Nat) : List (Nat × String) → List CallWitness → Bool
  | [], [] => true
  | _ :: calls, cw :: cws =>
    Obj.branchInRange (off + cw.roff) cw.targetOff && checkCallsRanges off calls cws
  | _, _ => false

def lhsCallLookups (syms stubs : List (String × Nat)) :
    List CallWitness → List (Nat × Option (String × Nat))
  | [] => []
  | cw :: cws =>
    (cw.roff, if cw.isSym then listGet? syms cw.kTarget else listGet? stubs cw.kTarget) ::
      lhsCallLookups syms stubs cws

def rhsCallLookups :
    List (Nat × String) → List CallWitness → List (Nat × Option (String × Nat))
  | (roff, sym) :: calls, cw :: cws => (roff, some (sym, cw.targetOff)) :: rhsCallLookups calls cws
  | _, _ => []

theorem calls_sound {li : Obj.LinkedImage} {syms stubSyms : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    (hstubs : li.stubs = toStringSymbols stubSyms) (hwf : wfStubCharSymbols stubSyms syms = true)
    (off : Nat) :
    ∀ (calls : List (Nat × String)) (cws : List CallWitness),
      checkCallsRanges off calls cws = true →
      lhsCallLookups li.symbols li.stubs cws = rhsCallLookups calls cws →
      (calls.all fun (roff, sym) =>
        match li.resolveSym sym with
        | some t => Obj.branchInRange (off + roff) t
        | none => false) = true ∧
      ∀ (x : Nat) (w : List (BitVec 8)),
        (match calls.find? (·.1 == x) with
         | some (_, sym) => Obj.patchBranchBytes w (off + x) ((li.resolveSym sym).getD 0)
         | none => w) =
        (match cws.find? (fun cw => cw.roff == x) with
         | some cw => Obj.patchBranchBytes w (off + x) cw.targetOff
         | none => w)
  | [], [], _, _ => ⟨rfl, fun _ _ => rfl⟩
  | (roff, sym) :: calls, cw :: cws, hrng, hlk => by
    simp only [checkCallsRanges, Bool.and_eq_true] at hrng
    simp only [lhsCallLookups, rhsCallLookups, List.cons.injEq, Prod.mk.injEq] at hlk
    rcases hlk with ⟨⟨hroff, htarget⟩, hlk_tl⟩
    have hres : li.resolveSym sym = some cw.targetOff := by
      cases hc : cw.isSym
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, listGet?_eq_getElem?] at htarget
        exact resolveSym_of_stub hsyms hstubs hwf htarget
      · simp only [hc, ↓reduceIte, listGet?_eq_getElem?] at htarget
        exact resolveSym_of_sym hsyms hfresh htarget
    obtain ⟨hall_tl, hfind_tl⟩ :=
      calls_sound hsyms hfresh hstubs hwf off calls cws hrng.2 hlk_tl
    refine ⟨?_, fun x w => ?_⟩
    · simp only [List.all_cons, hres, ← hroff, hrng.1, Bool.true_and]
      exact hall_tl
    · simp only [List.find?, hroff]
      cases roff == x
      · exact hfind_tl x w
      · simp [hres]
  | [], _ :: _, hrng, _ => by simp [checkCallsRanges] at hrng
  | _ :: _, [], hrng, _ => by simp [checkCallsRanges] at hrng

def checkFnsCode (t : WordTree) (n textEnd kLo kHi : Nat) :
    List (String × List (BitVec 8)) → List FnWitness → Bool
  | [], [] => true
  | (_, bs) :: fns, fw :: fws =>
    kLo ≤ fw.kSym && fw.kSym < kHi &&
    fw.off % 4 == 0 &&
    fw.off + bs.length ≤ textEnd &&
    (match WordTree.sliceBytesChecked t n fw.off bs.length with
     | some cs => cs == bs
     | none => false) &&
    checkFnsCode t n textEnd kLo kHi fns fws
  | _, _ => false

def lhsFnLookups (syms : List (String × Nat)) :
    List FnWitness → List (Option (String × Nat))
  | [] => []
  | fw :: fws => listGet? syms fw.kSym :: lhsFnLookups syms fws

def rhsFnLookups :
    List (String × List (BitVec 8)) → List FnWitness → List (Option (String × Nat))
  | (f, _) :: fns, fw :: fws => some (f, fw.off) :: rhsFnLookups fns fws
  | _, _ => []

theorem checkFnsCode_sound {li : Obj.LinkedImage} {t : WordTree} {n textEnd kLo kHi : Nat}
    {syms : List (List Char × Nat)} {oSyms : List (String × Nat)}
    (hcode : li.code = t.toBytes) (htree : t.checkSize? = some n)
    (htext_le : textEnd ≤ 4 * n)
    (hstub : noStubBefore textEnd li.stubs = true)
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    (huniq : ∀ k f off, kLo ≤ k → k < kHi → li.symbols[k]? = some (f, off) →
      Obj.lookupUnique f oSyms = some off) :
    ∀ (fns : List (String × List (BitVec 8))) (fws : List FnWitness),
      checkFnsCode t n textEnd kLo kHi fns fws = true →
      lhsFnLookups li.symbols fws = rhsFnLookups fns fws →
      (fns.all fun (f, bs) =>
        match Obj.lookupUnique f oSyms with
        | none => false
        | some off =>
          Obj.lookup f li.symbols == some off &&
          off % 4 == 0 && Obj.bytesAt li.code off bs &&
            li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true
  | [], [], _, _ => rfl
  | (f, bs) :: fns, fw :: fws, hc, hlk => by
    simp only [checkFnsCode, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨hlo, hhi⟩, hal⟩, hle⟩, hslice⟩, hc_tl⟩
    simp only [lhsFnLookups, rhsFnLookups, List.cons.injEq] at hlk
    rcases hlk with ⟨hget, hlk_tl⟩
    rw [listGet?_eq_getElem?] at hget
    have hu : Obj.lookupUnique f oSyms = some fw.off := huniq fw.kSym f fw.off hlo hhi hget
    have hl : (Obj.lookup f li.symbols == some fw.off) = true :=
      beq_iff_eq.mpr (lookup_and_unique_of_allFresh hsyms hfresh hget).1
    have hbytes : Obj.bytesAt li.code fw.off bs = true := by
      cases hs : WordTree.sliceBytesChecked t n fw.off bs.length with
      | none => simp [hs] at hslice
      | some cs =>
        simp only [hs] at hslice
        have hcs : cs = bs := beq_iff_eq.mp hslice
        have heq := (sliceBytesChecked_eq' htree hs).trans hcs
        have hlen_t : t.toBytes.length = 4 * n := WordTree.length_toBytesAux_nil' t htree
        have hbound : decide (fw.off + bs.length ≤ t.toBytes.length) = true :=
          decide_eq_true (by omega)
        simp only [Obj.bytesAt, hcode, heq, beq_self_eq_true, Bool.and_true]
        exact hbound
    have hst := stubs_all_of_noStubBefore hle hstub
    simp only [List.all_cons, hu, hl, hal, hbytes, hst, Bool.true_and]
    exact checkFnsCode_sound hcode htree htext_le hstub hsyms hfresh huniq fns fws hc_tl hlk_tl
  | [], _ :: _, hc, _ => by simp [checkFnsCode] at hc
  | _ :: _, [], hc, _ => by simp [checkFnsCode] at hc

def checkCallFnsCode (t : WordTree) (n textEnd kLo kHi : Nat) :
    List (String × List (BitVec 8) × List (Nat × String)) → List CallFnWitness → Bool
  | [], [] => true
  | (_, bs, calls) :: cfs, cfw :: cfws =>
    kLo ≤ cfw.kSym && cfw.kSym < kHi &&
    cfw.off % 4 == 0 && bs.length % 4 == 0 &&
    cfw.off + bs.length ≤ textEnd &&
    checkCallsRanges cfw.off calls cfw.calls &&
    (match WordTree.sliceBytesChecked t n cfw.off bs.length with
     | some cs => checkCallWordsCW cfw.off 0 bs cs cfw.calls
     | none => false) &&
    checkCallFnsCode t n textEnd kLo kHi cfs cfws
  | _, _ => false

def lhsCallFnLookups (syms stubs : List (String × Nat)) :
    List CallFnWitness →
    List (Option (String × Nat) × List (Nat × Option (String × Nat)))
  | [] => []
  | cfw :: cfws =>
    (listGet? syms cfw.kSym, lhsCallLookups syms stubs cfw.calls) ::
      lhsCallFnLookups syms stubs cfws

def rhsCallFnLookups :
    List (String × List (BitVec 8) × List (Nat × String)) → List CallFnWitness →
    List (Option (String × Nat) × List (Nat × Option (String × Nat)))
  | (f, _, calls) :: cfs, cfw :: cfws =>
    (some (f, cfw.off), rhsCallLookups calls cfw.calls) :: rhsCallFnLookups cfs cfws
  | _, _ => []

theorem checkCallFnsCode_sound {li : Obj.LinkedImage} {t : WordTree} {n textEnd kLo kHi : Nat}
    {syms stubSyms : List (List Char × Nat)} {oSyms : List (String × Nat)}
    (hcode : li.code = t.toBytes) (htree : t.checkSize? = some n)
    (htext_le : textEnd ≤ 4 * n)
    (hstub : noStubBefore textEnd li.stubs = true)
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    (hstubs : li.stubs = toStringSymbols stubSyms) (hwf : wfStubCharSymbols stubSyms syms = true)
    (huniq : ∀ k f off, kLo ≤ k → k < kHi → li.symbols[k]? = some (f, off) →
      Obj.lookupUnique f oSyms = some off) :
    ∀ (cfs : List (String × List (BitVec 8) × List (Nat × String))) (cfws : List CallFnWitness),
      checkCallFnsCode t n textEnd kLo kHi cfs cfws = true →
      lhsCallFnLookups li.symbols li.stubs cfws = rhsCallFnLookups cfs cfws →
      (cfs.all fun (f, bs, calls) =>
        match Obj.lookupUnique f oSyms with
        | none => false
        | some off =>
          Obj.lookup f li.symbols == some off &&
          off % 4 == 0 && bs.length % 4 == 0 && off + bs.length ≤ li.code.length &&
          (calls.all fun (roff, sym) =>
            match li.resolveSym sym with
            | some t => Obj.branchInRange (off + roff) t
            | none => false) &&
          ((List.range (bs.length / 4)).all fun j =>
            let w := (bs.drop (4 * j)).take 4
            let expected := match calls.find? (·.1 == 4 * j) with
              | some (_, sym) => Obj.patchBranchBytes w (off + 4 * j) ((li.resolveSym sym).getD 0)
              | none => w
            (li.code.drop (off + 4 * j)).take 4 == expected) &&
          li.stubs.all fun (_, s) => !(off ≤ s && s < off + bs.length)) = true
  | [], [], _, _ => rfl
  | (f, bs, calls) :: cfs, cfw :: cfws, hc, hlk => by
    simp only [checkCallFnsCode, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨⟨⟨⟨⟨hlo, hhi⟩, hal⟩, hbs4⟩, hle⟩, hrng⟩, hslice⟩, hc_tl⟩
    simp only [lhsCallFnLookups, rhsCallFnLookups, List.cons.injEq, Prod.mk.injEq] at hlk
    rcases hlk with ⟨⟨hget, hcalls_lk⟩, hlk_tl⟩
    rw [listGet?_eq_getElem?] at hget
    have hu : Obj.lookupUnique f oSyms = some cfw.off := huniq cfw.kSym f cfw.off hlo hhi hget
    have hl : (Obj.lookup f li.symbols == some cfw.off) = true :=
      beq_iff_eq.mpr (lookup_and_unique_of_allFresh hsyms hfresh hget).1
    have hlen_code : li.code.length = 4 * n := by
      rw [hcode, WordTree.toBytes, WordTree.length_toBytesAux_nil' t htree]
    have hbound : decide (cfw.off + bs.length ≤ li.code.length) = true :=
      decide_eq_true (by omega)
    obtain ⟨hcalls_all, hcalls_find⟩ :=
      calls_sound hsyms hfresh hstubs hwf cfw.off calls cfw.calls hrng hcalls_lk
    have hwords :
        ((List.range (bs.length / 4)).all fun j =>
          let w := (bs.drop (4 * j)).take 4
          let expected := match calls.find? (·.1 == 4 * j) with
            | some (_, sym) => Obj.patchBranchBytes w (cfw.off + 4 * j) ((li.resolveSym sym).getD 0)
            | none => w
          (li.code.drop (cfw.off + 4 * j)).take 4 == expected) = true := by
      cases hs : WordTree.sliceBytesChecked t n cfw.off bs.length with
      | none => simp [hs] at hslice
      | some cs =>
        simp only [hs] at hslice
        have heq : (li.code.drop cfw.off).take bs.length = cs := by
          rw [hcode]; exact sliceBytesChecked_eq' htree hs
        refine List.all_eq_true.mpr fun j hj => ?_
        have hj_lt : j < bs.length / 4 := List.mem_range.mp hj
        have hcw := checkCallWordsCW_get cfw.off cfw.calls bs cs 0 j hslice hj_lt
        simp only [Nat.zero_add] at hcw
        dsimp only
        rw [← drop_take_four_of_slice heq hj_lt, hcalls_find (4 * j)]
        exact hcw
    have hst := stubs_all_of_noStubBefore hle hstub
    simp only [List.all_cons, hu, hl, hal, hbs4, hbound, hcalls_all, hwords, hst, Bool.true_and]
    exact checkCallFnsCode_sound hcode htree htext_le hstub hsyms hfresh hstubs hwf huniq
      cfs cfws hc_tl hlk_tl
  | [], _ :: _, hc, _ => by simp [checkCallFnsCode] at hc
  | _ :: _, [], hc, _ => by simp [checkCallFnsCode] at hc

def checkObjsCode (t : WordTree) (n textEnd : Nat) :
    List Obj.ObjectInfo → List (Nat × Nat) → List (List FnWitness × List CallFnWitness) → Bool
  | [], [], [] => true
  | o :: os, (kLo, kHi) :: bounds, (fws, cfws) :: rest =>
    o.relocFns.isEmpty && o.dataSyms.isEmpty &&
    checkFnsCode t n textEnd kLo kHi o.fns fws &&
    checkCallFnsCode t n textEnd kLo kHi o.callFns cfws &&
    checkObjsCode t n textEnd os bounds rest
  | _, _, _ => false

def lhsLookups (syms stubs : List (String × Nat)) :
    List (List FnWitness × List CallFnWitness) →
    List (List (Option (String × Nat)) ×
      List (Option (String × Nat) × List (Nat × Option (String × Nat))))
  | [] => []
  | (fws, cfws) :: rest =>
    (lhsFnLookups syms fws, lhsCallFnLookups syms stubs cfws) :: lhsLookups syms stubs rest

def rhsLookups :
    List Obj.ObjectInfo → List (List FnWitness × List CallFnWitness) →
    List (List (Option (String × Nat)) ×
      List (Option (String × Nat) × List (Nat × Option (String × Nat))))
  | o :: os, (fws, cfws) :: rest =>
    (rhsFnLookups o.fns fws, rhsCallFnLookups o.callFns cfws) :: rhsLookups os rest
  | _, _ => []

/-- Pure relocation step corresponding to `Obj.DataReloc.apply`. -/
def DataReloc.applyPure (base : BitVec 64) (data : List (BitVec 8)) (r : Obj.DataReloc) :
    List (BitVec 8) :=
  let v := base + BitVec.ofNat 64 r.target
  data.take r.off ++ Obj.bytesLE r.width v ++ data.drop (r.off + r.width)

/-- Range check under which `Obj.DataReloc.apply` succeeds. -/
def DataReloc.okAt (base : BitVec 64) (r : Obj.DataReloc) : Bool :=
  let v := base + BitVec.ofNat 64 r.target
  !(r.width == 4 && !(-(2 ^ 31 : Int) ≤ v.toInt && v.toInt < (2 ^ 32 : Int)))

theorem dataReloc_apply_eq_ok {base : BitVec 64} {d : List (BitVec 8)} {r : Obj.DataReloc}
    (hok : DataReloc.okAt base r = true) :
    Obj.DataReloc.apply base d r = .ok (DataReloc.applyPure base d r) := by
  simp only [DataReloc.okAt, Bool.not_eq_true'] at hok
  simp only [Obj.DataReloc.apply, DataReloc.applyPure, hok]
  rfl

theorem foldlM_dataReloc_eq_ok {base : BitVec 64} :
    ∀ (rs : List Obj.DataReloc) (d : List (BitVec 8)),
      rs.all (DataReloc.okAt base) = true →
      rs.foldlM (Obj.DataReloc.apply base) d = .ok (rs.foldl (DataReloc.applyPure base) d)
  | [], _, _ => rfl
  | r :: rs, d, hall => by
    simp only [List.all_cons, Bool.and_eq_true] at hall
    simp only [List.foldlM_cons, List.foldl_cons, dataReloc_apply_eq_ok hall.1, bind, Except.bind]
    exact foldlM_dataReloc_eq_ok rs _ hall.2

theorem linkedImage_load_zero_eq_ok (li : Obj.LinkedImage)
    (hwrap : (0#64 : BitVec 64).toNat + li.gotOff + 8 * li.got.length ≤ 2 ^ 64)
    (hwf : li.wellFormed = true)
    (hrel : li.relocs.all (DataReloc.okAt 0#64) = true) :
    li.load 0#64 = .ok
      { base := 0#64
        code := li.code
        dataAddr := 0#64 + BitVec.ofNat 64 li.dataOff
        data := li.relocs.foldl (DataReloc.applyPure 0#64) (li.data ++ List.replicate li.bss 0)
        roData := li.roData.map fun (o, n) => (0#64 + BitVec.ofNat 64 o, n)
        externData := li.externData.map fun (x, o, n) => (x, 0#64 + BitVec.ofNat 64 o, n)
        gotAddr := 0#64 + BitVec.ofNat 64 li.gotOff
        got := li.got.map (Obj.GotEntry.value 0#64)
        symbols := li.symbols
        objSymbols := li.objSymbols
        stubs := li.stubs } := by
  have hal : ((0#64 : BitVec 64).toNat % Obj.pageSize != 0) = false := rfl
  have hw : ¬ ((0#64 : BitVec 64).toNat + li.gotOff + 8 * li.got.length > 2 ^ 64) := by omega
  have hwf' : (!li.wellFormed) = false := by simp [hwf]
  simp only [Obj.LinkedImage.load, bind, Except.bind, pure, Except.pure,
    hal, hw, hwf', Bool.false_eq_true, ↓reduceIte,
    foldlM_dataReloc_eq_ok li.relocs _ hrel]

noncomputable def objSyms0 : List (String × Nat) :=
  (libsignalSessionImage.objSymbols.headD ("", [])).2

noncomputable def objSyms1 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 1).headD ("", [])).2

noncomputable def objSyms2 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 2).headD ("", [])).2

noncomputable def objSyms3 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 3).headD ("", [])).2

noncomputable def objSyms4 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 4).headD ("", [])).2

noncomputable def objSyms5 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 5).headD ("", [])).2

noncomputable def objSyms6 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 6).headD ("", [])).2

noncomputable def objSyms7 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 7).headD ("", [])).2

noncomputable def objSyms8 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 8).headD ("", [])).2

noncomputable def objSyms9 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 9).headD ("", [])).2

noncomputable def objSyms10 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 10).headD ("", [])).2

noncomputable def objSyms11 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 11).headD ("", [])).2

noncomputable def objSyms12 : List (String × Nat) :=
  ((libsignalSessionImage.objSymbols.drop 12).headD ("", [])).2

noncomputable def objInfo0 : Obj.ObjectInfo :=
  libsignalSessionImage.objects.headD default

noncomputable def objInfo1 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 1).headD default

noncomputable def objInfo2 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 2).headD default

noncomputable def objInfo3 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 3).headD default

noncomputable def objInfo4 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 4).headD default

noncomputable def objInfo5 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 5).headD default

noncomputable def objInfo6 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 6).headD default

noncomputable def objInfo7 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 7).headD default

noncomputable def objInfo8 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 8).headD default

noncomputable def objInfo9 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 9).headD default

noncomputable def objInfo10 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 10).headD default

noncomputable def objInfo11 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 11).headD default

noncomputable def objInfo12 : Obj.ObjectInfo :=
  (libsignalSessionImage.objects.drop 12).headD default

theorem mem_mid_of_getElem?_append {α : Type} {pre mid post : List α} {k kLo kHi : Nat} {x : α}
    (hpre : pre.length = kLo) (hmid : pre.length + mid.length = kHi)
    (hlo : kLo ≤ k) (hhi : k < kHi)
    (hget : (pre ++ mid ++ post)[k]? = some x) :
    x ∈ mid := by
  rw [List.getElem?_append_left (by rw [List.length_append, hmid]; exact hhi)] at hget
  rw [List.getElem?_append_right (by rw [hpre]; exact hlo)] at hget
  exact List.mem_of_getElem? hget

theorem lookupUnique_of_sublist_range {li : Obj.LinkedImage}
    {syms : List (List Char × Nat)}
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    {pre mid post : List (String × Nat)} {kLo kHi : Nat}
    (hsplit : li.symbols = pre ++ mid ++ post)
    (hpre : pre.length = kLo) (hmid : pre.length + mid.length = kHi)
    (k : Nat) (f : String) (off : Nat)
    (hlo : kLo ≤ k) (hhi : k < kHi) (hget : li.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f mid = some off := by
  have hfilt := (lookup_and_unique_of_allFresh hsyms hfresh hget).2
  change li.symbols.filter _ = _ at hfilt
  rw [hsplit] at hfilt hget
  exact lookupUnique_of_filter_sublist hfilt (mem_mid_of_getElem?_append hpre hmid hlo hhi hget)

theorem honours_cons_of_checkObjsCode {li : Obj.LinkedImage} {t : WordTree} {n textEnd kLo kHi : Nat}
    {syms stubSyms : List (List Char × Nat)} {o : Obj.ObjectInfo} {oSyms : List (String × Nat)}
    {os : List Obj.ObjectInfo} {bounds : List (Nat × Nat)}
    (hcode : li.code = t.toBytes) (htree : t.checkSize? = some n)
    (htext_le : textEnd ≤ 4 * n)
    (hstub : noStubBefore textEnd li.stubs = true)
    (hsyms : li.symbols = toStringSymbols syms) (hfresh : allFreshCharSymbols syms = true)
    (hstubs : li.stubs = toStringSymbols stubSyms) (hwf : wfStubCharSymbols stubSyms syms = true)
    (hlookup : Obj.lookup o.name li.objSymbols = some oSyms)
    (huniq : ∀ k f off, kLo ≤ k → k < kHi → li.symbols[k]? = some (f, off) →
      Obj.lookupUnique f oSyms = some off)
    (hrest : ∀ {ws}, checkObjsCode t n textEnd os bounds ws = true →
      lhsLookups li.symbols li.stubs ws = rhsLookups os ws →
      (os.all li.honours) = true)
    {ws : List (List FnWitness × List CallFnWitness)}
    (hc : checkObjsCode t n textEnd (o :: os) ((kLo, kHi) :: bounds) ws = true)
    (hlk : lhsLookups li.symbols li.stubs ws = rhsLookups (o :: os) ws) :
    ((o :: os).all li.honours) = true := by
  cases ws with
  | nil => simp [checkObjsCode] at hc
  | cons w rest =>
    rcases w with ⟨fws, cfws⟩
    simp only [checkObjsCode, Bool.and_eq_true] at hc
    rcases hc with ⟨⟨⟨⟨hreloc_emp, hdata_emp⟩, hfn⟩, hcf⟩, hc_tl⟩
    have hreloc : o.relocFns = [] := by cases h : o.relocFns <;> simp_all [List.isEmpty]
    have hdata : o.dataSyms = [] := by cases h : o.dataSyms <;> simp_all [List.isEmpty]
    simp only [lhsLookups, rhsLookups, List.cons.injEq, Prod.mk.injEq] at hlk
    rcases hlk with ⟨⟨hlk_fn, hlk_cf⟩, hlk_tl⟩
    have ho_fn := checkFnsCode_sound hcode htree htext_le hstub hsyms hfresh huniq o.fns fws hfn hlk_fn
    have ho_cf := checkCallFnsCode_sound hcode htree htext_le hstub hsyms hfresh hstubs hwf huniq o.callFns cfws hcf hlk_cf
    have ho : li.honours o = true := by
      unfold Obj.LinkedImage.honours
      rw [hlookup, hreloc, hdata]
      simp only [List.all_nil, Bool.and_true, Bool.and_eq_true]
      exact ⟨ho_fn, ho_cf⟩
    simp only [List.all_cons, ho, Bool.true_and]
    exact hrest hc_tl hlk_tl

noncomputable def libsignalSessionObjWitnesses : List (List FnWitness × List CallFnWitness) :=
  build_witness% CryptoVerification.libsignalSessionImage

theorem libsignalSession_objSymbols_eq :
    libsignalSessionImage.objSymbols =
      [("libsignal_protocol", objSyms0),
       ("libsignal_session", objSyms1),
       ("libsignal_core", objSyms2),
       ("bytes", objSyms3),
       ("uuid", objSyms4),
       ("prost", objSyms5),
       ("spqr", objSyms6),
       ("libsignal_cli_ratchet", objSyms7),
       ("libsignal_cli_handshake", objSyms8),
       ("libsignal_cli", objSyms9),
       ("alloc", objSyms10),
       ("std", objSyms11),
       ("alloc_string_clone", objSyms12)] := by rfl_kernel

theorem libsignalSession_symbols_eq_append :
    libsignalSessionImage.symbols =
      objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12 := by rfl_kernel

theorem objSyms0_length : objSyms0.length = 571 := by rfl_kernel
theorem objSyms1_length : objSyms1.length = 79 := by rfl_kernel
theorem objSyms2_length : objSyms2.length = 47 := by rfl_kernel
theorem objSyms3_length : objSyms3.length = 87 := by rfl_kernel
theorem objSyms4_length : objSyms4.length = 59 := by rfl_kernel
theorem objSyms5_length : objSyms5.length = 61 := by rfl_kernel
theorem objSyms6_length : objSyms6.length = 315 := by rfl_kernel
theorem objSyms7_length : objSyms7.length = 78 := by rfl_kernel
theorem objSyms8_length : objSyms8.length = 40 := by rfl_kernel
theorem objSyms9_length : objSyms9.length = 81 := by rfl_kernel
theorem objSyms10_length : objSyms10.length = 2 := by rfl_kernel
theorem objSyms11_length : objSyms11.length = 7 := by rfl_kernel
theorem objSyms12_length : objSyms12.length = 1 := by rfl_kernel

theorem libsignalSession_objects_eq :
    libsignalSessionImage.objects = [objInfo0, objInfo1, objInfo2, objInfo3, objInfo4, objInfo5, objInfo6, objInfo7, objInfo8, objInfo9, objInfo10, objInfo11, objInfo12] := by
  rfl_kernel

theorem objInfo0_name : objInfo0.name = "libsignal_protocol" := by rfl_kernel
theorem objInfo1_name : objInfo1.name = "libsignal_session" := by rfl_kernel
theorem objInfo2_name : objInfo2.name = "libsignal_core" := by rfl_kernel
theorem objInfo3_name : objInfo3.name = "bytes" := by rfl_kernel
theorem objInfo4_name : objInfo4.name = "uuid" := by rfl_kernel
theorem objInfo5_name : objInfo5.name = "prost" := by rfl_kernel
theorem objInfo6_name : objInfo6.name = "spqr" := by rfl_kernel
theorem objInfo7_name : objInfo7.name = "libsignal_cli_ratchet" := by rfl_kernel
theorem objInfo8_name : objInfo8.name = "libsignal_cli_handshake" := by rfl_kernel
theorem objInfo9_name : objInfo9.name = "libsignal_cli" := by rfl_kernel
theorem objInfo10_name : objInfo10.name = "alloc" := by rfl_kernel
theorem objInfo11_name : objInfo11.name = "std" := by rfl_kernel
theorem objInfo12_name : objInfo12.name = "alloc_string_clone" := by rfl_kernel

theorem libsignalSession_lookups_eq :
    lhsLookups libsignalSessionImage.symbols libsignalSessionImage.stubs libsignalSessionObjWitnesses =
      rhsLookups [objInfo0, objInfo1, objInfo2, objInfo3, objInfo4, objInfo5, objInfo6, objInfo7, objInfo8, objInfo9, objInfo10, objInfo11, objInfo12] libsignalSessionObjWitnesses := by
  rfl_kernel

theorem libsignalSession_code_ok :
    checkObjsCode libsignalSessionCode_tree 139730 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      [objInfo0, objInfo1, objInfo2, objInfo3, objInfo4, objInfo5, objInfo6, objInfo7, objInfo8, objInfo9, objInfo10, objInfo11, objInfo12]
      [(0, 571), (571, 650), (650, 697), (697, 784), (784, 843), (843, 904), (904, 1219), (1219, 1297), (1297, 1337), (1337, 1418), (1418, 1420), (1420, 1427), (1427, 1428)]
      libsignalSessionObjWitnesses = true := by
  rfl_kernel

theorem libsignalSession_wf_prefix :
    (libsignalSessionImage.code.length ≤ libsignalSessionImage.dataOff &&
     libsignalSessionImage.dataOff % Obj.pageSize == 0 &&
     libsignalSessionImage.dataEnd ≤ libsignalSessionImage.gotOff &&
     libsignalSessionImage.gotOff % 8 == 0 &&
     libsignalSessionImage.roData.all (fun (o, n) => libsignalSessionImage.dataOff ≤ o && o + n ≤ libsignalSessionImage.dataEnd) &&
     libsignalSessionImage.externData.all (fun (_, o, n) => libsignalSessionImage.dataEnd ≤ o && o + n ≤ libsignalSessionImage.gotOff) &&
     libsignalSessionImage.relocs.all (fun r => (r.width == 8 || r.width == 4) && r.off + r.width ≤ libsignalSessionImage.data.length) &&
     libsignalSessionImage.stubs.all (fun (_, s) => s + 4 ≤ libsignalSessionImage.code.length)) = true := by
  rfl_kernel

theorem objSyms0_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 0 ≤ k) (hhi : k < 571) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms0 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := []) (mid := objSyms0) (post := objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.nil_append, List.append_assoc])
    rfl
    (by simp [objSyms0_length])
    k f off hlo hhi hget

theorem objSyms1_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 571 ≤ k) (hhi : k < 650) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms1 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0) (mid := objSyms1) (post := objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    objSyms0_length
    (by simp [objSyms0_length, objSyms1_length])
    k f off hlo hhi hget

theorem objSyms2_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 650 ≤ k) (hhi : k < 697) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms2 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1) (mid := objSyms2) (post := objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length])
    k f off hlo hhi hget

theorem objSyms3_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 697 ≤ k) (hhi : k < 784) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms3 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2) (mid := objSyms3) (post := objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length])
    k f off hlo hhi hget

theorem objSyms4_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 784 ≤ k) (hhi : k < 843) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms4 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3) (mid := objSyms4) (post := objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length])
    k f off hlo hhi hget

theorem objSyms5_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 843 ≤ k) (hhi : k < 904) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms5 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4) (mid := objSyms5) (post := objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length])
    k f off hlo hhi hget

theorem objSyms6_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 904 ≤ k) (hhi : k < 1219) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms6 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5) (mid := objSyms6) (post := objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length])
    k f off hlo hhi hget

theorem objSyms7_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1219 ≤ k) (hhi : k < 1297) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms7 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6) (mid := objSyms7) (post := objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length])
    k f off hlo hhi hget

theorem objSyms8_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1297 ≤ k) (hhi : k < 1337) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms8 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7) (mid := objSyms8) (post := objSyms9 ++ objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length])
    k f off hlo hhi hget

theorem objSyms9_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1337 ≤ k) (hhi : k < 1418) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms9 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8) (mid := objSyms9) (post := objSyms10 ++ objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length])
    k f off hlo hhi hget

theorem objSyms10_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1418 ≤ k) (hhi : k < 1420) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms10 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9) (mid := objSyms10) (post := objSyms11 ++ objSyms12)
    (by rw [libsignalSession_symbols_eq_append]; simp only [List.append_assoc])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length, objSyms10_length])
    k f off hlo hhi hget

theorem objSyms11_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1420 ≤ k) (hhi : k < 1427) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms11 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10) (mid := objSyms11) (post := objSyms12)
    libsignalSession_symbols_eq_append
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length, objSyms10_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length, objSyms10_length, objSyms11_length])
    k f off hlo hhi hget

theorem objSyms12_lookupUnique (k : Nat) (f : String) (off : Nat)
    (hlo : 1427 ≤ k) (hhi : k < 1428) (hget : libsignalSessionImage.symbols[k]? = some (f, off)) :
    Obj.lookupUnique f objSyms12 = some off :=
  lookupUnique_of_sublist_range libsignalSessionCode_symbols_eq libsignalSessionCode_symbols_fresh
    (pre := objSyms0 ++ objSyms1 ++ objSyms2 ++ objSyms3 ++ objSyms4 ++ objSyms5 ++ objSyms6 ++ objSyms7 ++ objSyms8 ++ objSyms9 ++ objSyms10 ++ objSyms11) (mid := objSyms12) (post := [])
    (by rw [libsignalSession_symbols_eq_append, List.append_nil])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length, objSyms10_length, objSyms11_length])
    (by simp [objSyms0_length, objSyms1_length, objSyms2_length, objSyms3_length, objSyms4_length, objSyms5_length, objSyms6_length, objSyms7_length, objSyms8_length, objSyms9_length, objSyms10_length, objSyms11_length, objSyms12_length])
    k f off hlo hhi hget

theorem objInfo0_lookup : Obj.lookup objInfo0.name libsignalSessionImage.objSymbols = some objSyms0 := by
  rw [objInfo0_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo1_lookup : Obj.lookup objInfo1.name libsignalSessionImage.objSymbols = some objSyms1 := by
  rw [objInfo1_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo2_lookup : Obj.lookup objInfo2.name libsignalSessionImage.objSymbols = some objSyms2 := by
  rw [objInfo2_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo3_lookup : Obj.lookup objInfo3.name libsignalSessionImage.objSymbols = some objSyms3 := by
  rw [objInfo3_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo4_lookup : Obj.lookup objInfo4.name libsignalSessionImage.objSymbols = some objSyms4 := by
  rw [objInfo4_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo5_lookup : Obj.lookup objInfo5.name libsignalSessionImage.objSymbols = some objSyms5 := by
  rw [objInfo5_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo6_lookup : Obj.lookup objInfo6.name libsignalSessionImage.objSymbols = some objSyms6 := by
  rw [objInfo6_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo7_lookup : Obj.lookup objInfo7.name libsignalSessionImage.objSymbols = some objSyms7 := by
  rw [objInfo7_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo8_lookup : Obj.lookup objInfo8.name libsignalSessionImage.objSymbols = some objSyms8 := by
  rw [objInfo8_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo9_lookup : Obj.lookup objInfo9.name libsignalSessionImage.objSymbols = some objSyms9 := by
  rw [objInfo9_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo10_lookup : Obj.lookup objInfo10.name libsignalSessionImage.objSymbols = some objSyms10 := by
  rw [objInfo10_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo11_lookup : Obj.lookup objInfo11.name libsignalSessionImage.objSymbols = some objSyms11 := by
  rw [objInfo11_name, libsignalSession_objSymbols_eq]; rfl

theorem objInfo12_lookup : Obj.lookup objInfo12.name libsignalSessionImage.objSymbols = some objSyms12 := by
  rw [objInfo12_name, libsignalSession_objSymbols_eq]; rfl

theorem libsignalSessionImage_wellFormed' : libsignalSessionImage.wellFormed = true := by
  unfold Obj.LinkedImage.wellFormed
  rw [Bool.and_eq_true]
  refine ⟨libsignalSession_wf_prefix, ?_⟩
  rw [libsignalSession_objects_eq]
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo0_lookup objSyms0_lookupUnique ?_ libsignalSession_code_ok libsignalSession_lookups_eq
  intro ws1 hc1 hlk1
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo1_lookup objSyms1_lookupUnique ?_ hc1 hlk1
  intro ws2 hc2 hlk2
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo2_lookup objSyms2_lookupUnique ?_ hc2 hlk2
  intro ws3 hc3 hlk3
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo3_lookup objSyms3_lookupUnique ?_ hc3 hlk3
  intro ws4 hc4 hlk4
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo4_lookup objSyms4_lookupUnique ?_ hc4 hlk4
  intro ws5 hc5 hlk5
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo5_lookup objSyms5_lookupUnique ?_ hc5 hlk5
  intro ws6 hc6 hlk6
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo6_lookup objSyms6_lookupUnique ?_ hc6 hlk6
  intro ws7 hc7 hlk7
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo7_lookup objSyms7_lookupUnique ?_ hc7 hlk7
  intro ws8 hc8 hlk8
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo8_lookup objSyms8_lookupUnique ?_ hc8 hlk8
  intro ws9 hc9 hlk9
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo9_lookup objSyms9_lookupUnique ?_ hc9 hlk9
  intro ws10 hc10 hlk10
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo10_lookup objSyms10_lookupUnique ?_ hc10 hlk10
  intro ws11 hc11 hlk11
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo11_lookup objSyms11_lookupUnique ?_ hc11 hlk11
  intro ws12 hc12 hlk12
  refine honours_cons_of_checkObjsCode libsignalSessionCode_code_eq libsignalSessionCode_tree_size
    (by decide) libsignalSessionCode_noStubBefore libsignalSessionCode_symbols_eq
    libsignalSessionCode_symbols_fresh libsignalSessionCode_stubs_eq libsignalSessionCode_stubs_wf
    objInfo12_lookup objSyms12_lookupUnique (fun _ _ => rfl) hc12 hlk12

theorem libsignalSession_relocs_ok :
    libsignalSessionImage.relocs.all (DataReloc.okAt 0#64) = true := by
  rfl_kernel

theorem libsignalSession_wrap_ok :
    decide ((0#64 : BitVec 64).toNat + libsignalSessionImage.gotOff +
      8 * libsignalSessionImage.got.length ≤ 2 ^ 64) = true := by
  rfl_kernel

theorem libsignalSessionImage_load_ok' : ∃ img, libsignalSessionImage.load 0#64 = .ok img :=
  ⟨_, linkedImage_load_zero_eq_ok libsignalSessionImage
    (of_decide_eq_true libsignalSession_wrap_ok)
    libsignalSessionImage_wellFormed'
    libsignalSession_relocs_ok⟩

theorem findSome?_stubs_eq_none_of_all_le {α : Type} {codeLen off : Nat}
    (hoff : codeLen < off)
    (f : String → Option α) :
    ∀ {stubs : List (String × Nat)},
      (stubs.all (fun (_, s) => decide (s + 4 ≤ codeLen))) = true →
      (stubs.findSome? fun (sym, s) => if s == off then f sym else none) = none
  | [], _ => rfl
  | (sym, s) :: rest, hall => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
    have hne : (s == off) = false := beq_eq_false_iff_ne.mpr (by omega)
    simp only [List.findSome?_cons, hne, Bool.false_eq_true, ↓reduceIte]
    exact findSome?_stubs_eq_none_of_all_le hoff f hall.2

theorem ofImage_externAt?_eq_none {img : Obj.Image} {codeLen : Nat}
    (hstubs : (img.stubs.all (fun (_, s) => decide (s + 4 ≤ codeLen))) = true)
    {pc : BitVec 64} (hoff : codeLen < (pc - img.base).toNat)
    (X : String → Option (Arm64.State → Arm64.State)) :
    (Program.ofImage img X).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.ofImage
  dsimp only
  have hsym : (img.symbols.findSome? fun (_ : String × Nat) => (none : Option (Arm64.State → Arm64.State))) = none :=
    Program.findSome?_eq_none_of_forall fun _ _ => rfl
  simp only [ite_self]
  rw [hsym, Option.or_none]
  exact findSome?_stubs_eq_none_of_all_le hoff X hstubs

theorem stubs_bound_of_wf_prefix :
    (libsignalSessionImage.stubs.all (fun (_, s) => decide (s + 4 ≤ libsignalSessionImage.code.length))) = true := by
  have h := libsignalSession_wf_prefix
  rw [Bool.and_eq_true] at h
  exact h.2

elab "exact_no_defeq " t:term : tactic =>
  Elab.Tactic.withMainContext do
    let e ← Elab.Tactic.elabTerm t none
    (← Elab.Tactic.getMainGoal).assign e
    Elab.Tactic.replaceMainGoal []

end CryptoVerification.E2E.Record.ImageWitness
