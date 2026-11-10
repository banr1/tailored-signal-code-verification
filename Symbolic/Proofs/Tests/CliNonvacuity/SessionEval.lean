/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import DY.ALaCarte.Basic
import DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Mathlib.Data.Subtype
public import ProofLib.Lemmas
public import Symbolic.Specifications.Refinement.Concretization
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Computable Kernel Evaluators for `gamma` and `DY.Bytes` Equality

Provides `concretizeAll_split`, transparent fuel-bounded `DY.Bytes` equality (`beqBareOptFast`,
`decEqBytesFast`), and `Nat`-keyed binary trie DAG memoization (`Trie`, `buildDagTrie`,
`evalGammaFast`) so `decide +kernel` reduces concrete symbolic-refinement `Bool` checks directly
in the Lean kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.SessionEval

open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
  (Ghost OpaqueSymbolSemantics ConcretizedTerm
   node opaqueNode spqrKeyNode
   concretizeRandom concretizeLit concretizeConcat concretizeDhPk concretizeDh
   concretizeKdf concretizeSym concretizeTrunc concretizeVariant
   concretizeKemPk concretizeKemEncap concretizeKemSS concretizeKemRej concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey concretizeSpqrSendMsg
   concretizeSpqrRecvState concretizeSpqrRecvKey concretizeSpqrChainKey concretizeTrWire
   litFuns concatFuns dhFuns kdfFuns symFuns truncFuns x25519Funs
   kemFuns sigFuns spqrFuns trWireFuns allFuns concretizeAll gamma' gamma)

unseal DY.Bytes

/-! ## Term Children and `concretizeAll_split` -/

def children (x : DY.BytesF DY.Bytes) : List DY.Bytes :=
  match x with
  | ⟨⟨0, _⟩, _⟩ | ⟨⟨1, _⟩, _⟩ => []
  | ⟨⟨2, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.lhs, v.rhs]
  | ⟨⟨3, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.sk]
  | ⟨⟨3, _⟩, ⟨⟨1, _⟩, v⟩⟩ => [v.pk, v.sk]
  | ⟨⟨4, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.salt, v.ikm]
  | ⟨⟨5, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.key, v.iv, v.msg]
  | ⟨⟨6, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.input]
  | ⟨⟨7, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.key]
  | ⟨⟨8, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.sk]
  | ⟨⟨8, _⟩, ⟨⟨1, _⟩, v⟩⟩ => [v.pk, v.entropy]
  | ⟨⟨8, _⟩, ⟨⟨2, _⟩, v⟩⟩ => [v.pk, v.entropy]
  | ⟨⟨8, _⟩, ⟨⟨3, _⟩, v⟩⟩ => [v.sk, v.cipher]
  | ⟨⟨9, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.sk]
  | ⟨⟨9, _⟩, ⟨⟨1, _⟩, v⟩⟩ => [v.sk, v.nonce, v.msg]
  | ⟨⟨10, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.authKey, v.params]
  | ⟨⟨10, _⟩, ⟨⟨1, _⟩, v⟩⟩ => [v.st, v.coins]
  | ⟨⟨10, _⟩, ⟨⟨2, _⟩, v⟩⟩ => [v.st, v.coins]
  | ⟨⟨10, _⟩, ⟨⟨3, _⟩, v⟩⟩ => [v.st, v.coins]
  | ⟨⟨10, _⟩, ⟨⟨4, _⟩, v⟩⟩ => [v.st, v.msg]
  | ⟨⟨10, _⟩, ⟨⟨5, _⟩, v⟩⟩ => [v.st, v.msg]
  | ⟨⟨10, _⟩, ⟨⟨6, _⟩, v⟩⟩ => [v.authKey, v.params, v.idx]
  | ⟨⟨11, _⟩, ⟨⟨0, _⟩, v⟩⟩ => [v.senderRatchetKey, v.ciphertext, v.pqRatchet]

theorem pack_of_view_some {b : DY.Bytes} {x : DY.BytesF DY.Bytes}
    (h : b.view? DY.BytesF = some x) : DY.BytesView.pack x = b := by
  have hp := DY.Bytes.pack_view? DY.BytesF b
  rw [h] at hp
  exact hp

private local instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeAll i S g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => rfl⟩

local macro "sstep" : tactic =>
  `(tactic| (
    intro h
    dsimp only [children, concretizeAll] at h ⊢
    simp only [Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    dsimp only [allFuns] at h ⊢
    try simp only [Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]
    dsimp only [litFuns, concatFuns, dhFuns, kdfFuns,
      symFuns, truncFuns, x25519Funs, kemFuns, sigFuns, spqrFuns, trWireFuns,
      concretizeRandom, concretizeLit, concretizeConcat, concretizeDhPk, concretizeDh,
      concretizeKdf, concretizeSym, concretizeTrunc, concretizeVariant,
      concretizeKemPk, concretizeKemEncap, concretizeKemSS, concretizeKemRej, concretizeVk, concretizeSign,
      concretizeSpqrInit, concretizeSpqrSendState, concretizeSpqrSendKey, concretizeSpqrSendMsg,
      concretizeSpqrRecvState, concretizeSpqrRecvKey, concretizeSpqrChainKey, concretizeTrWire,
      node, opaqueNode, spqrKeyNode] at h ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
    try split
    all_goals simp_all [List.flatMap_cons, List.flatMap_nil, List.append_assoc]))

theorem concretizeAll_split (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (f0 f : DY.Bytes → ConcretizedTerm) (x : DY.BytesF DY.Bytes) :
    (∀ y ∈ children x,
        (f0 y).bytes = (f y).bytes ∧ (f0 y).shape = (f y).shape ∧ (f0 y).memo = []) →
      (concretizeAll i S g x (fun y _ => f0 y)).bytes =
        (concretizeAll i S g x (fun y _ => f y)).bytes ∧
      (concretizeAll i S g x (fun y _ => f0 y)).shape =
        (concretizeAll i S g x (fun y _ => f y)).shape ∧
      (concretizeAll i S g x (fun y _ => f y)).memo =
        (concretizeAll i S g x (fun y _ => f0 y)).memo ++
          (children x).flatMap (fun y => (f y).memo) :=
  match x with
  | ⟨⟨0, _⟩, v⟩ => by cases v; sstep
  | ⟨⟨1, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨2, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨3, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨3, _⟩, ⟨⟨1, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨4, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨5, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨6, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨7, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨8, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨8, _⟩, ⟨⟨1, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨8, _⟩, ⟨⟨2, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨8, _⟩, ⟨⟨3, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨9, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨9, _⟩, ⟨⟨1, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨1, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨2, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨3, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨4, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨5, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨10, _⟩, ⟨⟨6, _⟩, v⟩⟩ => by cases v; sstep
  | ⟨⟨11, _⟩, ⟨⟨0, _⟩, v⟩⟩ => by cases v; sstep

/-! ## Transparent `beqBareOptFast` and Kernel `DecidableEq` for `DY.Bytes` -/

abbrev ComposedBare :=
  DY.ALaCarte.BareContainer (DY.ALaCarte.Representable.ctors (f := DY.BytesF))

local instance : DecidableEq (DY.ALaCarte.Representable.CtorId DY.BytesF) :=
  DY.ALaCarte.RepresentableDecidableEq.ctorid_deq (f := DY.BytesF)

local instance (id : DY.ALaCarte.Representable.CtorId DY.BytesF) :
    DecidableEq (DY.ALaCarte.Representable.ctors (f := DY.BytesF) id).Data :=
  DY.ALaCarte.RepresentableDecidableEq.ctor_data_deq (f := DY.BytesF) id

def beqListOpt {α : Type} (eq : α → α → Option Bool) : List α → List α → Option Bool
  | [], [] => some true
  | a :: as, b :: bs =>
    match eq a b with
    | some true => beqListOpt eq as bs
    | some false => some false
    | none => none
  | _, _ => some false

def beqBareOptFast : Nat → ComposedBare → ComposedBare → Option Bool
  | 0, _, _ => none
  | fuel + 1, ⟨id1, d1, as1⟩, ⟨id2, d2, as2⟩ =>
    if hid : id1 = id2 then
      if hid ▸ d1 = d2 then beqListOpt (beqBareOptFast fuel) as1.toList as2.toList
      else some false
    else some false

private theorem beqListOpt_true {α : Type} {eq : α → α → Option Bool} :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, ∀ b, eq a b = some true → a = b) →
      beqListOpt eq l1 l2 = some true → l1 = l2
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: as, b :: bs, ih, h => by
    dsimp only [beqListOpt] at h
    cases heq : eq a b with
    | none => rw [heq] at h; nomatch h
    | some v =>
      cases v with
      | false => rw [heq] at h; nomatch h
      | true =>
        rw [heq] at h
        rw [ih a List.mem_cons_self b heq,
          beqListOpt_true (fun x hx y => ih x (List.mem_cons_of_mem a hx) y) h]

private theorem beqListOpt_false {α : Type} {eq : α → α → Option Bool} :
    ∀ {l1 l2 : List α}, (∀ a ∈ l1, ∀ b, eq a b = some false → a ≠ b) →
      beqListOpt eq l1 l2 = some false → l1 ≠ l2
  | [], [], _, h => nomatch h
  | [], _ :: _, _, _ => fun h => nomatch h
  | _ :: _, [], _, _ => fun h => nomatch h
  | a :: as, b :: bs, ih, h => by
    dsimp only [beqListOpt] at h
    cases heq : eq a b with
    | none => rw [heq] at h; nomatch h
    | some v =>
      cases v with
      | false =>
        intro hl; injection hl with hab _
        exact ih a List.mem_cons_self b heq hab
      | true =>
        rw [heq] at h
        intro hl; injection hl with _ htail
        exact beqListOpt_false (fun x hx y => ih x (List.mem_cons_of_mem a hx) y) h htail

theorem beqBareOptFast_true :
    ∀ (fuel : Nat) (x y : ComposedBare), beqBareOptFast fuel x y = some true → x = y
  | 0, _, _, h => nomatch h
  | fuel + 1, ⟨id1, d1, ⟨l1⟩⟩, ⟨id2, d2, ⟨l2⟩⟩, h => by
    dsimp only [beqBareOptFast] at h
    split at h
    · next hid =>
      subst hid
      split at h
      · next hd =>
        subst hd; congr 2
        exact beqListOpt_true (fun a _ b => beqBareOptFast_true fuel a b) h
      · nomatch h
    · nomatch h

theorem beqBareOptFast_false :
    ∀ (fuel : Nat) (x y : ComposedBare), beqBareOptFast fuel x y = some false → x ≠ y
  | 0, _, _, h => nomatch h
  | fuel + 1, ⟨id1, d1, ⟨l1⟩⟩, ⟨id2, d2, ⟨l2⟩⟩, h => by
    dsimp only [beqBareOptFast] at h
    split at h
    · next hid =>
      subst hid
      split at h
      · next hd =>
        subst hd
        intro heq; injection heq with _ _ hl; injection hl with hl'
        exact beqListOpt_false (fun a _ b => beqBareOptFast_false fuel a b) h hl'
      · next hd => intro heq; cases heq; exact hd rfl
    · next hid => intro heq; cases heq; exact hid rfl

noncomputable def decEqBytesFast : DecidableEq DY.Bytes :=
  fun a b =>
    match h : beqBareOptFast 256 a.val b.val with
    | some true => isTrue (Subtype.ext (beqBareOptFast_true 256 a.val b.val h))
    | some false => isFalse (fun heq => beqBareOptFast_false 256 a.val b.val h (congrArg Subtype.val heq))
    | none => DY.instDecidableEqBytes a b

theorem instDecidableEqBytes_eq_fast :
    (@DY.instDecidableEqBytes DY.Libsignal.TripleRatchet.HasExecBytes.bytesFunc) = decEqBytesFast := by
  funext a b; exact Subsingleton.elim _ _

theorem instDecidableEqBytes_pq :
    (@DY.instDecidableEqBytes DY.Libsignal.PQXDH.HasExecBytes.bytesFunc) = decEqBytesFast := by
  funext a b; exact Subsingleton.elim _ _

theorem instDecidableEqBytes_composed :
    (@DY.instDecidableEqBytes DY.Libsignal.Composed.instBytesFunctor_symbolic) = decEqBytesFast := by
  funext a b; exact Subsingleton.elim _ _

/-! ## `Nat`-Keyed Binary `Trie` and `buildDagTrie` -/

inductive Trie (α : Type) where
  | leaf (bucket : List α)
  | branch (lo hi : Trie α)

def emptyTrie {α : Type} : Nat → Trie α
  | 0 => .leaf []
  | d + 1 => .branch (emptyTrie d) (emptyTrie d)

def trieBucket {α : Type} : Trie α → Nat → List α
  | .leaf bs, _ => bs
  | .branch lo hi, h =>
    if Nat.beq (h % 2) 0 then trieBucket lo (h / 2) else trieBucket hi (h / 2)

def trieInsert {α : Type} : Trie α → Nat → α → Trie α
  | .leaf bs, _, x => .leaf (x :: bs)
  | .branch lo hi, h, x =>
    if Nat.beq (h % 2) 0 then .branch (trieInsert lo (h / 2) x) hi
    else .branch lo (trieInsert hi (h / 2) x)

def trieToList {α : Type} : Trie α → List α
  | .leaf bs => bs
  | .branch lo hi => trieToList lo ++ trieToList hi

theorem trieBucket_mem_toList {α : Type} :
    ∀ (t : Trie α) (h : Nat) {x : α}, x ∈ trieBucket t h → x ∈ trieToList t
  | .leaf _, _, _, hx => hx
  | .branch lo hi, h, _, hx => by
    dsimp only [trieBucket, trieToList] at hx ⊢
    split at hx
    · exact List.mem_append_left _ (trieBucket_mem_toList lo (h / 2) hx)
    · exact List.mem_append_right _ (trieBucket_mem_toList hi (h / 2) hx)

theorem mem_trieToList_insert {α : Type} :
    ∀ (t : Trie α) (h : Nat) (x y : α),
      y ∈ trieToList (trieInsert t h x) ↔ y = x ∨ y ∈ trieToList t
  | .leaf bs, _, x, y => by simp [trieInsert, trieToList]
  | .branch lo hi, h, x, y => by
    cases hbit : Nat.beq (h % 2) 0 <;>
      simp [trieInsert, trieToList, hbit, mem_trieToList_insert, or_left_comm, or_assoc]

private theorem mem_trieBucket_insert_eq {α : Type} :
    ∀ (t : Trie α) (h : Nat) (x : α), x ∈ trieBucket (trieInsert t h x) h
  | .leaf _, _, _ => List.mem_cons_self
  | .branch lo hi, h, x => by
    cases hbit : Nat.beq (h % 2) 0 <;>
      simp [trieInsert, trieBucket, hbit, mem_trieBucket_insert_eq]

private theorem mem_trieBucket_insert_of_mem {α : Type} :
    ∀ (t : Trie α) (h k : Nat) (x y : α),
      y ∈ trieBucket t k → y ∈ trieBucket (trieInsert t h x) k
  | .leaf _, _, _, _, _, hy => List.mem_cons_of_mem _ hy
  | .branch lo hi, h, k, x, y, hy => by
    cases hbit : Nat.beq (h % 2) 0 <;> cases kbit : Nat.beq (k % 2) 0 <;>
      simp only [trieInsert, trieBucket, hbit, kbit, ↓reduceIte, Bool.false_eq_true] at hy ⊢
    · exact mem_trieBucket_insert_of_mem hi _ _ x y hy
    · exact hy
    · exact hy
    · exact mem_trieBucket_insert_of_mem lo _ _ x y hy

theorem foldl_memoTrie_mem {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (mt : Trie α),
      ∀ m, (m ∈ xs ∨ m ∈ trieBucket mt (f m)) →
        m ∈ trieBucket (xs.foldl (fun acc x => trieInsert acc (f x) x) mt) (f m)
  | [], _, _, hm => hm.elim (fun h => nomatch h) id
  | x :: xs, mt, m, hm =>
    foldl_memoTrie_mem f xs (trieInsert mt (f x) x) m <| by
      rcases hm with hmem | hbuck
      · rcases List.mem_cons.mp hmem with rfl | hrest
        · exact Or.inr (mem_trieBucket_insert_eq mt (f m) m)
        · exact Or.inl hrest
      · exact Or.inr (mem_trieBucket_insert_of_mem mt (f x) (f m) x m hbuck)

def forceListOnce {α β : Type} : List α → (List α → β) → β
  | [], k => k []
  | x :: xs, k => k (x :: xs)

theorem forceListOnce_eq {α β : Type} (xs : List α) (k : List α → β) :
    forceListOnce xs k = k xs := by
  cases xs <;> rfl

def forceTrieOnce {α β : Type} : Trie α → (Trie α → β) → β
  | .leaf bs, k => k (.leaf bs)
  | .branch lo hi, k => k (.branch lo hi)

theorem forceTrieOnce_eq {α β : Type} (t : Trie α) (k : Trie α → β) :
    forceTrieOnce t k = k t := by
  cases t <;> rfl

def withForcedList {α β : Type} : List α → List α → (List α → β) → β
  | [], acc, k => k acc.reverse
  | x :: xs, acc, k => withForcedList xs (x :: acc) k

theorem withForcedList_eq {α β : Type} (k : List α → β) :
    ∀ (xs acc : List α), withForcedList xs acc k = k (acc.reverse ++ xs)
  | [], acc => by simp [withForcedList]
  | x :: xs, acc => by
    simp [withForcedList, withForcedList_eq k xs (x :: acc), List.reverse_cons, List.append_assoc]

def withForcedTrie {α β : Type} : Trie α → (Trie α → β) → β
  | .leaf bs, k => withForcedList bs [] (fun bs' => k (.leaf bs'))
  | .branch lo hi, k =>
    withForcedTrie lo (fun lo' => withForcedTrie hi (fun hi' => k (.branch lo' hi')))

theorem withForcedTrie_eq {α : Type} :
    ∀ (t : Trie α) {β : Type} (k : Trie α → β), withForcedTrie t k = k t
  | .leaf bs, _, k => by
    dsimp only [withForcedTrie]
    rw [withForcedList_eq, List.reverse_nil, List.nil_append]
  | .branch lo hi, _, k => by
    dsimp only [withForcedTrie]
    rw [withForcedTrie_eq lo, withForcedTrie_eq hi]

def foldlTrie {α β : Type} (f : Trie α → β → Trie α) : Trie α → List β → Trie α
  | t, [] => t
  | t, x :: xs => withForcedTrie (f t x) fun t' => foldlTrie f t' xs

theorem foldlTrie_eq {α β : Type} (f : Trie α → β → Trie α) :
    ∀ (xs : List β) (t : Trie α), foldlTrie f t xs = xs.foldl f t
  | [], _ => rfl
  | x :: xs, t => by dsimp only [foldlTrie, List.foldl_cons]; rw [withForcedTrie_eq, foldlTrie_eq]

def hashTermNat : Nat → DY.Bytes → Nat
  | 0, _ => 7
  | fuel + 1, b =>
    match b.view? DY.BytesF with
    | none => 0
    | some x =>
      match x with
      | ⟨⟨0, _⟩, v⟩ => (v.timestamp * 257 + v.size + 3) % 65521
      | ⟨⟨1, _⟩, ⟨⟨0, _⟩, v⟩⟩ =>
        let b0 := if h0 : 0 < v.lit.size then v.lit[0].toNat else 0
        (v.lit.size * 131 + b0 + 5) % 65521
      | _ =>
        (children x).foldl (fun h y => (h * 131 + hashTermNat fuel y) % 65521)
          ((if x.1.val ≥ 7 then x.1.val + 1 else x.1.val) * 17 + 100)

structure DagEntry where
  hash : Nat
  rank : Nat := 0
  term : DY.Bytes
  bytes : HwBytes
  shape : DY.Bytes
  selfMemo : List (DY.Bytes × DY.Bytes × HwBytes)

def bucketLookup (bs : List DagEntry) (h : Nat) (b : DY.Bytes) : Option DagEntry :=
  match bs with
  | [] => none
  | e :: rest =>
    if Nat.beq e.hash h && beqBareOptFast 256 b.val e.term.val == some true then some e
    else bucketLookup rest h b

def dagTrieLookupH (t : Trie DagEntry) (h : Nat) (b : DY.Bytes) : Option DagEntry :=
  bucketLookup (trieBucket t h) h b

def dagTrieLookup (t : Trie DagEntry) (b : DY.Bytes) : Option DagEntry :=
  dagTrieLookupH t (hashTermNat 8 b) b

def buildDagTrie : Nat → ExternInterpretation → OpaqueSymbolSemantics → Ghost →
    Trie DagEntry → DY.Bytes → Trie DagEntry
  | 0, _, _, _, dag, _ => dag
  | fuel + 1, i, S, g, dag, b =>
    let hb := hashTermNat 8 b
    match dagTrieLookupH dag hb b with
    | some _ => dag
    | none =>
      match b.view? DY.BytesF with
      | none => dag
      | some x =>
        forceTrieOnce ((children x).foldl (buildDagTrie fuel i S g) dag) fun dag' =>
          if (children x).all (fun y => (dagTrieLookup dag' y).isSome) then
            match concretizeAll i S g x (fun y _ =>
              match dagTrieLookup dag' y with
              | some e => { bytes := e.bytes, shape := e.shape, memo := [] }
              | none => { bytes := [], shape := y, memo := [] }) with
            | { bytes := bs, shape := sh, memo := ms } =>
              withForcedList bs [] fun bsLit =>
                withForcedList ms [] fun memoLit =>
                  let rk := (children x).foldl (fun m y =>
                    match dagTrieLookup dag' y with
                    | some ey => Nat.max m (ey.rank + 1)
                    | none => m) 0
                  trieInsert dag' hb
                    { hash := hb, rank := rk, term := b, bytes := bsLit, shape := sh,
                      selfMemo := memoLit }
          else dag'

def DagSound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (dag : List DagEntry) : Prop :=
  ∀ e ∈ dag,
    e.bytes = (gamma' i S g e.term).bytes ∧
    e.shape = (gamma' i S g e.term).shape ∧
    ∀ m ∈ (gamma' i S g e.term).memo, ∃ e' ∈ dag, m ∈ e'.selfMemo

private theorem bucketLookup_mem {bs : List DagEntry} {h : Nat} {b : DY.Bytes} {e : DagEntry}
    (hl : bucketLookup bs h b = some e) : e ∈ bs ∧ b = e.term := by
  induction bs with
  | nil => cases hl
  | cons hd tl ih =>
    dsimp only [bucketLookup] at hl
    split at hl
    · next hcond =>
      injection hl with heq; subst heq
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact ⟨List.mem_cons_self, Subtype.ext (beqBareOptFast_true 256 b.val hd.term.val hcond.2)⟩
    · obtain ⟨hm, hb⟩ := ih hl
      exact ⟨List.mem_cons_of_mem _ hm, hb⟩

theorem dagTrieLookup_mem {t : Trie DagEntry} {b : DY.Bytes} {e : DagEntry}
    (hl : dagTrieLookup t b = some e) : e ∈ trieToList t ∧ b = e.term := by
  obtain ⟨hm, hb⟩ := bucketLookup_mem hl
  exact ⟨trieBucket_mem_toList t _ hm, hb⟩

private theorem foldl_buildDagTrie_step {fuel : Nat} {i : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost}
    (ih : ∀ dag b, DagSound i S g (trieToList dag) →
      DagSound i S g (trieToList (buildDagTrie fuel i S g dag b))) :
    ∀ (ys : List DY.Bytes) (dag : Trie DagEntry),
      DagSound i S g (trieToList dag) →
      DagSound i S g (trieToList (ys.foldl (buildDagTrie fuel i S g) dag))
  | [], _, hdag => hdag
  | y :: ys, dag, hdag => foldl_buildDagTrie_step ih ys _ (ih dag y hdag)

theorem buildDagTrie_sound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    ∀ (fuel : Nat) (dag : Trie DagEntry) (b : DY.Bytes),
      DagSound i S g (trieToList dag) →
      DagSound i S g (trieToList (buildDagTrie fuel i S g dag b))
  | 0, _, _, hdag => hdag
  | fuel + 1, dag, b, hdag => by
    dsimp only [buildDagTrie]
    cases hl : dagTrieLookupH dag (hashTermNat 8 b) b with
    | some _ => exact hdag
    | none =>
      cases hv : b.view? DY.BytesF with
      | none => exact hdag
      | some x =>
        dsimp only
        rw [forceTrieOnce_eq]
        have hdag' : DagSound i S g (trieToList ((children x).foldl (buildDagTrie fuel i S g) dag)) :=
          foldl_buildDagTrie_step (buildDagTrie_sound i S g fuel) (children x) dag hdag
        set dag' := (children x).foldl (buildDagTrie fuel i S g) dag
        split
        · next hall =>
          rw [withForcedList_eq, List.reverse_nil, List.nil_append,
              withForcedList_eq, List.reverse_nil, List.nil_append]
          set f0 : DY.Bytes → ConcretizedTerm := fun y =>
            match dagTrieLookup dag' y with
            | some e => { bytes := e.bytes, shape := e.shape, memo := [] }
            | none => { bytes := [], shape := y, memo := [] }
          have hchild : ∀ y ∈ children x,
              (f0 y).bytes = (gamma' i S g y).bytes ∧
              (f0 y).shape = (gamma' i S g y).shape ∧ (f0 y).memo = [] := by
            intro y hy
            have hySome := List.all_eq_true.mp hall y hy
            cases hly : dagTrieLookup dag' y with
            | none => rw [hly] at hySome; cases hySome
            | some ey =>
              obtain ⟨hmem, hyEq⟩ := dagTrieLookup_mem hly
              obtain ⟨hb, hs, _⟩ := hdag' ey hmem
              dsimp only [f0]; rw [hly]; subst hyEq; exact ⟨hb, hs, rfl⟩
          have hrec : gamma' i S g b = concretizeAll i S g x (fun y _ => gamma' i S g y) := by
            rw [← pack_of_view_some hv]
            exact DY.Bytes.rec_eq (concretizeAll i S g) (concretizeAll i S g) x
          obtain ⟨hb, hs, hm⟩ := concretizeAll_split i S g f0 (gamma' i S g) x hchild
          intro e he
          rcases (mem_trieToList_insert dag' _ _ e).mp he with rfl | he'
          · refine ⟨by dsimp only; rw [hrec]; exact hb,
                    by dsimp only; rw [hrec]; exact hs, ?_⟩
            intro m hm_in
            rw [hrec, hm, List.mem_append] at hm_in
            rcases hm_in with hself | hkids
            · exact ⟨_, (mem_trieToList_insert dag' _ _ _).mpr (Or.inl rfl), hself⟩
            · obtain ⟨y, hy, hmy⟩ := List.mem_flatMap.mp hkids
              have hySome := List.all_eq_true.mp hall y hy
              cases hly : dagTrieLookup dag' y with
              | none => rw [hly] at hySome; cases hySome
              | some ey =>
                obtain ⟨hmem, hyEq⟩ := dagTrieLookup_mem hly
                subst hyEq
                obtain ⟨e', he', hme'⟩ := (hdag' ey hmem).2.2 m hmy
                exact ⟨e', (mem_trieToList_insert dag' _ _ _).mpr (Or.inr he'), hme'⟩
          · obtain ⟨hb', hs', hm'⟩ := hdag' e he'
            exact ⟨hb', hs', fun m hm_in =>
              let ⟨e', he'', hme'⟩ := hm' m hm_in
              ⟨e', (mem_trieToList_insert dag' _ _ _).mpr (Or.inr he''), hme'⟩⟩
        · exact hdag'

theorem foldl_buildDagTrie_sound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ys : List DY.Bytes) (dag : Trie DagEntry) (hdag : DagSound i S g (trieToList dag)) :
    DagSound i S g (trieToList (ys.foldl (buildDagTrie 256 i S g) dag)) :=
  foldl_buildDagTrie_step (buildDagTrie_sound i S g 256) ys dag hdag

private theorem trieToList_emptyTrie {α : Type} : ∀ (d : Nat), trieToList (emptyTrie (α := α) d) = []
  | 0 => rfl
  | d + 1 => by simp [emptyTrie, trieToList, trieToList_emptyTrie d]

theorem emptyTrie_sound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) : DagSound i S g (trieToList (emptyTrie d)) := by
  rw [trieToList_emptyTrie]
  intro _ h
  nomatch h

private theorem buildDagTrie_mono (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    ∀ (fuel : Nat) (d : Trie DagEntry) (b : DY.Bytes),
      ∀ e ∈ trieToList d, e ∈ trieToList (buildDagTrie fuel i S g d b)
  | 0, _, _, _, he => he
  | fuel + 1, d, b, e, he => by
    dsimp only [buildDagTrie]
    cases dagTrieLookupH d (hashTermNat 8 b) b with
    | some _ => exact he
    | none =>
      cases b.view? DY.BytesF with
      | none => exact he
      | some x =>
        dsimp only
        rw [forceTrieOnce_eq]
        have hfold : ∀ (zs : List DY.Bytes) (d0 : Trie DagEntry),
            ∀ e0 ∈ trieToList d0, e0 ∈ trieToList (zs.foldl (buildDagTrie fuel i S g) d0) := by
          intro zs; induction zs with
          | nil => intro d0 e0 he0; exact he0
          | cons z zs ihz => intro d0 e0 he0; exact ihz _ e0 (buildDagTrie_mono i S g fuel d0 z e0 he0)
        have he' := hfold (children x) d e he
        split
        · rw [withForcedList_eq, List.reverse_nil, List.nil_append,
              withForcedList_eq, List.reverse_nil, List.nil_append]
          exact (mem_trieToList_insert _ _ _ e).mpr (Or.inr he')
        · exact he'

theorem foldl_buildDagTrie_mono (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    ∀ (ys : List DY.Bytes) (d : Trie DagEntry),
      ∀ e ∈ trieToList d, e ∈ trieToList (ys.foldl (buildDagTrie 256 i S g) d)
  | [], _, _, he => he
  | y :: ys, d, e, he =>
    foldl_buildDagTrie_mono i S g ys _ e (buildDagTrie_mono i S g 256 d y e he)

def dagTrieGamma (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (dag : Trie DagEntry) (b : DY.Bytes) : HwBytes :=
  match dagTrieLookup dag b with
  | some e => e.bytes
  | none => gamma i S g b

theorem gamma_eq_dagTrieGamma {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {dag : Trie DagEntry} (hs : DagSound i S g (trieToList dag)) :
    gamma i S g = dagTrieGamma i S g dag := by
  funext b; unfold dagTrieGamma
  cases hl : dagTrieLookup dag b with
  | none => rfl
  | some e =>
    obtain ⟨hmem, rfl⟩ := dagTrieLookup_mem hl
    exact ((hs e hmem).1).symm

def withDagGamma {β : Type} (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (roots : List DY.Bytes) (k : (DY.Bytes → HwBytes) → β) : β :=
  forceTrieOnce (roots.foldl (buildDagTrie 256 i S g) (emptyTrie 8)) fun dag =>
    k (dagTrieGamma i S g dag)

theorem withDagGamma_eq {β : Type} (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (roots : List DY.Bytes) (k : (DY.Bytes → HwBytes) → β) :
    withDagGamma i S g roots k = k (gamma i S g) := by
  unfold withDagGamma
  rw [forceTrieOnce_eq]
  have hs := foldl_buildDagTrie_sound i S g roots (emptyTrie 8) (emptyTrie_sound i S g 8)
  rw [← gamma_eq_dagTrieGamma hs]

def evalGammaFast (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (b : DY.Bytes) : HwBytes :=
  forceTrieOnce (buildDagTrie 256 i S g (emptyTrie 6) b) fun dag =>
    dagTrieGamma i S g dag b

theorem gamma_eq_fast (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma i S g = evalGammaFast i S g := by
  funext b; unfold evalGammaFast
  rw [forceTrieOnce_eq]
  have hs := buildDagTrie_sound i S g 256 (emptyTrie 6) b (emptyTrie_sound i S g 6)
  exact congrFun (gamma_eq_dagTrieGamma hs) b

end Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
