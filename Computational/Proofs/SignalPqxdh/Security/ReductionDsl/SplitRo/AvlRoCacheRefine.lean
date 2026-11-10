/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Reductions.ReductionDsl.TargetCodecs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec

/-!
# Shadow-Index Refinement and Shadow-Scan Lemmas

Protocol-independent refinement library for split random-oracle reductions with AVL caches.
Establishes clamped-fuel equivalence on `Expr` and `Comp` list combinators, the `ShadowRel` and
`RoCacheRel` invariants, shadow-scan equivalence on `OracleComp`, length-aware key separation, and
concrete `AvlB192Valid` / `AvlPair32Valid` bridges.
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine

open OracleSpec OracleComp
open _root_.ReductionDsl (
  Sig Ty Var Expr Comp Env Ops Iface
  pqAtomicSig pqAtomicOps B
  findML anyML mapML consumeFirstML foldML
)
open _root_.SignalPqxdh (Bytes)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableDefs (
  avlPathItemTy avlTy avlEmptyE dfltB192E dfltPair32E
  avlSearchB192C avlSearchPair32C avlInsertAtPathC
)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoTableSpec (
  AvlB192Valid AvlPair32Valid
  avlEmptyE_b192_valid avlEmptyE_pair32_valid
  avlSearchInsertB192_spec avlSearchInsertPair32_spec
  avlInsertAtPathC_eval_congr
)

section FuelIdentity

theorem take_min_right_of_length_le {α : Type} {l : List α} {L : ℕ} (K : ℕ)
    (hL : l.length ≤ L) :
    l.take (min K L) = l.take K := by
  by_cases hKL : K ≤ L
  · rw [Nat.min_eq_left hKL]
  · have hLK : L ≤ K := Nat.le_of_not_ge hKL
    rw [Nat.min_eq_right hLK, List.take_of_length_le hL,
      List.take_of_length_le (Nat.le_trans hL hLK)]

theorem take_min_left_of_length_le {α : Type} {l : List α} {L : ℕ} (K : ℕ)
    (hL : l.length ≤ L) :
    l.take (min L K) = l.take K := by
  rw [Nat.min_comm]
  exact take_min_right_of_length_le K hL

variable {S : Sig} {O : Ops S} {Γ : List (Ty S)}

theorem findB_min_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.findB (min K L) l p).eval ρ = (Expr.findB K l p).eval ρ := by
  simp only [Expr.eval, take_min_right_of_length_le K hL]

theorem findB_min_left_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.findB (min L K) l p).eval ρ = (Expr.findB K l p).eval ρ := by
  simp only [Expr.eval, take_min_left_of_length_le K hL]

theorem anyB_min_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.anyB (min K L) l p).eval ρ = (Expr.anyB K l p).eval ρ := by
  simp only [Expr.eval, take_min_right_of_length_le K hL]

theorem anyB_min_left_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Expr O (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.anyB (min L K) l p).eval ρ = (Expr.anyB K l p).eval ρ := by
  simp only [Expr.eval, take_min_left_of_length_le K hL]

theorem mapB_min_eval_eq {a b : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list a)) (f : Expr O (a :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.mapB (min K L) l f).eval ρ = (Expr.mapB K l f).eval ρ := by
  simp only [Expr.eval, take_min_right_of_length_le K hL]

theorem mapB_min_left_eval_eq {a b : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list a)) (f : Expr O (a :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.mapB (min L K) l f).eval ρ = (Expr.mapB K l f).eval ρ := by
  simp only [Expr.eval, take_min_left_of_length_le K hL]

theorem foldrB_min_eval_eq {a b : Ty S} (K L : ℕ) (l : Expr O Γ (.list a)) (z : Expr O Γ b)
    (f : Expr O (a :: b :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.foldrB (min K L) l z f).eval ρ = (Expr.foldrB K l z f).eval ρ := by
  simp only [Expr.eval, take_min_right_of_length_le K hL]

theorem foldrB_min_left_eval_eq {a b : Ty S} (K L : ℕ) (l : Expr O Γ (.list a)) (z : Expr O Γ b)
    (f : Expr O (a :: b :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Expr.foldrB (min L K) l z f).eval ρ = (Expr.foldrB K l z f).eval ρ := by
  simp only [Expr.eval, take_min_left_of_length_le K hL]

section CompFuelIdentity

variable {ι : Type} {T : OracleSpec ι} {I : Iface S T}

/-- Replacing fuel `K` by `min K L` in `Comp.findM` preserves `eval` when `(l.eval ρ).length ≤ L`. -/
theorem findM_min_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.findM (min K L) l p).eval ρ = (Comp.findM K l p).eval ρ := by
  simp only [Comp.eval, take_min_right_of_length_le K hL]

theorem findM_min_left_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.findM (min L K) l p).eval ρ = (Comp.findM K l p).eval ρ := by
  simp only [Comp.eval, take_min_left_of_length_le K hL]

theorem anyM_min_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.anyM (min K L) l p).eval ρ = (Comp.anyM K l p).eval ρ := by
  simp only [Comp.eval, take_min_right_of_length_le K hL]

theorem anyM_min_left_eval_eq {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.anyM (min L K) l p).eval ρ = (Comp.anyM K l p).eval ρ := by
  simp only [Comp.eval, take_min_left_of_length_le K hL]

theorem mapM_min_eval_eq {a b : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list a)) (f : Comp O I (a :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.mapM (min K L) l f).eval ρ = (Comp.mapM K l f).eval ρ := by
  simp only [Comp.eval, take_min_right_of_length_le K hL]

theorem mapM_min_left_eval_eq {a b : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list a)) (f : Comp O I (a :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.mapM (min L K) l f).eval ρ = (Comp.mapM K l f).eval ρ := by
  simp only [Comp.eval, take_min_left_of_length_le K hL]

theorem consumeFirstM_min_eval_eq {t : Ty S} (K L : ℕ) (l : Expr O Γ (.list t))
    (p : Comp O I (t :: Γ) .bool) (mk : Expr O (t :: Γ) t) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.consumeFirstM (min K L) l p mk).eval ρ = (Comp.consumeFirstM K l p mk).eval ρ := by
  simp only [Comp.eval, take_min_right_of_length_le K hL]

theorem consumeFirstM_min_left_eval_eq {t : Ty S} (K L : ℕ) (l : Expr O Γ (.list t))
    (p : Comp O I (t :: Γ) .bool) (mk : Expr O (t :: Γ) t) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.consumeFirstM (min L K) l p mk).eval ρ = (Comp.consumeFirstM K l p mk).eval ρ := by
  simp only [Comp.eval, take_min_left_of_length_le K hL]

theorem foldM_min_eval_eq {a b : Ty S} (K L : ℕ) (l : Expr O Γ (.list a)) (z : Expr O Γ b)
    (f : Comp O I (a :: b :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.foldM (min K L) l z f).eval ρ = (Comp.foldM K l z f).eval ρ := by
  simp only [Comp.eval, take_min_right_of_length_le K hL]

theorem foldM_min_left_eval_eq {a b : Ty S} (K L : ℕ) (l : Expr O Γ (.list a)) (z : Expr O Γ b)
    (f : Comp O I (a :: b :: Γ) b) (ρ : Env Γ) (hL : (l.eval ρ).length ≤ L) :
    (Comp.foldM (min L K) l z f).eval ρ = (Comp.foldM K l z f).eval ρ := by
  simp only [Comp.eval, take_min_left_of_length_le K hL]

theorem findM_min_simulateQ_eq {m : Type → Type} [Monad m]
    (qi : QueryImpl T m) {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ)
    (hL : (l.eval ρ).length ≤ L) :
    simulateQ qi ((Comp.findM (min K L) l p).eval ρ) =
      simulateQ qi ((Comp.findM K l p).eval ρ) := by
  rw [findM_min_eval_eq K L l p ρ hL]

theorem anyM_min_simulateQ_eq {m : Type → Type} [Monad m]
    (qi : QueryImpl T m) {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ)
    (hL : (l.eval ρ).length ≤ L) :
    simulateQ qi ((Comp.anyM (min K L) l p).eval ρ) =
      simulateQ qi ((Comp.anyM K l p).eval ρ) := by
  rw [anyM_min_eval_eq K L l p ρ hL]

theorem findM_min_isQueryBoundP_iff {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ)
    (P : T.Domain → Prop) [DecidablePred P] (n : ℕ)
    (hL : (l.eval ρ).length ≤ L) :
    ((Comp.findM (min K L) l p).eval ρ).IsQueryBoundP P n ↔
      ((Comp.findM K l p).eval ρ).IsQueryBoundP P n := by
  rw [findM_min_eval_eq K L l p ρ hL]

theorem anyM_min_isQueryBoundP_iff {t : Ty S} (K L : ℕ)
    (l : Expr O Γ (.list t)) (p : Comp O I (t :: Γ) .bool) (ρ : Env Γ)
    (P : T.Domain → Prop) [DecidablePred P] (n : ℕ)
    (hL : (l.eval ρ).length ≤ L) :
    ((Comp.anyM (min K L) l p).eval ρ).IsQueryBoundP P n ↔
      ((Comp.anyM K l p).eval ρ).IsQueryBoundP P n := by
  rw [anyM_min_eval_eq K L l p ρ hL]

end CompFuelIdentity
end FuelIdentity

/-- Source tag distinguishing offline random-oracle entries from online session entries. -/
inductive SourceTag (K : Type) : Type
  | ro (key : K)
  | sess
  deriving DecidableEq, Repr

/-- Entry paired with its global insertion index and source tag. -/
structure TaggedEntry (K E : Type) : Type where
  idx : ℕ
  tag : SourceTag K
  entry : E
  deriving DecidableEq, Repr

/-- Newest-first association list `(key, (valOf entry, idx))` of `.ro`-tagged entries. -/
@[expose] def roEntriesOf {K V E : Type} (valOf : E → V) (tagged : List (TaggedEntry K E)) :
    List (K × (V × ℕ)) :=
  tagged.filterMap fun te =>
    match te.tag with
    | .ro k => some (k, (valOf te.entry, te.idx))
    | .sess => none

/-- Newest-first `(idx, entry)` shadow list of `.sess`-tagged entries. -/
@[expose] def sessEntriesOf {K E : Type} (tagged : List (TaggedEntry K E)) : List (ℕ × E) :=
  tagged.filterMap fun te =>
    match te.tag with
    | .ro _ => none
    | .sess => some (te.idx, te.entry)

@[simp] theorem roEntriesOf_nil {K V E : Type} (valOf : E → V) :
    roEntriesOf (K := K) valOf [] = [] := rfl

@[simp] theorem roEntriesOf_cons_sess {K V E : Type} (valOf : E → V)
    (idx : ℕ) (e : E) (ts : List (TaggedEntry K E)) :
    roEntriesOf valOf (⟨idx, .sess, e⟩ :: ts) = roEntriesOf valOf ts := rfl

@[simp] theorem roEntriesOf_cons_ro {K V E : Type} (valOf : E → V)
    (idx : ℕ) (k : K) (e : E) (ts : List (TaggedEntry K E)) :
    roEntriesOf valOf (⟨idx, .ro k, e⟩ :: ts) = (k, (valOf e, idx)) :: roEntriesOf valOf ts := rfl

@[simp] theorem sessEntriesOf_nil {K E : Type} :
    sessEntriesOf (K := K) (E := E) [] = [] := rfl

@[simp] theorem sessEntriesOf_cons_sess {K E : Type}
    (idx : ℕ) (e : E) (ts : List (TaggedEntry K E)) :
    sessEntriesOf (⟨idx, .sess, e⟩ :: ts) = (idx, e) :: sessEntriesOf ts := rfl

@[simp] theorem sessEntriesOf_cons_ro {K E : Type}
    (idx : ℕ) (k : K) (e : E) (ts : List (TaggedEntry K E)) :
    sessEntriesOf (⟨idx, .ro k, e⟩ :: ts) = sessEntriesOf ts := rfl

/-- Refinement invariant relating a newest-first mixed list `l` of length `ctr ≤ cap` to its
    indexed `tagged` trace, AVL lookup map `avlLookup` over unique `.ro` keys, and `.sess` shadow
    list `sess`. -/
structure ShadowRel {K V E : Type} [BEq K] (cap : ℕ) (valOf : E → V)
    (l : List E) (tagged : List (TaggedEntry K E))
    (avlLookup : K → Option (V × ℕ)) (sess : List (ℕ × E)) (ctr : ℕ) : Prop where
  forget_eq : tagged.map TaggedEntry.entry = l
  ctr_eq : ctr = l.length
  len_le : l.length ≤ cap
  indices_eq : tagged.map TaggedEntry.idx = (List.range ctr).reverse
  sess_eq : sess = sessEntriesOf tagged
  avl_eq : ∀ k : K, avlLookup k = ((roEntriesOf valOf tagged).find? (fun p => p.1 == k)).map Prod.snd
  ro_keys_nodup : ((roEntriesOf valOf tagged).map Prod.fst).Nodup

/-- Refinement invariant relating a duplicate-free key-value list `l` of length `≤ cap` to an AVL
    lookup map `avlLookup`. -/
structure RoCacheRel {K V : Type} [BEq K] (cap : ℕ)
    (l : List (K × V)) (avlLookup : K → Option V) : Prop where
  len_le : l.length ≤ cap
  avl_eq : ∀ k : K, avlLookup k = (l.find? (fun p => p.1 == k)).map Prod.snd
  keys_nodup : (l.map Prod.fst).Nodup

theorem roEntriesOf_length_le {K V E : Type} (valOf : E → V) (ts : List (TaggedEntry K E)) :
    (roEntriesOf valOf ts).length ≤ ts.length :=
  List.length_filterMap_le _ _

theorem sessEntriesOf_length_le {K E : Type} (ts : List (TaggedEntry K E)) :
    (sessEntriesOf ts).length ≤ ts.length :=
  List.length_filterMap_le _ _

theorem ShadowRel.tagged_length_eq {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    tagged.length = l.length := by
  have := congrArg List.length h.forget_eq
  simpa using this

theorem ShadowRel.sess_length_le {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    sess.length ≤ l.length := by
  rw [h.sess_eq, ← h.tagged_length_eq]
  exact sessEntriesOf_length_le tagged

theorem ShadowRel.ro_length_le {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    (roEntriesOf valOf tagged).length ≤ l.length := by
  rw [← h.tagged_length_eq]
  exact roEntriesOf_length_le valOf tagged

theorem roEntriesOf_length_add_sessEntriesOf_length {K V E : Type} (valOf : E → V)
    (ts : List (TaggedEntry K E)) :
    (roEntriesOf valOf ts).length + (sessEntriesOf ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
    rcases t with ⟨idx, tag, e⟩
    cases tag <;> simp only [roEntriesOf_cons_sess, sessEntriesOf_cons_sess,
      roEntriesOf_cons_ro, sessEntriesOf_cons_ro, List.length_cons] <;> omega

theorem ShadowRel.length_eq_ro_add_sess {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    l.length = (roEntriesOf valOf tagged).length + sess.length := by
  rw [h.sess_eq, roEntriesOf_length_add_sessEntriesOf_length valOf tagged, h.tagged_length_eq]

theorem ShadowRel.ctr_eq_ro_add_sess {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    ctr = (roEntriesOf valOf tagged).length + sess.length :=
  h.ctr_eq.trans h.length_eq_ro_add_sess

private theorem pairwise_gt_of_map_eq_reverse_range {K E : Type} :
    ∀ (n : ℕ) (ts : List (TaggedEntry K E)),
      ts.map TaggedEntry.idx = (List.range n).reverse →
      ts.Pairwise (fun a b => b.idx < a.idx)
  | 0, ts, h => by
      cases ts with
      | nil => exact List.Pairwise.nil
      | cons _ _ => simp at h
  | n + 1, ts, h => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append] at h
      cases ts with
      | nil => simp at h
      | cons te rest =>
          simp only [List.map_cons, List.cons.injEq] at h
          rcases h with ⟨hHead, hTail⟩
          refine List.Pairwise.cons ?_ (pairwise_gt_of_map_eq_reverse_range n rest hTail)
          intro b hb
          have hbMem : b.idx ∈ rest.map TaggedEntry.idx := List.mem_map_of_mem hb
          rw [hTail, List.mem_reverse, List.mem_range] at hbMem
          omega

theorem ShadowRel.tagged_pairwise_gt {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)} {avlLookup : K → Option (V × ℕ)}
    {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    tagged.Pairwise (fun a b => b.idx < a.idx) :=
  pairwise_gt_of_map_eq_reverse_range ctr tagged h.indices_eq

section ShadowScan

/-- Two-branch shadow scan checking `sess` entries newer than an optional AVL hit `(v_ro, idx_ro)`
    before falling back to `v_ro`. -/
@[expose] def shadowScanSplit {ι : Type} {T : OracleSpec ι} {V E : Type}
    (valOf : E → V) (p : E → OracleComp T Bool)
    (avlHit : Option (V × ℕ)) (sess : List (ℕ × E)) : OracleComp T (Option V) :=
  match avlHit with
  | none => (Option.map (fun ie => valOf ie.2)) <$> findML (fun ie => p ie.2) sess
  | some (v_ro, idx_ro) =>
      (fun sHit =>
        match sHit with
        | some (_, e) => some (valOf e)
        | none => some v_ro) <$>
        findML (fun ie => if decide (idx_ro < ie.1) then p ie.2 else pure false) sess

/-- Single-loop formulation of `shadowScanSplit`. -/
@[expose] def shadowScanUnified {ι : Type} {T : OracleSpec ι} {V E : Type}
    (valOf : E → V) (p : E → OracleComp T Bool)
    (avlHit : Option (V × ℕ)) (sess : List (ℕ × E)) : OracleComp T (Option V) :=
  let condIdx : ℕ → Bool := fun idx =>
    match avlHit with
    | none => true
    | some (_, idx_ro) => decide (idx_ro < idx)
  (fun sHit =>
    match sHit with
    | some (_, e) => some (valOf e)
    | none => avlHit.map Prod.fst) <$>
    findML (fun ie => if condIdx ie.1 then p ie.2 else pure false) sess

/-- Threshold-index (`minIdx`) formulation of `shadowScanSplit`. -/
@[expose] def shadowScanMinIdx {ι : Type} {T : OracleSpec ι} {V E : Type}
    (valOf : E → V) (p : E → OracleComp T Bool)
    (avlHit : Option (V × ℕ)) (sess : List (ℕ × E)) : OracleComp T (Option V) :=
  let minIdx : ℕ :=
    match avlHit with
    | none => 0
    | some (_, idx_ro) => idx_ro + 1
  (fun sHit =>
    match sHit with
    | some (_, e) => some (valOf e)
    | none => avlHit.map Prod.fst) <$>
    findML (fun ie => if decide (minIdx ≤ ie.1) then p ie.2 else pure false) sess

theorem shadowScanUnified_eq_split {ι : Type} {T : OracleSpec ι} {V E : Type}
    (valOf : E → V) (p : E → OracleComp T Bool)
    (avlHit : Option (V × ℕ)) (sess : List (ℕ × E)) :
    shadowScanUnified valOf p avlHit sess = shadowScanSplit valOf p avlHit sess := by
  cases avlHit with
  | none =>
      simp only [shadowScanUnified, shadowScanSplit, ↓reduceIte, Option.map_none]
      congr 1
      funext sHit
      cases sHit <;> rfl
  | some h =>
      rcases h with ⟨v_ro, idx_ro⟩
      simp only [shadowScanUnified, shadowScanSplit, Option.map_some]

theorem shadowScanMinIdx_eq_split {ι : Type} {T : OracleSpec ι} {V E : Type}
    (valOf : E → V) (p : E → OracleComp T Bool)
    (avlHit : Option (V × ℕ)) (sess : List (ℕ × E)) :
    shadowScanMinIdx valOf p avlHit sess = shadowScanSplit valOf p avlHit sess := by
  rw [← shadowScanUnified_eq_split]
  cases avlHit with
  | none =>
      simp [shadowScanMinIdx, shadowScanUnified]
  | some h =>
      rcases h with ⟨v_ro, idx_ro⟩
      simp only [shadowScanMinIdx, shadowScanUnified]
      rfl

private theorem findML_pure_false {ι : Type} {T : OracleSpec ι} {α : Type}
    (q : α → OracleComp T Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, q x = pure false) →
      findML q xs = (pure none : OracleComp T (Option α))
  | [], _ => rfl
  | x :: xs, h => by
      simp only [findML, h x (List.Mem.head xs), pure_bind, Bool.false_eq_true, ↓reduceIte]
      exact findML_pure_false q xs (fun y hy => h y (List.Mem.tail x hy))

private theorem roEntriesOf_find?_idx_mem {K V E : Type} (valOf : E → V)
    (pred : K × (V × ℕ) → Bool) :
    ∀ (ts : List (TaggedEntry K E)) {v : V} {idx : ℕ},
      ((roEntriesOf valOf ts).find? pred).map Prod.snd = some (v, idx) →
      ∃ te ∈ ts, te.idx = idx
  | [], _, _, h => by simp [roEntriesOf] at h
  | ⟨i, .sess, e⟩ :: rest, v, idx, h => by
      simp only [roEntriesOf_cons_sess] at h
      obtain ⟨te, hMem, hIdx⟩ := roEntriesOf_find?_idx_mem valOf pred rest h
      exact ⟨te, List.Mem.tail _ hMem, hIdx⟩
  | ⟨i, .ro k', e⟩ :: rest, v, idx, h => by
      simp only [roEntriesOf_cons_ro, List.find?] at h
      cases hPred : pred (k', (valOf e, i))
      · simp only [hPred] at h
        obtain ⟨te, hMem, hIdx⟩ := roEntriesOf_find?_idx_mem valOf pred rest h
        exact ⟨te, List.Mem.tail _ hMem, hIdx⟩
      · simp only [hPred, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨⟨i, .ro k', e⟩, List.Mem.head rest, h.2⟩

private theorem sessEntriesOf_idx_mem {K E : Type} :
    ∀ (ts : List (TaggedEntry K E)) {ie : ℕ × E},
      ie ∈ sessEntriesOf ts → ∃ te ∈ ts, te.idx = ie.1 ∧ te.entry = ie.2
  | [], _, h => by simp [sessEntriesOf] at h
  | ⟨i, .ro _, _⟩ :: rest, ie, h => by
      simp only [sessEntriesOf_cons_ro] at h
      obtain ⟨te, hMem, hEq⟩ := sessEntriesOf_idx_mem rest h
      exact ⟨te, List.Mem.tail _ hMem, hEq⟩
  | ⟨i, .sess, e⟩ :: rest, ie, h => by
      simp only [sessEntriesOf_cons_sess, List.mem_cons] at h
      rcases h with rfl | hRest
      · exact ⟨⟨i, .sess, e⟩, List.Mem.head rest, rfl, rfl⟩
      · obtain ⟨te, hMem, hEq⟩ := sessEntriesOf_idx_mem rest hRest
        exact ⟨te, List.Mem.tail _ hMem, hEq⟩

theorem findML_tagged_eq_shadowScanSplit {ι : Type} {T : OracleSpec ι}
    {K V E : Type} [BEq K]
    (valOf : E → V) (k : K) (p : E → OracleComp T Bool) :
    ∀ (ts : List (TaggedEntry K E)),
      ts.Pairwise (fun a b => b.idx < a.idx) →
      (∀ te ∈ ts, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k)) →
      Option.map valOf <$> findML p (ts.map TaggedEntry.entry) =
        shadowScanSplit valOf p
          (((roEntriesOf valOf ts).find? (fun q => q.1 == k)).map Prod.snd)
          (sessEntriesOf ts)
  | [], _, _ => by
      simp [shadowScanSplit, roEntriesOf, sessEntriesOf, findML]
  | ⟨idx, .sess, e⟩ :: rest, hPair, hp_ro => by
      obtain ⟨hGt, hPairRest⟩ := List.pairwise_cons.mp hPair
      have hpRest : ∀ te ∈ rest, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k) :=
        fun te hMem => hp_ro te (List.Mem.tail _ hMem)
      have ih := findML_tagged_eq_shadowScanSplit valOf k p rest hPairRest hpRest
      simp only [List.map_cons, findML, roEntriesOf_cons_sess, sessEntriesOf_cons_sess, map_bind]
      cases hAvl : ((roEntriesOf valOf rest).find? (fun q => q.1 == k)).map Prod.snd with
      | none =>
          rw [hAvl] at ih
          simp only [shadowScanSplit, findML, map_bind] at ih ⊢
          congr 1
          funext b
          cases b
          · simpa using ih
          · simp
      | some hit =>
          rcases hit with ⟨v_ro, idx_ro⟩
          obtain ⟨teHit, hMemHit, hIdxHit⟩ :=
            roEntriesOf_find?_idx_mem valOf (fun q => q.1 == k) rest hAvl
          have hLt : idx_ro < idx := hIdxHit ▸ hGt teHit hMemHit
          rw [hAvl] at ih
          simp only [shadowScanSplit, findML, decide_eq_true hLt, ↓reduceIte, map_bind] at ih ⊢
          congr 1
          funext b
          cases b
          · simpa using ih
          · simp
  | ⟨idx, .ro k', e⟩ :: rest, hPair, hp_ro => by
      obtain ⟨hGt, hPairRest⟩ := List.pairwise_cons.mp hPair
      have hpHead : p e = pure (k' == k) := hp_ro ⟨idx, .ro k', e⟩ (List.Mem.head rest) k' rfl
      have hpRest : ∀ te ∈ rest, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k) :=
        fun te hMem => hp_ro te (List.Mem.tail _ hMem)
      simp only [List.map_cons, findML, hpHead, pure_bind, roEntriesOf_cons_ro,
        sessEntriesOf_cons_ro, List.find?]
      cases hk : (k' == k)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact findML_tagged_eq_shadowScanSplit valOf k p rest hPairRest hpRest
      · simp only [↓reduceIte, map_pure, Option.map_some, shadowScanSplit]
        have hNoNewer :
            findML (fun ie => if decide (idx < ie.1) then p ie.2 else pure false)
              (sessEntriesOf rest) = pure none := by
          refine findML_pure_false _ (sessEntriesOf rest) ?_
          intro ie hie
          obtain ⟨te, hMem, hIdx, _⟩ := sessEntriesOf_idx_mem rest hie
          have hLt : te.idx < idx := hGt te hMem
          have hNotLt : ¬ (idx < ie.1) := by omega
          simp [hNotLt]
        rw [hNoNewer]
        simp

/-- Under `ShadowRel` and `sess.length ≤ K_sess`, scanning `l.take cap` with `p` and projecting
    `valOf` equals `shadowScanSplit valOf p (avlLookup k) (sess.take K_sess)`. -/
theorem findML_take_eq_shadowScanSplit {ι : Type} {T : OracleSpec ι} {K V E : Type} [BEq K]
    {cap K_sess : ℕ} {valOf : E → V} {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (hRel : ShadowRel cap valOf l tagged avlLookup sess ctr)
    (hSessCap : sess.length ≤ K_sess) (k : K) (p : E → OracleComp T Bool)
    (hp_ro : ∀ te ∈ tagged, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k)) :
    Option.map valOf <$> findML p (l.take cap) =
      shadowScanSplit valOf p (avlLookup k) (sess.take K_sess) := by
  rw [List.take_of_length_le hRel.len_le, List.take_of_length_le hSessCap,
    ← hRel.forget_eq, hRel.avl_eq k, hRel.sess_eq]
  exact findML_tagged_eq_shadowScanSplit valOf k p tagged hRel.tagged_pairwise_gt hp_ro

theorem findML_take_eq_shadowScanUnified {ι : Type} {T : OracleSpec ι} {K V E : Type} [BEq K]
    {cap K_sess : ℕ} {valOf : E → V} {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (hRel : ShadowRel cap valOf l tagged avlLookup sess ctr)
    (hSessCap : sess.length ≤ K_sess) (k : K) (p : E → OracleComp T Bool)
    (hp_ro : ∀ te ∈ tagged, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k)) :
    Option.map valOf <$> findML p (l.take cap) =
      shadowScanUnified valOf p (avlLookup k) (sess.take K_sess) := by
  rw [shadowScanUnified_eq_split]
  exact findML_take_eq_shadowScanSplit hRel hSessCap k p hp_ro

theorem findML_take_eq_shadowScanMinIdx {ι : Type} {T : OracleSpec ι} {K V E : Type} [BEq K]
    {cap K_sess : ℕ} {valOf : E → V} {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (hRel : ShadowRel cap valOf l tagged avlLookup sess ctr)
    (hSessCap : sess.length ≤ K_sess) (k : K) (p : E → OracleComp T Bool)
    (hp_ro : ∀ te ∈ tagged, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k)) :
    Option.map valOf <$> findML p (l.take cap) =
      shadowScanMinIdx valOf p (avlLookup k) (sess.take K_sess) := by
  rw [shadowScanMinIdx_eq_split]
  exact findML_take_eq_shadowScanSplit hRel hSessCap k p hp_ro

/-- Scanning `sess` with clamped fuel `min cap L_sess` agrees with `Comp.findM cap lE pC` under
    `ShadowRel`. -/
theorem comp_findM_eq_shadowScanSplit {S : Sig} {O : Ops S}
    {ι : Type} {T : OracleSpec ι} {I : Iface S T} {Γ : List (Ty S)}
    {K V : Type} [BEq K] {eTy : Ty S} {cap L_sess : ℕ} {valOf : eTy.denote → V}
    {l : List eTy.denote} {tagged : List (TaggedEntry K eTy.denote)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × eTy.denote)} {ctr : ℕ}
    (hRel : ShadowRel cap valOf l tagged avlLookup sess ctr) (hSessL : sess.length ≤ L_sess)
    (lE : Expr O Γ (.list eTy)) (pC : Comp O I (eTy :: Γ) .bool) (ρ : Env Γ)
    (hlE : lE.eval ρ = l) (k : K)
    (hp_ro : ∀ te ∈ tagged, ∀ k', te.tag = .ro k' →
      pC.eval (.cons te.entry ρ) = pure (k' == k)) :
    Option.map valOf <$> (Comp.findM cap lE pC).eval ρ =
      shadowScanSplit valOf (fun e => pC.eval (.cons e ρ))
        (avlLookup k) (sess.take (min cap L_sess)) := by
  have hSessMin : sess.length ≤ min cap L_sess :=
    Nat.le_min.mpr ⟨Nat.le_trans hRel.sess_length_le hRel.len_le, hSessL⟩
  simp only [Comp.eval, hlE]
  exact findML_take_eq_shadowScanSplit hRel hSessMin k (fun e => pC.eval (.cons e ρ)) hp_ro

/-- If `none` is in the support of `Option.map valOf <$> findML p (l.take cap)` under `ShadowRel`,
    then `avlLookup k = none`. -/
theorem avlLookup_eq_none_of_miss_support {ι : Type} {T : OracleSpec ι} {K V E : Type} [BEq K]
    {cap : ℕ} {valOf : E → V} {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (hRel : ShadowRel cap valOf l tagged avlLookup sess ctr) (k : K) (p : E → OracleComp T Bool)
    (hp_ro : ∀ te ∈ tagged, ∀ k', te.tag = .ro k' → p te.entry = pure (k' == k))
    (hMiss : none ∈ support (Option.map valOf <$> findML p (l.take cap))) :
    avlLookup k = none := by
  rw [findML_take_eq_shadowScanSplit hRel (Nat.le_refl sess.length) k p hp_ro,
    List.take_of_length_le (Nat.le_refl _)] at hMiss
  cases hAvl : avlLookup k with
  | none => rfl
  | some hit =>
      rcases hit with ⟨v_ro, idx_ro⟩
      rw [hAvl, shadowScanSplit, support_map, Set.mem_image] at hMiss
      rcases hMiss with ⟨sHit, _, hEq⟩
      cases sHit <;> simp at hEq

theorem RoCacheRel.find?_take_map_snd {K V : Type} [BEq K] {cap : ℕ}
    {l : List (K × V)} {avlLookup : K → Option V}
    (hRel : RoCacheRel cap l avlLookup) (k : K) :
    ((l.take cap).find? (fun p => p.1 == k)).map Prod.snd = avlLookup k := by
  rw [List.take_of_length_le hRel.len_le, ← hRel.avl_eq k]

end ShadowScan

section Preservation

theorem ShadowRel.empty {K V E : Type} [BEq K] (cap : ℕ) (valOf : E → V) :
    ShadowRel (K := K) cap valOf [] [] (fun _ => none) [] 0 where
  forget_eq := rfl; ctr_eq := rfl; len_le := Nat.zero_le cap
  indices_eq := rfl; sess_eq := rfl; avl_eq := fun _ => rfl; ro_keys_nodup := by simp

theorem ShadowRel.mono_cap {K V E : Type} [BEq K] {cap cap' : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) (hLe : cap ≤ cap') :
    ShadowRel cap' valOf l tagged avlLookup sess ctr :=
  { h with len_le := Nat.le_trans h.len_le hLe }

theorem ShadowRel.hit {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) :
    ShadowRel cap valOf l tagged avlLookup sess ctr := h

/-- Consing an online session entry preserves `ShadowRel` with `avlLookup` unchanged when
    `ctr + 1 ≤ cap`. -/
theorem ShadowRel.cons_sess {K V E : Type} [BEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) (e : E) (hCap : ctr + 1 ≤ cap) :
    ShadowRel cap valOf (e :: l) (⟨ctr, .sess, e⟩ :: tagged)
      avlLookup ((ctr, e) :: sess) (ctr + 1) where
  forget_eq := by simp [h.forget_eq]
  ctr_eq := by simp [h.ctr_eq]
  len_le := by simp only [List.length_cons]; have := h.ctr_eq; omega
  indices_eq := by
    simp only [List.map_cons, h.indices_eq, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
  sess_eq := by simp [h.sess_eq]
  avl_eq := fun k => by simpa using h.avl_eq k
  ro_keys_nodup := by simpa using h.ro_keys_nodup

private theorem not_mem_fst_of_find?_map_snd_none {K α : Type} [BEq K] [LawfulBEq K]
    {xs : List (K × α)} {k : K}
    (hNone : (xs.find? (fun p => p.1 == k)).map Prod.snd = none) :
    k ∉ xs.map Prod.fst := by
  intro hMem
  rw [List.mem_map] at hMem
  rcases hMem with ⟨⟨k', a⟩, hIn, hFst⟩
  dsimp only at hFst; subst hFst
  have hFindNone : xs.find? (fun p => p.1 == k') = none := Option.map_eq_none_iff.mp hNone
  have hFalse := List.find?_eq_none.mp hFindNone (k', a) hIn
  simp at hFalse

/-- Inserting a missing random-oracle key `k` preserves `ShadowRel` with `sess` unchanged when
    `ctr + 1 ≤ cap`. -/
theorem ShadowRel.cons_ro_of_miss {K V E : Type} [BEq K] [LawfulBEq K] {cap : ℕ} {valOf : E → V}
    {l : List E} {tagged : List (TaggedEntry K E)}
    {avlLookup avlLookup' : K → Option (V × ℕ)} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRel cap valOf l tagged avlLookup sess ctr) (k : K) (e : E)
    (hMiss : avlLookup k = none) (hCap : ctr + 1 ≤ cap)
    (hAvl' : ∀ q : K, avlLookup' q = if k == q then some (valOf e, ctr) else avlLookup q) :
    ShadowRel cap valOf (e :: l) (⟨ctr, .ro k, e⟩ :: tagged) avlLookup' sess (ctr + 1) where
  forget_eq := by simp [h.forget_eq]
  ctr_eq := by simp [h.ctr_eq]
  len_le := by simp only [List.length_cons]; have := h.ctr_eq; omega
  indices_eq := by
    simp only [List.map_cons, h.indices_eq, List.range_succ, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
  sess_eq := by simp [h.sess_eq]
  avl_eq := fun q => by
    rw [hAvl' q, roEntriesOf_cons_ro, List.find?]
    cases (k == q) <;> simp [h.avl_eq q]
  ro_keys_nodup := by
    simp only [roEntriesOf_cons_ro, List.map_cons]
    refine List.Nodup.cons ?_ h.ro_keys_nodup
    have hFindNone : ((roEntriesOf valOf tagged).find? (fun p => p.1 == k)).map Prod.snd = none := by
      rw [← h.avl_eq k, hMiss]
    exact not_mem_fst_of_find?_map_snd_none hFindNone

theorem RoCacheRel.empty {K V : Type} [BEq K] (cap : ℕ) :
    RoCacheRel (K := K) (V := V) cap [] (fun _ => none) where
  len_le := Nat.zero_le cap; avl_eq := fun _ => rfl; keys_nodup := by simp

theorem RoCacheRel.mono_cap {K V : Type} [BEq K] {cap cap' : ℕ}
    {l : List (K × V)} {avlLookup : K → Option V}
    (h : RoCacheRel cap l avlLookup) (hLe : cap ≤ cap') :
    RoCacheRel cap' l avlLookup :=
  { h with len_le := Nat.le_trans h.len_le hLe }

theorem RoCacheRel.cons_of_miss {K V : Type} [BEq K] [LawfulBEq K]
    {cap : ℕ} {l : List (K × V)} {avlLookup avlLookup' : K → Option V}
    (h : RoCacheRel cap l avlLookup) (k : K) (v : V)
    (hMiss : avlLookup k = none) (hCap : l.length + 1 ≤ cap)
    (hAvl' : ∀ q : K, avlLookup' q = if k == q then some v else avlLookup q) :
    RoCacheRel cap ((k, v) :: l) avlLookup' where
  len_le := by simpa using hCap
  avl_eq := fun q => by
    rw [hAvl' q, List.find?]
    cases (k == q) <;> simp [h.avl_eq q]
  keys_nodup := by
    simp only [List.map_cons]
    refine List.Nodup.cons ?_ h.keys_nodup
    have hFindNone : (l.find? (fun p => p.1 == k)).map Prod.snd = none := by
      rw [← h.avl_eq k, hMiss]
    exact not_mem_fst_of_find?_map_snd_none hFindNone

end Preservation

section LengthAwareKeys

theorem bytes_beq_false_of_length_ne {a b : Bytes} (h : a.length ≠ b.length) :
    (a == b) = false := by
  cases hab : (a == b)
  · rfl
  · exfalso
    exact h (congrArg List.length (eq_of_beq hab))

theorem pair32_beq_false_of_length_ne {rk1 dh1 rk2 dh2 : Bytes}
    (h : rk1.length ≠ rk2.length ∨ dh1.length ≠ dh2.length) :
    ((rk1 == rk2) && (dh1 == dh2)) = false := by
  rcases h with h1 | h2
  · rw [bytes_beq_false_of_length_ne h1, Bool.false_and]
  · rw [bytes_beq_false_of_length_ne h2, Bool.and_false]

@[simp] theorem ofU8_length_eq (bs : Bytes) :
    (CryptoVerification.E2E.ofU8 bs).length = bs.length := by
  simp [CryptoVerification.E2E.ofU8]

theorem ofU8_beq_false_of_length_ne {a b : Bytes} (h : a.length ≠ b.length) :
    (CryptoVerification.E2E.ofU8 a == CryptoVerification.E2E.ofU8 b) = false := by
  cases hab : (CryptoVerification.E2E.ofU8 a == CryptoVerification.E2E.ofU8 b)
  · rfl
  · exfalso
    have hLen := congrArg List.length (eq_of_beq hab)
    simp only [ofU8_length_eq] at hLen
    exact h hLen

/-- Secrets of lengths `160`, `192`, and `∉ {160, 192}` are pairwise distinct under `Bytes` and
    `E2E.ofU8` equality. -/
theorem c5_b192_key_no_collision_160_192_raw
    {k160 k192 kraw : Bytes}
    (h160 : k160.length = 160) (h192 : k192.length = 192)
    (hraw160 : kraw.length ≠ 160) (hraw192 : kraw.length ≠ 192) :
    (k160 == k192) = false ∧
    (k160 == kraw) = false ∧
    (k192 == kraw) = false ∧
    (CryptoVerification.E2E.ofU8 k160 == CryptoVerification.E2E.ofU8 k192) = false ∧
    (CryptoVerification.E2E.ofU8 k160 == CryptoVerification.E2E.ofU8 kraw) = false ∧
    (CryptoVerification.E2E.ofU8 k192 == CryptoVerification.E2E.ofU8 kraw) = false := by
  have hne_160_192 : k160.length ≠ k192.length := by omega
  have hne_160_raw : k160.length ≠ kraw.length := by omega
  have hne_192_raw : k192.length ≠ kraw.length := by omega
  exact ⟨bytes_beq_false_of_length_ne hne_160_192,
    bytes_beq_false_of_length_ne hne_160_raw,
    bytes_beq_false_of_length_ne hne_192_raw,
    ofU8_beq_false_of_length_ne hne_160_192,
    ofU8_beq_false_of_length_ne hne_160_raw,
    ofU8_beq_false_of_length_ne hne_192_raw⟩

theorem c5_pair32_key_no_collision_of_length_ne {rk1 dh1 rk2 dh2 : Bytes}
    (h : rk1.length ≠ rk2.length ∨ dh1.length ≠ dh2.length) :
    ((CryptoVerification.E2E.ofU8 rk1 == CryptoVerification.E2E.ofU8 rk2) &&
     (CryptoVerification.E2E.ofU8 dh1 == CryptoVerification.E2E.ofU8 dh2)) = false := by
  rcases h with h1 | h2
  · rw [ofU8_beq_false_of_length_ne h1, Bool.false_and]
  · rw [ofU8_beq_false_of_length_ne h2, Bool.and_false]

end LengthAwareKeys

section AvlSpecBridge

private theorem isNone_of_map_snd_eq_none {α β : Type} {o : Option (α × β)}
    (h : o.map Prod.snd = none) : o.isNone = true := by
  cases o <;> simp at h ⊢

theorem pair32_find?_beq_eq {W : Type}
    (entries : List ((Bytes × Bytes) × W)) (rk dh : Bytes) :
    entries.find? (fun p => p.1.1 == rk && p.1.2 == dh) =
      entries.find? (fun p => p.1 == (rk, dh)) := by
  congr 1

/-- Concrete `B 192` mixed-table shadow invariant pairing `ShadowRel` with `AvlB192Valid`. -/
@[expose] def ShadowRelB192 (V : Ty pqAtomicSig) {E : Type}
    (listCap avlCap : ℕ) (valOf : E → V.denote)
    (l : List E) (tagged : List (TaggedEntry Bytes E))
    (tbl : (avlTy (B 192) (.prod V .nat)).denote) (sess : List (ℕ × E)) (ctr : ℕ) : Prop :=
  ShadowRel listCap valOf l tagged
    (fun sec => ((roEntriesOf valOf tagged).find? (fun p => p.1 == sec)).map Prod.snd)
    sess ctr ∧
  AvlB192Valid (V := .prod V .nat) avlCap tbl (roEntriesOf valOf tagged)

abbrev ShadowRelAvlB192 := @ShadowRelB192

theorem ShadowRelB192.empty {Γ : List (Ty pqAtomicSig)} (V : Ty pqAtomicSig) {E : Type}
    (listCap avlCap : ℕ) (valOf : E → V.denote)
    (dfltValIdx : Expr pqAtomicOps Γ (.prod V .nat)) (ρ : Env Γ) :
    ShadowRelB192 V listCap avlCap valOf ([] : List E) []
      ((avlEmptyE dfltB192E dfltValIdx).eval ρ) [] 0 :=
  ⟨ShadowRel.empty listCap valOf, avlEmptyE_b192_valid avlCap dfltValIdx ρ⟩

theorem ShadowRelB192.mono_cap {V : Ty pqAtomicSig} {E : Type}
    {listCap listCap' avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)}
    {tbl : (avlTy (B 192) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelB192 V listCap avlCap valOf l tagged tbl sess ctr) (hLe : listCap ≤ listCap') :
    ShadowRelB192 V listCap' avlCap valOf l tagged tbl sess ctr :=
  ⟨h.1.mono_cap hLe, h.2⟩

theorem ShadowRelB192.ro_length_le {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)}
    {tbl : (avlTy (B 192) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelB192 V listCap avlCap valOf l tagged tbl sess ctr) :
    (roEntriesOf valOf tagged).length ≤ ctr :=
  h.1.ctr_eq ▸ h.1.ro_length_le

theorem ShadowRelB192.length_eq_ro_add_sess {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)}
    {tbl : (avlTy (B 192) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelB192 V listCap avlCap valOf l tagged tbl sess ctr) :
    l.length = (roEntriesOf valOf tagged).length + sess.length :=
  h.1.length_eq_ro_add_sess

theorem ShadowRelB192.cons_sess {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)}
    {tbl : (avlTy (B 192) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelB192 V listCap avlCap valOf l tagged tbl sess ctr)
    (e : E) (hCap : ctr + 1 ≤ listCap) :
    ShadowRelB192 V listCap avlCap valOf
      (e :: l) (⟨ctr, .sess, e⟩ :: tagged) tbl ((ctr, e) :: sess) (ctr + 1) :=
  ⟨h.1.cons_sess e hCap, h.2⟩

theorem ShadowRelB192.cons_ro_of_miss {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)}
    {tbl tbl' : (avlTy (B 192) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelB192 V listCap avlCap valOf l tagged tbl sess ctr)
    (sec : Bytes) (e : E)
    (hMiss : ((roEntriesOf valOf tagged).find? (fun p => p.1 == sec)).map Prod.snd = none)
    (hCap : ctr + 1 ≤ listCap)
    (hValid' : AvlB192Valid (V := .prod V .nat) avlCap tbl'
      ((sec, (valOf e, ctr)) :: roEntriesOf valOf tagged)) :
    ShadowRelB192 V listCap avlCap valOf
      (e :: l) (⟨ctr, .ro sec, e⟩ :: tagged) tbl' sess (ctr + 1) := by
  refine ⟨h.1.cons_ro_of_miss sec e hMiss hCap (fun q => ?_), hValid'⟩
  simp only [roEntriesOf_cons_ro, List.find?]
  cases (sec == q) <;> rfl

/-- Search and miss-insert correctness for `B 192` mixed session and random-oracle tables. -/
theorem ShadowRelB192.search_and_insert_spec
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry Bytes E)} {sess : List (ℕ × E)} {ctr : ℕ}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) (.prod V .nat)))
    (keyE : Expr pqAtomicOps Γ (B 192)) (ρ : Env Γ) (sec : Bytes)
    (hKey : keyE.eval ρ = CryptoVerification.E2E.ofU8 sec)
    (hRel : ShadowRelB192 V listCap avlCap valOf l tagged (tblE.eval ρ) sess ctr) :
    ∃ path : List (ℕ × Bool),
      (avlSearchB192C (I := I) avlCap tblE keyE).eval ρ =
        pure (((roEntriesOf valOf tagged).find? (fun p => p.1 == sec)).map Prod.snd, path) ∧
      (((roEntriesOf valOf tagged).find? (fun p => p.1 == sec)).map Prod.snd = none →
        ctr + 1 ≤ listCap →
        (roEntriesOf valOf tagged).length + 1 ≤ avlCap →
        ∀ (e : E),
          ∃ tbl' : (avlTy (B 192) (.prod V .nat)).denote,
            (avlInsertAtPathC (I := I) avlCap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path (.cons (CryptoVerification.E2E.ofU8 sec)
                (.cons (valOf e, ctr) .nil)))) = pure tbl' ∧
            ShadowRelB192 V listCap avlCap valOf
              (e :: l) (⟨ctr, .ro sec, e⟩ :: tagged) tbl' sess (ctr + 1)) := by
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertB192_spec (I := I) (V := .prod V .nat)
      avlCap tblE keyE ρ sec (roEntriesOf valOf tagged) hKey hRel.2
  refine ⟨path, hSearch, fun hMiss hListCap hAvlCap e => ?_⟩
  obtain ⟨tbl', hInsEval, hValid'⟩ :=
    hIns (isNone_of_map_snd_eq_none hMiss) hAvlCap (valOf e, ctr)
  exact ⟨tbl', hInsEval, hRel.cons_ro_of_miss sec e hMiss hListCap hValid'⟩

/-- Concrete `B 32 × B 32` mixed-table shadow invariant pairing `ShadowRel` with `AvlPair32Valid`. -/
@[expose] def ShadowRelPair32 (V : Ty pqAtomicSig) {E : Type}
    (listCap avlCap : ℕ) (valOf : E → V.denote)
    (l : List E) (tagged : List (TaggedEntry (Bytes × Bytes) E))
    (tbl : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote) (sess : List (ℕ × E)) (ctr : ℕ) : Prop :=
  ShadowRel listCap valOf l tagged
    (fun k => ((roEntriesOf valOf tagged).find? (fun p => p.1 == k)).map Prod.snd)
    sess ctr ∧
  AvlPair32Valid (V := .prod V .nat) avlCap tbl (roEntriesOf valOf tagged)

abbrev ShadowRelAvlPair32 := @ShadowRelPair32

theorem ShadowRelPair32.empty {Γ : List (Ty pqAtomicSig)} (V : Ty pqAtomicSig) {E : Type}
    (listCap avlCap : ℕ) (valOf : E → V.denote)
    (dfltValIdx : Expr pqAtomicOps Γ (.prod V .nat)) (ρ : Env Γ) :
    ShadowRelPair32 V listCap avlCap valOf ([] : List E) []
      ((avlEmptyE dfltPair32E dfltValIdx).eval ρ) [] 0 :=
  ⟨ShadowRel.empty listCap valOf, avlEmptyE_pair32_valid avlCap dfltValIdx ρ⟩

theorem ShadowRelPair32.mono_cap {V : Ty pqAtomicSig} {E : Type}
    {listCap listCap' avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)}
    {tbl : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelPair32 V listCap avlCap valOf l tagged tbl sess ctr) (hLe : listCap ≤ listCap') :
    ShadowRelPair32 V listCap' avlCap valOf l tagged tbl sess ctr :=
  ⟨h.1.mono_cap hLe, h.2⟩

theorem ShadowRelPair32.ro_length_le {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)}
    {tbl : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelPair32 V listCap avlCap valOf l tagged tbl sess ctr) :
    (roEntriesOf valOf tagged).length ≤ ctr :=
  h.1.ctr_eq ▸ h.1.ro_length_le

theorem ShadowRelPair32.length_eq_ro_add_sess {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)}
    {tbl : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelPair32 V listCap avlCap valOf l tagged tbl sess ctr) :
    l.length = (roEntriesOf valOf tagged).length + sess.length :=
  h.1.length_eq_ro_add_sess

theorem ShadowRelPair32.cons_sess {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)}
    {tbl : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelPair32 V listCap avlCap valOf l tagged tbl sess ctr)
    (e : E) (hCap : ctr + 1 ≤ listCap) :
    ShadowRelPair32 V listCap avlCap valOf
      (e :: l) (⟨ctr, .sess, e⟩ :: tagged) tbl ((ctr, e) :: sess) (ctr + 1) :=
  ⟨h.1.cons_sess e hCap, h.2⟩

theorem ShadowRelPair32.cons_ro_of_miss {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)}
    {tbl tbl' : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote} {sess : List (ℕ × E)} {ctr : ℕ}
    (h : ShadowRelPair32 V listCap avlCap valOf l tagged tbl sess ctr)
    (rk dh : Bytes) (e : E)
    (hMiss : ((roEntriesOf valOf tagged).find? (fun p => p.1 == (rk, dh))).map Prod.snd = none)
    (hCap : ctr + 1 ≤ listCap)
    (hValid' : AvlPair32Valid (V := .prod V .nat) avlCap tbl'
      (((rk, dh), (valOf e, ctr)) :: roEntriesOf valOf tagged)) :
    ShadowRelPair32 V listCap avlCap valOf
      (e :: l) (⟨ctr, .ro (rk, dh), e⟩ :: tagged) tbl' sess (ctr + 1) := by
  refine ⟨h.1.cons_ro_of_miss (rk, dh) e hMiss hCap (fun q => ?_), hValid'⟩
  simp only [roEntriesOf_cons_ro, List.find?]
  cases ((rk, dh) == q) <;> rfl

/-- Search and miss-insert correctness for `B 32 × B 32` mixed session and random-oracle tables. -/
theorem ShadowRelPair32.search_and_insert_spec
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig} {E : Type}
    {listCap avlCap : ℕ} {valOf : E → V.denote}
    {l : List E} {tagged : List (TaggedEntry (Bytes × Bytes) E)} {sess : List (ℕ × E)} {ctr : ℕ}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) (.prod V .nat)))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) (ρ : Env Γ) (rk dh : Bytes)
    (hKey : keyE.eval ρ = (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh))
    (hRel : ShadowRelPair32 V listCap avlCap valOf l tagged (tblE.eval ρ) sess ctr) :
    ∃ path : List (ℕ × Bool),
      (avlSearchPair32C (I := I) avlCap tblE keyE).eval ρ =
        pure (((roEntriesOf valOf tagged).find? (fun p => p.1 == (rk, dh))).map Prod.snd, path) ∧
      (((roEntriesOf valOf tagged).find? (fun p => p.1 == (rk, dh))).map Prod.snd = none →
        ctr + 1 ≤ listCap →
        (roEntriesOf valOf tagged).length + 1 ≤ avlCap →
        ∀ (e : E),
          ∃ tbl' : (avlTy (.prod (B 32) (B 32)) (.prod V .nat)).denote,
            (avlInsertAtPathC (I := I) avlCap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path
                (.cons (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)
                  (.cons (valOf e, ctr) .nil)))) = pure tbl' ∧
            ShadowRelPair32 V listCap avlCap valOf
              (e :: l) (⟨ctr, .ro (rk, dh), e⟩ :: tagged) tbl' sess (ctr + 1)) := by
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertPair32_spec (I := I) (V := .prod V .nat)
      avlCap tblE keyE ρ rk dh (roEntriesOf valOf tagged) hKey hRel.2
  rw [pair32_find?_beq_eq] at hSearch hIns
  refine ⟨path, hSearch, fun hMiss hListCap hAvlCap e => ?_⟩
  obtain ⟨tbl', hInsEval, hValid'⟩ :=
    hIns (isNone_of_map_snd_eq_none hMiss) hAvlCap (valOf e, ctr)
  exact ⟨tbl', hInsEval, hRel.cons_ro_of_miss rk dh e hMiss hListCap hValid'⟩

/-- Concrete `B 192` random-oracle cache invariant pairing `RoCacheRel` with `AvlB192Valid`. -/
@[expose] def RoCacheRelB192 (V : Ty pqAtomicSig) (listCap avlCap : ℕ)
    (l : List (Bytes × V.denote)) (tbl : (avlTy (B 192) V).denote) : Prop :=
  RoCacheRel listCap l (fun sec => (l.find? (fun p => p.1 == sec)).map Prod.snd) ∧
  AvlB192Valid avlCap tbl l

theorem RoCacheRelB192.empty {Γ : List (Ty pqAtomicSig)} (V : Ty pqAtomicSig)
    (listCap avlCap : ℕ) (dfltV : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    RoCacheRelB192 V listCap avlCap [] ((avlEmptyE dfltB192E dfltV).eval ρ) :=
  ⟨RoCacheRel.empty listCap, avlEmptyE_b192_valid avlCap dfltV ρ⟩

theorem RoCacheRelB192.mono_cap {V : Ty pqAtomicSig} {listCap listCap' avlCap : ℕ}
    {l : List (Bytes × V.denote)} {tbl : (avlTy (B 192) V).denote}
    (h : RoCacheRelB192 V listCap avlCap l tbl) (hLe : listCap ≤ listCap') :
    RoCacheRelB192 V listCap' avlCap l tbl :=
  ⟨h.1.mono_cap hLe, h.2⟩

theorem RoCacheRelB192.search_and_insert_spec
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    {listCap avlCap : ℕ} {l : List (Bytes × V.denote)}
    (tblE : Expr pqAtomicOps Γ (avlTy (B 192) V))
    (keyE : Expr pqAtomicOps Γ (B 192)) (ρ : Env Γ) (sec : Bytes)
    (hKey : keyE.eval ρ = CryptoVerification.E2E.ofU8 sec)
    (hRel : RoCacheRelB192 V listCap avlCap l (tblE.eval ρ)) :
    ∃ path : List (ℕ × Bool),
      (avlSearchB192C (I := I) avlCap tblE keyE).eval ρ =
        pure ((l.find? (fun p => p.1 == sec)).map Prod.snd, path) ∧
      ((l.find? (fun p => p.1 == sec)).map Prod.snd = none →
        l.length + 1 ≤ listCap →
        l.length + 1 ≤ avlCap →
        ∀ (val : V.denote),
          ∃ tbl' : (avlTy (B 192) V).denote,
            (avlInsertAtPathC (I := I) avlCap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path (.cons (CryptoVerification.E2E.ofU8 sec)
                (.cons val .nil)))) = pure tbl' ∧
            RoCacheRelB192 V listCap avlCap ((sec, val) :: l) tbl') := by
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertB192_spec (I := I) avlCap tblE keyE ρ sec l hKey hRel.2
  refine ⟨path, hSearch, fun hMiss hListCap hAvlCap val => ?_⟩
  obtain ⟨tbl', hInsEval, hValid'⟩ :=
    hIns (isNone_of_map_snd_eq_none hMiss) hAvlCap val
  refine ⟨tbl', hInsEval, hRel.1.cons_of_miss sec val hMiss hListCap (fun q => ?_), hValid'⟩
  simp only [List.find?]
  cases (sec == q) <;> rfl

/-- Concrete `B 32 × B 32` random-oracle cache invariant pairing `RoCacheRel` with `AvlPair32Valid`. -/
@[expose] def RoCacheRelPair32 (V : Ty pqAtomicSig) (listCap avlCap : ℕ)
    (l : List ((Bytes × Bytes) × V.denote))
    (tbl : (avlTy (.prod (B 32) (B 32)) V).denote) : Prop :=
  RoCacheRel listCap l (fun k => (l.find? (fun p => p.1 == k)).map Prod.snd) ∧
  AvlPair32Valid avlCap tbl l

theorem RoCacheRelPair32.empty {Γ : List (Ty pqAtomicSig)} (V : Ty pqAtomicSig)
    (listCap avlCap : ℕ) (dfltV : Expr pqAtomicOps Γ V) (ρ : Env Γ) :
    RoCacheRelPair32 V listCap avlCap [] ((avlEmptyE dfltPair32E dfltV).eval ρ) :=
  ⟨RoCacheRel.empty listCap, avlEmptyE_pair32_valid avlCap dfltV ρ⟩

theorem RoCacheRelPair32.mono_cap {V : Ty pqAtomicSig} {listCap listCap' avlCap : ℕ}
    {l : List ((Bytes × Bytes) × V.denote)} {tbl : (avlTy (.prod (B 32) (B 32)) V).denote}
    (h : RoCacheRelPair32 V listCap avlCap l tbl) (hLe : listCap ≤ listCap') :
    RoCacheRelPair32 V listCap' avlCap l tbl :=
  ⟨h.1.mono_cap hLe, h.2⟩

theorem RoCacheRelPair32.search_and_insert_spec
    {ι : Type} {T : OracleSpec ι} {I : Iface pqAtomicSig T}
    {Γ : List (Ty pqAtomicSig)} {V : Ty pqAtomicSig}
    {listCap avlCap : ℕ} {l : List ((Bytes × Bytes) × V.denote)}
    (tblE : Expr pqAtomicOps Γ (avlTy (.prod (B 32) (B 32)) V))
    (keyE : Expr pqAtomicOps Γ (.prod (B 32) (B 32))) (ρ : Env Γ) (rk dh : Bytes)
    (hKey : keyE.eval ρ = (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh))
    (hRel : RoCacheRelPair32 V listCap avlCap l (tblE.eval ρ)) :
    ∃ path : List (ℕ × Bool),
      (avlSearchPair32C (I := I) avlCap tblE keyE).eval ρ =
        pure ((l.find? (fun p => p.1 == (rk, dh))).map Prod.snd, path) ∧
      ((l.find? (fun p => p.1 == (rk, dh))).map Prod.snd = none →
        l.length + 1 ≤ listCap →
        l.length + 1 ≤ avlCap →
        ∀ (val : V.denote),
          ∃ tbl' : (avlTy (.prod (B 32) (B 32)) V).denote,
            (avlInsertAtPathC (I := I) avlCap
              (.var .zero) (.var (.succ .zero)) (.var (.succ (.succ .zero)))
              (.var (.succ (.succ (.succ .zero))))).eval
              (.cons (tblE.eval ρ) (.cons path
                (.cons (CryptoVerification.E2E.ofU8 rk, CryptoVerification.E2E.ofU8 dh)
                  (.cons val .nil)))) = pure tbl' ∧
            RoCacheRelPair32 V listCap avlCap (((rk, dh), val) :: l) tbl') := by
  obtain ⟨path, hSearch, hIns⟩ :=
    avlSearchInsertPair32_spec (I := I) avlCap tblE keyE ρ rk dh l hKey hRel.2
  rw [pair32_find?_beq_eq] at hSearch hIns
  refine ⟨path, hSearch, fun hMiss hListCap hAvlCap val => ?_⟩
  obtain ⟨tbl', hInsEval, hValid'⟩ :=
    hIns (isNone_of_map_snd_eq_none hMiss) hAvlCap val
  refine ⟨tbl', hInsEval, hRel.1.cons_of_miss (rk, dh) val hMiss hListCap (fun q => ?_), hValid'⟩
  simp only [List.find?]
  cases ((rk, dh) == q) <;> rfl

end AvlSpecBridge

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.SplitRo.AvlRoCacheRefine
