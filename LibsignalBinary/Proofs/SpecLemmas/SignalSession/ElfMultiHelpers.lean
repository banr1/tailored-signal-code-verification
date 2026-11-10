/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Multi
public import ProofLib.Process.FastParse

/-!
# Tree-Accelerated Multi-Block Placement and Relocation-Inversion Helpers

Supplements `ProofLib.Placed.Multi` with:
- multi-block hook-equality and cross-block stepping/call lemmas (`externAt?_blockProgram_eq_of_externs_eq`,
  `sepWP_of_other_block_hooks`, `subroutine_ok_of_block_hooks`);
- order-independent `multiDataDisjointB` and `checkMultiDisjointB_spec`;
- balanced `VecTree`-accelerated `O(N log N)` library projection (`toMultiPlacedLibFast`) and split/sliced
  `Placeable ∧ InElf ∧ DataDisjoint` kernel checkers (`checkMultiFastB`, `checkMultiSplit_spec`,
  `checkMultiSliced_spec`); and
- the static relocation-inversion DAG checker (`checkRelocInvStepsB`, `checkRelocInvStepsB_sound`).
-/

@[expose] public section

namespace Arm64.Obj

open Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection

theorem allIdx_of_forall {α : Type} {f : Nat → α → Bool} :
    ∀ {k : Nat} {xs : List α},
      (∀ (i : Nat) (hi : i < xs.length), f (k + i) xs[i] = true) →
      allIdx f k xs = true
  | _, [], _ => rfl
  | k, _ :: xs, h => by
    simp only [allIdx, Bool.and_eq_true]
    refine ⟨?_, allIdx_of_forall fun i hi => ?_⟩
    · have h0 := h 0 (by simp)
      rw [Nat.add_zero] at h0
      exact h0
    · rw [show (k + 1) + i = k + (i + 1) by omega]
      exact h (i + 1) (by simp; omega)

namespace Interned

set_option linter.literalFetch false

/-! ## Balanced `VecTree` Random Access -/

def withHeadTail {α β : Type} (d : α) (xs : List α) (k : α → List α → β) : β :=
  List.casesOn xs (k d []) (fun x xs' => k x xs')

@[simp] theorem withHeadTail_eq {α β : Type} (d : α) (xs : List α) (k : α → List α → β) :
    withHeadTail d xs k = k (xs.getD 0 d) (xs.drop 1) := by
  cases xs <;> rfl

def withBitVec64 {α : Type} (v : BitVec 64) (k : BitVec 64 → α) : α :=
  BitVec.casesOn v fun f => k (BitVec.ofFin f)

@[simp] theorem withBitVec64_eq {α : Type} (v : BitVec 64) (k : BitVec 64 → α) :
    withBitVec64 v k = k v := by
  cases v; rfl

def bv8Beq (a b : BitVec 8) : Bool :=
  Nat.beq a.toNat b.toNat

@[simp] theorem bv8Beq_eq (a b : BitVec 8) : bv8Beq a b = (a == b) := by
  unfold bv8Beq
  cases h : a == b
  · rw [Bool.eq_false_iff]; intro h'
    rw [Nat.beq_eq] at h'
    exact absurd (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h')) (by simp [h])
  · rw [beq_iff_eq] at h; subst h; exact Nat.beq_refl _

def isPrefixOfFast : List (BitVec 8) → List (BitVec 8) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => bv8Beq x y && isPrefixOfFast xs ys

@[simp] theorem isPrefixOfFast_eq :
    ∀ (xs ys : List (BitVec 8)), isPrefixOfFast xs ys = xs.isPrefixOf ys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [isPrefixOfFast, List.isPrefixOf, bv8Beq_eq, isPrefixOfFast_eq xs ys]

def bytes4Eq (xs : List (BitVec 8)) (s0 s1 s2 s3 : BitVec 8) : Bool :=
  match xs with
  | [x0, x1, x2, x3] => bv8Beq x0 s0 && bv8Beq x1 s1 && bv8Beq x2 s2 && bv8Beq x3 s3
  | _ => false

@[simp] theorem bytes4Eq_bytesOfWordLE (w : BitVec 32) (s0 s1 s2 s3 : BitVec 8) :
    bytes4Eq (bytesOfWordLE w) s0 s1 s2 s3 = (bytesOfWordLE w == [s0, s1, s2, s3]) := by
  have h : bytesOfWordLE w =
      [BitVec.extractLsb' 0 8 (BitVec.setWidth 64 w),
       BitVec.extractLsb' 8 8 (BitVec.setWidth 64 w),
       BitVec.extractLsb' 16 8 (BitVec.setWidth 64 w),
       BitVec.extractLsb' 24 8 (BitVec.setWidth 64 w)] := rfl
  rw [h]
  change (bv8Beq _ s0 && bv8Beq _ s1 && bv8Beq _ s2 && bv8Beq _ s3) =
    (_ == s0 && (_ == s1 && (_ == s2 && (_ == s3 && true))))
  simp only [bv8Beq_eq, Bool.and_true, Bool.and_assoc]

/-- Builds a balanced `VecTree α` in CPS over `n` elements in a single linear pass over `xs`. -/
def buildVecTree {α : Type} (d : α) :
    Nat → Nat → List α → (VecTree α → List α → VecTree α) → VecTree α
  | 0, _, xs, k => k .leaf xs
  | fuel + 1, n, xs, k =>
    Nat.casesOn n (k .leaf xs) fun n =>
      withNat (n / 2) fun half =>
        buildVecTree d fuel half xs fun l rest =>
          withHeadTail d rest fun v rest' =>
            withNat (n - half) fun rlen =>
              buildVecTree d fuel rlen rest' fun r rest'' =>
                k (.node half l v r) rest''

theorem buildVecTree_spec {α : Type} (d : α) :
    ∀ (fuel n : Nat) (xs : List α) (k : VecTree α → List α → VecTree α),
      n < 2 ^ fuel →
      ∃ t, buildVecTree d fuel n xs k = k t (xs.drop n) ∧
        (∀ i < n, t.getD d i = xs.getD i d) ∧
        (∀ i, n ≤ i → t.getD d i = d)
  | 0, n, xs, k, hn => by
    have hn0 : n = 0 := by simp [Nat.pow_zero] at hn; omega
    subst hn0
    exact ⟨.leaf, rfl, (fun i hi => by omega), (fun _ _ => rfl)⟩
  | fuel + 1, 0, xs, k, _ =>
    ⟨.leaf, rfl, (fun i hi => by omega), (fun _ _ => rfl)⟩
  | fuel + 1, n + 1, xs, k, hn => by
    simp only [buildVecTree, withNat_eq]
    rw [Nat.pow_succ] at hn
    have h1 : n / 2 < 2 ^ fuel := by omega
    have h2 : n - n / 2 < 2 ^ fuel := by omega
    obtain ⟨l, hl_eq, hl_lt, _⟩ := buildVecTree_spec d fuel (n / 2) xs _ h1
    rw [hl_eq, withHeadTail_eq, getD_drop, Nat.add_zero]
    obtain ⟨r, hr_eq, hr_lt, hr_ge⟩ := buildVecTree_spec d fuel (n - n / 2)
      ((xs.drop (n / 2)).drop 1) _ h2
    rw [hr_eq, List.drop_drop, List.drop_drop,
      show n / 2 + (1 + (n - n / 2)) = n + 1 by omega]
    refine ⟨.node (n / 2) l (xs.getD (n / 2) d) r, rfl, (fun i hi => ?_), (fun i hi => ?_)⟩
    · simp only [VecTree.getD]
      by_cases hlt : i < n / 2
      · rw [show Nat.blt i (n / 2) = true by rw [Nat.blt_eq]; exact hlt]
        exact hl_lt i hlt
      · rw [show Nat.blt i (n / 2) = false by rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; omega]
        by_cases heq : i = n / 2
        · subst heq; simp [Nat.beq_refl]
        · rw [nat_beq_false_of_ne heq]
          have hr := hr_lt (i - (n / 2 + 1)) (by omega)
          rw [getD_drop, getD_drop,
            show n / 2 + (1 + (i - (n / 2 + 1))) = i by omega] at hr
          exact hr
    · simp only [VecTree.getD]
      rw [show Nat.blt i (n / 2) = false by rw [Bool.eq_false_iff, Ne, Nat.blt_eq]; omega]
      rw [nat_beq_false_of_ne (by omega)]
      exact hr_ge (i - (n / 2 + 1)) (by omega)

def toVecTree {α : Type} (d : α) (xs : List α) : VecTree α :=
  withNat xs.length fun n =>
    buildVecTree d 20 n xs (fun t _ => t)

/-- Forces `t` to WHNF constructor form via `VecTree.casesOn` before invoking `k`, avoiding
repeated call-by-name evaluation in the kernel. -/
def forceVecTree {α β : Type} (t : VecTree α) (k : VecTree α → β) : β :=
  VecTree.casesOn t (k .leaf) (fun half l v r => k (.node half l v r))

@[simp] theorem forceVecTree_eq {α β : Type} (t : VecTree α) (k : VecTree α → β) :
    forceVecTree t k = k t := by
  cases t <;> rfl

def withVecTree {α β : Type} (d : α) (xs : List α) (k : VecTree α → β) : β :=
  forceVecTree (toVecTree d xs) k

@[simp] theorem withVecTree_eq {α β : Type} (d : α) (xs : List α) (k : VecTree α → β) :
    withVecTree d xs k = k (toVecTree d xs) := by
  simp [withVecTree]

theorem getD_eq_default_of_le {α : Type} (d : α) :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → xs.getD i d = d
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: xs, i + 1, h => getD_eq_default_of_le d xs i (by simp at h; omega)

theorem toVecTree_getD_all {α : Type} (d : α) (xs : List α) (hn : xs.length < 2 ^ 20) (i : Nat) :
    (toVecTree d xs).getD d i = xs.getD i d := by
  unfold toVecTree
  rw [withNat_eq]
  obtain ⟨t, ht_eq, ht_lt, ht_ge⟩ := buildVecTree_spec d 20 xs.length xs (fun t _ => t) hn
  rw [ht_eq]
  by_cases hi : i < xs.length
  · exact ht_lt i hi
  · rw [ht_ge i (by omega), getD_eq_default_of_le d xs i (by omega)]

/-! ## Tree-Accelerated `toMultiPlacedLibFast` -/

abbrev toStrTree (xs : List String) : VecTree String := toVecTree "" xs

theorem toStrTree_getD {xs : List String} (hn : xs.length < 2 ^ 20) {i : Nat} (_ : i < xs.length) :
    (toStrTree xs).getD "" i = xs.getD i "" :=
  toVecTree_getD_all "" xs hn i

def Reloc.toEntryTree (t : VecTree String) (r : Reloc) : RelocEntry :=
  { off := r.off, kind := r.kind, sym := t.getD "" r.sym, addend := r.addend, localSym := r.localSym }

def Block.toCodeBlockTree (t : VecTree String) (extStrings : List String) (b : Block) : CodeBlock :=
  { code := b.code
    align := b.align
    symbols := b.symbols.map fun s => (t.getD "" s.1, s.2)
    relocs := b.relocs.map (Reloc.toEntryTree t)
    externs := extStrings
    weakRefs := b.weakRefs.map fun e => t.getD "" e }

def Data.toInfoTree (t : VecTree String) (d : Data) : SymDataInfo :=
  { sym := t.getD "" d.sym
    align := d.align
    readOnly := d.readOnly
    bytes := d.bytes
    zeroTail := d.zeroTail
    relocs := d.relocs.map (Reloc.toEntryTree t) }

def MultiLib.toMultiPlacedLibFast (ML : MultiLib) (sharedExterns : List Nat) : MultiPlacedLib :=
  withVecTree "" ML.names fun t =>
    let extStrings := sharedExterns.map fun e => t.getD "" e
    { name := ML.name
      blocks := ML.blocks.map (Block.toCodeBlockTree t extStrings)
      data := ML.data.map (Data.toInfoTree t)
      exports := ML.exports.map fun e => t.getD "" e
      exportSyms := ML.exportSyms.map fun p => (t.getD "" p.1, t.getD "" p.2) }

theorem natListBeq_eq : ∀ {l₁ l₂ : List Nat}, natListBeq l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | n₁ :: ns₁, n₂ :: ns₂, h => by
    change (if Nat.beq n₁ n₂ = true then natListBeq ns₁ ns₂ else false) = true at h
    cases hn : Nat.beq n₁ n₂ with
    | false => rw [hn] at h; nomatch h
    | true =>
      simp only [hn, ↓reduceIte] at h
      rw [Nat.eq_of_beq_eq_true hn, natListBeq_eq h]

def blocksSharedExternsOk (ML : MultiLib) (sharedExterns : List Nat) : Bool :=
  ML.blocks.all fun b => natListBeq b.externs sharedExterns

def multiIdsOkFast (ML : MultiLib) : Bool :=
  withNat ML.names.length fun n =>
    ML.blocks.all (Block.idsOk n) &&
    ML.exports.all (fun e => Nat.blt e n) &&
    ML.data.all fun d => Nat.blt d.sym n && d.relocs.all fun r => Nat.blt r.sym n

@[simp] theorem multiIdsOkFast_eq (ML : MultiLib) : multiIdsOkFast ML = ML.idsOk := by
  simp [multiIdsOkFast, MultiLib.idsOk, withNat_eq]

theorem toMultiPlacedLib_of_fast {lib : MultiPlacedLib} {ML : MultiLib} {sharedExterns : List Nat}
    (hfast : lib = ML.toMultiPlacedLibFast sharedExterns)
    (hids : multiIdsOkFast ML = true)
    (hlen : Nat.blt ML.names.length 1048576 = true)
    (hext : blocksSharedExternsOk ML sharedExterns = true) :
    lib = ML.toMultiPlacedLib := by
  subst hfast
  have _ := hids
  have hn : ML.names.length < 2 ^ 20 := by rw [Nat.blt_eq] at hlen; exact hlen
  have hget : ∀ i, (toVecTree "" ML.names).getD "" i = ML.names.getD i "" :=
    toVecTree_getD_all "" ML.names hn
  have hext_all := List.all_eq_true.1 hext
  unfold MultiLib.toMultiPlacedLibFast MultiLib.toMultiPlacedLib
  simp only [withVecTree_eq]
  congr 1
  · refine List.map_congr_left fun b hb => ?_
    have hb_ext : b.externs = sharedExterns := natListBeq_eq (hext_all b hb)
    unfold Block.toCodeBlockTree Block.toCodeBlock Reloc.toEntryTree Reloc.toEntry
    simp only [hget, ← hb_ext]
  · refine List.map_congr_left fun d _ => ?_
    unfold Data.toInfoTree Data.toInfo Reloc.toEntryTree Reloc.toEntry
    simp only [hget]
  · refine List.map_congr_left fun e _ => hget e
  · refine List.map_congr_left fun p _ => ?_
    simp only [hget]

/-! ## `VecTree.setFresh` for `O(N log N)` Block-Symbol Distinctness and Lookup -/

def mkNoneTree {α : Type} : Nat → Nat → VecTree (Option α)
  | 0, _ => .leaf
  | fuel + 1, n =>
    Nat.casesOn n .leaf fun n =>
      withNat (n / 2) fun half =>
        withNat (n - half) fun rlen =>
          forceVecTree (mkNoneTree fuel half) fun l =>
            forceVecTree (mkNoneTree fuel rlen) fun r =>
              .node half l none r

theorem getD_mkNoneTree {α : Type} :
    ∀ (fuel n j : Nat), (mkNoneTree (α := α) fuel n).getD none j = none
  | 0, _, _ => rfl
  | fuel + 1, 0, _ => rfl
  | fuel + 1, n + 1, j => by
    simp only [mkNoneTree, withNat_eq, forceVecTree_eq, VecTree.getD]
    cases Nat.blt j (n / 2)
    · cases Nat.beq j (n / 2)
      · exact getD_mkNoneTree fuel (n - n / 2) (j - (n / 2 + 1))
      · rfl
    · exact getD_mkNoneTree fuel (n / 2) j

def VecTree.setFresh {α : Type} : VecTree (Option α) → Nat → α → Option (VecTree (Option α))
  | .leaf, _, _ => none
  | .node half l v r, i, x =>
    match Nat.blt i half with
    | true =>
      match l.setFresh i x with
      | some l' => some (.node half l' v r)
      | none => none
    | false =>
      match Nat.beq i half with
      | true =>
        match v with
        | none => some (.node half l (some x) r)
        | some _ => none
      | false =>
        withNat (i - (half + 1)) fun idx =>
          match r.setFresh idx x with
          | some r' => some (.node half l v r')
          | none => none

theorem VecTree.getD_setFresh_self {α : Type} :
    ∀ {t t' : VecTree (Option α)} {i : Nat} {x : α},
      t.setFresh i x = some t' →
      t.getD none i = none ∧ t'.getD none i = some x
  | .leaf, _, _, _, h => nomatch h
  | .node half l v r, t', i, x, h => by
    simp only [VecTree.setFresh, withNat_eq] at h
    cases hlt : Nat.blt i half
    · rw [hlt] at h
      cases heq : Nat.beq i half
      · rw [heq] at h
        cases hr : r.setFresh (i - (half + 1)) x with
        | none => rw [hr] at h; nomatch h
        | some r' =>
          rw [hr] at h; cases h
          simp only [VecTree.getD, hlt, heq]
          exact VecTree.getD_setFresh_self hr
      · rw [heq] at h
        cases v with
        | some _ => nomatch h
        | none =>
          cases h
          simp [VecTree.getD, hlt, heq]
    · rw [hlt] at h
      cases hl : l.setFresh i x with
      | none => rw [hl] at h; nomatch h
      | some l' =>
        rw [hl] at h; cases h
        simp only [VecTree.getD, hlt]
        exact VecTree.getD_setFresh_self hl

theorem VecTree.getD_setFresh_of_ne {α : Type} :
    ∀ {t t' : VecTree (Option α)} {i j : Nat} {x : α},
      t.setFresh i x = some t' → j ≠ i →
      t'.getD none j = t.getD none j
  | .leaf, _, _, _, _, h, _ => nomatch h
  | .node half l v r, t', i, j, x, h, hne => by
    simp only [VecTree.setFresh, withNat_eq] at h
    cases hlt_i : Nat.blt i half
    · rw [hlt_i] at h
      cases heq_i : Nat.beq i half
      · rw [heq_i] at h
        cases hr : r.setFresh (i - (half + 1)) x with
        | none => rw [hr] at h; nomatch h
        | some r' =>
          rw [hr] at h; cases h
          simp only [VecTree.getD]
          cases hlt_j : Nat.blt j half
          · cases heq_j : Nat.beq j half
            · have hi_ge : half + 1 ≤ i := by
                rw [Bool.eq_false_iff, Ne, Nat.blt_eq] at hlt_i
                rw [Bool.eq_false_iff, Ne, Nat.beq_eq] at heq_i
                omega
              have hj_ge : half + 1 ≤ j := by
                rw [Bool.eq_false_iff, Ne, Nat.blt_eq] at hlt_j
                rw [Bool.eq_false_iff, Ne, Nat.beq_eq] at heq_j
                omega
              exact VecTree.getD_setFresh_of_ne hr (by omega)
            · rfl
          · rfl
      · rw [heq_i] at h
        cases v with
        | some _ => nomatch h
        | none =>
          cases h
          have hi_eq : i = half := Nat.eq_of_beq_eq_true heq_i
          subst hi_eq
          simp only [VecTree.getD, nat_beq_false_of_ne hne]
    · rw [hlt_i] at h
      cases hl : l.setFresh i x with
      | none => rw [hl] at h; nomatch h
      | some l' =>
        rw [hl] at h; cases h
        simp only [VecTree.getD]
        cases hlt_j : Nat.blt j half
        · rfl
        · exact VecTree.getD_setFresh_of_ne hl hne

def insertBlockSyms (blkIdx : Nat) :
    List (Nat × Nat) → VecTree (Option (Nat × Nat)) → Option (VecTree (Option (Nat × Nat)))
  | [], t => some t
  | (s, off) :: rest, t =>
    match t.setFresh s (blkIdx, off) with
    | some t' => insertBlockSyms blkIdx rest t'
    | none => none

theorem insertBlockSyms_spec (blkIdx : Nat) :
    ∀ (syms : List (Nat × Nat)) (t t' : VecTree (Option (Nat × Nat))),
      insertBlockSyms blkIdx syms t = some t' →
      (syms.map (·.1)).Nodup ∧
      (∀ s ∈ syms.map (·.1), t.getD none s = none) ∧
      (∀ q, t'.getD none q =
        match t.getD none q with
        | some v => some v
        | none => (lookupId q syms).map fun off => (blkIdx, off))
  | [], t, t', h => by
    injection h with h; subst h
    refine ⟨List.nodup_nil, (fun _ hm => nomatch hm), fun q => ?_⟩
    cases t.getD none q <;> rfl
  | (s, off) :: rest, t, t', h => by
    simp only [insertBlockSyms] at h
    cases hs : t.setFresh s (blkIdx, off) with
    | none => rw [hs] at h; nomatch h
    | some t1 =>
      rw [hs] at h
      obtain ⟨h_s_none, h_s_some⟩ := VecTree.getD_setFresh_self hs
      obtain ⟨hnd_rest, hnone_rest, hget_rest⟩ := insertBlockSyms_spec blkIdx rest t1 t' h
      have hs_not_rest : s ∉ rest.map (·.1) := by
        intro hm
        have := hnone_rest s hm
        rw [h_s_some] at this
        nomatch this
      refine ⟨List.nodup_cons.2 ⟨hs_not_rest, hnd_rest⟩, ?_, fun q => ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx_rest
        · exact h_s_none
        · have hx_ne : x ≠ s := fun heq => hs_not_rest (heq ▸ hx_rest)
          rw [← VecTree.getD_setFresh_of_ne hs hx_ne]
          exact hnone_rest x hx_rest
      · rw [hget_rest q]
        by_cases hqs : q = s
        · subst hqs
          simp [h_s_some, h_s_none, lookupId, Nat.beq_refl]
        · rw [VecTree.getD_setFresh_of_ne hs hqs]
          cases t.getD none q with
          | some v => rfl
          | none => simp [lookupId, nat_beq_false_of_ne (Ne.symm hqs)]

theorem nodup_append_of_disjoint {α : Type} :
    ∀ {l1 l2 : List α}, l1.Nodup → l2.Nodup → (∀ x ∈ l1, x ∉ l2) → (l1 ++ l2).Nodup
  | [], _, _, h2, _ => h2
  | x :: xs, _, h1, h2, hd => by
    obtain ⟨hx1, hxs1⟩ := List.nodup_cons.1 h1
    rw [List.cons_append, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_append_of_disjoint hxs1 h2 fun y hy => hd y (List.mem_cons_of_mem x hy)⟩
    rcases List.mem_append.1 hm with h | h
    · exact hx1 h
    · exact hd x List.mem_cons_self h

theorem lookupId_isSome_of_mem :
    ∀ {s : Nat} {syms : List (Nat × Nat)}, (∃ off, (s, off) ∈ syms) → lookupId s syms ≠ none
  | _, [], ⟨_, hm⟩ => nomatch hm
  | s, (k, v) :: rest, ⟨off, hm⟩ => by
    simp only [lookupId]
    cases hk : Nat.beq k s with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases List.mem_cons.1 hm with heq | hm_rest
      · injection heq with hs _
        subst hs
        rw [Nat.beq_refl] at hk
        nomatch hk
      · exact lookupId_isSome_of_mem ⟨off, hm_rest⟩

def insertAllBlocks :
    Nat → List Block → VecTree (Option (Nat × Nat)) → Option (VecTree (Option (Nat × Nat)))
  | _, [], t => some t
  | blkIdx, b :: rest, t =>
    match insertBlockSyms blkIdx b.symbols t with
    | some t' => insertAllBlocks (blkIdx + 1) rest t'
    | none => none

theorem insertAllBlocks_spec :
    ∀ (k : Nat) (blks : List Block) (t t' : VecTree (Option (Nat × Nat))),
      insertAllBlocks k blks t = some t' →
      ((blks.flatMap (·.symbols)).map (·.1)).Nodup ∧
      (∀ s ∈ (blks.flatMap (·.symbols)).map (·.1), t.getD none s = none) ∧
      (∀ q, t'.getD none q =
        match t.getD none q with
        | some v => some v
        | none => lookupBlockSymIdAux q k blks)
  | _, [], t, t', h => by
    injection h with h; subst h
    refine ⟨List.nodup_nil, (fun _ hm => nomatch hm), fun q => ?_⟩
    cases t.getD none q <;> rfl
  | k, b :: rest, t, t', h => by
    simp only [insertAllBlocks] at h
    cases hb : insertBlockSyms k b.symbols t with
    | none => rw [hb] at h; nomatch h
    | some t1 =>
      rw [hb] at h
      obtain ⟨hnd_b, hnone_b, hget_b⟩ := insertBlockSyms_spec k b.symbols t t1 hb
      obtain ⟨hnd_r, hnone_r, hget_r⟩ := insertAllBlocks_spec (k + 1) rest t1 t' h
      simp only [List.flatMap_cons, List.map_append]
      have hdisj : ∀ x ∈ b.symbols.map (·.1), x ∉ (rest.flatMap (·.symbols)).map (·.1) := by
        intro x hxb hxr
        have h1 := hnone_r x hxr
        rw [hget_b x, hnone_b x hxb] at h1
        obtain ⟨⟨s, off⟩, hmem, rfl⟩ := List.mem_map.1 hxb
        cases hl : lookupId s b.symbols with
        | some _ => rw [hl] at h1; nomatch h1
        | none => exact lookupId_isSome_of_mem ⟨off, hmem⟩ hl
      refine ⟨nodup_append_of_disjoint hnd_b hnd_r hdisj, ?_, fun q => ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hxb | hxr
        · exact hnone_b x hxb
        · have h1 := hnone_r x hxr
          rw [hget_b x] at h1
          cases htq : t.getD none x with
          | none => rfl
          | some v => rw [htq] at h1; nomatch h1
      · rw [hget_r q, hget_b q]
        cases t.getD none q with
        | some v => rfl
        | none =>
          simp only [lookupBlockSymIdAux]
          cases lookupId q b.symbols <;> rfl

theorem natNodup_of_nodup : ∀ {l : List Nat}, l.Nodup → natNodup l = true
  | [], _ => rfl
  | n :: ns, h => by
    obtain ⟨hn, hns⟩ := List.nodup_cons.1 h
    simp only [natNodup, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne, memNat_iff]
    exact ⟨hn, natNodup_of_nodup hns⟩

/-! ## Split and Sliced `Placeable` / `InElf` / `DataDisjoint` Checkers -/

def blockSymsMatchTree (ML : MultiLib) (tBase tAddr : VecTree (BitVec 64)) : Bool :=
  allIdx (fun i b =>
    withBitVec64 (tBase.getD 0#64 i) fun base =>
      b.symbols.all fun s =>
        tAddr.getD 0#64 s.1 == base + BitVec.ofNat 64 s.2)
    0 ML.blocks

theorem blockSymsMatchTree_eq (ML : MultiLib) (mly : MultiLayout)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20) :
    blockSymsMatchTree ML (toVecTree 0#64 mly.bases) (toVecTree 0#64 mly.addrs) =
      blockSymsMatchB ML mly := by
  simp only [blockSymsMatchTree, blockSymsMatchB, withBitVec64_eq,
    toVecTree_getD_all _ _ hb, toVecTree_getD_all _ _ ha]

def buildExtAddrs (tAddr : VecTree (BitVec 64)) :
    List Nat → (List (Nat × BitVec 64) → Bool) → Bool
  | [], k => k []
  | e :: es, k =>
    withBitVec64 (tAddr.getD 0#64 e) fun addr =>
      buildExtAddrs tAddr es fun rest => k ((e, addr) :: rest)

theorem buildExtAddrs_eq (tAddr : VecTree (BitVec 64)) :
    ∀ (exts : List Nat) (k : List (Nat × BitVec 64) → Bool),
      buildExtAddrs tAddr exts k = k (exts.map fun e => (e, tAddr.getD 0#64 e))
  | [], _ => rfl
  | _ :: es, k => by
    simp only [buildExtAddrs, withBitVec64_eq, buildExtAddrs_eq tAddr es, List.map_cons]

theorem ext0Addrs_all_eq (getAddr : Nat → BitVec 64) (ext0 : List Nat) (b : Block)
    (base : BitVec 64) (len : Nat) :
    (if natListBeq b.externs ext0 then
      (ext0.map fun e => (e, getAddr e)).all fun (e, addr) =>
        (lookupId e b.symbols).isNone && Nat.ble len (addr - base).toNat
    else
      b.externs.all fun e =>
        (lookupId e b.symbols).isNone && Nat.ble len (getAddr e - base).toNat) =
    (b.externs.all fun e =>
      (lookupId e b.symbols).isNone && Nat.ble len (getAddr e - base).toNat) := by
  split
  · next hbeq =>
    rw [natListBeq_eq hbeq, List.all_map]
    rfl
  · rfl

def textPlaceableTreeMulti (ML : MultiLib) (tBase tAddr : VecTree (BitVec 64)) : Bool :=
  let ext0 := (ML.blocks.headD { code := [] }).externs
  buildExtAddrs tAddr ext0 fun ext0Addrs =>
    allIdx (fun i b =>
      withBitVec64 (tBase.getD 0#64 i) fun base =>
        withNat (fastLen512 4096 b.code) fun len =>
          Nat.blt 0 b.align && Nat.beq (b.align % 4) 0 && Nat.beq (base.toNat % b.align) 0 &&
            Nat.ble (base.toNat + len) 18446744073709551616 && Nat.beq (len % 4) 0 &&
            relocsWf len 0 b.relocs &&
            b.symbols.all (fun s => Nat.beq (s.2 % 4) 0 && Nat.ble s.2 len) &&
            (if natListBeq b.externs ext0 then
              ext0Addrs.all fun (e, addr) =>
                (lookupId e b.symbols).isNone && Nat.ble len (addr - base).toNat
            else
              b.externs.all fun e =>
                (lookupId e b.symbols).isNone && Nat.ble len (tAddr.getD 0#64 e - base).toNat))
      0 ML.blocks

theorem textPlaceableTreeMulti_eq (ML : MultiLib) (mly : MultiLayout)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20) :
    textPlaceableTreeMulti ML (toVecTree 0#64 mly.bases) (toVecTree 0#64 mly.addrs) =
      allIdx (fun i b => textPlaceableB (ML.blockLib b) (mly.blockLayout i)) 0 ML.blocks := by
  simp only [textPlaceableTreeMulti, buildExtAddrs_eq, textPlaceableB, MultiLib.blockLib,
    MultiLayout.blockLayout, withBitVec64_eq, withNat_eq, fastLen512_eq_length, ext0Addrs_all_eq,
    toVecTree_getD_all _ _ hb, toVecTree_getD_all _ _ ha]

def blockRanges (tBase : VecTree (BitVec 64)) : Nat → List Block → List (BitVec 64 × Nat)
  | _, [] => []
  | i, b :: bs =>
    withBitVec64 (tBase.getD 0#64 i) fun base =>
      withNat (fastLen512 4096 b.code) fun len =>
        (base, len) :: blockRanges tBase (i + 1) bs

theorem blockRanges_length (tBase : VecTree (BitVec 64)) :
    ∀ (k : Nat) (blks : List Block), (blockRanges tBase k blks).length = blks.length
  | _, [] => rfl
  | k, _ :: bs => by simp [blockRanges, blockRanges_length tBase (k + 1) bs]

theorem blockRanges_getElem (tBase : VecTree (BitVec 64)) :
    ∀ (k : Nat) (blks : List Block) (i : Nat) (hi : i < (blockRanges tBase k blks).length),
      (blockRanges tBase k blks)[i] =
        (tBase.getD 0#64 (k + i), (blks[i]'(by rw [← blockRanges_length tBase k]; exact hi)).code.length)
  | _, [], _, hi => nomatch hi
  | k, b :: bs, 0, _ => by simp [blockRanges, fastLen512_eq_length]
  | k, b :: bs, i + 1, hi => by
    simp only [blockRanges, withBitVec64_eq, withNat_eq, fastLen512_eq_length, List.getElem_cons_succ]
    rw [blockRanges_getElem tBase (k + 1) bs i (by simp [blockRanges] at hi; omega)]
    rw [show k + 1 + i = k + (i + 1) by omega]

theorem pairwise_rel_of_lt {α : Type} {R : α → α → Prop} :
    ∀ {xs : List α}, xs.Pairwise R →
      ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length), i < j → R xs[i] xs[j]
  | [], _, _, _, hi, _, _ => nomatch hi
  | x :: xs, hpw, 0, j + 1, _, hj, _ => by
    obtain ⟨hhead, _⟩ := List.pairwise_cons.1 hpw
    have hj' : j < xs.length := by simp at hj; omega
    exact hhead xs[j] (List.getElem_mem hj')
  | _ :: xs, hpw, i + 1, j + 1, hi, hj, hij => by
    obtain ⟨_, htail⟩ := List.pairwise_cons.1 hpw
    exact pairwise_rel_of_lt htail i j (by simp at hi; omega) (by simp at hj; omega) (by omega)

theorem blocksDisjoint_of_rangesSorted {ML : MultiLib} {mly : MultiLayout}
    (hb : mly.bases.length < 2 ^ 20)
    (h : rangesSorted (blockRanges (toVecTree 0#64 mly.bases) 0 ML.blocks) = true) :
    allIdx (fun i b1 =>
      allIdx (fun j b2 =>
        !Nat.blt i j ||
          checkRangesDisjoint (mly.bases.getD i 0#64).toNat b1.code.length
            (mly.bases.getD j 0#64).toNat b2.code.length)
        0 ML.blocks) 0 ML.blocks = true := by
  have ⟨hpw, _⟩ := rangesSorted_pairwise h
  apply allIdx_of_forall
  intro i hi
  apply allIdx_of_forall
  intro j hj
  simp only [Nat.zero_add, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne, Nat.blt_eq]
  by_cases hij : i < j
  · right
    have hi' : i < (blockRanges (toVecTree 0#64 mly.bases) 0 ML.blocks).length := by
      rw [blockRanges_length]; exact hi
    have hj' : j < (blockRanges (toVecTree 0#64 mly.bases) 0 ML.blocks).length := by
      rw [blockRanges_length]; exact hj
    have hrel := pairwise_rel_of_lt hpw i j hi' hj' hij
    rw [blockRanges_getElem _ 0 ML.blocks i hi', blockRanges_getElem _ 0 ML.blocks j hj'] at hrel
    simp only [Nat.zero_add, toVecTree_getD_all _ _ hb] at hrel
    simp only [checkRangesDisjoint, Bool.or_eq_true, Nat.ble_eq]
    exact Or.inl hrel
  · exact Or.inl hij

def dataRelocOkTreeMulti (tAddr : VecTree (BitVec 64))
    (addr : BitVec 64) (n : Nat) (r : Reloc) : Bool :=
  let tgt := addSignedAddr (tAddr.getD 0#64 r.sym) r.addend
  Nat.blt 0 (dataRelocWidth r.kind) && Nat.ble (r.off + dataRelocWidth r.kind) n &&
    match r.kind with
    | .abs32 => sInRange (-2147483648) 4294967296 tgt
    | .prel32 => sInRange (-2147483648) 2147483648 (tgt - (addr + BitVec.ofNat 64 r.off))
    | _ => true

def dataPlaceableTreeMulti (ML : MultiLib) (tAddr : VecTree (BitVec 64)) : Bool :=
  ML.data.all fun d =>
    withBitVec64 (tAddr.getD 0#64 d.sym) fun a =>
      withNat (fastLen512 4096 d.bytes) fun dlen =>
        Nat.blt 0 d.align && Nat.beq (a.toNat % d.align) 0 &&
          Nat.ble (a.toNat + dlen + d.zeroTail) 18446744073709551616 &&
          d.relocs.all (dataRelocOkTreeMulti tAddr a dlen)

theorem dataPlaceableTreeMulti_imp (ML : MultiLib) (mly : MultiLayout)
    (ha : mly.addrs.length < 2 ^ 20)
    (hnd : (ML.data.map (·.sym)).Nodup)
    (h : dataPlaceableTreeMulti ML (toVecTree 0#64 mly.addrs) = true) :
    dataPlaceableB (ML.blockLib { code := [] }) mly.dataLayout = true := by
  have hrel : dataRelocOkTreeMulti (toVecTree 0#64 mly.addrs) =
      dataRelocOkB (ML.blockLib { code := [] }) mly.dataLayout := by
    funext a n r
    simp only [dataRelocOkTreeMulti, dataRelocOkB, targetId, resolveId,
      MultiLib.blockLib, MultiLayout.dataLayout, toVecTree_getD_all _ _ ha]
    rfl
  simp only [dataPlaceableTreeMulti, withBitVec64_eq, withNat_eq, fastLen512_eq_length,
    toVecTree_getD_all _ _ ha, hrel] at h
  simp only [dataPlaceableB, Bool.and_eq_true]
  refine ⟨by simp [natNodupFast, MultiLib.blockLib, natNodup_of_nodup hnd], ?_⟩
  simpa [lookupId, MultiLib.blockLib, MultiLayout.dataLayout] using h

def resolveTree (b : Block) (base : BitVec 64) (tAddr : VecTree (BitVec 64)) (sym : Nat) : BitVec 64 :=
  match lookupId sym b.symbols with
  | some off => base + BitVec.ofNat 64 off
  | none => tAddr.getD 0#64 sym

def targetTreeMulti (b : Block) (base : BitVec 64) (tAddr : VecTree (BitVec 64)) (r : Reloc) : BitVec 64 :=
  addSignedAddr (resolveTree b base tAddr r.sym) r.addend

def relocTargetTreeMulti (L : Lib) (b : Block) (base : BitVec 64) (b2b : List Nat)
    (tAddr : VecTree (BitVec 64)) (off : Nat) (r : Reloc) : BitVec 64 :=
  match (if memNat off b2b then b2bNextId L r else none) with
  | some r2 => targetTreeMulti b base tAddr r2
  | none => targetTreeMulti b base tAddr r

def siteOutTreeMulti (L : Lib) (ly : Layout) (b : Block) (tAddr : VecTree (BitVec 64))
    (o : Nat) (r : Reloc) (w : BitVec 32) (rel prev : Bool) : BitVec 32 :=
  let place := ly.base + BitVec.ofNat 64 o
  if rel then nopWord
  else if prev then adrWord (adrTemplate w) place (targetTreeMulti b ly.base tAddr r)
  else if r.kind.isGotOrTlsIe && 4 ≤ o &&
      (memNat (o - 4) ly.relax && gotPairId L (o - 4)) then
    adrWord (adrTemplate w) place (targetTreeMulti b ly.base tAddr r)
  else if r.kind.isGotOrTlsIe && memNat o ly.relax &&
      (gotPairId L o || tlsieRelaxableId L o ||
        (4 ≤ o && gotPairId L (o - 4))) then
    CodeBlock.patchGotOrTlsIeRelaxed w place (targetTreeMulti b ly.base tAddr r) r.kind
  else patchRelocWord r.kind w place
    (if undefWeakId L ly r then place + 4 else relocTargetTreeMulti L b ly.base ly.b2b tAddr o r)

def siteRangeOkTreeMulti (L : Lib) (ly : Layout) (b : Block) (tAddr : VecTree (BitVec 64))
    (o : Nat) (r : Reloc) (prev : Bool) : Bool :=
  let place := ly.base + BitVec.ofNat 64 o
  relocInRangeB L ly r.kind o place (relocTargetTreeMulti L b ly.base ly.b2b tAddr o r) &&
    (!prev || sInRange (-1048576) 1048576 (targetTreeMulti b ly.base tAddr r - place))

def walkTreeMulti (L : Lib) (ly : Layout) (b : Block) (tAddr : VecTree (BitVec 64)) :
    Nat → Bool → List Reloc → List (BitVec 8) → List (BitVec 8) → Bool
  | _, _, _, [], _ => true
  | o, prev, rs, b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss =>
    match rs with
    | r :: rs' =>
      if Nat.beq r.off o then
        let w := b3 ++ b2 ++ b1 ++ b0
        let rel := relaxHead ly o r w rs' cs
        bytes4Eq (bytesOfWordLE (siteOutTreeMulti L ly b tAddr o r w rel prev)) s0 s1 s2 s3 &&
          siteRangeOkTreeMulti L ly b tAddr o r prev &&
          walkTreeMulti L ly b tAddr (o + 4) rel rs' cs ss
      else
        bv8Beq b0 s0 && bv8Beq b1 s1 && bv8Beq b2 s2 && bv8Beq b3 s3 &&
          walkTreeMulti L ly b tAddr (o + 4) false rs cs ss
    | [] =>
      bv8Beq b0 s0 && bv8Beq b1 s1 && bv8Beq b2 s2 && bv8Beq b3 s3 &&
        walkTreeMulti L ly b tAddr (o + 4) false [] cs ss
  | _, _, _, _ :: _, _ => false

theorem walkTreeMulti_eq (ML : MultiLib) (mly : MultiLayout) (ha : mly.addrs.length < 2 ^ 20)
    (b : Block) (i : Nat) :
    ∀ (o : Nat) (prev : Bool) (rs : List Reloc) (cs ss : List (BitVec 8)),
      walkTreeMulti (ML.blockLib b) (mly.blockLayout i) b (toVecTree 0#64 mly.addrs) o prev rs cs ss =
        walk (ML.blockLib b) (mly.blockLayout i) o prev rs cs ss
  | _, _, _, [], _ => rfl
  | _, _, _, [_], [] | _, _, _, [_, _], [] | _, _, _, [_, _, _], []
  | _, _, _, _ :: _ :: _ :: _ :: _, []
  | _, _, _, [_], [_] | _, _, _, [_, _], [_] | _, _, _, [_, _, _], [_]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_]
  | _, _, _, [_], [_, _] | _, _, _, [_, _], [_, _] | _, _, _, [_, _, _], [_, _]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_, _]
  | _, _, _, [_], [_, _, _] | _, _, _, [_, _], [_, _, _] | _, _, _, [_, _, _], [_, _, _]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_, _, _]
  | _, _, _, [_], _ :: _ :: _ :: _ :: _
  | _, _, _, [_, _], _ :: _ :: _ :: _ :: _
  | _, _, _, [_, _, _], _ :: _ :: _ :: _ :: _ => rfl
  | o, prev, [], b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss => by
    simp only [walkTreeMulti, walk, bv8Beq_eq,
      walkTreeMulti_eq ML mly ha b i (o + 4) false [] cs ss]
  | o, prev, r :: rs', b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss => by
    have htgt : ∀ r', targetTreeMulti b (mly.blockLayout i).base (toVecTree 0#64 mly.addrs) r' =
        targetId (ML.blockLib b) (mly.blockLayout i) r' := by
      intro r'
      simp only [targetTreeMulti, targetId, resolveTree, resolveId, MultiLib.blockLib,
        MultiLayout.blockLayout, toVecTree_getD_all _ _ ha]
      rfl
    have hrtgt : relocTargetTreeMulti (ML.blockLib b) b (mly.blockLayout i).base
        (mly.blockLayout i).b2b (toVecTree 0#64 mly.addrs) o r =
        relocTargetId (ML.blockLib b) (mly.blockLayout i) o r := by
      unfold relocTargetTreeMulti relocTargetId
      cases (if memNat o (mly.blockLayout i).b2b then b2bNextId (ML.blockLib b) r else none) <;>
        simp only [htgt]
    simp only [walkTreeMulti, walk, siteOutTreeMulti, siteOut, siteRangeOkTreeMulti, siteRangeOk,
      bytes4Eq_bytesOfWordLE, bv8Beq_eq, htgt, hrtgt,
      walkTreeMulti_eq ML mly ha b i (o + 4) _ _ cs ss]

def withRegionsWithLen {α : Type} :
    List Snapshot.Region → (List (Snapshot.Region × Nat) → α) → α
  | [], k => k []
  | r :: rs, k =>
    withNat (fastLen512 4096 r.bytes) fun len =>
      withRegionsWithLen rs fun tail =>
        k ((r, len) :: tail)

@[simp] theorem withRegionsWithLen_eq {α : Type} :
    ∀ (rs : List Snapshot.Region) (k : List (Snapshot.Region × Nat) → α),
      withRegionsWithLen rs k = k (rs.map (fun r => (r, r.bytes.length)))
  | [], _ => rfl
  | r :: rs, k => by
    simp [withRegionsWithLen, withNat_eq, fastLen512_eq_length, withRegionsWithLen_eq rs]

def regionViewWithLen (addr : BitVec 64) :
    List (Snapshot.Region × Nat) → Option (Perm × List (BitVec 8) × Nat)
  | [] => none
  | (r, len) :: rs =>
    withNat (addr - r.start).toNat fun d =>
      if Nat.blt d len then
        if Nat.ble len 18446744073709551616 then
          withForcedList (fastDrop d r.bytes) fun bs =>
            withNat (len - d) fun m =>
              some (r.perm, bs, m)
        else none
      else
        match regionViewWithLen addr rs with
        | some (p, bs, m) =>
          if Nat.ble len d && Nat.ble (d + m) 18446744073709551616 then some (p, bs, m) else none
        | none => none

@[simp] theorem regionViewWithLen_eq (addr : BitVec 64) :
    ∀ (regions : List Snapshot.Region),
      regionViewWithLen addr (regions.map (fun r => (r, r.bytes.length))) =
        regionView addr regions
  | [] => rfl
  | _ :: rs => by
    simp only [List.map_cons, regionViewWithLen, regionView, withNat_eq,
      withForcedList_eq, fastDrop_eq_drop, regionViewWithLen_eq addr rs]
    rfl

def nextViewWithLen (regsWithLen : List (Snapshot.Region × Nat)) (a : BitVec 64) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → Option (Perm × List (BitVec 8))
  | some (c, p, bs) =>
    if Nat.ble c.toNat a.toNat then
      match dropN? (a - c).toNat bs with
      | some bs' => some (p, bs')
      | none => (regionViewWithLen a regsWithLen).map fun v => (v.1, v.2.1)
    else (regionViewWithLen a regsWithLen).map fun v => (v.1, v.2.1)
  | none => (regionViewWithLen a regsWithLen).map fun v => (v.1, v.2.1)

@[simp] theorem nextViewWithLen_eq (regions : List Snapshot.Region) (a : BitVec 64)
    (cur : Option (BitVec 64 × Perm × List (BitVec 8))) :
    nextViewWithLen (regions.map (fun r => (r, r.bytes.length))) a cur =
      nextView regions a cur := by
  rcases cur with _ | ⟨c, p, bs⟩ <;>
    simp only [nextViewWithLen, nextView, regionViewWithLen_eq] <;> rfl

def multiTextWalkTree (ML : MultiLib) (tBase tAddr : VecTree (BitVec 64))
    (tRelax tB2b : VecTree (List Nat)) (undefWeak : List Nat)
    (regsWithLen : List (Snapshot.Region × Nat)) :
    Nat → Option (BitVec 64 × Perm × List (BitVec 8)) → List Block → Bool
  | _, _, [] => true
  | i, cur, b :: rest =>
    withBitVec64 (tBase.getD 0#64 i) fun base =>
      let ly : Layout :=
        { base := base
          addrs := []
          relax := tRelax.getD [] i
          b2b := tB2b.getD [] i
          undefWeak := undefWeak }
      match nextViewWithLen regsWithLen base cur with
      | some (p, bs) =>
        (p == Perm.rx) && walkTreeMulti (ML.blockLib b) ly b tAddr 0 false b.relocs b.code bs &&
          multiTextWalkTree ML tBase tAddr tRelax tB2b undefWeak regsWithLen (i + 1) (some (base, p, bs)) rest
      | none => false

theorem walkTreeMulti_addrs_irrel (L : Lib) (base : BitVec 64) (addrs1 addrs2 : List (BitVec 64))
    (relax b2b undefWeak : List Nat) (b : Block) (tAddr : VecTree (BitVec 64)) :
    ∀ (o : Nat) (prev : Bool) (rs : List Reloc) (cs ss : List (BitVec 8)),
      walkTreeMulti L { base := base, addrs := addrs1, relax := relax, b2b := b2b, undefWeak := undefWeak } b tAddr o prev rs cs ss =
        walkTreeMulti L { base := base, addrs := addrs2, relax := relax, b2b := b2b, undefWeak := undefWeak } b tAddr o prev rs cs ss
  | _, _, _, [], _ => rfl
  | _, _, _, [_], [] | _, _, _, [_, _], [] | _, _, _, [_, _, _], []
  | _, _, _, _ :: _ :: _ :: _ :: _, []
  | _, _, _, [_], [_] | _, _, _, [_, _], [_] | _, _, _, [_, _, _], [_]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_]
  | _, _, _, [_], [_, _] | _, _, _, [_, _], [_, _] | _, _, _, [_, _, _], [_, _]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_, _]
  | _, _, _, [_], [_, _, _] | _, _, _, [_, _], [_, _, _] | _, _, _, [_, _, _], [_, _, _]
  | _, _, _, _ :: _ :: _ :: _ :: _, [_, _, _]
  | _, _, _, [_], _ :: _ :: _ :: _ :: _
  | _, _, _, [_, _], _ :: _ :: _ :: _ :: _
  | _, _, _, [_, _, _], _ :: _ :: _ :: _ :: _ => rfl
  | o, prev, [], b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss => by
    simp only [walkTreeMulti, walkTreeMulti_addrs_irrel L base addrs1 addrs2 relax b2b undefWeak b tAddr (o + 4) false [] cs ss]
  | o, prev, r :: rs', b0 :: b1 :: b2 :: b3 :: cs, s0 :: s1 :: s2 :: s3 :: ss => by
    simp only [walkTreeMulti, relaxHead, siteOutTreeMulti, siteRangeOkTreeMulti, relocInRangeB, undefWeakId,
      walkTreeMulti_addrs_irrel L base addrs1 addrs2 relax b2b undefWeak b tAddr (o + 4) _ _ cs ss]
    rfl

theorem multiTextWalkTree_eq (ML : MultiLib) (mly : MultiLayout)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20)
    (hrx : mly.relax.length < 2 ^ 20) (hb2b : mly.b2b.length < 2 ^ 20)
    (regions : List Snapshot.Region) :
    ∀ (i : Nat) (cur : Option (BitVec 64 × Perm × List (BitVec 8))) (blks : List Block),
      multiTextWalkTree ML (toVecTree 0#64 mly.bases) (toVecTree 0#64 mly.addrs)
        (toVecTree [] mly.relax) (toVecTree [] mly.b2b) mly.undefWeak
        (regions.map (fun r => (r, r.bytes.length))) i cur blks =
        multiTextWalk ML mly regions i cur blks
  | _, _, [] => rfl
  | i, cur, b :: rest => by
    simp only [multiTextWalkTree, multiTextWalk, MultiLayout.blockLayout, withBitVec64_eq,
      nextViewWithLen_eq, toVecTree_getD_all _ _ hb, toVecTree_getD_all _ _ hrx,
      toVecTree_getD_all _ _ hb2b]
    cases nextView regions (mly.bases.getD i 0#64) cur with
    | none => rfl
    | some v =>
      rcases v with ⟨p, bs⟩
      dsimp only
      rw [walkTreeMulti_addrs_irrel (ML.blockLib b) (mly.bases.getD i 0#64) [] mly.addrs
        (mly.relax.getD i []) (mly.b2b.getD i []) mly.undefWeak b (toVecTree 0#64 mly.addrs)]
      rw [show ({ base := mly.bases.getD i 0#64, addrs := mly.addrs, relax := mly.relax.getD i [], b2b := mly.b2b.getD i [], undefWeak := mly.undefWeak } : Layout) = mly.blockLayout i from rfl]
      rw [walkTreeMulti_eq ML mly ha b i]
      rw [multiTextWalkTree_eq ML mly hb ha hrx hb2b regions (i + 1) _ rest]

def patchDataRelocTreeMulti (tAddr : VecTree (BitVec 64)) (addr : BitVec 64)
    (bytes : List (BitVec 8)) (r : Reloc) : List (BitVec 8) :=
  let t := addSignedAddr (tAddr.getD 0#64 r.sym) r.addend
  let put (n : Nat) (v : BitVec 64) := bytes.take r.off ++ bytesLE n v ++ bytes.drop (r.off + n)
  match r.kind with
  | .abs64 => put 8 t
  | .abs32 => put 4 t
  | .prel32 => put 4 (t - (addr + BitVec.ofNat 64 r.off))
  | _ => bytes

def patchedDataTreeMulti (tAddr : VecTree (BitVec 64)) (a : BitVec 64) (d : Data) : List (BitVec 8) :=
  d.relocs.foldl (patchDataRelocTreeMulti tAddr a) d.bytes ++
    List.replicate d.zeroTail 0#8

def dataWalkTreeMulti (tAddr : VecTree (BitVec 64)) (regsWithLen : List (Snapshot.Region × Nat)) :
    Option (BitVec 64 × Perm × List (BitVec 8)) → List Data → Bool
  | _, [] => true
  | cur, d :: ds =>
    withBitVec64 (tAddr.getD 0#64 d.sym) fun a =>
      match nextViewWithLen regsWithLen a cur with
      | some (p, bs) =>
        dataPermOk d.readOnly p && isPrefixOfFast (patchedDataTreeMulti tAddr a d) bs &&
          dataWalkTreeMulti tAddr regsWithLen (some (a, p, bs)) ds
      | none => false

theorem dataWalkTreeMulti_eq (ML : MultiLib) (mly : MultiLayout)
    (ha : mly.addrs.length < 2 ^ 20) (regions : List Snapshot.Region) :
    ∀ (cur : Option (BitVec 64 × Perm × List (BitVec 8))) (ds : List Data),
      dataWalkTreeMulti (toVecTree 0#64 mly.addrs)
        (regions.map (fun r => (r, r.bytes.length))) cur ds =
        dataWalk (ML.blockLib { code := [] }) mly.dataLayout regions cur ds
  | _, [] => rfl
  | cur, d :: ds => by
    have hpr : patchDataRelocTreeMulti (toVecTree 0#64 mly.addrs) =
        patchDataRelocId (ML.blockLib { code := [] }) mly.dataLayout := by
      funext addr bytes r
      simp only [patchDataRelocTreeMulti, patchDataRelocId, targetId, resolveId,
        MultiLib.blockLib, MultiLayout.dataLayout, toVecTree_getD_all _ _ ha]
      rfl
    have hpd : patchedDataTreeMulti (toVecTree 0#64 mly.addrs) (mly.addrs.getD d.sym 0#64) d =
        patchedDataId (ML.blockLib { code := [] }) mly.dataLayout d := by
      simp only [patchedDataTreeMulti, patchedDataId, MultiLayout.dataLayout, hpr]
    simp only [dataWalkTreeMulti, dataWalk, MultiLayout.dataLayout, withBitVec64_eq,
      nextViewWithLen_eq, isPrefixOfFast_eq, toVecTree_getD_all _ _ ha]
    cases nextView regions (mly.addrs.getD d.sym 0#64) cur with
    | none => rfl
    | some v =>
      rcases v with ⟨p, bs⟩
      dsimp only
      rw [hpd]
      rw [show ({ base := 0#64, addrs := mly.addrs } : Layout) = mly.dataLayout from rfl]
      rw [dataWalkTreeMulti_eq ML mly ha regions (some (mly.addrs.getD d.sym 0#64, p, bs)) ds]

def forceNatList {α : Type} : List Nat → (List Nat → α) → α
  | [], k => k []
  | x :: xs, k =>
    withNat x fun x' =>
      forceNatList xs fun xs' =>
        k (x' :: xs')

@[simp] theorem forceNatList_eq {α : Type} : ∀ (xs : List Nat) (k : List Nat → α),
    forceNatList xs k = k xs
  | [], _ => rfl
  | _ :: xs, k => by simp [forceNatList, withNat_eq, forceNatList_eq xs]

def withEncodeCharKey {α : Type} (cs : List Char) (k : (Nat × List Nat) → α) : α :=
  withNat cs.length fun len =>
    forceNatList (cs.map (·.val.toNat)) fun codes =>
      k (len, codes)

@[simp] theorem withEncodeCharKey_eq {α : Type} (cs : List Char) (k : (Nat × List Nat) → α) :
    withEncodeCharKey cs k = k (encodeCharKey cs) := by
  simp [withEncodeCharKey, encodeCharKey]

def buildEncSymTable {α : Type} :
    List (List Char × BitVec 64) → (EncSymTable (BitVec 64) → α) → α
  | [], k => k []
  | (cs, v) :: rest, k =>
    withEncodeCharKey cs fun key =>
      withBitVec64 v fun v' =>
        buildEncSymTable rest fun tail =>
          k ((key, v') :: tail)

@[simp] theorem buildEncSymTable_eq {α : Type} :
    ∀ (symChars : List (List Char × BitVec 64)) (k : EncSymTable (BitVec 64) → α),
      buildEncSymTable symChars k = k (prepareCharAssocVal symChars)
  | [], _ => rfl
  | _ :: rest, k => by
    simp [buildEncSymTable, prepareCharAssocVal, buildEncSymTable_eq rest]

def multiExportsOkTree (ML : MultiLib) (tBase : VecTree (BitVec 64))
    (tSym : VecTree (Option (Nat × Nat))) (tNameChars : VecTree (List Char))
    (enc : EncSymTable (BitVec 64)) : Bool :=
  ML.exportSyms.all (fun p => Nat.blt p.1 ML.names.length) &&
  ML.exports.all fun e =>
    match tSym.getD none e with
    | some (i, off) =>
      withEncodeCharKey (tNameChars.getD [] ((lookupId e ML.exportSyms).getD e)) fun key =>
        match lookupUniqueEnc key enc with
        | some a => a == tBase.getD 0#64 i + BitVec.ofNat 64 off
        | none => false
    | none => false

theorem multiExportsOkTree_eq (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (enc : EncSymTable (BitVec 64)) (tSym : VecTree (Option (Nat × Nat)))
    (hb : mly.bases.length < 2 ^ 20) (hnc : nameChars.length < 2 ^ 20)
    (hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks) :
    multiExportsOkTree ML (toVecTree 0#64 mly.bases) tSym (toVecTree [] nameChars) enc =
      multiExportsOk ML mly nameChars enc := by
  unfold multiExportsOkTree multiExportsOk
  congr 1
  congr 1
  funext e
  rw [hlookup e, toVecTree_getD_all _ _ hnc]
  cases lookupBlockSymId e ML.blocks with
  | none => rfl
  | some p =>
    rcases p with ⟨i, off⟩
    simp only [withEncodeCharKey_eq, toVecTree_getD_all _ _ hb]
    rfl

def dataEntriesDisjointFastAux (rw : List (Bool × BitVec 64 × Nat)) :
    List (Bool × BitVec 64 × Nat) → Bool
  | [] => true
  | (ro1, a1, n1) :: rest =>
    Nat.ble (a1.toNat + n1) 18446744073709551616 &&
    (if ro1 then
      rw.all (fun (_, a2, n2) => checkRangesDisjoint a1.toNat n1 a2.toNat n2)
    else
      rest.all (fun (_, a2, n2) => checkRangesDisjoint a1.toNat n1 a2.toNat n2)) &&
    dataEntriesDisjointFastAux rw rest

theorem dataEntriesDisjointFastAux_imp {rw : List (Bool × BitVec 64 × Nat)} :
    ∀ {ds : List (Bool × BitVec 64 × Nat)},
      (∀ y ∈ ds, y.1 = false → y ∈ rw) →
      dataEntriesDisjointFastAux rw ds = true →
      dataEntriesDisjointB ds = true
  | [], _, _ => rfl
  | (ro1, a1, n1) :: rest, hrw, h => by
    simp only [dataEntriesDisjointFastAux, dataEntriesDisjointB, Bool.and_eq_true,
      List.all_eq_true] at h ⊢
    obtain ⟨⟨hb1, hchk⟩, hrest⟩ := h
    refine ⟨⟨hb1, fun ⟨ro2, a2, n2⟩ hy => ?_⟩,
      dataEntriesDisjointFastAux_imp (fun y hy' => hrw y (List.mem_cons_of_mem _ hy')) hrest⟩
    cases ro1
    · simp only [Bool.false_eq_true, ↓reduceIte, List.all_eq_true] at hchk
      simp [hchk (ro2, a2, n2) hy]
    · simp only [↓reduceIte, List.all_eq_true] at hchk
      cases ro2
      · have hmem_rw := hrw (false, a2, n2) (List.mem_cons_of_mem _ hy) rfl
        simp [hchk (false, a2, n2) hmem_rw]
      · simp

def buildDisjointLists (tAddr : VecTree (BitVec 64)) :
    List Data →
    (List (Bool × BitVec 64 × Nat) → List (Bool × BitVec 64 × Nat) → Bool) → Bool
  | [], k => k [] []
  | d :: rest, k =>
    withBitVec64 (tAddr.getD 0#64 d.sym) fun a =>
      withNat (fastLen512 4096 d.bytes + d.zeroTail) fun len =>
        buildDisjointLists tAddr rest fun rw ds =>
          let entry := (d.readOnly, a, len)
          if d.readOnly then
            k rw (entry :: ds)
          else
            k (entry :: rw) (entry :: ds)

theorem buildDisjointLists_eq (tAddr : VecTree (BitVec 64)) :
    ∀ (data : List Data)
      (k : List (Bool × BitVec 64 × Nat) → List (Bool × BitVec 64 × Nat) → Bool),
      buildDisjointLists tAddr data k =
        let ds := data.map fun d => (d.readOnly, tAddr.getD 0#64 d.sym, d.bytes.length + d.zeroTail)
        k (ds.filter fun x => !x.1) ds
  | [], _ => rfl
  | d :: rest, k => by
    simp only [buildDisjointLists, withBitVec64_eq, withNat_eq, fastLen512_eq_length,
      buildDisjointLists_eq tAddr rest, List.map_cons, List.filter_cons]
    cases d.readOnly <;> rfl

def multiDataDisjointTree (ML : MultiLib) (tAddr : VecTree (BitVec 64)) : Bool :=
  buildDisjointLists tAddr ML.data dataEntriesDisjointFastAux

theorem multiDataDisjointTree_imp {ML : MultiLib} {mly : MultiLayout}
    (ha : mly.addrs.length < 2 ^ 20)
    (h : multiDataDisjointTree ML (toVecTree 0#64 mly.addrs) = true) :
    multiDataDisjointB ML mly = true := by
  simp only [multiDataDisjointTree, buildDisjointLists_eq, toVecTree_getD_all _ _ ha] at h
  exact dataEntriesDisjointFastAux_imp
    (fun y hy hfalse => List.mem_filter.2 ⟨hy, by simp [hfalse]⟩) h

/-- Combined tree-accelerated checker for `MultiPlacedLib.Placeable`, `InElf`, and `DataDisjoint`. -/
def checkMultiFastB (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (img : ElfImage) (enc : EncSymTable (BitVec 64)) : Bool :=
  Nat.blt mly.bases.length 1048576 &&
  Nat.blt mly.addrs.length 1048576 &&
  Nat.blt mly.relax.length 1048576 &&
  Nat.blt mly.b2b.length 1048576 &&
  Nat.blt nameChars.length 1048576 &&
  namesNodup nameChars &&
  multiIdsOkFast ML &&
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree 0#64 mly.addrs fun tAddr =>
  withVecTree [] mly.relax fun tRelax =>
  withVecTree [] mly.b2b fun tB2b =>
  withVecTree [] nameChars fun tNameChars =>
  withRegionsWithLen img.segments fun regsWithLen =>
  withNat ML.names.length fun nNames =>
  match insertAllBlocks 0 ML.blocks (mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => false
    | some _ =>
      blockSymsMatchTree ML tBase tAddr &&
      textPlaceableTreeMulti ML tBase tAddr &&
      rangesSorted (blockRanges tBase 0 ML.blocks) &&
      dataPlaceableTreeMulti ML tAddr &&
      multiTextWalkTree ML tBase tAddr tRelax tB2b mly.undefWeak regsWithLen 0 none ML.blocks &&
      dataWalkTreeMulti tAddr regsWithLen none ML.data &&
      multiExportsOkTree ML tBase tSym tNameChars enc &&
      multiDataDisjointTree ML tAddr

theorem checkMultiFastB_spec {ML : MultiLib} {mly : MultiLayout} {nameChars : List (List Char)}
    {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (h : checkMultiFastB ML mly nameChars img (prepareCharAssocVal symChars) = true) :
    let lib := ML.toMultiPlacedLib
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  unfold checkMultiFastB at h
  simp only [withVecTree_eq, withRegionsWithLen_eq, withNat_eq, multiIdsOkFast_eq,
    Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := h
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest
    dsimp only at hrest
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdp⟩, htwalk⟩, hdwalk⟩, hexp⟩, hddisj⟩ := hrest
      obtain ⟨hnd_syms, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
      obtain ⟨hnd_data_raw, hnone_data_raw, _⟩ :=
        insertBlockSyms_spec 0 (ML.data.map fun d => (d.sym, 0)) tSym tSymData hdsym
      have hmap_data : ((ML.data.map fun d => (d.sym, 0)).map (·.1)) = ML.data.map (·.sym) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_data] at hnd_data_raw hnone_data_raw
      have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
        intro q
        rw [hget_sym q, getD_mkNoneTree]
        rfl
      rw [blockSymsMatchTree_eq ML mly hb ha] at hmatch
      rw [textPlaceableTreeMulti_eq ML mly hb ha] at htp
      have hdisj' := blocksDisjoint_of_rangesSorted hb hdisj
      have hnd_b : natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) = true := by
        simp [natNodupFast, natNodup_of_nodup hnd_syms]
      have hdp' := dataPlaceableTreeMulti_imp ML mly ha hnd_data_raw hdp
      have hdnone' : (ML.data.all fun d => (lookupBlockSymId d.sym ML.blocks).isNone) = true := by
        rw [List.all_eq_true]
        intro d hd
        have hnone := hnone_data_raw d.sym (List.mem_map_of_mem hd)
        rw [hlookup d.sym] at hnone
        simp [hnone]
      rw [multiTextWalkTree_eq ML mly hb ha hrx hb2b] at htwalk
      rw [dataWalkTreeMulti_eq ML mly ha] at hdwalk
      rw [multiExportsOkTree_eq ML mly nameChars _ tSym hb hnc hlookup] at hexp
      have hddisj' := multiDataDisjointTree_imp ha hddisj
      have hmp : multiPlaceableB ML mly = true := by
        simp only [multiPlaceableB, Bool.and_eq_true]
        exact ⟨⟨⟨⟨htp, (Bool.or_eq_true _ _).mpr (Or.inr hdisj')⟩, hnd_b⟩, hdp'⟩, hdnone'⟩
      apply checkMultiDisjoint_spec hnames hsyms
      simp only [checkMultiDisjoint, checkMulti, Bool.and_eq_true]
      exact ⟨⟨⟨⟨⟨⟨⟨hnn, hids⟩, hmatch⟩, hmp⟩, htwalk⟩, hdwalk⟩, hexp⟩, hddisj'⟩

/-- Metadata, `Placeable`, exports, and `DataDisjoint` checker factored out from ELF segment byte
walks so each walk can be checked in a separate `rfl_kernel` declaration. -/
def checkMultiMetaFastB (ML : MultiLib) (mly : MultiLayout) (nameChars : List (List Char))
    (symChars : List (List Char × BitVec 64)) : Bool :=
  Nat.blt mly.bases.length 1048576 &&
  Nat.blt mly.addrs.length 1048576 &&
  Nat.blt mly.relax.length 1048576 &&
  Nat.blt mly.b2b.length 1048576 &&
  Nat.blt nameChars.length 1048576 &&
  namesNodup nameChars &&
  multiIdsOkFast ML &&
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree 0#64 mly.addrs fun tAddr =>
  withVecTree [] nameChars fun tNameChars =>
  buildEncSymTable symChars fun enc =>
  withNat ML.names.length fun nNames =>
  match insertAllBlocks 0 ML.blocks (mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => false
    | some _ =>
      blockSymsMatchTree ML tBase tAddr &&
      textPlaceableTreeMulti ML tBase tAddr &&
      rangesSorted (blockRanges tBase 0 ML.blocks) &&
      dataPlaceableTreeMulti ML tAddr &&
      multiExportsOkTree ML tBase tSym tNameChars enc &&
      multiDataDisjointTree ML tAddr

def checkMultiMetaCoreFastB (ML : MultiLib) (mly : MultiLayout)
    (nameChars : List (List Char)) : Bool :=
  Nat.blt mly.bases.length 1048576 &&
  Nat.blt mly.addrs.length 1048576 &&
  Nat.blt mly.relax.length 1048576 &&
  Nat.blt mly.b2b.length 1048576 &&
  Nat.blt nameChars.length 1048576 &&
  namesNodup nameChars &&
  multiIdsOkFast ML &&
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree 0#64 mly.addrs fun tAddr =>
  withNat ML.names.length fun nNames =>
  match insertAllBlocks 0 ML.blocks (mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => false
    | some _ =>
      blockSymsMatchTree ML tBase tAddr &&
      textPlaceableTreeMulti ML tBase tAddr &&
      rangesSorted (blockRanges tBase 0 ML.blocks)

def checkMultiMetaDataFastB (ML : MultiLib) (mly : MultiLayout) : Bool :=
  withVecTree 0#64 mly.addrs fun tAddr =>
    dataPlaceableTreeMulti ML tAddr &&
    multiDataDisjointTree ML tAddr

def checkMultiMetaExportsFastB (ML : MultiLib) (mly : MultiLayout)
    (nameChars : List (List Char)) (symChars : List (List Char × BitVec 64)) : Bool :=
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree [] nameChars fun tNameChars =>
  buildEncSymTable symChars fun enc =>
  withNat ML.names.length fun nNames =>
  match insertAllBlocks 0 ML.blocks (mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    multiExportsOkTree ML tBase tSym tNameChars enc

theorem checkMultiMetaFastB_of_parts {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {symChars : List (List Char × BitVec 64)}
    (hcore : checkMultiMetaCoreFastB ML mly nameChars = true)
    (hdata : checkMultiMetaDataFastB ML mly = true)
    (hexp : checkMultiMetaExportsFastB ML mly nameChars symChars = true) :
    checkMultiMetaFastB ML mly nameChars symChars = true := by
  unfold checkMultiMetaFastB
  unfold checkMultiMetaCoreFastB at hcore
  unfold checkMultiMetaDataFastB at hdata
  unfold checkMultiMetaExportsFastB at hexp
  simp only [withVecTree_eq, buildEncSymTable_eq, withNat_eq, Bool.and_eq_true] at hcore hdata hexp ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hcore
  refine ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, ?_⟩
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest hexp
    dsimp only at hrest hexp ⊢
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest ⊢
      simp only [Bool.and_eq_true] at hrest ⊢
      obtain ⟨⟨hmatch, htp⟩, hdisj⟩ := hrest
      exact ⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdata.1⟩, hexp⟩, hdata.2⟩

def checkMultiDataWalkFastB (ML : MultiLib) (mly : MultiLayout) (img : ElfImage) : Bool :=
  withVecTree 0#64 mly.addrs fun tAddr =>
  withRegionsWithLen img.segments fun regsWithLen =>
    dataWalkTreeMulti tAddr regsWithLen none ML.data

def checkMultiTextWalkFastB (ML : MultiLib) (mly : MultiLayout) (img : ElfImage) : Bool :=
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree 0#64 mly.addrs fun tAddr =>
  withVecTree [] mly.relax fun tRelax =>
  withVecTree [] mly.b2b fun tB2b =>
  withRegionsWithLen img.segments fun regsWithLen =>
    multiTextWalkTree ML tBase tAddr tRelax tB2b mly.undefWeak regsWithLen 0 none ML.blocks

theorem checkMultiSplit_spec {lib : MultiPlacedLib} {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hmeta : checkMultiMetaFastB ML mly nameChars symChars = true)
    (hdwalk : checkMultiDataWalkFastB ML mly img = true)
    (htwalk : checkMultiTextWalkFastB ML mly img = true) :
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  subst hlib
  apply checkMultiFastB_spec hnames hsyms
  unfold checkMultiFastB
  unfold checkMultiMetaFastB at hmeta
  unfold checkMultiDataWalkFastB at hdwalk
  unfold checkMultiTextWalkFastB at htwalk
  simp only [withVecTree_eq, withRegionsWithLen_eq, buildEncSymTable_eq, withNat_eq,
    Bool.and_eq_true] at hmeta hdwalk htwalk ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hmeta
  refine ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, ?_⟩
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest
    dsimp only at hrest ⊢
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest ⊢
      simp only [Bool.and_eq_true] at hrest ⊢
      obtain ⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdp⟩, hexp⟩, hddisj⟩ := hrest
      exact ⟨⟨⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdp⟩, htwalk⟩, hdwalk⟩, hexp⟩, hddisj⟩

/-- `.text` segment walk restricted to block slice `[start, start + count)`. -/
def checkMultiTextSliceB (ML : MultiLib) (mly : MultiLayout) (img : ElfImage)
    (start count : Nat) : Bool :=
  withVecTree 0#64 mly.bases fun tBase =>
  withVecTree 0#64 mly.addrs fun tAddr =>
  withVecTree [] mly.relax fun tRelax =>
  withVecTree [] mly.b2b fun tB2b =>
  withRegionsWithLen img.segments fun regsWithLen =>
    multiTextWalkTree ML tBase tAddr tRelax tB2b mly.undefWeak regsWithLen
      start none ((ML.blocks.drop start).take count)

def BlockTextWalkOk (ML : MultiLib) (mly : MultiLayout) (regions : List Snapshot.Region)
    (i : Nat) (hi : i < ML.blocks.length) : Prop :=
  (∃ p bs, View regions (mly.blockLayout i).base p bs ∧ p = Perm.rx ∧
    ((ML.blockLib ML.blocks[i]).block.patched
      ((mly.blockLayout i).toPlacement ML.names)).IsPrefix bs) ∧
  WalkOk (ML.blockLib ML.blocks[i]) (mly.blockLayout i) 0 ML.blocks[i].relocs
    ((ML.blockLib ML.blocks[i]).block.patched
      ((mly.blockLayout i).toPlacement ML.names) ++ [])

theorem checkMultiTextSliceB_sound {ML : MultiLib} {mly : MultiLayout} {img : ElfImage}
    {start count : Nat}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20)
    (hrx : mly.relax.length < 2 ^ 20) (hb2b : mly.b2b.length < 2 ^ 20)
    (hs : checkMultiTextSliceB ML mly img start count = true)
    {i : Nat} (hlo : start ≤ i) (hhi : i < start + count) (hi : i < ML.blocks.length) :
    BlockTextWalkOk ML mly img.segments i hi := by
  unfold checkMultiTextSliceB at hs
  simp only [withVecTree_eq, withRegionsWithLen_eq] at hs
  rw [multiTextWalkTree_eq ML mly hb ha hrx hb2b] at hs
  have hmem : ∀ b ∈ (ML.blocks.drop start).take count, b ∈ ML.blocks :=
    fun _ hb' => List.mem_of_mem_drop (List.mem_of_mem_take hb')
  have hwf' : ∀ b ∈ (ML.blocks.drop start).take count, relocsWf b.code.length 0 b.relocs = true :=
    fun b hb' => hwf b (hmem b hb')
  have hsound := multiTextWalk_sound (mly := mly) hnd hids start none
    ((ML.blocks.drop start).take count) hmem hwf' (fun _ _ _ hc => nomatch hc) hs
  have hj : i - start < ((ML.blocks.drop start).take count).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hstep := hsound (i - start) hj
  have hidx : start + (i - start) = i := Nat.add_sub_of_le hlo
  have hget : ((ML.blocks.drop start).take count)[i - start] = ML.blocks[i] := by
    simp only [List.getElem_take, List.getElem_drop, hidx]
  simpa only [BlockTextWalkOk, hidx, hget] using hstep

/-- Inductive accumulator of `checkMultiTextSliceB` certificates over `[0, bound)`. -/
inductive SlicesTextOk (ML : MultiLib) (mly : MultiLayout) (img : ElfImage) (count : Nat) :
    Nat → Prop
  | zero : SlicesTextOk ML mly img count 0
  | step {endIdx : Nat} :
      SlicesTextOk ML mly img count endIdx →
      checkMultiTextSliceB ML mly img endIdx count = true →
      SlicesTextOk ML mly img count (endIdx + count)

theorem slicesTextOk_sound {ML : MultiLib} {mly : MultiLayout} {img : ElfImage}
    {count bound : Nat}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true)
    (hb : mly.bases.length < 2 ^ 20) (ha : mly.addrs.length < 2 ^ 20)
    (hrx : mly.relax.length < 2 ^ 20) (hb2b : mly.b2b.length < 2 ^ 20)
    (hs : SlicesTextOk ML mly img count bound) :
    ∀ (i : Nat) (hi : i < ML.blocks.length), i < bound →
      BlockTextWalkOk ML mly img.segments i hi := by
  induction hs with
  | zero => intro _ _ hlt; nomatch hlt
  | @step endIdx _ hslice ih =>
    intro i hi hlt
    by_cases hlt' : i < endIdx
    · exact ih i hi hlt'
    · exact checkMultiTextSliceB_sound hnd hids hwf hb ha hrx hb2b hslice
        (by omega) hlt hi

theorem checkMultiSliced_spec {lib : MultiPlacedLib} {ML : MultiLib} {mly : MultiLayout}
    {nameChars : List (List Char)} {img : ElfImage} {symChars : List (List Char × BitVec 64)}
    {count bound : Nat}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hsyms : img.symbols = toStringAssoc symChars)
    (hmeta : checkMultiMetaFastB ML mly nameChars symChars = true)
    (hdwalk : checkMultiDataWalkFastB ML mly img = true)
    (hbound : Nat.ble ML.blocks.length bound = true)
    (hslices : SlicesTextOk ML mly img count bound) :
    let mpl := mly.toMultiPlacement ML.names
    lib.Placeable mpl ∧ lib.InElf img mpl ∧ lib.DataDisjoint mpl := by
  subst hlib
  unfold checkMultiMetaFastB at hmeta
  unfold checkMultiDataWalkFastB at hdwalk
  simp only [withVecTree_eq, withRegionsWithLen_eq, buildEncSymTable_eq, withNat_eq,
    multiIdsOkFast_eq, Bool.and_eq_true, Nat.blt_eq] at hmeta hdwalk
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, ha⟩, hrx⟩, hb2b⟩, hnc⟩, hnn⟩, hids⟩, hrest⟩ := hmeta
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest
    dsimp only at hrest
    cases hdsym : insertBlockSyms 0 (ML.data.map fun d => (d.sym, 0)) tSym with
    | none => rw [hdsym] at hrest; nomatch hrest
    | some tSymData =>
      rw [hdsym] at hrest
      dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨⟨⟨⟨⟨hmatch, htp⟩, hdisj⟩, hdp⟩, hexp⟩, hddisj⟩ := hrest
      obtain ⟨hnd_syms, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
      obtain ⟨hnd_data_raw, hnone_data_raw, _⟩ :=
        insertBlockSyms_spec 0 (ML.data.map fun d => (d.sym, 0)) tSym tSymData hdsym
      have hmap_data : ((ML.data.map fun d => (d.sym, 0)).map (·.1)) = ML.data.map (·.sym) := by
        simp [List.map_map, Function.comp_def]
      rw [hmap_data] at hnd_data_raw hnone_data_raw
      have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
        intro q
        rw [hget_sym q, getD_mkNoneTree]
        rfl
      rw [blockSymsMatchTree_eq ML mly hb ha] at hmatch
      rw [textPlaceableTreeMulti_eq ML mly hb ha] at htp
      have hdisj' := blocksDisjoint_of_rangesSorted hb hdisj
      have hnd_b : natNodupFast ((ML.blocks.flatMap (·.symbols)).map (·.1)) = true := by
        simp [natNodupFast, natNodup_of_nodup hnd_syms]
      have hdp' := dataPlaceableTreeMulti_imp ML mly ha hnd_data_raw hdp
      have hd_none : ∀ d ∈ ML.data, (lookupBlockSymId d.sym ML.blocks).isNone = true := by
        intro d hd
        have hnone := hnone_data_raw d.sym (List.mem_map_of_mem hd)
        rw [hlookup d.sym] at hnone
        simp [hnone]
      rw [dataWalkTreeMulti_eq ML mly ha] at hdwalk
      rw [multiExportsOkTree_eq ML mly nameChars _ tSym hb hnc hlookup] at hexp
      have hddisj' := multiDataDisjointTree_imp ha hddisj
      have hnd := nodup_of_namesNodup hnames hnn
      have hok0 := ML.emptyBlock_idsOk hids
      have hwf : ∀ b ∈ ML.blocks, relocsWf b.code.length 0 b.relocs = true := by
        intro b hbm
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hbm
        have hti := allIdx_spec htp i hi
        rw [Nat.zero_add] at hti
        simp only [textPlaceableB, Bool.and_eq_true] at hti
        exact hti.1.1.2
      have hlen_le : ML.blocks.length ≤ bound := by rwa [Nat.ble_eq] at hbound
      have hwalk : ∀ (i : Nat) (hi : i < ML.blocks.length),
          BlockTextWalkOk ML mly img.segments i hi :=
        fun i hi => slicesTextOk_sound hnd hids hwf hb ha hrx hb2b hslices i hi
          (Nat.lt_of_lt_of_le hi hlen_le)
      have htp0 : textPlaceableB (ML.blockLib { code := [] }) mly.dataLayout = true := by
        dsimp only [textPlaceableB, MultiLib.blockLib, MultiLayout.dataLayout, relocsWf, List.all]
        decide
      have hwalk0 : WalkOk (ML.blockLib { code := [] }) mly.dataLayout 0 [] [] := by
        refine ⟨?_, ?_, ?_⟩
        · simp [MultiLib.blockLib, CodeBlock.patched]
        · intro _ hr; nomatch hr
        · intro _ _ _ _ hr; nomatch hr
      have hpl0 := placeable_of hnd hok0 htp0 hdp' hwalk0
      have hbp_eq : ∀ i, ML.toMultiPlacedLib.blockPlacement (mly.toMultiPlacement ML.names) i =
          (mly.blockLayout i).toPlacement ML.names :=
        toMultiPlacement_blockPlacement_eq hnd hids hmatch
      have hres_eq : ∀ s, ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) s =
          (mly.dataLayout.toPlacement ML.names).ρ s :=
        toMultiPlacement_resolve_eq hnd hids hmatch
      have hpl : ML.toMultiPlacedLib.Placeable (mly.toMultiPlacement ML.names) := by
        refine ⟨?_, ?_, ?_, hpl0.data_nodup, ?_, ?_⟩
        · intro i hi
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
          rw [hbp_eq i, ← MultiLib.blockLib_block]
          have hti := allIdx_spec htp i hi
          rw [Nat.zero_add] at hti
          have ⟨_, hw⟩ := hwalk i hi
          exact textPlaceable_of hnd (ML.blockLib_idsOk hids (List.getElem_mem hi)) hti hw
        · intro i j hi hj hij
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi hj ⊢
          have h1 := allIdx_spec hdisj' i hi
          rw [Nat.zero_add] at h1
          have h2 := allIdx_spec h1 j hj
          rw [Nat.zero_add] at h2
          simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Nat.blt_eq] at h2
          rcases h2 with hnot | hok
          · exact absurd hij hnot
          · exact rangesDisjoint_of_check hok
        · rw [MultiLib.toMultiPlacedLib_blocks, flatMap_toCodeBlock_symbols_fst]
          have hn := natNodupFast_spec hnd_b
          rw [List.nodup_iff_pairwise_ne] at hn ⊢
          rw [List.pairwise_map]
          refine hn.imp_of_mem fun {x y} hx hy hxy heq => hxy ?_
          exact getD_inj hnd (mem_flatMap_symbols_lt hids hx) (mem_flatMap_symbols_lt hids hy) heq
        · intro d hd
          have hdo := hpl0.data_ok d hd
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
          obtain ⟨d', hd', rfl⟩ := hd
          have hdi := (hok0.data d' hd').1
          have hln : lookupBlockSym (Data.toInfo ML.names d').sym ML.toMultiPlacedLib.blocks = none := by
            show lookupBlockSym (ML.names.getD d'.sym "") ML.toMultiPlacedLib.blocks = none
            rw [lookupBlockSym_toMultiPlacedLib hnd hids hdi]
            exact Option.isNone_iff_eq_none.1 (hd_none d' hd')
          exact ⟨hln, hdo.2⟩
        · intro d hd r hr
          have hdro := hpl0.data_relocs_ok d hd r hr
          have hres0 : (Block.toCodeBlock ML.names { code := [] }).resolve
              (mly.dataLayout.toPlacement ML.names) r.sym =
              ML.toMultiPlacedLib.resolve (mly.toMultiPlacement ML.names) r.sym := by
            rw [hres_eq r.sym]
            rfl
          have hρ0 : (mly.dataLayout.toPlacement ML.names).ρ d.sym =
              (mly.toMultiPlacement ML.names).ρ d.sym := rfl
          simpa only [Lib.toLib_text, MultiLib.blockLib_block, MultiLib.blockLib_names, hres0, hρ0]
            using hdro
      have hin : ML.toMultiPlacedLib.InElf img (mly.toMultiPlacement ML.names) := by
        refine ⟨?_, ?_, ?_⟩
        · intro i hi
          simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map, List.getElem_map] at hi ⊢
          rw [hbp_eq i, ← MultiLib.blockLib_block]
          have ⟨⟨p, bs, hv, hp, hpre⟩, _⟩ := hwalk i hi
          exact elfMaps_of_view (hv.of_prefix hpre) (by simp [hp])
        · intro d hd
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at hd
          obtain ⟨d', hd', rfl⟩ := hd
          obtain ⟨p, hv, hp⟩ := dataWalk_sound none ML.data (fun _ _ _ hc => nomatch hc) hdwalk d' hd'
          have hi := (hok0.data d' hd').1
          have hρ : (mly.toMultiPlacement ML.names).ρ (Data.toInfo ML.names d').sym =
              mly.dataLayout.addrs.getD d'.sym 0#64 :=
            toPlacement_ρ (ly := mly.dataLayout) hnd hi
          have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
              (Data.toInfo ML.names d') =
              patchedDataId (ML.blockLib { code := [] }) mly.dataLayout d' := by
            rw [← patchedData_toLib (L := ML.blockLib { code := [] }) (ly := mly.dataLayout)
              hnd hok0 hd']
            have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
                (ML.blockLib { code := [] }).toLib.patchDataReloc
                  (mly.dataLayout.toPlacement ML.names) := by
              funext addr bytes r
              simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
              rfl
            simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
            rfl
          rw [show (Data.toInfo ML.names d').readOnly = d'.readOnly from rfl, hρ, hpd]
          exact elfMaps_of_view hv hp
        · intro e he
          simp only [MultiLib.toMultiPlacedLib, List.mem_map] at he
          obtain ⟨e', he', rfl⟩ := he
          have he_lt : e' < ML.names.length := by
            simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at hids
            exact hids.1.2 e' he'
          simp only [multiExportsOk, Bool.and_eq_true] at hexp
          obtain ⟨hesb, hexp⟩ := hexp
          have hes : ∀ p ∈ ML.exportSyms, p.1 < ML.names.length := fun p hp =>
            blt_iff.1 (List.all_eq_true.1 hesb p hp)
          have helf : ML.toMultiPlacedLib.elfSym (ML.names.getD e' "") =
              ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" := by
            have hmap : ∀ xs : List (Nat × Nat),
                lookupId e' (xs.map fun p => (p.1, ML.names.getD p.2 "")) =
                  (lookupId e' xs).map fun j => ML.names.getD j "" := by
              intro xs
              induction xs with
              | nil => rfl
              | cons p rest ih =>
                simp only [List.map_cons, lookupId]
                cases Nat.beq p.1 e'
                · simpa using ih
                · rfl
            have hl := lookup_map_getD hnd he_lt
              (ML.exportSyms.map fun p => (p.1, ML.names.getD p.2 ""))
              (fun p hp => by
                obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
                exact hes q hq)
            rw [List.map_map] at hl
            show (lookup (ML.names.getD e' "")
                (ML.exportSyms.map fun p => (ML.names.getD p.1 "", ML.names.getD p.2 ""))).getD
                  (ML.names.getD e' "") = _
            rw [show (fun p : Nat × Nat => (ML.names.getD p.1 "", ML.names.getD p.2 "")) =
                ((fun s : Nat × String => (ML.names.getD s.1 "", s.2)) ∘
                  fun p => (p.1, ML.names.getD p.2 "")) from rfl, hl, hmap]
            cases lookupId e' ML.exportSyms <;> rfl
          have hex := List.all_eq_true.1 hexp e' he'
          split at hex
          · rename_i i off hblk
            split at hex
            · rename_i a ha_enc
              rw [beq_iff_eq] at hex
              subst hex
              refine ⟨i, off, ?_, ?_⟩
              · rw [lookupBlockSym_toMultiPlacedLib hnd hids he_lt, hblk]
              · have hng : ML.names.getD ((lookupId e' ML.exportSyms).getD e') "" =
                    String.ofList (nameChars.getD ((lookupId e' ML.exportSyms).getD e') []) :=
                  names_getD (L := ML.blockLib { code := [] }) hnames _
                rw [helf, lookupUnique_eq_lookupUniqueEnc hsyms rfl hng, ha_enc]
                rfl
            · cases hex
          · cases hex
      refine ⟨hpl, hin, ?_⟩
      have ⟨_, hpw⟩ := dataEntriesDisjointB_pairwise hddisj'
      have heq : (ML.toMultiPlacedLib.data.map fun d =>
          (d.readOnly, (mly.toMultiPlacement ML.names).ρ d.sym,
            (ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names) d).length)) =
          ML.data.map fun d =>
            (d.readOnly, mly.addrs.getD d.sym 0#64, d.bytes.length + d.zeroTail) := by
        simp only [MultiLib.toMultiPlacedLib_data, List.map_map]
        refine List.map_congr_left fun d hd => ?_
        have hdi : d.toInfo ML.names ∈ ML.toMultiPlacedLib.data := by
          simp only [MultiLib.toMultiPlacedLib_data]; exact List.mem_map_of_mem hd
        simp only [Function.comp_apply, Prod.mk.injEq]
        refine ⟨rfl, toPlacement_ρ (ly := mly.dataLayout) hnd (hok0.data d hd).1, ?_⟩
        have hpr : ML.toMultiPlacedLib.patchDataReloc (mly.toMultiPlacement ML.names) =
            (ML.blockLib { code := [] }).toLib.patchDataReloc
              (mly.dataLayout.toPlacement ML.names) := by
          funext addr bytes r
          simp only [MultiPlacedLib.patchDataReloc, PlacedLib.patchDataReloc, hres_eq]
          rfl
        have hpd : ML.toMultiPlacedLib.patchedData (mly.toMultiPlacement ML.names)
            (d.toInfo ML.names) =
            (ML.blockLib { code := [] }).toLib.patchedData
              (mly.dataLayout.toPlacement ML.names) (d.toInfo ML.names) := by
          simp only [MultiPlacedLib.patchedData, PlacedLib.patchedData, hpr]
          rfl
        rw [hpd, PlacedLib.length_patchedData fun r hr => (hpl.data_relocs_ok _ hdi r hr).2.1]
        rfl
      rw [← heq, List.pairwise_map] at hpw
      exact hpw

/-! ## Relocation-Inversion DAG Checker -/

theorem elfMaps_eq_of_eq_addr {img : ElfImage} {addr : BitVec 64} {bs₁ bs₂ : List (BitVec 8)}
    {ok₁ ok₂ : Perm → Bool}
    (h₁ : ElfMaps img addr bs₁ ok₁) (h₂ : ElfMaps img addr bs₂ ok₂)
    (hlen : bs₁.length = bs₂.length) :
    bs₁ = bs₂ := by
  refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
  obtain ⟨_, hc₁, _⟩ := h₁ i hi₁
  obtain ⟨_, hc₂, _⟩ := h₂ i hi₂
  rw [hc₁] at hc₂
  injection hc₂ with hc₂
  injection hc₂

theorem wordOfBytesLE_bytesOfWordLE (w : BitVec 32) :
    wordOfBytesLE (bytesOfWordLE w) 0 = w := by
  have h : wordOfBytesLE (bytesOfWordLE w) 0 =
    (((w.zeroExtend 64 >>> 0).truncate 8).zeroExtend 32) |||
    (((w.zeroExtend 64 >>> 8).truncate 8).zeroExtend 32 <<< 8) |||
    (((w.zeroExtend 64 >>> 16).truncate 8).zeroExtend 32 <<< 16) |||
    (((w.zeroExtend 64 >>> 24).truncate 8).zeroExtend 32 <<< 24) := rfl
  rw [h]
  bv_bits

theorem bytesOfWordLE_inj {w₁ w₂ : BitVec 32} (h : bytesOfWordLE w₁ = bytesOfWordLE w₂) :
    w₁ = w₂ := by
  have := congrArg (fun bs => wordOfBytesLE bs 0) h
  simpa only [wordOfBytesLE_bytesOfWordLE] using this

theorem patchedWord_eq_of_inElf_eq_base {lib : MultiPlacedLib} {mpl mpl₀ : MultiPlacement}
    {img : ElfImage} {bi off : Nat} (hbi : bi < lib.blocks.length)
    (hin : lib.InElf img mpl) (hin₀ : lib.InElf img mpl₀)
    (hbase : mpl.base bi = mpl₀.base bi)
    (hal : off % 4 = 0) (hlen : off + 4 ≤ lib.blocks[bi].code.length) :
    lib.blocks[bi].patchedWord (lib.blockPlacement mpl bi) off =
      lib.blocks[bi].patchedWord (lib.blockPlacement mpl₀ bi) off := by
  have h1 := hin.blocks bi hbi
  have h2 := hin₀.blocks bi hbi
  rw [← hbase] at h2
  have hlen_p : (lib.blocks[bi].patched (lib.blockPlacement mpl bi)).length =
      (lib.blocks[bi].patched (lib.blockPlacement mpl₀ bi)).length := by
    rw [CodeBlock.length_patched, CodeBlock.length_patched]
  have hp := elfMaps_eq_of_eq_addr h1 h2 hlen_p
  have ht := congrArg (fun bs => (bs.drop off).take 4) hp
  rw [CodeBlock.take4_drop_patched hal hlen, CodeBlock.take4_drop_patched hal hlen] at ht
  exact bytesOfWordLE_inj ht

theorem length_patchedData_multi {lib : MultiPlacedLib} {mpl : MultiPlacement} {d : SymDataInfo}
    (h : ∀ r ∈ d.relocs, r.off + dataRelocWidth r.kind ≤ d.bytes.length) :
    (lib.patchedData mpl d).length = d.bytes.length + d.zeroTail := by
  unfold MultiPlacedLib.patchedData
  suffices ∀ (rs : List RelocEntry) (bs : List (BitVec 8)),
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bs.length) →
      (rs.foldl (lib.patchDataReloc mpl (mpl.ρ d.sym)) bs).length = bs.length by
    rw [List.length_append, this d.relocs d.bytes h, List.length_replicate]
  intro rs
  induction rs with
  | nil => intro _ _; rfl
  | cons r rs ih =>
    intro bs hrs
    have hl : (lib.patchDataReloc mpl (mpl.ρ d.sym) bs r).length = bs.length := by
      unfold MultiPlacedLib.patchDataReloc
      have hr := hrs r List.mem_cons_self
      cases hk : r.kind <;> simp only [hk, dataRelocWidth] at hr ⊢ <;>
        simp only [List.length_append, List.length_take, List.length_drop,
          ProofLib.ObjectLoad.RoDataFactsAux.bytesLE_length] <;> omega
    simp only [List.foldl_cons]
    rw [ih _ (fun r' hr' => hl ▸ hrs r' (List.mem_cons_of_mem _ hr')), hl]

theorem patchedData_eq_of_inElf_eq_addr {lib : MultiPlacedLib} {mpl mpl₀ : MultiPlacement}
    {img : ElfImage} {d : SymDataInfo} (hd : d ∈ lib.data)
    (hpl : lib.Placeable mpl) (hpl₀ : lib.Placeable mpl₀)
    (hin : lib.InElf img mpl) (hin₀ : lib.InElf img mpl₀)
    (haddr : mpl.ρ d.sym = mpl₀.ρ d.sym) :
    lib.patchedData mpl d = lib.patchedData mpl₀ d := by
  have h1 := hin.data d hd
  have h2 := hin₀.data d hd
  rw [← haddr] at h2
  have hlen : (lib.patchedData mpl d).length = (lib.patchedData mpl₀ d).length := by
    rw [length_patchedData_multi fun r hr => (hpl.data_relocs_ok d hd r hr).2.1,
      length_patchedData_multi fun r hr => (hpl₀.data_relocs_ok d hd r hr).2.1]
  exact elfMaps_eq_of_eq_addr h1 h2 hlen

theorem add_right_inj_bv64 {a b c : BitVec 64} (h : a + c = b + c) : a = b := by bv_omega

theorem sub_left_inj_bv64 {a b c : BitVec 64} (h : a - c = b - c) : a = b := by bv_omega

theorem MultiPlacedLib.resolve_of_lookup_some {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {s : String} {bi off : Nat} (h : lookupBlockSym s lib.blocks = some (bi, off)) :
    lib.resolve mpl s = mpl.base bi + BitVec.ofNat 64 off := by
  unfold MultiPlacedLib.resolve; rw [h]

theorem MultiPlacedLib.resolve_of_lookup_none {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {s : String} (h : lookupBlockSym s lib.blocks = none) :
    lib.resolve mpl s = mpl.ρ s := by
  unfold MultiPlacedLib.resolve; rw [h]

theorem pairwise_of_map_eq {α β : Type} {R : β → β → Prop} (f g : α → β) {xs : List α}
    (heq : xs.map f = xs.map g)
    (h : xs.Pairwise (fun a b => R (g a) (g b))) :
    xs.Pairwise (fun a b => R (f a) (f b)) := by
  rw [← List.pairwise_map] at h ⊢
  rwa [heq]

theorem addSignedAddr_inj {a₁ a₂ : BitVec 64} {addend : Int}
    (h : addSignedAddr a₁ addend = addSignedAddr a₂ addend) : a₁ = a₂ := by
  unfold addSignedAddr at h
  split at h <;> bv_omega

theorem patchRelocWord_eq_of_patchedWord_eq {blk : CodeBlock} {pl₁ pl₂ : Placement}
    {off : Nat} {r : RelocEntry}
    (hbase : pl₁.base = pl₂.base)
    (hr : blk.relocAt? off = some r)
    (hng : r.kind.isGotOrTlsIe = false)
    (hb2b : blk.b2bNext? r = none)
    (hw₁ : blk.undefWeakBranch pl₁ r = false)
    (hw₂ : blk.undefWeakBranch pl₂ r = false)
    (hrelax₂ : ∀ o, pl₂.relax o = false)
    (hnop : patchRelocWord r.kind (blk.wordAt off) (pl₁.base + BitVec.ofNat 64 off)
        (blk.target pl₂ r) ≠ nopWord)
    (hadr : ∀ t, patchRelocWord r.kind (blk.wordAt off) (pl₁.base + BitVec.ofNat 64 off)
        (blk.target pl₂ r) ≠ adrWord (adrTemplate (blk.wordAt off))
        (pl₁.base + BitVec.ofNat 64 off) t)
    (hpw : blk.patchedWord pl₁ off = blk.patchedWord pl₂ off) :
    patchRelocWord r.kind (blk.wordAt off) (pl₁.base + BitVec.ofNat 64 off) (blk.target pl₁ r) =
      patchRelocWord r.kind (blk.wordAt off) (pl₁.base + BitVec.ofNat 64 off) (blk.target pl₂ r) := by
  have hp₂ := CodeBlock.patchedWord_of_notRelaxed hr
    (CodeBlock.relaxedAt_of_relax_false (hrelax₂ off))
    (Or.inr (CodeBlock.relaxedAt_of_relax_false (hrelax₂ (off - 4)))) hng hw₂
  rw [CodeBlock.relocTarget_of_b2bNext_none hb2b, ← hbase] at hp₂
  rw [hp₂] at hpw
  unfold CodeBlock.patchedWord at hpw
  rw [hr] at hpw
  simp only [hng, hw₁, CodeBlock.relocTarget_of_b2bNext_none hb2b, Bool.false_and] at hpw
  split at hpw
  · exact absurd hpw.symm hnop
  · split at hpw
    · exact absurd hpw.symm (hadr _)
    · exact hpw

theorem branchWord_mask_7c (w : BitVec 32) (place target : BitVec 64) :
    branchWord w place target &&& 0x7c000000#32 = w &&& 0x7c000000#32 := by
  have hm := congrArg (· &&& 0x7c000000#32) (branchWord_mask (w := w) (place := place) (target := target))
  have hc : (0xfc000000#32 &&& 0x7c000000#32) = 0x7c000000#32 := by decide
  rw [BitVec.and_assoc, BitVec.and_assoc, hc] at hm
  exact hm

theorem branchWord_ne_nopWord {w : BitVec 32} {place target : BitVec 64}
    (hw : w &&& 0x7c000000#32 = 0x14000000#32) :
    branchWord w place target ≠ nopWord := by
  intro h
  have hm := branchWord_mask_7c w place target
  have hnop : nopWord &&& 0x7c000000#32 = 0x54000000#32 := by decide
  rw [h, hnop, hw] at hm
  revert hm; decide

theorem adrWord_mask_1c (w : BitVec 32) (place t : BitVec 64) :
    adrWord (adrTemplate w) place t &&& 0x1c000000#32 = 0x10000000#32 := by
  have hm : adrWord (adrTemplate w) place t &&& 0x9f000000#32 = 0x10000000#32 :=
    (adrp_mask_preserve (adrWordOff_mask (adrTemplate w) (t - place))).1.trans (adrTemplate_mask w)
  have hm' := congrArg (· &&& 0x1c000000#32) hm
  have hc1 : (0x9f000000#32 &&& 0x1c000000#32) = 0x1c000000#32 := by decide
  have hc2 : (0x10000000#32 &&& 0x1c000000#32) = 0x10000000#32 := by decide
  rw [BitVec.and_assoc, hc1, hc2] at hm'
  exact hm'

theorem branchWord_ne_adrWord {w : BitVec 32} {place target t : BitVec 64}
    (hw : w &&& 0x7c000000#32 = 0x14000000#32) :
    branchWord w place target ≠ adrWord (adrTemplate w) place t := by
  intro h
  have hm := congrArg (· &&& 0x1c000000#32) ((branchWord_mask_7c w place target).trans hw)
  have hc1 : (0x7c000000#32 &&& 0x1c000000#32) = 0x1c000000#32 := by decide
  have hc2 : (0x14000000#32 &&& 0x1c000000#32) = 0x14000000#32 := by decide
  rw [BitVec.and_assoc, hc1, hc2, h, adrWord_mask_1c] at hm
  revert hm; decide

theorem adrpWord_ne_nopWord {w : BitVec 32} {place target : BitVec 64}
    (hw : w &&& 0x9f000000#32 = 0x90000000#32) :
    adrpWord w place target ≠ nopWord := by
  intro h
  have hm : adrpWord w place target &&& 0x9f000000#32 = w &&& 0x9f000000#32 :=
    (adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))).1
  have hnop : nopWord &&& 0x9f000000#32 = 0x95000000#32 := by decide
  rw [h, hnop, hw] at hm
  revert hm; decide

theorem adrpWord_ne_adrWord {w : BitVec 32} {place target t : BitVec 64}
    (hw : w &&& 0x9f000000#32 = 0x90000000#32) :
    adrpWord w place target ≠ adrWord (adrTemplate w) place t := by
  intro h
  have hm : adrpWord w place target &&& 0x9f000000#32 = w &&& 0x9f000000#32 :=
    (adrp_mask_preserve (adrpWordOff_mask w (pageOf target - pageOf place))).1
  have hadr : adrWord (adrTemplate w) place t &&& 0x9f000000#32 = 0x10000000#32 :=
    (adrp_mask_preserve (adrWordOff_mask (adrTemplate w) (t - place))).1.trans (adrTemplate_mask w)
  rw [h, hadr, hw] at hm
  revert hm; decide

theorem lo12Word_mask_9f {scale : Nat} (w : BitVec 32) (target : BitVec 64) :
    lo12Word scale w target &&& 0x9f000000#32 = w &&& 0x9f000000#32 := by
  have hm := congrArg (· &&& 0x9f000000#32) (lo12Word_mask (scale := scale) w target)
  have hc : (0xffc003ff#32 &&& 0x9f000000#32) = 0x9f000000#32 := by decide
  rw [BitVec.and_assoc, BitVec.and_assoc, hc] at hm
  exact hm

theorem lo12Word_ne_nopWord {scale : Nat} {w : BitVec 32} {target : BitVec 64}
    (hw : w &&& 0x9f000000#32 ≠ 0x95000000#32) :
    lo12Word scale w target ≠ nopWord := by
  intro h
  apply hw
  have hnop : nopWord &&& 0x9f000000#32 = 0x95000000#32 := by decide
  rw [← lo12Word_mask_9f (scale := scale) w target, h, hnop]

theorem lo12Word_ne_adrWord {scale : Nat} {w : BitVec 32} {place target t : BitVec 64}
    (hw : w &&& 0x9f000000#32 ≠ 0x10000000#32) :
    lo12Word scale w target ≠ adrWord (adrTemplate w) place t := by
  intro h
  apply hw
  have hadr : adrWord (adrTemplate w) place t &&& 0x9f000000#32 = 0x10000000#32 :=
    (adrp_mask_preserve (adrWordOff_mask (adrTemplate w) (t - place))).1.trans (adrTemplate_mask w)
  rw [← lo12Word_mask_9f (scale := scale) w target, h, hadr]

def lo12Scale? : RelocKind → Option Nat
  | .addLo12 | .ldst8Lo12 => some 0
  | .ldst16Lo12 => some 1
  | .ldst32Lo12 => some 2
  | .ldst64Lo12 => some 3
  | .ldst128Lo12 => some 4
  | _ => none

theorem lo12Scale?_props {kind : RelocKind} {scale : Nat}
    (hs : lo12Scale? kind = some scale) :
    kind.isGotOrTlsIe = false ∧
    (kind == .call26 || kind == .jump26) = false ∧
    ∀ w place t, patchRelocWord kind w place t = lo12Word scale w t := by
  cases kind <;> simp only [lo12Scale?, reduceCtorEq, Option.some.injEq] at hs
  all_goals
    subst hs
    exact ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem lo12Of_eq_of_lo12Scale {kind : RelocKind} {scale : Nat}
    (hs : lo12Scale? kind = some scale) {w : BitVec 32} {place t₁ t₂ : BitVec 64}
    (hr₁ : CodeRelocInRange kind place t₁) (hr₂ : CodeRelocInRange kind place t₂)
    (heq : patchRelocWord kind w place t₁ = patchRelocWord kind w place t₂) :
    lo12Of t₁ = lo12Of t₂ := by
  cases kind <;> simp only [lo12Scale?, reduceCtorEq, Option.some.injEq] at hs
  all_goals
    subst hs
    simp only [patchRelocWord] at heq
    simp only [CodeRelocInRange] at hr₁ hr₂
  · rw [← lo12Word0_imm w t₁, ← lo12Word0_imm w t₂, heq]
  · rw [← lo12Word0_imm w t₁, ← lo12Word0_imm w t₂, heq]
  · rw [← lo12Word1_imm w t₁ hr₁, ← lo12Word1_imm w t₂ hr₂, heq]
  · rw [← lo12Word2_imm w t₁ hr₁, ← lo12Word2_imm w t₂ hr₂, heq]
  · rw [← lo12Word3_imm w t₁ hr₁, ← lo12Word3_imm w t₂ hr₂, heq]
  · rw [← lo12Word4_imm w t₁ hr₁, ← lo12Word4_imm w t₂ hr₂, heq]

def val64LE (bs : List (BitVec 8)) : BitVec 64 :=
  (bs.getD 0 0#8).zeroExtend 64 |||
  ((bs.getD 1 0#8).zeroExtend 64 <<< 8) |||
  ((bs.getD 2 0#8).zeroExtend 64 <<< 16) |||
  ((bs.getD 3 0#8).zeroExtend 64 <<< 24) |||
  ((bs.getD 4 0#8).zeroExtend 64 <<< 32) |||
  ((bs.getD 5 0#8).zeroExtend 64 <<< 40) |||
  ((bs.getD 6 0#8).zeroExtend 64 <<< 48) |||
  ((bs.getD 7 0#8).zeroExtend 64 <<< 56)

theorem val64LE_bytesLE_8 (v : BitVec 64) : val64LE (bytesLE 8 v) = v := by
  have h : val64LE (bytesLE 8 v) =
    ((v >>> 0).truncate 8).zeroExtend 64 |||
    (((v >>> 8).truncate 8).zeroExtend 64 <<< 8) |||
    (((v >>> 16).truncate 8).zeroExtend 64 <<< 16) |||
    (((v >>> 24).truncate 8).zeroExtend 64 <<< 24) |||
    (((v >>> 32).truncate 8).zeroExtend 64 <<< 32) |||
    (((v >>> 40).truncate 8).zeroExtend 64 <<< 40) |||
    (((v >>> 48).truncate 8).zeroExtend 64 <<< 48) |||
    (((v >>> 56).truncate 8).zeroExtend 64 <<< 56) := rfl
  rw [h]
  bv_bits

theorem bytesLE_8_inj {v₁ v₂ : BitVec 64} (h : bytesLE 8 v₁ = bytesLE 8 v₂) : v₁ = v₂ := by
  have := congrArg val64LE h
  simpa only [val64LE_bytesLE_8] using this

theorem splice_drop_take_self {d bs : List (BitVec 8)} {off : Nat}
    (hb : off + bs.length ≤ d.length) :
    ((d.take off ++ bs ++ d.drop (off + bs.length)).drop off).take bs.length = bs := by
  have hlen_take : (d.take off).length = off := by simp [List.length_take]; omega
  rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    hlen_take, Nat.sub_self, List.drop_zero, List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

/-- Checks that `relocs` contains an `.abs64` relocation at `off` targeting `(sym, addend)` with
`off + 8 ≤ bytesLen` and all subsequent relocations in bounds and disjoint from `[off, off + 8)`. -/
def hasUnoverwrittenAbs64 (bytesLen off sym : Nat) (addend : Int) : List Reloc → Bool
  | [] => false
  | r :: rs =>
    if Nat.beq r.off off && (r.kind == .abs64) && Nat.beq r.sym sym && (r.addend == addend) &&
        Nat.ble (off + 8) bytesLen &&
        rs.all (fun r' =>
          Nat.ble (r'.off + dataRelocWidth r'.kind) bytesLen &&
          (Nat.ble (r'.off + dataRelocWidth r'.kind) off || Nat.ble (off + 8) r'.off)) then
      true
    else
      hasUnoverwrittenAbs64 bytesLen off sym addend rs

theorem splice_bytesLE_step {bs : List (BitVec 8)} {r_off off n bytesLen w : Nat} {v : BitVec 64}
    (hlen : bs.length = bytesLen)
    (hr_bound : r_off + w ≤ bytesLen)
    (hr_disj : r_off + w ≤ off ∨ off + n ≤ r_off) :
    (((bs.take r_off ++ bytesLE w v ++ bs.drop (r_off + w)).drop off).take n =
      (bs.drop off).take n) ∧
    (bs.take r_off ++ bytesLE w v ++ bs.drop (r_off + w)).length = bytesLen := by
  have hbw : (bytesLE w v).length = w := RoDataFactsAux.bytesLE_length w v
  have hb : r_off + (bytesLE w v).length ≤ bs.length := by omega
  have hdisj : r_off + (bytesLE w v).length ≤ off ∨ off + n ≤ r_off := by rw [hbw]; exact hr_disj
  have h1 := splice_drop_take_eq hb hdisj
  have h2 := (splice_length hb).trans hlen
  rw [hbw] at h1 h2
  exact ⟨h1, h2⟩

theorem foldl_patchDataReloc_preserves_slice {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {names : List String} {addr : BitVec 64} {bytesLen off n : Nat} :
    ∀ (rs : List Reloc) (bs : List (BitVec 8)),
      bs.length = bytesLen →
      (rs.all fun r' =>
        Nat.ble (r'.off + dataRelocWidth r'.kind) bytesLen &&
        (Nat.ble (r'.off + dataRelocWidth r'.kind) off || Nat.ble (off + n) r'.off)) = true →
      (((rs.map (Reloc.toEntry names)).foldl (lib.patchDataReloc mpl addr) bs).drop off).take n =
        (bs.drop off).take n ∧
      ((rs.map (Reloc.toEntry names)).foldl (lib.patchDataReloc mpl addr) bs).length = bytesLen
  | [], bs, hlen, _ => ⟨rfl, hlen⟩
  | r :: rs, bs, hlen, hall => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hall
    obtain ⟨⟨hr_bound, hr_disj⟩, hrs⟩ := hall
    have hstep : ((lib.patchDataReloc mpl addr bs (r.toEntry names)).drop off).take n =
        (bs.drop off).take n ∧
        (lib.patchDataReloc mpl addr bs (r.toEntry names)).length = bytesLen := by
      obtain ⟨r_off, r_kind, r_sym, r_addend, r_ls⟩ := r
      unfold MultiPlacedLib.patchDataReloc Reloc.toEntry
      cases r_kind <;>
        simp only [dataRelocWidth] at hr_bound hr_disj <;>
        dsimp only
      all_goals
        first
        | exact ⟨rfl, hlen⟩
        | exact splice_bytesLE_step hlen hr_bound hr_disj
    simp only [List.map_cons, List.foldl_cons]
    have ⟨hs₂, hl₂⟩ := foldl_patchDataReloc_preserves_slice (lib := lib) (mpl := mpl)
      (names := names) (addr := addr) (off := off) (n := n) rs _ hstep.2
      (by simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hrs ⊢; exact hrs)
    exact ⟨hs₂.trans hstep.1, hl₂⟩

theorem foldl_patchDataReloc_slice_abs64 {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {names : List String} {addr : BitVec 64} {bytesLen off sym : Nat} {addend : Int} :
    ∀ (rs : List Reloc) (bs : List (BitVec 8)),
      bs.length = bytesLen →
      (∀ r ∈ rs, r.off + dataRelocWidth r.kind ≤ bytesLen) →
      hasUnoverwrittenAbs64 bytesLen off sym addend rs = true →
      (((rs.map (Reloc.toEntry names)).foldl (lib.patchDataReloc mpl addr) bs).drop off).take 8 =
        bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD sym "")) addend) ∧
      ((rs.map (Reloc.toEntry names)).foldl (lib.patchDataReloc mpl addr) bs).length = bytesLen
  | [], _, _, _, h => nomatch h
  | r :: rs, bs, hlen, hrs_ok, h => by
    unfold hasUnoverwrittenAbs64 at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, Nat.ble_eq] at hcond
      obtain ⟨⟨⟨⟨⟨rfl, hkind⟩, rfl⟩, rfl⟩, hbound⟩, hall⟩ := hcond
      simp only [List.map_cons, List.foldl_cons]
      have hpr : lib.patchDataReloc mpl addr bs (r.toEntry names) =
          bs.take r.off ++ bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend) ++
            bs.drop (r.off + 8) := by
        unfold MultiPlacedLib.patchDataReloc
        simp [Reloc.toEntry, hkind]
      rw [hpr]
      have hbw : (bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend)).length = 8 :=
        RoDataFactsAux.bytesLE_length 8 _
      have hb : r.off + (bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend)).length ≤
          bs.length := by omega
      have hlen₁ : (bs.take r.off ++ bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend) ++
          bs.drop (r.off + 8)).length = bytesLen := by
        have hs := splice_length hb
        rw [hbw] at hs
        exact hs.trans hlen
      have hself : ((bs.take r.off ++ bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend) ++
          bs.drop (r.off + 8)).drop r.off).take 8 =
          bytesLE 8 (addSignedAddr (lib.resolve mpl (names.getD r.sym "")) r.addend) := by
        have hs := splice_drop_take_self hb
        rwa [hbw] at hs
      have ⟨hs₂, hl₂⟩ := foldl_patchDataReloc_preserves_slice (lib := lib) (mpl := mpl)
        (names := names) (addr := addr) (n := 8) rs _ hlen₁ hall
      exact ⟨hs₂.trans hself, hl₂⟩
    · have hr_ok := hrs_ok r List.mem_cons_self
      have hlen₁ : (lib.patchDataReloc mpl addr bs (r.toEntry names)).length = bytesLen := by
        obtain ⟨r_off, r_kind, r_sym, r_addend, r_ls⟩ := r
        unfold MultiPlacedLib.patchDataReloc Reloc.toEntry
        cases r_kind <;>
          simp only [dataRelocWidth] at hr_ok <;>
          dsimp only <;>
          first
          | exact hlen
          | exact (splice_bytesLE_step (off := 0) (n := 0) hlen hr_ok (Or.inr (Nat.zero_le _))).2
      simp only [List.map_cons, List.foldl_cons]
      exact foldl_patchDataReloc_slice_abs64 rs _ hlen₁
        (fun r' hr' => hrs_ok r' (List.mem_cons_of_mem _ hr')) h

/-- Step in a static relocation-inversion DAG for `ML : MultiLib`. -/
inductive InvStep where
  | exportSym (e bi off : Nat)
  | symOfBlock (bi sym off : Nat)
  | blockOfSym (sym bi off : Nat)
  | branch (bi off sym : Nat) (addend : Int)
  | adrpLo12 (bi off1 off2 sym : Nat) (addend : Int)
  | dataAbs64 (di off sym : Nat) (addend : Int)
  deriving DecidableEq, Repr, Inhabited

def defaultBlock : Block := { code := [] }
def defaultData : Data := { sym := 0 }

def fastWordOfBytesLE (xs : List (BitVec 8)) (off : Nat) : BitVec 32 :=
  withForcedList (fastDrop off xs) fun ys => wordOfBytesLE ys 0

@[simp] theorem fastWordOfBytesLE_eq (xs : List (BitVec 8)) (off : Nat) :
    fastWordOfBytesLE xs off = wordOfBytesLE xs off := by
  simp only [fastWordOfBytesLE, withForcedList_eq, fastDrop_eq_drop, wordOfBytesLE,
    getD_drop, Nat.add_zero]

def checkInvStepB (ML : MultiLib) (tBlk : VecTree Block) (tData : VecTree Data)
    (tSym : VecTree (Option (Nat × Nat)))
    (tBlkKnown tSymKnown : VecTree (Option Unit)) (step : InvStep) :
    Option (VecTree (Option Unit) × VecTree (Option Unit)) :=
  match step with
  | .exportSym e bi off =>
    if memNat e ML.exports && (tSym.getD none e == some (bi, off)) then
      match tBlkKnown.setFresh bi () with
      | some tBlkKnown' => some (tBlkKnown', tSymKnown)
      | none => none
    else none
  | .symOfBlock bi sym off =>
    if (tBlkKnown.getD none bi).isSome && Nat.blt sym ML.names.length &&
        (tSym.getD none sym == some (bi, off)) then
      match tSymKnown.setFresh sym () with
      | some tSymKnown' => some (tBlkKnown, tSymKnown')
      | none => none
    else none
  | .blockOfSym sym bi off =>
    if (tSymKnown.getD none sym).isSome && Nat.blt sym ML.names.length &&
        (tSym.getD none sym == some (bi, off)) then
      match tBlkKnown.setFresh bi () with
      | some tBlkKnown' => some (tBlkKnown', tSymKnown)
      | none => none
    else none
  | .branch bi off sym addend =>
    if (tBlkKnown.getD none bi).isSome && Nat.blt bi ML.blocks.length &&
        Nat.beq (off % 4) 0 then
      let b := tBlk.getD defaultBlock bi
      match relocAtId? b.relocs off with
      | some r =>
        if Nat.beq r.sym sym && (r.addend == addend) &&
            (r.kind == .call26 || r.kind == .jump26) &&
            (lookupId sym b.symbols).isNone &&
            (b.weakRefs.all fun w => Nat.blt w ML.names.length && !Nat.beq w sym) &&
            ((fastWordOfBytesLE b.code off &&& 0x7c000000#32) == 0x14000000#32) then
          match tSymKnown.setFresh sym () with
          | some tSymKnown' => some (tBlkKnown, tSymKnown')
          | none => none
        else none
      | none => none
    else none
  | .adrpLo12 bi off1 off2 sym addend =>
    if (tBlkKnown.getD none bi).isSome && Nat.blt bi ML.blocks.length &&
        Nat.beq (off1 % 4) 0 && Nat.beq (off2 % 4) 0 then
      let b := tBlk.getD defaultBlock bi
      match relocAtId? b.relocs off1, relocAtId? b.relocs off2 with
      | some r1, some r2 =>
        let w1 := fastWordOfBytesLE b.code off1
        let w2 := fastWordOfBytesLE b.code off2
        if Nat.beq r1.sym sym && Nat.beq r2.sym sym &&
            (r1.addend == addend) && (r2.addend == addend) &&
            (r1.kind == .adrpHi21) && (lo12Scale? r2.kind).isSome &&
            ((w1 &&& 0x9f000000#32) == 0x90000000#32) &&
            ((w2 &&& 0x9f000000#32) != 0x95000000#32) &&
            ((w2 &&& 0x9f000000#32) != 0x10000000#32) then
          match tSymKnown.setFresh sym () with
          | some tSymKnown' => some (tBlkKnown, tSymKnown')
          | none => none
        else none
      | _, _ => none
    else none
  | .dataAbs64 di off sym addend =>
    if Nat.blt di ML.data.length then
      let d := tData.getD defaultData di
      if (tSymKnown.getD none d.sym).isSome &&
          hasUnoverwrittenAbs64 (fastLen512 4096 d.bytes) off sym addend d.relocs then
        match tSymKnown.setFresh sym () with
        | some tSymKnown' => some (tBlkKnown, tSymKnown')
        | none => none
      else none
    else none

def checkInvStepsLoop (ML : MultiLib) (tBlk : VecTree Block) (tData : VecTree Data)
    (tSym : VecTree (Option (Nat × Nat))) :
    VecTree (Option Unit) → VecTree (Option Unit) → List InvStep →
      Option (VecTree (Option Unit) × VecTree (Option Unit))
  | tBlkKnown, tSymKnown, [] => some (tBlkKnown, tSymKnown)
  | tBlkKnown, tSymKnown, s :: rest =>
    match checkInvStepB ML tBlk tData tSym tBlkKnown tSymKnown s with
    | some (tBlkKnown', tSymKnown') =>
      checkInvStepsLoop ML tBlk tData tSym tBlkKnown' tSymKnown' rest
    | none => none

/-- Boolean checker validating a relocation-inversion DAG `steps` on `ML`. -/
def checkRelocInvStepsB (ML : MultiLib) (nameChars : List (List Char))
    (steps : List InvStep) : Bool :=
  Nat.blt ML.blocks.length 1048576 &&
  Nat.blt ML.data.length 1048576 &&
  Nat.blt ML.names.length 1048576 &&
  namesNodup nameChars &&
  multiIdsOkFast ML &&
  withVecTree defaultBlock ML.blocks fun tBlk =>
  withVecTree defaultData ML.data fun tData =>
  withNat ML.blocks.length fun nBlks =>
  withNat ML.names.length fun nNames =>
  match insertAllBlocks 0 ML.blocks (mkNoneTree 20 nNames) with
  | none => false
  | some tSym =>
    match checkInvStepsLoop ML tBlk tData tSym
        (mkNoneTree 20 nBlks) (mkNoneTree 20 nNames) steps with
    | none => false
    | some (tBlkKnown, tSymKnown) =>
      (List.range nBlks).all (fun i => (tBlkKnown.getD none i).isSome) &&
      (List.range nNames).all (fun s => (tSymKnown.getD none s).isSome)

theorem setFresh_unit_preserves {P : Nat → Prop} {t t' : VecTree (Option Unit)} {i : Nat}
    (hset : t.setFresh i () = some t')
    (hP : ∀ j, t.getD none j = some () → P j)
    (hi : P i) :
    ∀ j, t'.getD none j = some () → P j := by
  intro j hj
  by_cases hji : j = i
  · exact hji ▸ hi
  · rw [VecTree.getD_setFresh_of_ne hset hji] at hj
    exact hP j hj

theorem allKnown_of_all {P : Nat → Prop} {n : Nat} {t : VecTree (Option Unit)}
    (hP : ∀ j, t.getD none j = some () → P j)
    (hall : ((List.range n).all fun j => (t.getD none j).isSome) = true) :
    ∀ j < n, P j := by
  intro j hj
  have h := List.all_eq_true.1 hall j (List.mem_range.2 hj)
  cases hget : t.getD none j with
  | none => rw [hget] at h; nomatch h
  | some u => cases u; exact hP j hget

theorem not_contains_map_getD_of_all_ne {names : List String} (hnd : names.Nodup)
    {sym : Nat} (hs : sym < names.length) {xs : List Nat}
    (hall : (xs.all fun w => Nat.blt w names.length && !Nat.beq w sym) = true) :
    (xs.map fun e => names.getD e "").contains (names.getD sym "") = false := by
  rw [Bool.eq_false_iff, Ne, List.contains_iff_mem, List.mem_map]
  rintro ⟨x, hx, heq⟩
  have hx_ok := List.all_eq_true.1 hall x hx
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne,
    Nat.blt_eq, Nat.beq_eq] at hx_ok
  exact hx_ok.2 (getD_inj hnd hx_ok.1 hs heq)

theorem checkInvStepB_sound {ML : MultiLib} {mpl mpl₀ : MultiPlacement} {img : ElfImage}
    {tSym : VecTree (Option (Nat × Nat))}
    {tBlkKnown tSymKnown tBlkKnown' tSymKnown' : VecTree (Option Unit)}
    {step : InvStep}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hblks_lt : ML.blocks.length < 2 ^ 20) (hdata_lt : ML.data.length < 2 ^ 20)
    (hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks)
    (hpl : ML.toMultiPlacedLib.Placeable mpl) (hin : ML.toMultiPlacedLib.InElf img mpl)
    (hpl₀ : ML.toMultiPlacedLib.Placeable mpl₀) (hin₀ : ML.toMultiPlacedLib.InElf img mpl₀)
    (hrelax₀ : ∀ i o, mpl₀.relax i o = false)
    (hB : ∀ i, tBlkKnown.getD none i = some () → i < ML.blocks.length ∧ mpl.base i = mpl₀.base i)
    (hS : ∀ s, tSymKnown.getD none s = some () →
      ML.toMultiPlacedLib.resolve mpl (ML.names.getD s "") =
        ML.toMultiPlacedLib.resolve mpl₀ (ML.names.getD s ""))
    (hstep : checkInvStepB ML (toVecTree defaultBlock ML.blocks) (toVecTree defaultData ML.data)
      tSym tBlkKnown tSymKnown step = some (tBlkKnown', tSymKnown')) :
    (∀ i, tBlkKnown'.getD none i = some () → i < ML.blocks.length ∧ mpl.base i = mpl₀.base i) ∧
    (∀ s, tSymKnown'.getD none s = some () →
      ML.toMultiPlacedLib.resolve mpl (ML.names.getD s "") =
        ML.toMultiPlacedLib.resolve mpl₀ (ML.names.getD s "")) := by
  cases step with
  | exportSym e bi off =>
    simp only [checkInvStepB] at hstep
    split at hstep
    · rename_i hcond
      cases hset : tBlkKnown.setFresh bi () with
      | none => rw [hset] at hstep; nomatch hstep
      | some tb' =>
        rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
        simp only [Bool.and_eq_true, memNat_iff, beq_iff_eq] at hcond
        obtain ⟨he_mem, htsym⟩ := hcond
        have he_lt : e < ML.names.length := by
          simp only [MultiLib.idsOk, Bool.and_eq_true, List.all_eq_true, blt_iff] at hids
          exact hids.1.2 e he_mem
        have hblk : lookupBlockSym (ML.names.getD e "") ML.toMultiPlacedLib.blocks = some (bi, off) := by
          rw [lookupBlockSym_toMultiPlacedLib hnd hids he_lt, ← hlookup e, htsym]
        obtain ⟨hbi_lt, _⟩ := lookupBlockSym_some hblk
        simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map] at hbi_lt
        have hexp_mem : ML.names.getD e "" ∈ ML.toMultiPlacedLib.exports :=
          List.mem_map.2 ⟨e, he_mem, rfl⟩
        obtain ⟨i₁, off₁, hblk₁, hu₁⟩ := hin.exports _ hexp_mem
        obtain ⟨i₂, off₂, hblk₂, hu₂⟩ := hin₀.exports _ hexp_mem
        rw [hblk] at hblk₁ hblk₂
        cases hblk₁; cases hblk₂
        rw [hu₁] at hu₂
        injection hu₂ with hu₂
        have hbase : mpl.base bi = mpl₀.base bi := add_right_inj_bv64 hu₂
        exact ⟨setFresh_unit_preserves hset hB ⟨hbi_lt, hbase⟩, hS⟩
    · nomatch hstep
  | symOfBlock bi sym off =>
    simp only [checkInvStepB] at hstep
    split at hstep
    · rename_i hcond
      cases hset : tSymKnown.setFresh sym () with
      | none => rw [hset] at hstep; nomatch hstep
      | some ts' =>
        rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
        simp only [Bool.and_eq_true, Option.isSome_iff_exists, Nat.blt_eq, beq_iff_eq] at hcond
        obtain ⟨⟨⟨⟨⟩, hbi_kn⟩, hsym_lt⟩, htsym⟩ := hcond
        have ⟨_, hbase⟩ := hB bi hbi_kn
        have hblk : lookupBlockSym (ML.names.getD sym "") ML.toMultiPlacedLib.blocks = some (bi, off) := by
          rw [lookupBlockSym_toMultiPlacedLib hnd hids hsym_lt, ← hlookup sym, htsym]
        have hres : ML.toMultiPlacedLib.resolve mpl (ML.names.getD sym "") =
            ML.toMultiPlacedLib.resolve mpl₀ (ML.names.getD sym "") := by
          rw [MultiPlacedLib.resolve_of_lookup_some hblk,
            MultiPlacedLib.resolve_of_lookup_some hblk, hbase]
        exact ⟨hB, setFresh_unit_preserves hset hS hres⟩
    · nomatch hstep
  | blockOfSym sym bi off =>
    simp only [checkInvStepB] at hstep
    split at hstep
    · rename_i hcond
      cases hset : tBlkKnown.setFresh bi () with
      | none => rw [hset] at hstep; nomatch hstep
      | some tb' =>
        rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
        simp only [Bool.and_eq_true, Option.isSome_iff_exists, Nat.blt_eq, beq_iff_eq] at hcond
        obtain ⟨⟨⟨⟨⟩, hsym_kn⟩, hsym_lt⟩, htsym⟩ := hcond
        have hres := hS sym hsym_kn
        have hblk : lookupBlockSym (ML.names.getD sym "") ML.toMultiPlacedLib.blocks = some (bi, off) := by
          rw [lookupBlockSym_toMultiPlacedLib hnd hids hsym_lt, ← hlookup sym, htsym]
        obtain ⟨hbi_lt, _⟩ := lookupBlockSym_some hblk
        simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map] at hbi_lt
        rw [MultiPlacedLib.resolve_of_lookup_some hblk,
          MultiPlacedLib.resolve_of_lookup_some hblk] at hres
        have hbase : mpl.base bi = mpl₀.base bi := add_right_inj_bv64 hres
        exact ⟨setFresh_unit_preserves hset hB ⟨hbi_lt, hbase⟩, hS⟩
    · nomatch hstep
  | branch bi off sym addend =>
    simp only [checkInvStepB, fastWordOfBytesLE_eq] at hstep
    split at hstep
    · rename_i hpre
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, Nat.blt_eq, Nat.beq_eq] at hpre
      obtain ⟨⟨⟨⟨⟩, hbi_kn⟩, hbi_lt⟩, hal⟩ := hpre
      have ⟨_, hbase⟩ := hB bi hbi_kn
      rw [toVecTree_getD_all defaultBlock ML.blocks hblks_lt bi, getD_of_lt hbi_lt] at hstep
      cases hr_id : relocAtId? ML.blocks[bi].relocs off with
      | none => rw [hr_id] at hstep; nomatch hstep
      | some r =>
        rw [hr_id] at hstep; dsimp only at hstep
        split at hstep
        · rename_i hcond
          cases hset : tSymKnown.setFresh sym () with
          | none => rw [hset] at hstep; nomatch hstep
          | some ts' =>
            rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
            simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, Option.isNone_iff_eq_none] at hcond
            obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hkind⟩, hsym_none⟩, hweaks⟩, hw_mask⟩ := hcond
            let L := ML.blockLib ML.blocks[bi]
            have hok : L.IdsOk := ML.blockLib_idsOk hids (List.getElem_mem hbi_lt)
            have hr_mem : r ∈ ML.blocks[bi].relocs := relocAtId?_mem hr_id
            have hsym_lt : r.sym < ML.names.length := hok.relocs r hr_mem
            have hbi_lib : bi < ML.toMultiPlacedLib.blocks.length := by
              simp [MultiLib.toMultiPlacedLib_blocks, hbi_lt]
            have hblk_eq : ML.toMultiPlacedLib.blocks[bi] = L.block := by
              simp [MultiLib.toMultiPlacedLib_blocks, MultiLib.blockLib_block, L]
            have hr_blk : L.block.relocAt? off = some (r.toEntry ML.names) := by
              rw [relocAt?_block L off, show L.relocs = ML.blocks[bi].relocs from rfl, hr_id]; rfl
            have hr_blk_mem : r.toEntry ML.names ∈ L.block.relocs := CodeBlock.relocAt?_mem hr_blk
            have hrok₁ := (hpl.blocks_ok bi hbi_lib).relocs_ok (r.toEntry ML.names)
              (by rw [hblk_eq]; exact hr_blk_mem)
            have hrok₂ := (hpl₀.blocks_ok bi hbi_lib).relocs_ok (r.toEntry ML.names)
              (by rw [hblk_eq]; exact hr_blk_mem)
            have hpl_base : (ML.toMultiPlacedLib.blockPlacement mpl bi).base = mpl.base bi := rfl
            have hpl₀_base : (ML.toMultiPlacedLib.blockPlacement mpl₀ bi).base = mpl₀.base bi := rfl
            rw [hblk_eq, show (r.toEntry ML.names).off = off from relocAtId?_off hr_id, hpl_base] at hrok₁
            rw [hblk_eq, show (r.toEntry ML.names).off = off from relocAtId?_off hr_id, hpl₀_base, ← hbase] at hrok₂
            have hb2b : L.block.b2bNext? (r.toEntry ML.names) = none := by
              rw [show ML.names = L.names from rfl, b2bNext?_block hnd hok hsym_lt]
              unfold b2bNextId
              rw [show L.symbols = ML.blocks[bi].symbols from rfl, hsym_none]
              cases (r.kind == .call26 || r.kind == .jump26) <;> rfl
            have hnot_weak : L.block.weakRefs.contains (r.toEntry ML.names).sym = false :=
              not_contains_map_getD_of_all_ne hnd hsym_lt hweaks
            have hw₁ := CodeBlock.undefWeakBranch_of_not_weak (pl := ML.toMultiPlacedLib.blockPlacement mpl bi) hnot_weak
            have hw₂ := CodeBlock.undefWeakBranch_of_not_weak (pl := ML.toMultiPlacedLib.blockPlacement mpl₀ bi) hnot_weak
            have hng : (r.toEntry ML.names).kind.isGotOrTlsIe = false := by
              rcases Bool.or_eq_true_iff.1 hkind with hk | hk <;>
                rw [beq_iff_eq] at hk <;> simp [Reloc.toEntry_kind, hk, RelocKind.isGotOrTlsIe]
            have hpw : L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl bi) off =
                L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) off := by
              have := patchedWord_eq_of_inElf_eq_base hbi_lib hin hin₀ hbase hal
                (by rw [hblk_eq]; exact hrok₁.2.1)
              rwa [hblk_eq] at this
            have hbw : ∀ place t, patchRelocWord (r.toEntry ML.names).kind (L.block.wordAt off) place t =
                branchWord (L.block.wordAt off) place t := by
              intro place t
              rcases Bool.or_eq_true_iff.1 hkind with hk | hk <;>
                rw [beq_iff_eq] at hk <;> simp [Reloc.toEntry_kind, hk, patchRelocWord]
            have hprw := patchRelocWord_eq_of_patchedWord_eq hbase hr_blk hng hb2b hw₁ hw₂
              (fun o => hrelax₀ bi o)
              (by rw [hbw]; exact branchWord_ne_nopWord hw_mask)
              (fun t => by rw [hbw]; exact branchWord_ne_adrWord hw_mask) hpw
            rw [hbw, hbw, hpl_base] at hprw
            have hbr₁ : BranchInRange (mpl.base bi + BitVec.ofNat 64 off)
                (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r.toEntry ML.names)) := by
              have hr1 := hrok₁.2.2
              rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hng,
                CodeBlock.relocTarget_of_b2bNext_none hb2b] at hr1
              rcases Bool.or_eq_true_iff.1 hkind with hk | hk <;>
                rw [beq_iff_eq] at hk <;> simpa [Reloc.toEntry_kind, hk, CodeRelocInRange] using hr1
            have hbr₂ : BranchInRange (mpl.base bi + BitVec.ofNat 64 off)
                (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r.toEntry ML.names)) := by
              have hr2 := hrok₂.2.2
              rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hng,
                CodeBlock.relocTarget_of_b2bNext_none hb2b] at hr2
              rcases Bool.or_eq_true_iff.1 hkind with hk | hk <;>
                rw [beq_iff_eq] at hk <;> simpa [Reloc.toEntry_kind, hk, CodeRelocInRange] using hr2
            have himm₁ := branchWord_imm (w := L.block.wordAt off) hbr₁
            have himm₂ := branchWord_imm (w := L.block.wordAt off) hbr₂
            have hsub : L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r.toEntry ML.names) -
                (mpl.base bi + BitVec.ofNat 64 off) =
                L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r.toEntry ML.names) -
                (mpl.base bi + BitVec.ofNat 64 off) := by
              rw [← himm₁, ← himm₂, hprw]
            have htgt := sub_left_inj_bv64 hsub
            simp only [CodeBlock.target, ← hblk_eq,
              ML.toMultiPlacedLib.resolve_block hbi_lib hpl.symbols_nodup] at htgt
            exact ⟨hB, setFresh_unit_preserves hset hS (addSignedAddr_inj htgt)⟩
        · nomatch hstep
    · nomatch hstep
  | adrpLo12 bi off1 off2 sym addend =>
    simp only [checkInvStepB, fastWordOfBytesLE_eq] at hstep
    split at hstep
    · rename_i hpre
      simp only [Bool.and_eq_true, Option.isSome_iff_exists, Nat.blt_eq, Nat.beq_eq] at hpre
      obtain ⟨⟨⟨⟨⟨⟩, hbi_kn⟩, hbi_lt⟩, hal1⟩, hal2⟩ := hpre
      have ⟨_, hbase⟩ := hB bi hbi_kn
      rw [toVecTree_getD_all defaultBlock ML.blocks hblks_lt bi, getD_of_lt hbi_lt] at hstep
      cases hr1_id : relocAtId? ML.blocks[bi].relocs off1 with
      | none => rw [hr1_id] at hstep; nomatch hstep
      | some r1 =>
        rw [hr1_id] at hstep
        cases hr2_id : relocAtId? ML.blocks[bi].relocs off2 with
        | none => rw [hr2_id] at hstep; nomatch hstep
        | some r2 =>
          rw [hr2_id] at hstep; dsimp only at hstep
          split at hstep
          · rename_i hcond
            cases hset : tSymKnown.setFresh sym () with
            | none => rw [hset] at hstep; nomatch hstep
            | some ts' =>
              rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
              simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq, bne_iff_ne, Option.isSome_iff_exists] at hcond
              obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs1, hs2⟩, ha1⟩, ha2⟩, hk1⟩, ⟨scale, hk2⟩⟩, hw1⟩, hw2_nop⟩, hw2_adr⟩ := hcond
              subst hs1 ha1
              let L := ML.blockLib ML.blocks[bi]
              have hbi_lib : bi < ML.toMultiPlacedLib.blocks.length := by
                simp [MultiLib.toMultiPlacedLib_blocks, hbi_lt]
              have hblk_eq : ML.toMultiPlacedLib.blocks[bi] = L.block := by
                simp [MultiLib.toMultiPlacedLib_blocks, MultiLib.blockLib_block, L]
              have hpl_base : (ML.toMultiPlacedLib.blockPlacement mpl bi).base = mpl.base bi := rfl
              have hpl₀_base : (ML.toMultiPlacedLib.blockPlacement mpl₀ bi).base = mpl₀.base bi := rfl
              -- Site 1 (adrpHi21 at off1)
              have hr1_blk : L.block.relocAt? off1 = some (r1.toEntry ML.names) := by
                rw [relocAt?_block L off1, show L.relocs = ML.blocks[bi].relocs from rfl, hr1_id]; rfl
              have hrok1₁ := (hpl.blocks_ok bi hbi_lib).relocs_ok (r1.toEntry ML.names)
                (by rw [hblk_eq]; exact CodeBlock.relocAt?_mem hr1_blk)
              have hrok1₂ := (hpl₀.blocks_ok bi hbi_lib).relocs_ok (r1.toEntry ML.names)
                (by rw [hblk_eq]; exact CodeBlock.relocAt?_mem hr1_blk)
              rw [hblk_eq, show (r1.toEntry ML.names).off = off1 from relocAtId?_off hr1_id, hpl_base] at hrok1₁
              rw [hblk_eq, show (r1.toEntry ML.names).off = off1 from relocAtId?_off hr1_id, hpl₀_base, ← hbase] at hrok1₂
              have hng1 : (r1.toEntry ML.names).kind.isGotOrTlsIe = false := by
                simp [Reloc.toEntry_kind, hk1, RelocKind.isGotOrTlsIe]
              have hb2b1 : L.block.b2bNext? (r1.toEntry ML.names) = none := by
                simp [CodeBlock.b2bNext?, Reloc.toEntry_kind, hk1]
              have hw1₁ : L.block.undefWeakBranch (ML.toMultiPlacedLib.blockPlacement mpl bi) (r1.toEntry ML.names) = false := by
                simp [CodeBlock.undefWeakBranch, Reloc.toEntry_kind, hk1]
              have hw1₂ : L.block.undefWeakBranch (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r1.toEntry ML.names) = false := by
                simp [CodeBlock.undefWeakBranch, Reloc.toEntry_kind, hk1]
              have hpw1 : L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl bi) off1 =
                  L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) off1 := by
                have := patchedWord_eq_of_inElf_eq_base hbi_lib hin hin₀ hbase hal1
                  (by rw [hblk_eq]; exact hrok1₁.2.1)
                rwa [hblk_eq] at this
              have hprw1 := patchRelocWord_eq_of_patchedWord_eq hbase hr1_blk hng1 hb2b1 hw1₁ hw1₂
                (fun o => hrelax₀ bi o)
                (by simp only [Reloc.toEntry_kind, hk1, patchRelocWord]; exact adrpWord_ne_nopWord hw1)
                (fun t => by simp only [Reloc.toEntry_kind, hk1, patchRelocWord]; exact adrpWord_ne_adrWord hw1)
                hpw1
              simp only [Reloc.toEntry_kind, hk1, patchRelocWord, hpl_base] at hprw1
              have hadrp₁ : AdrpInRange (mpl.base bi + BitVec.ofNat 64 off1)
                  (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r1.toEntry ML.names)) := by
                have hr := hrok1₁.2.2
                rwa [CodeBlock.relocInRange_of_not_gotOrTlsIe hng1,
                  CodeBlock.relocTarget_of_b2bNext_none hb2b1, Reloc.toEntry_kind, hk1] at hr
              have hadrp₂ : AdrpInRange (mpl.base bi + BitVec.ofNat 64 off1)
                  (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r1.toEntry ML.names)) := by
                have hr := hrok1₂.2.2
                rwa [CodeBlock.relocInRange_of_not_gotOrTlsIe hng1,
                  CodeBlock.relocTarget_of_b2bNext_none hb2b1,
                  Reloc.toEntry_kind, hk1] at hr
              have himm1₁ := adrpWord_imm (w := L.block.wordAt off1) hadrp₁
              have himm1₂ := adrpWord_imm (w := L.block.wordAt off1) hadrp₂
              have hpage_sub : pageOf (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r1.toEntry ML.names)) -
                  pageOf (mpl.base bi + BitVec.ofNat 64 off1) =
                  pageOf (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r1.toEntry ML.names)) -
                  pageOf (mpl.base bi + BitVec.ofNat 64 off1) := by
                rw [← himm1₁, ← himm1₂, hprw1]
              have hpage := sub_left_inj_bv64 hpage_sub
              -- Site 2 (lo12 at off2)
              have hr2_blk : L.block.relocAt? off2 = some (r2.toEntry ML.names) := by
                rw [relocAt?_block L off2, show L.relocs = ML.blocks[bi].relocs from rfl, hr2_id]; rfl
              have hrok2₁ := (hpl.blocks_ok bi hbi_lib).relocs_ok (r2.toEntry ML.names)
                (by rw [hblk_eq]; exact CodeBlock.relocAt?_mem hr2_blk)
              have hrok2₂ := (hpl₀.blocks_ok bi hbi_lib).relocs_ok (r2.toEntry ML.names)
                (by rw [hblk_eq]; exact CodeBlock.relocAt?_mem hr2_blk)
              rw [hblk_eq, show (r2.toEntry ML.names).off = off2 from relocAtId?_off hr2_id, hpl_base] at hrok2₁
              rw [hblk_eq, show (r2.toEntry ML.names).off = off2 from relocAtId?_off hr2_id, hpl₀_base, ← hbase] at hrok2₂
              obtain ⟨hng2_raw, hnb2_raw, hlo12_raw⟩ := lo12Scale?_props hk2
              have hng2 : (r2.toEntry ML.names).kind.isGotOrTlsIe = false := hng2_raw
              have hnb2 : ((r2.toEntry ML.names).kind == .call26 || (r2.toEntry ML.names).kind == .jump26) = false := hnb2_raw
              have hb2b2 : L.block.b2bNext? (r2.toEntry ML.names) = none := by
                unfold CodeBlock.b2bNext?; rw [hnb2]; rfl
              have hw2₁ : L.block.undefWeakBranch (ML.toMultiPlacedLib.blockPlacement mpl bi) (r2.toEntry ML.names) = false :=
                CodeBlock.undefWeakBranch_of_not_branch hnb2
              have hw2₂ : L.block.undefWeakBranch (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r2.toEntry ML.names) = false :=
                CodeBlock.undefWeakBranch_of_not_branch hnb2
              have hpw2 : L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl bi) off2 =
                  L.block.patchedWord (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) off2 := by
                have := patchedWord_eq_of_inElf_eq_base hbi_lib hin hin₀ hbase hal2
                  (by rw [hblk_eq]; exact hrok2₁.2.1)
                rwa [hblk_eq] at this
              have hlo12_prw : ∀ place t,
                  patchRelocWord (r2.toEntry ML.names).kind (L.block.wordAt off2) place t =
                  lo12Word scale (L.block.wordAt off2) t :=
                fun place t => hlo12_raw (L.block.wordAt off2) place t
              have hprw2 := patchRelocWord_eq_of_patchedWord_eq hbase hr2_blk hng2 hb2b2 hw2₁ hw2₂
                (fun o => hrelax₀ bi o)
                (by rw [hlo12_prw]; exact lo12Word_ne_nopWord hw2_nop)
                (fun t => by rw [hlo12_prw]; exact lo12Word_ne_adrWord hw2_adr)
                hpw2
              rw [hpl_base] at hprw2
              have hcr2₁ : CodeRelocInRange r2.kind (mpl.base bi + BitVec.ofNat 64 off2)
                  (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r2.toEntry ML.names)) := by
                have hr := hrok2₁.2.2
                rwa [CodeBlock.relocInRange_of_not_gotOrTlsIe hng2,
                  CodeBlock.relocTarget_of_b2bNext_none hb2b2] at hr
              have hcr2₂ : CodeRelocInRange r2.kind (mpl.base bi + BitVec.ofNat 64 off2)
                  (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r2.toEntry ML.names)) := by
                have hr := hrok2₂.2.2
                rwa [CodeBlock.relocInRange_of_not_gotOrTlsIe hng2,
                  CodeBlock.relocTarget_of_b2bNext_none hb2b2] at hr
              have hlo12 := lo12Of_eq_of_lo12Scale hk2 hcr2₁ hcr2₂ hprw2
              have htgt_eq : ∀ pl, L.block.target pl (r2.toEntry ML.names) =
                  L.block.target pl (r1.toEntry ML.names) := by
                intro pl
                simp [CodeBlock.target, Reloc.toEntry_sym, Reloc.toEntry_addend, hs2, ha2]
              rw [htgt_eq, htgt_eq] at hlo12
              have htgt : L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r1.toEntry ML.names) =
                  L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r1.toEntry ML.names) := by
                rw [← pageOf_add_lo12Of (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl bi) (r1.toEntry ML.names)),
                  ← pageOf_add_lo12Of (L.block.target (ML.toMultiPlacedLib.blockPlacement mpl₀ bi) (r1.toEntry ML.names)),
                  hpage, hlo12]
              simp only [CodeBlock.target, ← hblk_eq,
                ML.toMultiPlacedLib.resolve_block hbi_lib hpl.symbols_nodup] at htgt
              exact ⟨hB, setFresh_unit_preserves hset hS (addSignedAddr_inj htgt)⟩
          · nomatch hstep
    · nomatch hstep
  | dataAbs64 di off sym addend =>
    simp only [checkInvStepB, fastLen512_eq_length] at hstep
    split at hstep
    · rename_i hdi_lt
      rw [Nat.blt_eq] at hdi_lt
      rw [toVecTree_getD_all defaultData ML.data hdata_lt di, getD_of_lt hdi_lt] at hstep
      split at hstep
      · rename_i hcond
        cases hset : tSymKnown.setFresh sym () with
        | none => rw [hset] at hstep; nomatch hstep
        | some ts' =>
          rw [hset] at hstep; injection hstep with hstep; injection hstep with h1 h2; subst h1 h2
          simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hcond
          obtain ⟨⟨⟨⟩, hdsym_kn⟩, hhas⟩ := hcond
          let d := ML.data[di]
          let dInfo := d.toInfo ML.names
          have hd_mem : dInfo ∈ ML.toMultiPlacedLib.data := by
            simp only [MultiLib.toMultiPlacedLib_data]
            exact List.mem_map_of_mem (List.getElem_mem hdi_lt)
          have hres_d := hS d.sym hdsym_kn
          have hd_none := (hpl.data_ok dInfo hd_mem).1
          have haddr : mpl.ρ dInfo.sym = mpl₀.ρ dInfo.sym := by
            change ML.toMultiPlacedLib.resolve mpl dInfo.sym =
              ML.toMultiPlacedLib.resolve mpl₀ dInfo.sym at hres_d
            rwa [MultiPlacedLib.resolve_of_lookup_none hd_none,
              MultiPlacedLib.resolve_of_lookup_none hd_none] at hres_d
          have hpd := patchedData_eq_of_inElf_eq_addr hd_mem hpl hpl₀ hin hin₀ haddr
          have hrs_ok : ∀ r ∈ d.relocs, r.off + dataRelocWidth r.kind ≤ d.bytes.length := by
            intro r hr
            have hdro := hpl.data_relocs_ok dInfo hd_mem (r.toEntry ML.names)
              (List.mem_map_of_mem hr)
            exact hdro.2.1
          have ⟨hslice₁, hlen₁⟩ := foldl_patchDataReloc_slice_abs64 (lib := ML.toMultiPlacedLib)
            (mpl := mpl) (names := ML.names) (addr := mpl.ρ dInfo.sym) d.relocs d.bytes rfl hrs_ok hhas
          have ⟨hslice₂, hlen₂⟩ := foldl_patchDataReloc_slice_abs64 (lib := ML.toMultiPlacedLib)
            (mpl := mpl₀) (names := ML.names) (addr := mpl₀.ρ dInfo.sym) d.relocs d.bytes rfl hrs_ok hhas
          have hlen_s₁ : (((d.relocs.map (Reloc.toEntry ML.names)).foldl
              (ML.toMultiPlacedLib.patchDataReloc mpl (mpl.ρ dInfo.sym)) d.bytes).drop off).length ≥ 8 := by
            have := congrArg List.length hslice₁
            rw [List.length_take, RoDataFactsAux.bytesLE_length] at this
            omega
          have hlen_s₂ : (((d.relocs.map (Reloc.toEntry ML.names)).foldl
              (ML.toMultiPlacedLib.patchDataReloc mpl₀ (mpl₀.ρ dInfo.sym)) d.bytes).drop off).length ≥ 8 := by
            have := congrArg List.length hslice₂
            rw [List.length_take, RoDataFactsAux.bytesLE_length] at this
            omega
          have hpd_slice := congrArg (fun bs => (bs.drop off).take 8) hpd
          unfold MultiPlacedLib.patchedData at hpd_slice
          change (((((d.relocs.map (Reloc.toEntry ML.names)).foldl
              (ML.toMultiPlacedLib.patchDataReloc mpl (mpl.ρ dInfo.sym)) d.bytes) ++
              List.replicate d.zeroTail 0#8).drop off).take 8) =
            (((((d.relocs.map (Reloc.toEntry ML.names)).foldl
              (ML.toMultiPlacedLib.patchDataReloc mpl₀ (mpl₀.ρ dInfo.sym)) d.bytes) ++
              List.replicate d.zeroTail 0#8).drop off).take 8) at hpd_slice
          rw [List.drop_append_of_le_length (by rw [List.length_drop] at hlen_s₁; omega),
            List.take_append_of_le_length hlen_s₁,
            List.drop_append_of_le_length (by rw [List.length_drop] at hlen_s₂; omega),
            List.take_append_of_le_length hlen_s₂,
            hslice₁, hslice₂] at hpd_slice
          have hres := addSignedAddr_inj (bytesLE_8_inj hpd_slice)
          exact ⟨hB, setFresh_unit_preserves hset hS hres⟩
      · nomatch hstep
    · nomatch hstep

theorem checkInvStepsLoop_sound {ML : MultiLib} {mpl mpl₀ : MultiPlacement} {img : ElfImage}
    {tSym : VecTree (Option (Nat × Nat))}
    (hnd : ML.names.Nodup) (hids : ML.idsOk = true)
    (hblks_lt : ML.blocks.length < 2 ^ 20) (hdata_lt : ML.data.length < 2 ^ 20)
    (hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks)
    (hpl : ML.toMultiPlacedLib.Placeable mpl) (hin : ML.toMultiPlacedLib.InElf img mpl)
    (hpl₀ : ML.toMultiPlacedLib.Placeable mpl₀) (hin₀ : ML.toMultiPlacedLib.InElf img mpl₀)
    (hrelax₀ : ∀ i o, mpl₀.relax i o = false) :
    ∀ (steps : List InvStep) (tBlkKnown tSymKnown tBlkKnown' tSymKnown' : VecTree (Option Unit)),
      (∀ i, tBlkKnown.getD none i = some () → i < ML.blocks.length ∧ mpl.base i = mpl₀.base i) →
      (∀ s, tSymKnown.getD none s = some () →
        ML.toMultiPlacedLib.resolve mpl (ML.names.getD s "") =
          ML.toMultiPlacedLib.resolve mpl₀ (ML.names.getD s "")) →
      checkInvStepsLoop ML (toVecTree defaultBlock ML.blocks) (toVecTree defaultData ML.data)
        tSym tBlkKnown tSymKnown steps = some (tBlkKnown', tSymKnown') →
      (∀ i, tBlkKnown'.getD none i = some () → i < ML.blocks.length ∧ mpl.base i = mpl₀.base i) ∧
      (∀ s, tSymKnown'.getD none s = some () →
        ML.toMultiPlacedLib.resolve mpl (ML.names.getD s "") =
          ML.toMultiPlacedLib.resolve mpl₀ (ML.names.getD s ""))
  | [], tB, tS, tB', tS', hB, hS, h => by
    injection h with h
    cases h
    exact ⟨hB, hS⟩
  | step :: rest, tB, tS, tB', tS', hB, hS, h => by
    simp only [checkInvStepsLoop] at h
    cases hs : checkInvStepB ML (toVecTree defaultBlock ML.blocks) (toVecTree defaultData ML.data)
        tSym tB tS step with
    | none => rw [hs] at h; nomatch h
    | some p =>
      rcases p with ⟨tB1, tS1⟩
      rw [hs] at h
      obtain ⟨hB1, hS1⟩ := checkInvStepB_sound hnd hids hblks_lt hdata_lt hlookup
        hpl hin hpl₀ hin₀ hrelax₀ hB hS hs
      exact checkInvStepsLoop_sound hnd hids hblks_lt hdata_lt hlookup
        hpl hin hpl₀ hin₀ hrelax₀ rest tB1 tS1 tB' tS' hB1 hS1 h

/-- Soundness of `checkRelocInvStepsB`: any `mpl` satisfying `lib.Placeable mpl ∧ lib.InElf img mpl`
agrees with `mpl₀` on all block bases, symbol resolutions in `ML.names`, and `lib.DataDisjoint`. -/
theorem checkRelocInvStepsB_sound {lib : MultiPlacedLib} {ML : MultiLib}
    {nameChars : List (List Char)} {steps : List InvStep}
    {img : ElfImage} {mpl mpl₀ : MultiPlacement}
    (hlib : lib = ML.toMultiPlacedLib)
    (hnames : ML.names = nameChars.map String.ofList)
    (hchk : checkRelocInvStepsB ML nameChars steps = true)
    (hrelax₀ : ∀ i o, mpl₀.relax i o = false)
    (h₀ : lib.Placeable mpl₀ ∧ lib.InElf img mpl₀ ∧ lib.DataDisjoint mpl₀)
    (h : lib.Placeable mpl ∧ lib.InElf img mpl) :
    (∀ i < lib.blocks.length, mpl.base i = mpl₀.base i) ∧
    (∀ s ∈ ML.names, lib.resolve mpl s = lib.resolve mpl₀ s) ∧
    (∀ s ∈ ML.names, lookupBlockSym s lib.blocks = none → mpl.ρ s = mpl₀.ρ s) ∧
    lib.DataDisjoint mpl := by
  subst hlib
  unfold checkRelocInvStepsB at hchk
  simp only [withVecTree_eq, withNat_eq, multiIdsOkFast_eq, Bool.and_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hblks_lt, hdata_lt⟩, hnames_lt⟩, hnn⟩, hids⟩, hrest⟩ := hchk
  have hnd := nodup_of_namesNodup hnames hnn
  cases hsym : insertAllBlocks 0 ML.blocks (mkNoneTree 20 ML.names.length) with
  | none => rw [hsym] at hrest; nomatch hrest
  | some tSym =>
    rw [hsym] at hrest; dsimp only at hrest
    obtain ⟨_, _, hget_sym⟩ := insertAllBlocks_spec 0 ML.blocks _ tSym hsym
    have hlookup : ∀ q, tSym.getD none q = lookupBlockSymId q ML.blocks := by
      intro q; rw [hget_sym q, getD_mkNoneTree]; rfl
    cases hloop : checkInvStepsLoop ML (toVecTree defaultBlock ML.blocks)
        (toVecTree defaultData ML.data) tSym
        (mkNoneTree 20 ML.blocks.length) (mkNoneTree 20 ML.names.length) steps with
    | none => rw [hloop] at hrest; nomatch hrest
    | some p =>
      rcases p with ⟨tBlkKnown, tSymKnown⟩
      rw [hloop] at hrest; dsimp only at hrest
      simp only [Bool.and_eq_true] at hrest
      obtain ⟨hall_blk, hall_sym⟩ := hrest
      obtain ⟨hB, hS⟩ := checkInvStepsLoop_sound hnd hids hblks_lt hdata_lt hlookup
        h.1 h.2 h₀.1 h₀.2.1 hrelax₀ steps _ _ _ _
        (fun i hi => by rw [getD_mkNoneTree] at hi; nomatch hi)
        (fun s hs => by rw [getD_mkNoneTree] at hs; nomatch hs)
        hloop
      have hB_all := allKnown_of_all hB hall_blk
      have hS_all := allKnown_of_all hS hall_sym
      have hbase_eq : ∀ i < ML.toMultiPlacedLib.blocks.length, mpl.base i = mpl₀.base i := by
        intro i hi
        simp only [MultiLib.toMultiPlacedLib_blocks, List.length_map] at hi
        exact (hB_all i hi).2
      have hres_eq : ∀ s ∈ ML.names,
          ML.toMultiPlacedLib.resolve mpl s = ML.toMultiPlacedLib.resolve mpl₀ s := by
        intro s hs
        obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hs
        rw [← getD_of_lt hidx]
        exact hS_all idx hidx
      have hρ_eq : ∀ s ∈ ML.names,
          lookupBlockSym s ML.toMultiPlacedLib.blocks = none → mpl.ρ s = mpl₀.ρ s := by
        intro s hs hnone
        have hr := hres_eq s hs
        rwa [MultiPlacedLib.resolve_of_lookup_none hnone,
          MultiPlacedLib.resolve_of_lookup_none hnone] at hr
      refine ⟨hbase_eq, hres_eq, hρ_eq, ?_⟩
      unfold MultiPlacedLib.DataDisjoint
      have hdd₀ := h₀.2.2
      unfold MultiPlacedLib.DataDisjoint at hdd₀
      have hok0 := ML.emptyBlock_idsOk hids
      have hmap_eq : (ML.toMultiPlacedLib.data.map fun d =>
          (d.readOnly, mpl.ρ d.sym, (ML.toMultiPlacedLib.patchedData mpl d).length)) =
          (ML.toMultiPlacedLib.data.map fun d =>
            (d.readOnly, mpl₀.ρ d.sym, (ML.toMultiPlacedLib.patchedData mpl₀ d).length)) := by
        refine List.map_congr_left fun d hd => ?_
        have hd' := hd
        simp only [MultiLib.toMultiPlacedLib_data, List.mem_map] at hd'
        obtain ⟨d_raw, hd_raw, rfl⟩ := hd'
        have hdsym_lt : d_raw.sym < ML.names.length := (hok0.data d_raw hd_raw).1
        have hdsym_mem : (d_raw.toInfo ML.names).sym ∈ ML.names := by
          show ML.names.getD d_raw.sym "" ∈ ML.names
          rw [getD_of_lt hdsym_lt]
          exact List.getElem_mem hdsym_lt
        have haddr := hρ_eq _ hdsym_mem (h.1.data_ok _ hd).1
        have hlen₁ := length_patchedData_multi (lib := ML.toMultiPlacedLib) (mpl := mpl)
          (fun r hr => (h.1.data_relocs_ok _ hd r hr).2.1)
        have hlen₂ := length_patchedData_multi (lib := ML.toMultiPlacedLib) (mpl := mpl₀)
          (fun r hr => (h₀.1.data_relocs_ok _ hd r hr).2.1)
        rw [haddr, hlen₁, hlen₂]
      exact pairwise_of_map_eq
        (R := fun (ro1, a1, n1) (ro2, a2, n2) =>
          (ro1 = true ∧ ro2 = true) ∨ ∀ a, InRegion a1 n1 a → ¬ InRegion a2 n2 a)
        (fun d => (d.readOnly, mpl.ρ d.sym, (ML.toMultiPlacedLib.patchedData mpl d).length))
        (fun d => (d.readOnly, mpl₀.ρ d.sym, (ML.toMultiPlacedLib.patchedData mpl₀ d).length))
        hmap_eq hdd₀

end Interned

end Arm64.Obj
