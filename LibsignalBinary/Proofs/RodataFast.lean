/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RoDataReloc
public import GeneratedLean.LibsignalSessionObj

/-!
# Reflected `.rodata` and Relocation Lookup Trees

**Checked by Lean.**

Elaboration-time reflected balanced trees over `libsignalSessionImage` reducing `.rodata` and
`.data.rel.ro` queries from linear scans over `data` / `relocs` / `roData` to $O(\log N + n)$
kernel steps:
1. `ByteTree` (`lsDataTree`): balanced byte tree (`lsDataTree.toBytes = libsignalSessionImage.data`
   by `rfl_kernel`) with $O(\log N + n)$ slice extraction (`lsData_slice_eq`).
2. `RelocTree` (`lsRelocTree`): offset-sorted BST of `libsignalSessionImage.relocs` supporting
   $O(\log N)$ `noRelocInRange` (`noRelocInRange_of_tree`) and `reloc64At` (`reloc64At_of_tree`).
3. `RoRangeTree` (`lsRoRangeTree`): interval BST of `libsignalSessionImage.roData` supporting
   $O(\log N)$ `inLiRoData` (`inLiRoData_of_tree`) and `mem_roData_of_tree`.
4. Separation-logic introduction lemmas (`rodata_slice_fast_intro`, `rodata64_fast_intro`,
   `reloc64_fast_intro`, `rodata_loads_fast_intro`, and `SepWP` counterparts).
-/

@[expose] public section

namespace CryptoVerification.RodataFast

open Arm64 Arm64.Obj ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoProofLib.RoDataReloc

/-! ## 1. `ByteTree`: $O(\log N + n)$ Byte-Slice Tree -/

/-- Balanced binary tree of bytes storing the left-subtree byte count at each internal node. -/
inductive ByteTree where
  | empty : ByteTree
  | leaf : BitVec 8 → ByteTree
  | node : Nat → ByteTree → ByteTree → ByteTree

/-- Flatten `t` onto `acc` without intermediate list appends. -/
def ByteTree.toBytesAux : ByteTree → List (BitVec 8) → List (BitVec 8)
  | .empty, acc => acc
  | .leaf b, acc => b :: acc
  | .node _ l r, acc => l.toBytesAux (r.toBytesAux acc)

/-- Byte list represented by `t`. -/
def ByteTree.toBytes (t : ByteTree) : List (BitVec 8) :=
  t.toBytesAux []

private theorem ByteTree.toBytesAux_eq_append :
    ∀ (t : ByteTree) (acc : List (BitVec 8)), t.toBytesAux acc = t.toBytes ++ acc
  | .empty, _ => rfl
  | .leaf _, _ => rfl
  | .node _ l r, acc => by
    dsimp only [toBytes, toBytesAux]
    rw [toBytesAux_eq_append l (r.toBytesAux acc),
        toBytesAux_eq_append r acc,
        toBytesAux_eq_append l (r.toBytesAux []),
        toBytesAux_eq_append r [],
        List.append_nil, List.append_assoc]

/-- Verify every internal `leftLen` field and return total byte count using pure `Nat` primitives. -/
def ByteTree.checkSize? : ByteTree → Option Nat
  | .empty => some 0
  | .leaf _ => some 1
  | .node lw l r =>
    match l.checkSize?, r.checkSize? with
    | some nl, some nr =>
      match Nat.beq lw nl with
      | true => some (nl + nr)
      | false => none
    | _, _ => none

theorem ByteTree.toBytes_length_of_checkSize? :
    ∀ (t : ByteTree) {sz : Nat}, t.checkSize? = some sz → t.toBytes.length = sz
  | .empty, _, h => by
    simp only [checkSize?, Option.some.injEq] at h
    subst h; rfl
  | .leaf _, _, h => by
    simp only [checkSize?, Option.some.injEq] at h
    subst h; rfl
  | .node lw l r, _, h => by
    dsimp only [checkSize?] at h
    cases hl : l.checkSize? with
    | none => rw [hl] at h; nomatch h
    | some nl =>
      cases hr : r.checkSize? with
      | none => rw [hl, hr] at h; nomatch h
      | some nr =>
        rw [hl, hr] at h
        dsimp only at h
        cases hbeq : Nat.beq lw nl with
        | false => rw [hbeq] at h; nomatch h
        | true =>
          rw [hbeq] at h
          injection h with hsz
          subst hsz
          rw [toBytes, toBytesAux, toBytesAux_eq_append l, toBytesAux_eq_append r,
              List.append_nil, List.length_append,
              toBytes_length_of_checkSize? l hl, toBytes_length_of_checkSize? r hr]

/-- Accumulator-based $O(\log N + n)$ slice extraction using primitive `Nat.beq`/`Nat.ble`. -/
def ByteTree.sliceAux : ByteTree → Nat → Nat → List (BitVec 8) → List (BitVec 8)
  | .empty, _, _, acc => acc
  | .leaf b, k, n, acc =>
    match Nat.beq k 0, Nat.beq n 0 with
    | true, false => b :: acc
    | _, _ => acc
  | .node lw l r, k, n, acc =>
    match Nat.beq n 0 with
    | true => acc
    | false =>
      match Nat.ble lw k with
      | true => r.sliceAux (k - lw) n acc
      | false =>
        match Nat.ble (k + n) lw with
        | true => l.sliceAux k n acc
        | false => l.sliceAux k (lw - k) (r.sliceAux 0 (k + n - lw) acc)

/-- Extract `(t.toBytes.drop k).take n` in $O(\log N + n)$ steps. -/
def ByteTree.slice (t : ByteTree) (k n : Nat) : List (BitVec 8) :=
  t.sliceAux k n []

private theorem ByteTree.sliceAux_eq :
    ∀ (t : ByteTree) {sz : Nat}, t.checkSize? = some sz →
      ∀ (k n : Nat) (acc : List (BitVec 8)),
        t.sliceAux k n acc = (t.toBytes.drop k).take n ++ acc
  | .empty, _, _, k, n, acc => by
    simp [sliceAux, toBytes, toBytesAux]
  | .leaf b, _, _, k, n, acc => by
    dsimp only [sliceAux, toBytes, toBytesAux]
    cases hk : Nat.beq k 0 <;> cases hn : Nat.beq n 0 <;> dsimp only
    · have hk' : 1 ≤ k := by have := Nat.ne_of_beq_eq_false hk; omega
      rw [List.drop_eq_nil_of_le (by simp; omega), List.take_nil, List.nil_append]
    · have hn' : n = 0 := Nat.eq_of_beq_eq_true hn
      subst hn'; simp
    · have hk' : k = 0 := Nat.eq_of_beq_eq_true hk
      have hn' : n ≠ 0 := Nat.ne_of_beq_eq_false hn
      subst hk'
      rcases Nat.exists_eq_succ_of_ne_zero hn' with ⟨m, rfl⟩
      simp
    · have hn' : n = 0 := Nat.eq_of_beq_eq_true hn
      subst hn'; simp
  | .node lw l r, _, hsz, k, n, acc => by
    dsimp only [checkSize?] at hsz
    cases hl : l.checkSize? with
    | none => rw [hl] at hsz; nomatch hsz
    | some nl =>
      cases hr : r.checkSize? with
      | none => rw [hl, hr] at hsz; nomatch hsz
      | some nr =>
        rw [hl, hr] at hsz
        dsimp only at hsz
        cases hbeq : Nat.beq lw nl with
        | false => rw [hbeq] at hsz; nomatch hsz
        | true =>
          have hlw : lw = nl := Nat.eq_of_beq_eq_true hbeq
          subst hlw
          have hlen_l : l.toBytes.length = lw := toBytes_length_of_checkSize? l hl
          have htb : (ByteTree.node lw l r).toBytes = l.toBytes ++ r.toBytes := by
            rw [toBytes, toBytesAux, toBytesAux_eq_append l, toBytesAux_eq_append r, List.append_nil]
          rw [htb]
          dsimp only [sliceAux]
          cases hn : Nat.beq n 0 <;> dsimp only
          · cases hble1 : Nat.ble lw k <;> dsimp only
            · have hk_lt : k < lw := by
                cases Nat.lt_or_ge k lw with
                | inl h => exact h
                | inr h => exfalso; rw [Nat.ble_eq.mpr h] at hble1; nomatch hble1
              have hk_sub : k - l.toBytes.length = 0 := by omega
              rw [List.drop_append, hk_sub, List.drop_zero]
              cases hble2 : Nat.ble (k + n) lw <;> dsimp only
              · have hkn_gt : lw < k + n := by
                  cases Nat.lt_or_ge lw (k + n) with
                  | inl h => exact h
                  | inr h => exfalso; rw [Nat.ble_eq.mpr h] at hble2; nomatch hble2
                rw [sliceAux_eq l hl k (lw - k), sliceAux_eq r hr 0 (k + n - lw),
                    List.drop_zero, List.take_append]
                have hdrop_len : (l.toBytes.drop k).length = lw - k := by
                  rw [List.length_drop, hlen_l]
                have htake1 : (l.toBytes.drop k).take (lw - k) = l.toBytes.drop k :=
                  List.take_of_length_le (by omega)
                have htake2 : (l.toBytes.drop k).take n = l.toBytes.drop k :=
                  List.take_of_length_le (by omega)
                have hrem : n - (l.toBytes.drop k).length = k + n - lw := by omega
                rw [htake1, htake2, hrem, List.append_assoc]
              · have hkn_le : k + n ≤ lw := Nat.le_of_ble_eq_true hble2
                rw [sliceAux_eq l hl k n, List.take_append]
                have hdrop_len : (l.toBytes.drop k).length = lw - k := by
                  rw [List.length_drop, hlen_l]
                have hrem : n - (l.toBytes.drop k).length = 0 := by omega
                rw [hrem, List.take_zero, List.append_nil]
            · have hk_ge : lw ≤ k := Nat.le_of_ble_eq_true hble1
              have hdrop_nil : l.toBytes.drop k = [] := List.drop_eq_nil_of_le (by omega)
              rw [sliceAux_eq r hr (k - lw) n acc, List.drop_append, hdrop_nil, hlen_l,
                  List.nil_append]
          · have hn' : n = 0 := Nat.eq_of_beq_eq_true hn
            subst hn'; simp

theorem ByteTree.slice_eq_drop_take {t : ByteTree} {sz : Nat}
    (hsz : t.checkSize? = some sz) (k n : Nat) :
    (t.toBytes.drop k).take n = t.slice k n := by
  rw [slice, sliceAux_eq t hsz k n [], List.append_nil]

/-- Pure `Bool` equality on `List (BitVec 8)` using `Nat.beq` (zero `Decidable` proof terms). -/
def byteListBeq : List (BitVec 8) → List (BitVec 8) → Bool
  | [], [] => true
  | a :: as, b :: bs =>
    match Nat.beq a.toNat b.toNat with
    | true => byteListBeq as bs
    | false => false
  | _, _ => false

theorem eq_of_byteListBeq :
    ∀ {xs ys : List (BitVec 8)}, byteListBeq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | a :: as, b :: bs, h => by
    dsimp only [byteListBeq] at h
    cases hb : Nat.beq a.toNat b.toNat with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      have hab : a = b := BitVec.eq_of_toNat_eq (Nat.eq_of_beq_eq_true hb)
      rw [hab, eq_of_byteListBeq h]

/-! ## 2. `IdxTree α`: Balanced Original-Order Tree for $O(\log N)$ Witness Indexing -/

/-- Balanced binary tree preserving exact list order so `.toList = srcList` holds by `rfl_kernel`. -/
inductive IdxTree (α : Type) where
  | empty : IdxTree α
  | leaf : α → IdxTree α
  | node : Nat → IdxTree α → IdxTree α → IdxTree α

def IdxTree.toListAux {α : Type} : IdxTree α → List α → List α
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node _ l r, acc => l.toListAux (r.toListAux acc)

def IdxTree.toList {α : Type} (t : IdxTree α) : List α :=
  t.toListAux []

private theorem IdxTree.toListAux_eq_append {α : Type} :
    ∀ (t : IdxTree α) (acc : List α), t.toListAux acc = t.toList ++ acc
  | .empty, _ => rfl
  | .leaf _, _ => rfl
  | .node _ l r, acc => by
    dsimp only [toList, toListAux]
    rw [toListAux_eq_append l (r.toListAux acc),
        toListAux_eq_append r acc,
        toListAux_eq_append l (r.toListAux []),
        toListAux_eq_append r [],
        List.append_nil, List.append_assoc]

def IdxTree.get? {α : Type} : IdxTree α → Nat → Option α
  | .empty, _ => none
  | .leaf x, idx =>
    match Nat.beq idx 0 with
    | true => some x
    | false => none
  | .node lw l r, idx =>
    match Nat.ble lw idx with
    | true => r.get? (idx - lw)
    | false => l.get? idx

theorem IdxTree.mem_toList_of_get? {α : Type} :
    ∀ (t : IdxTree α) (idx : Nat) {x : α}, t.get? idx = some x → x ∈ t.toList
  | .empty, _, _, h => nomatch h
  | .leaf y, idx, _, h => by
    dsimp only [get?] at h
    cases hb : Nat.beq idx 0 with
    | false => rw [hb] at h; nomatch h
    | true =>
      rw [hb] at h
      injection h with hy
      subst hy
      exact List.mem_singleton.mpr rfl
  | .node lw l r, idx, _, h => by
    have htl : (IdxTree.node lw l r).toList = l.toList ++ r.toList := by
      rw [toList, toListAux, toListAux_eq_append l, toListAux_eq_append r, List.append_nil]
    rw [htl]
    dsimp only [get?] at h
    cases hb : Nat.ble lw idx with
    | true =>
      rw [hb] at h
      exact List.mem_append_right _ (mem_toList_of_get? r (idx - lw) h)
    | false =>
      rw [hb] at h
      exact List.mem_append_left _ (mem_toList_of_get? l idx h)

def IdxTree.all {α : Type} (p : α → Bool) : IdxTree α → Bool
  | .empty => true
  | .leaf x => p x
  | .node _ l r =>
    match l.all p with
    | true => r.all p
    | false => false

theorem IdxTree.forall_toList_of_all {α : Type} {p : α → Bool} :
    ∀ (t : IdxTree α), t.all p = true → ∀ x ∈ t.toList, p x = true
  | .empty, _, _, hx => nomatch hx
  | .leaf y, h, x, hx => by
    simp only [toList, toListAux, List.mem_singleton] at hx
    subst hx
    exact h
  | .node lw l r, h, x, hx => by
    have htl : (IdxTree.node lw l r).toList = l.toList ++ r.toList := by
      rw [toList, toListAux, toListAux_eq_append l, toListAux_eq_append r, List.append_nil]
    rw [htl, List.mem_append] at hx
    dsimp only [all] at h
    cases hl : l.all p with
    | false => rw [hl] at h; nomatch h
    | true =>
      rw [hl] at h
      rcases hx with hxl | hxr
      · exact forall_toList_of_all l hl x hxl
      · exact forall_toList_of_all r h x hxr

/-! ## 3. `RelocTree`: Balanced BST over `DataReloc` -/

/-- Balanced BST of data relocations `(off, width, target, origIdx)` sorted by `off`. -/
inductive RelocTree where
  | empty : RelocTree
  | node : Nat → Nat → Nat → Nat → RelocTree → RelocTree → RelocTree

/-- Tree membership predicate for `DataReloc`. -/
def RelocTree.InTree (q : DataReloc) : RelocTree → Prop
  | .empty => False
  | .node off width target _ l r =>
    q = DataReloc.mk off width target ∨ l.InTree q ∨ r.InTree q

/-- Check that all relocations in `t` are non-empty, pairwise disjoint, and inside `[lo, hi]`. -/
def RelocTree.checkDisjoint (lo hi : Nat) : RelocTree → Bool
  | .empty => Nat.ble lo hi
  | .node off width _ _ l r =>
    match Nat.ble 1 width, Nat.ble lo off, Nat.ble (off + width) hi with
    | true, true, true =>
      match l.checkDisjoint lo off with
      | true => r.checkDisjoint (off + width) hi
      | false => false
    | _, _, _ => false

/-- Check that every node in `t` matches its witness index in `orig`. -/
def RelocTree.allMatchOrig (orig : IdxTree DataReloc) : RelocTree → Bool
  | .empty => true
  | .node off width target origIdx l r =>
    let okHere :=
      match orig.get? origIdx with
      | some d => Nat.beq d.off off && Nat.beq d.width width && Nat.beq d.target target
      | none => false
    match okHere with
    | true =>
      match l.allMatchOrig orig with
      | true => r.allMatchOrig orig
      | false => false
    | false => false

/-- $O(\log N)$ exact relocation lookup by `q.off`. -/
def RelocTree.containsExact (q : DataReloc) : RelocTree → Bool
  | .empty => false
  | .node off width target _ l r =>
    match Nat.ble (q.off + 1) off with
    | true => l.containsExact q
    | false =>
      match Nat.ble (off + 1) q.off with
      | true => r.containsExact q
      | false => Nat.beq q.off off && Nat.beq q.width width && Nat.beq q.target target

/-- $O(\log N)$ range disjointness check for `[k, k + n)`. -/
def RelocTree.noOverlap (k n : Nat) : RelocTree → Bool
  | .empty => true
  | .node off width _ _ l r =>
    match Nat.ble (k + n) off with
    | true => l.noOverlap k n
    | false =>
      match Nat.ble (off + width) k with
      | true => r.noOverlap k n
      | false => false

/-- $O(\log N)$ 8-byte relocation lookup at `(k, target)`. -/
def RelocTree.hasReloc64At (k target : Nat) : RelocTree → Bool
  | .empty => false
  | .node off width tgt _ l r =>
    match Nat.ble (k + 1) off with
    | true => l.hasReloc64At k target
    | false =>
      match Nat.ble (off + 1) k with
      | true => r.hasReloc64At k target
      | false => Nat.beq off k && Nat.beq width 8 && Nat.beq tgt target

private theorem RelocTree.inTree_of_containsExact :
    ∀ (t : RelocTree) {q : DataReloc}, t.containsExact q = true → t.InTree q
  | .empty, _, h => nomatch h
  | .node off width target _ l r, q, h => by
    dsimp only [containsExact] at h
    cases hb1 : Nat.ble (q.off + 1) off with
    | true =>
      rw [hb1] at h
      exact Or.inr (Or.inl (inTree_of_containsExact l h))
    | false =>
      rw [hb1] at h
      cases hb2 : Nat.ble (off + 1) q.off with
      | true =>
        rw [hb2] at h
        exact Or.inr (Or.inr (inTree_of_containsExact r h))
      | false =>
        rw [hb2] at h
        simp only [Bool.and_eq_true] at h
        have h1 := Nat.eq_of_beq_eq_true h.1.1
        have h2 := Nat.eq_of_beq_eq_true h.1.2
        have h3 := Nat.eq_of_beq_eq_true h.2
        cases q
        dsimp only at h1 h2 h3
        subst h1; subst h2; subst h3
        exact Or.inl rfl

private theorem RelocTree.inTree_of_hasReloc64At :
    ∀ (t : RelocTree) {k target : Nat},
      t.hasReloc64At k target = true → t.InTree (DataReloc.mk k 8 target)
  | .empty, _, _, h => nomatch h
  | .node off width tgt _ l r, k, target, h => by
    dsimp only [hasReloc64At] at h
    cases hb1 : Nat.ble (k + 1) off with
    | true =>
      rw [hb1] at h
      exact Or.inr (Or.inl (inTree_of_hasReloc64At l h))
    | false =>
      rw [hb1] at h
      cases hb2 : Nat.ble (off + 1) k with
      | true =>
        rw [hb2] at h
        exact Or.inr (Or.inr (inTree_of_hasReloc64At r h))
      | false =>
        rw [hb2] at h
        simp only [Bool.and_eq_true] at h
        have h1 := Nat.eq_of_beq_eq_true h.1.1
        have h2 := Nat.eq_of_beq_eq_true h.1.2
        have h3 := Nat.eq_of_beq_eq_true h.2
        subst h1; subst h2; subst h3
        exact Or.inl rfl

private theorem RelocTree.mem_orig_of_allMatchOrig {orig : IdxTree DataReloc} :
    ∀ (t : RelocTree), t.allMatchOrig orig = true → ∀ {q : DataReloc}, t.InTree q → q ∈ orig.toList
  | .empty, _, _, hq => nomatch hq
  | .node off width target origIdx l r, h, q, hq => by
    dsimp only [allMatchOrig] at h
    cases hg : orig.get? origIdx with
    | none => simp only [hg] at h; nomatch h
    | some d =>
      simp only [hg] at h
      cases hok : (Nat.beq d.off off && Nat.beq d.width width && Nat.beq d.target target) with
      | false => rw [hok] at h; nomatch h
      | true =>
        rw [hok] at h
        cases hl : l.allMatchOrig orig with
        | false => rw [hl] at h; nomatch h
        | true =>
          rw [hl] at h
          rcases hq with rfl | hql | hqr
          · simp only [Bool.and_eq_true] at hok
            have h1 := Nat.eq_of_beq_eq_true hok.1.1
            have h2 := Nat.eq_of_beq_eq_true hok.1.2
            have h3 := Nat.eq_of_beq_eq_true hok.2
            have hd : d = DataReloc.mk off width target := by
              cases d; dsimp only at h1 h2 h3; subst h1; subst h2; subst h3; rfl
            rw [← hd]
            exact IdxTree.mem_toList_of_get? orig origIdx hg
          · exact mem_orig_of_allMatchOrig l hl hql
          · exact mem_orig_of_allMatchOrig r h hqr

private theorem RelocTree.unpack_checkDisjoint {lo hi off width target origIdx : Nat}
    {l r : RelocTree}
    (h : (RelocTree.node off width target origIdx l r).checkDisjoint lo hi = true) :
    1 ≤ width ∧ lo ≤ off ∧ off + width ≤ hi ∧
      l.checkDisjoint lo off = true ∧ r.checkDisjoint (off + width) hi = true := by
  dsimp only [checkDisjoint] at h
  cases hw : Nat.ble 1 width <;> cases hlo : Nat.ble lo off <;>
    cases hhi : Nat.ble (off + width) hi <;> simp only [hw, hlo, hhi] at h <;> try contradiction
  cases hl : l.checkDisjoint lo off with
  | false => rw [hl] at h; nomatch h
  | true =>
    rw [hl] at h
    exact ⟨Nat.le_of_ble_eq_true hw, Nat.le_of_ble_eq_true hlo,
      Nat.le_of_ble_eq_true hhi, rfl, h⟩

private theorem RelocTree.inTree_bounds :
    ∀ (t : RelocTree) {lo hi : Nat},
      t.checkDisjoint lo hi = true →
      ∀ {q : DataReloc}, t.InTree q → 1 ≤ q.width ∧ lo ≤ q.off ∧ q.off + q.width ≤ hi
  | .empty, _, _, _, _, hq => nomatch hq
  | .node off width target origIdx l r, lo, hi, hwf, q, hq => by
    obtain ⟨hw, hlo, hhi, hl, hr⟩ := unpack_checkDisjoint hwf
    rcases hq with rfl | hql | hqr
    · exact ⟨hw, hlo, hhi⟩
    · obtain ⟨qw, qlo, qhi⟩ := inTree_bounds l hl hql
      exact ⟨qw, qlo, by omega⟩
    · obtain ⟨qw, qlo, qhi⟩ := inTree_bounds r hr hqr
      exact ⟨qw, by omega, qhi⟩

private theorem RelocTree.noOverlap_sound :
    ∀ (t : RelocTree) {lo hi k n : Nat},
      t.checkDisjoint lo hi = true →
      t.noOverlap k n = true →
      ∀ {q : DataReloc}, t.InTree q →
        q.off + q.width ≤ hi ∧ (q.off + q.width ≤ k ∨ k + n ≤ q.off)
  | .empty, _, _, _, _, _, _, _, hq => nomatch hq
  | .node off width target origIdx l r, lo, hi, k, n, hwf, hno, q, hq => by
    obtain ⟨hw, _, hhi, hl, hr⟩ := unpack_checkDisjoint hwf
    dsimp only [noOverlap] at hno
    cases hb1 : Nat.ble (k + n) off with
    | true =>
      rw [hb1] at hno
      have hkn : k + n ≤ off := Nat.le_of_ble_eq_true hb1
      rcases hq with rfl | hql | hqr
      · exact ⟨hhi, Or.inr hkn⟩
      · obtain ⟨qb, qd⟩ := noOverlap_sound l hl hno hql
        exact ⟨by omega, qd⟩
      · obtain ⟨_, qlo, qhi⟩ := inTree_bounds r hr hqr
        exact ⟨qhi, Or.inr (by omega)⟩
    | false =>
      rw [hb1] at hno
      cases hb2 : Nat.ble (off + width) k with
      | false => rw [hb2] at hno; nomatch hno
      | true =>
        rw [hb2] at hno
        have hok : off + width ≤ k := Nat.le_of_ble_eq_true hb2
        rcases hq with rfl | hql | hqr
        · exact ⟨hhi, Or.inl hok⟩
        · obtain ⟨_, _, qhi⟩ := inTree_bounds l hl hql
          exact ⟨by omega, Or.inl (by omega)⟩
        · exact noOverlap_sound r hr hno hqr

private theorem RelocTree.inTree_pairwise_disjoint :
    ∀ (t : RelocTree) {lo hi : Nat},
      t.checkDisjoint lo hi = true →
      ∀ {x y : DataReloc}, t.InTree x → t.InTree y →
        x = y ∨ x.off + x.width ≤ y.off ∨ y.off + y.width ≤ x.off
  | .empty, _, _, _, _, _, hx, _ => nomatch hx
  | .node off width target origIdx l r, lo, hi, hwf, x, y, hx, hy => by
    obtain ⟨hw, _, _, hl, hr⟩ := unpack_checkDisjoint hwf
    rcases hx with rfl | hxl | hxr
    · rcases hy with rfl | hyl | hyr
      · exact Or.inl rfl
      · obtain ⟨_, _, yhi⟩ := inTree_bounds l hl hyl
        exact Or.inr (Or.inr yhi)
      · obtain ⟨_, ylo, _⟩ := inTree_bounds r hr hyr
        exact Or.inr (Or.inl ylo)
    · rcases hy with rfl | hyl | hyr
      · obtain ⟨_, _, xhi⟩ := inTree_bounds l hl hxl
        exact Or.inr (Or.inl xhi)
      · exact inTree_pairwise_disjoint l hl hxl hyl
      · obtain ⟨_, _, xhi⟩ := inTree_bounds l hl hxl
        obtain ⟨_, ylo, _⟩ := inTree_bounds r hr hyr
        exact Or.inr (Or.inl (by omega))
    · rcases hy with rfl | hyl | hyr
      · obtain ⟨_, xlo, _⟩ := inTree_bounds r hr hxr
        exact Or.inr (Or.inr xlo)
      · obtain ⟨_, xlo, _⟩ := inTree_bounds r hr hxr
        obtain ⟨_, _, yhi⟩ := inTree_bounds l hl hyl
        exact Or.inr (Or.inr (by omega))
      · exact inTree_pairwise_disjoint r hr hxr hyr

private theorem reloc64At_of_mem_disjoint {rs : List DataReloc} {dataLen k target : Nat}
    (hmem : DataReloc.mk k 8 target ∈ rs)
    (hall : ∀ r ∈ rs, r.off + r.width ≤ dataLen ∧
      (r = DataReloc.mk k 8 target ∨ r.off + r.width ≤ k ∨ k + 8 ≤ r.off)) :
    reloc64At rs dataLen k target = true := by
  induction rs with
  | nil => nomatch hmem
  | cons r tail ih =>
    have hr_all := hall r (.head _)
    have hr_le : decide (r.off + r.width ≤ dataLen) = true := decide_eq_true hr_all.1
    dsimp only [reloc64At]
    rw [hr_le, Bool.true_and]
    by_cases htail : DataReloc.mk k 8 target ∈ tail
    · have hih := ih htail (fun r' hr' => hall r' (.tail _ hr'))
      rw [hih, Bool.or_true]
    · have hr_eq : r = DataReloc.mk k 8 target := by
        rcases List.mem_cons.mp hmem with h | h
        · exact h.symm
        · exact absurd h htail
      subst hr_eq
      have hmatch : decide (k = k ∧ 8 = 8 ∧ target = target) = true := decide_eq_true ⟨rfl, rfl, rfl⟩
      have hno : noRelocInRange tail dataLen k 8 = true := by
        rw [noRelocInRange, List.all_eq_true]
        intro r' hr'
        obtain ⟨hb, hdisj⟩ := hall r' (.tail _ hr')
        rcases hdisj with heq | h1 | h2
        · subst heq; exact absurd hr' htail
        · exact decide_eq_true ⟨hb, Or.inl h1⟩
        · exact decide_eq_true ⟨hb, Or.inr h2⟩
      rw [hmatch, hno, Bool.and_self, Bool.true_or]

/-! ## 4. `RoRangeTree`: Balanced BST over `.rodata` Ranges -/

/-- Balanced BST of `(rOff, rLen, lMaxEnd, origIdx)` `.rodata` intervals sorted by `(rOff, rLen)`. -/
inductive RoRangeTree where
  | empty : RoRangeTree
  | node : Nat → Nat → Nat → Nat → RoRangeTree → RoRangeTree → RoRangeTree

def RoRangeTree.InTree (p : Nat × Nat) : RoRangeTree → Prop
  | .empty => False
  | .node rOff rLen _ _ l r => p = (rOff, rLen) ∨ l.InTree p ∨ r.InTree p

def RoRangeTree.allMatchOrig (orig : IdxTree (Nat × Nat)) : RoRangeTree → Bool
  | .empty => true
  | .node rOff rLen _ origIdx l r =>
    let okHere :=
      match orig.get? origIdx with
      | some p => Nat.beq p.1 rOff && Nat.beq p.2 rLen
      | none => false
    match okHere with
    | true =>
      match l.allMatchOrig orig with
      | true => r.allMatchOrig orig
      | false => false
    | false => false

/-- $O(\log N)$ exact `(secOff, secLen)` pair lookup. -/
def RoRangeTree.containsPair (secOff secLen : Nat) : RoRangeTree → Bool
  | .empty => false
  | .node rOff rLen _ _ l r =>
    match Nat.ble (secOff + 1) rOff with
    | true => l.containsPair secOff secLen
    | false =>
      match Nat.ble (rOff + 1) secOff with
      | true => r.containsPair secOff secLen
      | false =>
        match Nat.ble (secLen + 1) rLen with
        | true => l.containsPair secOff secLen
        | false =>
          match Nat.ble (rLen + 1) secLen with
          | true => r.containsPair secOff secLen
          | false => Nat.beq secOff rOff && Nat.beq secLen rLen

/-- $O(\log N)$ check that some `.rodata` interval covers `[off, off + len)` without 64-bit wrap. -/
def RoRangeTree.covers (off len : Nat) : RoRangeTree → Bool
  | .empty => false
  | .node rOff rLen lMaxEnd _ l r =>
    match Nat.ble rOff off with
    | false => l.covers off len
    | true =>
      match Nat.ble (off + len) (rOff + rLen) && Nat.ble (rOff + rLen + 1) (2 ^ 64) with
      | true => true
      | false =>
        match r.covers off len with
        | true => true
        | false =>
          match Nat.ble (off + 1) lMaxEnd with
          | true => l.covers off len
          | false => false

private theorem RoRangeTree.mem_orig_of_allMatchOrig {orig : IdxTree (Nat × Nat)} :
    ∀ (t : RoRangeTree), t.allMatchOrig orig = true → ∀ {p : Nat × Nat}, t.InTree p → p ∈ orig.toList
  | .empty, _, _, hp => nomatch hp
  | .node rOff rLen _ origIdx l r, h, p, hp => by
    dsimp only [allMatchOrig] at h
    cases hg : orig.get? origIdx with
    | none => simp only [hg] at h; nomatch h
    | some d =>
      simp only [hg] at h
      cases hok : (Nat.beq d.1 rOff && Nat.beq d.2 rLen) with
      | false => rw [hok] at h; nomatch h
      | true =>
        rw [hok] at h
        cases hl : l.allMatchOrig orig with
        | false => rw [hl] at h; nomatch h
        | true =>
          rw [hl] at h
          rcases hp with rfl | hpl | hpr
          · simp only [Bool.and_eq_true] at hok
            have h1 := Nat.eq_of_beq_eq_true hok.1
            have h2 := Nat.eq_of_beq_eq_true hok.2
            have hd : d = (rOff, rLen) := Prod.ext h1 h2
            rw [← hd]
            exact IdxTree.mem_toList_of_get? orig origIdx hg
          · exact mem_orig_of_allMatchOrig l hl hpl
          · exact mem_orig_of_allMatchOrig r h hpr

private theorem RoRangeTree.inTree_of_containsPair :
    ∀ (t : RoRangeTree) {secOff secLen : Nat},
      t.containsPair secOff secLen = true → t.InTree (secOff, secLen)
  | .empty, _, _, h => nomatch h
  | .node rOff rLen _ _ l r, secOff, secLen, h => by
    dsimp only [containsPair] at h
    cases hb1 : Nat.ble (secOff + 1) rOff with
    | true => rw [hb1] at h; exact Or.inr (Or.inl (inTree_of_containsPair l h))
    | false =>
      rw [hb1] at h
      cases hb2 : Nat.ble (rOff + 1) secOff with
      | true => rw [hb2] at h; exact Or.inr (Or.inr (inTree_of_containsPair r h))
      | false =>
        rw [hb2] at h
        cases hb3 : Nat.ble (secLen + 1) rLen with
        | true => rw [hb3] at h; exact Or.inr (Or.inl (inTree_of_containsPair l h))
        | false =>
          rw [hb3] at h
          cases hb4 : Nat.ble (rLen + 1) secLen with
          | true => rw [hb4] at h; exact Or.inr (Or.inr (inTree_of_containsPair r h))
          | false =>
            rw [hb4] at h
            simp only [Bool.and_eq_true] at h
            exact Or.inl (Prod.ext (Nat.eq_of_beq_eq_true h.1) (Nat.eq_of_beq_eq_true h.2))

private theorem RoRangeTree.covers_sound :
    ∀ (t : RoRangeTree) {off len : Nat},
      t.covers off len = true →
      ∃ p : Nat × Nat, t.InTree p ∧ p.1 ≤ off ∧ off + len ≤ p.1 + p.2 ∧ p.1 + p.2 < 2 ^ 64
  | .empty, _, _, h => nomatch h
  | .node rOff rLen lMaxEnd _ l r, off, len, h => by
    dsimp only [covers] at h
    cases hb1 : Nat.ble rOff off with
    | false =>
      rw [hb1] at h
      obtain ⟨p, hp, h1, h2, h3⟩ := covers_sound l h
      exact ⟨p, Or.inr (Or.inl hp), h1, h2, h3⟩
    | true =>
      rw [hb1] at h
      cases hb2 : (Nat.ble (off + len) (rOff + rLen) && Nat.ble (rOff + rLen + 1) (2 ^ 64)) with
      | true =>
        simp only [Bool.and_eq_true] at hb2
        have hle1 := Nat.le_of_ble_eq_true hb1
        have hle2 := Nat.le_of_ble_eq_true hb2.1
        have hlt3 : rOff + rLen < 2 ^ 64 := Nat.le_of_ble_eq_true hb2.2
        exact ⟨(rOff, rLen), Or.inl rfl, hle1, hle2, hlt3⟩
      | false =>
        rw [hb2] at h
        cases hrc : r.covers off len with
        | true =>
          obtain ⟨p, hp, h1, h2, h3⟩ := covers_sound r hrc
          exact ⟨p, Or.inr (Or.inr hp), h1, h2, h3⟩
        | false =>
          rw [hrc] at h
          cases hb3 : Nat.ble (off + 1) lMaxEnd with
          | false => rw [hb3] at h; nomatch h
          | true =>
            rw [hb3] at h
            obtain ⟨p, hp, h1, h2, h3⟩ := covers_sound l h
            exact ⟨p, Or.inr (Or.inl hp), h1, h2, h3⟩

/-! ## 5. Elaboration-Time Reflection of `libsignalSessionImage` -/

set_option maxRecDepth 2000000

open Lean Elab Term Meta in
local elab "ls_data_tree_of% " imgId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.data) (Lean.mkConst c))
  let leafFn := Lean.mkConst ``ByteTree.leaf
  let nodeFn := Lean.mkConst ``ByteTree.node
  let emptyTree := Lean.mkConst ``ByteTree.empty
  let rec build (fuel lo hi : Nat) : TermElabM Expr := do
    match fuel with
    | 0 => return emptyTree
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then return emptyTree
      else if len == 1 then return mkApp leafFn elems[lo]!
      else
        let half := len / 2
        let mid := lo + half
        let l ← build fuel' lo mid
        let r ← build fuel' mid hi
        return mkApp3 nodeFn (mkRawNatLit half) l r
  build 64 0 elems.size

open Lean Elab Term Meta in
local elab "ls_data_len_of% " imgId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.data) (Lean.mkConst c))
  elabTerm (Syntax.mkNumLit (toString elems.size)) (some (Lean.mkConst ``Nat))

open Lean Elab Term Meta in
local elab "ls_idx_tree_of% " imgId:ident fieldId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let fName := Name.mkStr (``Obj.LinkedImage) fieldId.getId.toString
  let fieldApp := mkApp (Lean.mkConst fName) (Lean.mkConst c)
  let fieldTy ← inferType fieldApp
  let fieldTyWhnf ← withTransparency .all (whnf fieldTy)
  unless fieldTyWhnf.isAppOfArity ``List 1 do
    throwError "ls_idx_tree_of%: expected `List` field, got {fieldTyWhnf}"
  let elemTy := fieldTyWhnf.getArg! 0
  let elems ← listElemsWhnf fieldApp
  let leafFn := mkApp (Lean.mkConst ``IdxTree.leaf) elemTy
  let nodeFn := mkApp (Lean.mkConst ``IdxTree.node) elemTy
  let emptyTree := mkApp (Lean.mkConst ``IdxTree.empty) elemTy
  let rec build (fuel lo hi : Nat) : TermElabM Expr := do
    match fuel with
    | 0 => return emptyTree
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then return emptyTree
      else if len == 1 then return mkApp leafFn elems[lo]!
      else
        let half := len / 2
        let mid := lo + half
        let l ← build fuel' lo mid
        let r ← build fuel' mid hi
        return mkApp3 nodeFn (mkRawNatLit half) l r
  build 64 0 elems.size

open Lean Elab Term Meta in
local elab "ls_reloc_tree_of% " imgId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.relocs) (Lean.mkConst c))
  let rec getNat (fuel : Nat) (e : Expr) : MetaM Nat := do
    if let some n := e.rawNatLit? then return n
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if let some n := (e.getArg! 1).rawNatLit? then return n
    match fuel with
    | 0 =>
      let r ← withTransparency .all (reduce e)
      if let some n := r.rawNatLit? then return n
      if r.isAppOfArity ``OfNat.ofNat 3 then
        if let some n := (r.getArg! 1).rawNatLit? then return n
      throwError "ls_reloc_tree_of%: expected Nat literal, got {e}"
    | fuel' + 1 =>
      let e' ← withTransparency .all (whnf e)
      getNat fuel' e'
  let mut arr : Array (Nat × Nat × Nat × Nat) := #[]
  for idx in [0 : elems.size] do
    let r ← withTransparency .all (whnf elems[idx]!)
    unless r.isAppOfArity ``Obj.DataReloc.mk 3 do
      throwError "ls_reloc_tree_of%: expected DataReloc.mk, got {r}"
    let off ← getNat 4 (r.getArg! 0)
    let width ← getNat 4 (r.getArg! 1)
    let target ← getNat 4 (r.getArg! 2)
    arr := arr.push (off, width, target, idx)
  let sorted := arr.qsort (fun a b => a.1 < b.1)
  let nodeFn := Lean.mkConst ``RelocTree.node
  let emptyTree := Lean.mkConst ``RelocTree.empty
  let rec build (fuel lo hi : Nat) : TermElabM Expr := do
    match fuel with
    | 0 => return emptyTree
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then return emptyTree
      else
        let mid := lo + len / 2
        let (off, width, target, origIdx) := sorted[mid]!
        let l ← build fuel' lo mid
        let r ← build fuel' (mid + 1) hi
        return mkApp6 nodeFn
          (mkRawNatLit off) (mkRawNatLit width) (mkRawNatLit target) (mkRawNatLit origIdx) l r
  build 64 0 sorted.size

open Lean Elab Term Meta in
local elab "ls_rorange_tree_of% " imgId:ident : term => do
  let c ← realizeGlobalConstNoOverload imgId
  let elems ← listElemsWhnf (mkApp (Lean.mkConst ``Obj.LinkedImage.roData) (Lean.mkConst c))
  let rec getNat (fuel : Nat) (e : Expr) : MetaM Nat := do
    if let some n := e.rawNatLit? then return n
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if let some n := (e.getArg! 1).rawNatLit? then return n
    match fuel with
    | 0 =>
      let r ← withTransparency .all (reduce e)
      if let some n := r.rawNatLit? then return n
      if r.isAppOfArity ``OfNat.ofNat 3 then
        if let some n := (r.getArg! 1).rawNatLit? then return n
      throwError "ls_rorange_tree_of%: expected Nat literal, got {e}"
    | fuel' + 1 =>
      let e' ← withTransparency .all (whnf e)
      getNat fuel' e'
  let mut arr : Array (Nat × Nat × Nat) := #[]
  for idx in [0 : elems.size] do
    let p ← withTransparency .all (whnf elems[idx]!)
    unless p.isAppOfArity ``Prod.mk 4 do
      throwError "ls_rorange_tree_of%: expected Prod.mk, got {p}"
    let rOff ← getNat 4 (p.getArg! 2)
    let rLen ← getNat 4 (p.getArg! 3)
    arr := arr.push (rOff, rLen, idx)
  let sorted := arr.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1))
  let nodeFn := Lean.mkConst ``RoRangeTree.node
  let emptyTree := Lean.mkConst ``RoRangeTree.empty
  let rec build (fuel lo hi : Nat) : TermElabM (Expr × Nat) := do
    match fuel with
    | 0 => return (emptyTree, 0)
    | fuel' + 1 =>
      let len := hi - lo
      if len == 0 then return (emptyTree, 0)
      else
        let mid := lo + len / 2
        let (rOff, rLen, origIdx) := sorted[mid]!
        let (l, lMax) ← build fuel' lo mid
        let (r, rMax) ← build fuel' (mid + 1) hi
        let myEnd := rOff + rLen
        let subMax := max myEnd (max lMax rMax)
        let e := mkApp6 nodeFn
          (mkRawNatLit rOff) (mkRawNatLit rLen) (mkRawNatLit lMax) (mkRawNatLit origIdx) l r
        return (e, subMax)
  return (← build 64 0 sorted.size).1

/-- Balanced `ByteTree` for `libsignalSessionImage.data`. -/
noncomputable def lsDataTree : ByteTree :=
  ls_data_tree_of% CryptoVerification.libsignalSessionImage

/-- Precomputed byte length of `libsignalSessionImage.data`. -/
def lsDataLen : Nat :=
  ls_data_len_of% CryptoVerification.libsignalSessionImage

/-- Balanced `IdxTree` for `libsignalSessionImage.relocs` in original list order. -/
noncomputable def lsRelocOrigTree : IdxTree DataReloc :=
  ls_idx_tree_of% CryptoVerification.libsignalSessionImage relocs

/-- Balanced BST for `libsignalSessionImage.relocs` sorted by offset. -/
noncomputable def lsRelocTree : RelocTree :=
  ls_reloc_tree_of% CryptoVerification.libsignalSessionImage

/-- Balanced `IdxTree` for `libsignalSessionImage.roData` in original list order. -/
noncomputable def lsRoOrigTree : IdxTree (Nat × Nat) :=
  ls_idx_tree_of% CryptoVerification.libsignalSessionImage roData

/-- Balanced BST for `libsignalSessionImage.roData` sorted by `(rOff, rLen)`. -/
noncomputable def lsRoRangeTree : RoRangeTree :=
  ls_rorange_tree_of% CryptoVerification.libsignalSessionImage

/-! ## 6. Once-Proved Soundness Certificates for `libsignalSessionImage` -/

theorem lsDataTree_toBytes : lsDataTree.toBytes = libsignalSessionImage.data := by
  rfl_kernel

theorem lsDataTree_checkSize : lsDataTree.checkSize? = some lsDataLen := by
  rfl_kernel

theorem lsDataLen_eq : libsignalSessionImage.data.length = lsDataLen := by
  rw [← lsDataTree_toBytes]
  exact ByteTree.toBytes_length_of_checkSize? lsDataTree lsDataTree_checkSize

theorem lsData_slice_eq (k n : Nat) :
    (libsignalSessionImage.data.drop k).take n = lsDataTree.slice k n := by
  rw [← lsDataTree_toBytes]
  exact ByteTree.slice_eq_drop_take lsDataTree_checkSize k n

theorem lsData_slice_eq_of_beq {k n : Nat} {bs : List (BitVec 8)}
    (h : byteListBeq (lsDataTree.slice k n) bs = true := by rfl_kernel) :
    (libsignalSessionImage.data.drop k).take n = bs := by
  rw [lsData_slice_eq]
  exact eq_of_byteListBeq h

private theorem lsRelocOrigTree_toList :
    lsRelocOrigTree.toList = libsignalSessionImage.relocs := by
  rfl_kernel

private theorem lsRelocTree_wf :
    lsRelocTree.checkDisjoint 0 (lsDataLen + libsignalSessionImage.bss) = true := by
  rfl_kernel

private theorem lsRelocTree_matchOrig :
    lsRelocTree.allMatchOrig lsRelocOrigTree = true := by
  rfl_kernel

private theorem lsRelocOrig_allInBst :
    lsRelocOrigTree.all (fun r => lsRelocTree.containsExact r) = true := by
  rfl_kernel

private theorem lsRoOrigTree_toList :
    lsRoOrigTree.toList = libsignalSessionImage.roData := by
  rfl_kernel

private theorem lsRoRangeTree_matchOrig :
    lsRoRangeTree.allMatchOrig lsRoOrigTree = true := by
  rfl_kernel

private theorem mem_relocs_inTree {r : DataReloc} (hr : r ∈ libsignalSessionImage.relocs) :
    lsRelocTree.InTree r := by
  rw [← lsRelocOrigTree_toList] at hr
  exact RelocTree.inTree_of_containsExact lsRelocTree
    (IdxTree.forall_toList_of_all lsRelocOrigTree lsRelocOrig_allInBst r hr)

private theorem inTree_mem_relocs {r : DataReloc} (hr : lsRelocTree.InTree r) :
    r ∈ libsignalSessionImage.relocs := by
  rw [← lsRelocOrigTree_toList]
  exact RelocTree.mem_orig_of_allMatchOrig lsRelocTree lsRelocTree_matchOrig hr

private theorem inTree_mem_roData {p : Nat × Nat} (hp : lsRoRangeTree.InTree p) :
    p ∈ libsignalSessionImage.roData := by
  rw [← lsRoOrigTree_toList]
  exact RoRangeTree.mem_orig_of_allMatchOrig lsRoRangeTree lsRoRangeTree_matchOrig hp

/-! ## 7. $O(\log N)$ Query Theorems & Separation-Logic Wrappers -/

/-- $O(\log N)$ proof of `noRelocInRange` for `libsignalSessionImage`. -/
theorem noRelocInRange_of_tree {k n : Nat}
    (h : lsRelocTree.noOverlap k n = true := by rfl_kernel) :
    noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss) k n = true := by
  rw [lsDataLen_eq, noRelocInRange, List.all_eq_true]
  intro r hr
  exact decide_eq_true
    (RelocTree.noOverlap_sound lsRelocTree lsRelocTree_wf h (mem_relocs_inTree hr))

/-- $O(\log N)$ proof of `relocs.all` disjointness (for `Satisfies.of_rodata_loads`). -/
theorem relocs_all_disjoint_of_tree {k n : Nat}
    (h : lsRelocTree.noOverlap k n = true := by rfl_kernel) :
    libsignalSessionImage.relocs.all
      (fun r => decide (r.off + r.width ≤ k ∨ k + n ≤ r.off)) = true := by
  rw [List.all_eq_true]
  intro r hr
  exact decide_eq_true
    (RelocTree.noOverlap_sound lsRelocTree lsRelocTree_wf h (mem_relocs_inTree hr)).2

/-- $O(\log N)$ proof of `CryptoProofLib.RoDataReloc.reloc64At` for `libsignalSessionImage`. -/
theorem reloc64At_of_tree {k target : Nat}
    (h : lsRelocTree.hasReloc64At k target = true := by rfl_kernel) :
    reloc64At libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss) k target = true := by
  rw [lsDataLen_eq]
  have hin0 : lsRelocTree.InTree (DataReloc.mk k 8 target) :=
    RelocTree.inTree_of_hasReloc64At lsRelocTree h
  apply reloc64At_of_mem_disjoint (inTree_mem_relocs hin0)
  intro r hr
  have hin : lsRelocTree.InTree r := mem_relocs_inTree hr
  obtain ⟨_, _, hhi⟩ := RelocTree.inTree_bounds lsRelocTree lsRelocTree_wf hin
  refine ⟨hhi, ?_⟩
  rcases RelocTree.inTree_pairwise_disjoint lsRelocTree lsRelocTree_wf hin hin0 with
    heq | hle1 | hle2
  · exact Or.inl heq
  · exact Or.inr (Or.inl hle1)
  · exact Or.inr (Or.inr hle2)

/-- $O(\log N)$ proof of `inLiRoData` for `libsignalSessionImage`. -/
theorem inLiRoData_of_tree {off len : Nat}
    (h : lsRoRangeTree.covers off len = true := by rfl_kernel) :
    inLiRoData libsignalSessionImage off len = true := by
  obtain ⟨p, hp, h1, h2, h3⟩ := RoRangeTree.covers_sound lsRoRangeTree h
  rw [inLiRoData, List.any_eq_true]
  exact ⟨p, inTree_mem_roData hp, decide_eq_true ⟨h1, h2, h3⟩⟩

/-- $O(\log N)$ proof of `(secOff, secLen) ∈ libsignalSessionImage.roData`. -/
theorem mem_roData_of_tree {secOff secLen : Nat}
    (h : lsRoRangeTree.containsPair secOff secLen = true := by rfl_kernel) :
    (secOff, secLen) ∈ libsignalSessionImage.roData :=
  inTree_mem_roData (RoRangeTree.inTree_of_containsPair lsRoRangeTree h)

/-- Introduce a relocation-free `.rodata` byte slice `(img.base + off) ↦ᵣ bs` in $O(\log N + n)$. -/
theorem rodata_slice_fast_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s)
    {off n : Nat} {bs : List (BitVec 8)}
    (hguard :
      (Nat.ble libsignalSessionImage.dataOff off &&
       Nat.ble ((off - libsignalSessionImage.dataOff) + n) lsDataLen &&
       lsRelocTree.noOverlap (off - libsignalSessionImage.dataOff) n &&
       lsRoRangeTree.covers off n &&
       Nat.ble n (2 ^ 64)) = true := by rfl_kernel)
    (hlen : bs.length = n)
    (hbs : (libsignalSessionImage.data.drop (off - libsignalSessionImage.dataOff)).take n = bs)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦ᵣ bs) ∗ P := by
  simp only [Bool.and_eq_true] at hguard
  have hoff : libsignalSessionImage.dataOff ≤ off := Nat.le_of_ble_eq_true hguard.1.1.1.1
  have hk : (off - libsignalSessionImage.dataOff) + n ≤ libsignalSessionImage.data.length := by
    rw [lsDataLen_eq]; exact Nat.le_of_ble_eq_true hguard.1.1.1.2
  have hno := noRelocInRange_of_tree hguard.1.1.2
  have hro := inLiRoData_of_tree hguard.1.2
  have hn_le : bs.length ≤ 2 ^ 64 := by rw [hlen]; exact Nat.le_of_ble_eq_true hguard.2
  have hhb := loads_rodata_holdsBytes himg hF hoff hk hno hro hlen hbs
  obtain ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 hn_le hP

/-- Introduce an 8-byte non-relocated `.rodata` word `(img.base + off) ↦₆₄ᵣ val` in $O(\log N)$. -/
theorem rodata64_fast_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s)
    {off : Nat} {val : BitVec 64}
    (hguard :
      (Nat.ble libsignalSessionImage.dataOff off &&
       Nat.ble ((off - libsignalSessionImage.dataOff) + 8) lsDataLen &&
       lsRelocTree.noOverlap (off - libsignalSessionImage.dataOff) 8 &&
       lsRoRangeTree.covers off 8 &&
       byteListBeq (lsDataTree.slice (off - libsignalSessionImage.dataOff) 8)
         (unpack64 val)) = true := by rfl_kernel)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ val) ∗ P := by
  simp only [Bool.and_eq_true] at hguard
  have hoff : libsignalSessionImage.dataOff ≤ off := Nat.le_of_ble_eq_true hguard.1.1.1.1
  have hk : (off - libsignalSessionImage.dataOff) + 8 ≤ libsignalSessionImage.data.length := by
    rw [lsDataLen_eq]; exact Nat.le_of_ble_eq_true hguard.1.1.1.2
  have hno := noRelocInRange_of_tree hguard.1.1.2
  have hro := inLiRoData_of_tree hguard.1.2
  have hbs := lsData_slice_eq_of_beq hguard.2
  have hh := loads_rodata_holdsBytes himg hF hoff hk hno hro (unpack64_length val) hbs
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

/-- Introduce an 8-byte relocated `.rodata` / `.data.rel.ro` pointer slot in $O(\log N)$. -/
theorem reloc64_fast_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s)
    {off target : Nat}
    (hguard :
      (Nat.ble libsignalSessionImage.dataOff off &&
       lsRelocTree.hasReloc64At (off - libsignalSessionImage.dataOff) target &&
       lsRoRangeTree.covers off 8) = true := by rfl_kernel)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦₆₄ᵣ (img.base + BitVec.ofNat 64 target)) ∗ P := by
  simp only [Bool.and_eq_true] at hguard
  exact Satisfies.of_reloc64 himg hF
    (Nat.le_of_ble_eq_true hguard.1.1)
    (reloc64At_of_tree hguard.1.2)
    (inLiRoData_of_tree hguard.2)
    hP

/-- Introduce a `.rodata` section from `img.RoDataLoaded m` in $O(\log N)$. -/
theorem rodata_loads_fast_intro {img : Obj.Image} {m : Memory} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img)
    {dataOff secOff secLen : Nat}
    (hdo : libsignalSessionImage.dataOff = dataOff := by rfl)
    (hguard :
      (lsRoRangeTree.containsPair secOff secLen &&
       Nat.ble dataOff secOff &&
       Nat.ble (secLen + 1) (2 ^ 32) &&
       Nat.ble (secOff - dataOff + secLen) lsDataLen &&
       lsRelocTree.noOverlap (secOff - dataOff) secLen) = true := by rfl_kernel)
    (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + BitVec.ofNat 64 secOff) ↦ᵣ
      (libsignalSessionImage.data.drop (secOff - dataOff)).take secLen) ∗ P := by
  simp only [Bool.and_eq_true] at hguard
  exact ProofLib.Satisfies.of_rodata_loads himg hdo
    (mem_roData_of_tree hguard.1.1.1.1)
    (Nat.le_of_ble_eq_true hguard.1.1.1.2)
    (Nat.le_of_ble_eq_true hguard.1.1.2)
    (by rw [lsDataLen_eq]; exact Nat.le_of_ble_eq_true hguard.1.2)
    (relocs_all_disjoint_of_tree hguard.2)
    hro hP

end CryptoVerification.RodataFast
