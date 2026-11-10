/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.Accounting
import VerifiedLibraries.Mallocng.Proofs.TryAvailHelpers
import VerifiedLibraries.Mallocng.Proofs.GetMetaHelpers
import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers

/-!
# Helper Lemmas for Placed `free` and `nontrivial_free`

Provides circular doubly-linked list `queue`/`dequeue` preservation lemmas, 32-bit slot-mask
identities for slot freeing and `activate_group`, and `CodeLoaded`-preserving sub-word and
exclusive store step rules.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

/-! ## Circular Doubly-Linked List (`queue` and `dequeue`) -/

private theorem list_nodup_map_getElem_inj {α β : Type} {f : α → β} {xs : List α}
    (h : (xs.map f).Nodup) {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (heq : f (xs[i]'hi) = f (xs[j]'hj)) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x tl ih =>
    obtain ⟨hxNotMem, htlNd⟩ := List.nodup_cons.mp h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hxNotMem (heq ▸ List.mem_map_of_mem (List.getElem_mem _)))
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hxNotMem (heq.symm ▸ List.mem_map_of_mem (List.getElem_mem _)))
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ih htlNd (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

/-- Appending a fresh non-null node `m` at the back of `CircularDllWf head nodes` (musl's
    `queue(&head, m)`). -/
theorem CircularDllWf.snoc {head : BitVec 64}
    {nodes : List (BitVec 64 × BitVec 64 × BitVec 64)}
    {m : BitVec 64} (hmNe0 : m ≠ 0#64) (hmFresh : m ∉ nodes.map Prod.fst)
    (h : CircularDllWf head nodes) :
    match nodes with
    | [] => CircularDllWf m [(m, m, m)]
    | (p0, pv0, _) :: _ =>
      let nodes' := nodes.map fun d =>
        (d.1, if d.1 == p0 then m else d.2.1, if d.1 == pv0 then m else d.2.2)
      CircularDllWf p0 (nodes' ++ [(m, pv0, p0)]) := by
  cases nodes with
  | nil =>
    exact CircularDllWf.singleton hmNe0
  | cons hd tl =>
    rcases hd with ⟨p0, pv0, nx0⟩
    dsimp only []
    obtain ⟨hHead, hNd, hNonNull, hLinks⟩ := h
    let n := (p0, pv0, nx0) :: tl |>.length
    have hnVal : n = tl.length + 1 := rfl
    have hnPos : 0 < n := Nat.succ_pos _
    have h0Links := hLinks 0 hnPos
    have hModLast : (0 + n - 1) % n = n - 1 := by
      have : 0 + n - 1 = n - 1 := by omega
      rw [this]
      exact Nat.mod_eq_of_lt (by omega)
    have hpv0Eq : pv0 = (((p0, pv0, nx0) :: tl)[n - 1]'(by omega)).1 := by
      have hprv : (((p0, pv0, nx0) :: tl)[0]'hnPos).2.1 =
          (((p0, pv0, nx0) :: tl)[(0 + n - 1) % n]'(Nat.mod_lt _ hnPos)).1 := h0Links.2
      simpa only [List.getElem_cons_zero, hModLast] using hprv
    let upd := fun d : BitVec 64 × BitVec 64 × BitVec 64 =>
      (d.1, if d.1 == p0 then m else d.2.1, if d.1 == pv0 then m else d.2.2)
    let res := List.map upd ((p0, pv0, nx0) :: tl) ++ [(m, pv0, p0)]
    change CircularDllWf p0 res
    refine ⟨rfl, ?_, ?_, ?_⟩
    · have hMapFst : res.map Prod.fst = (((p0, pv0, nx0) :: tl).map Prod.fst) ++ [m] := by
        simp [res, upd, List.map_append, List.map_map, Function.comp_def]
      change res.map Prod.fst |>.Nodup
      rw [hMapFst]
      exact List.nodup_append.mpr ⟨hNd, by simp, fun x hx y hy hxy => by
        subst hxy
        have : x = m := by simpa using hy
        subst this
        exact hmFresh hx⟩
    · intro x hx
      change x ∈ res at hx
      rcases List.mem_append.mp hx with hxOld | hxNew
      · obtain ⟨d, hdMem, rfl⟩ := List.mem_map.mp hxOld
        exact hNonNull d hdMem
      · have hxEq : x = (m, pv0, p0) := by simpa using hxNew
        rw [hxEq]
        exact hmNe0
    · intro i hi
      change i < res.length at hi
      have hResLen : res.length = n + 1 := by
        simp [res, n]
      have hiLt : i < n + 1 := hResLen ▸ hi
      have hFstAtLt : ∀ k : Nat, (hkn : k < n) →
          (res[k]'(by rw [hResLen]; omega)).1 = (((p0, pv0, nx0) :: tl)[k]'hkn).1 := by
        intro k hkn
        dsimp only [res]
        rw [List.getElem_append_left (by simp; exact hkn), List.getElem_map]
      have hFstAtN : (res[n]'(by rw [hResLen]; omega)).1 = m := by
        simp [res, n]
      have hInj : ∀ j k : Nat, (hj : j < n) → (hk : k < n) →
          (((p0, pv0, nx0) :: tl)[j]'hj).1 = (((p0, pv0, nx0) :: tl)[k]'hk).1 → j = k :=
        fun j k hj hk hEq => list_nodup_map_getElem_inj hNd hj hk hEq
      show (res[i]'hi).2.2 = (res[(i + 1) % res.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))).1 ∧
        (res[i]'hi).2.1 = (res[(i + res.length - 1) % res.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))).1
      simp only [hResLen]
      by_cases hin : i < n
      · have hCurEq : res[i]'hi = upd (((p0, pv0, nx0) :: tl)[i]'hin) := by
          dsimp only [res]
          rw [List.getElem_append_left (by simp; exact hin), List.getElem_map]
        rw [hCurEq]
        have hOldLink := hLinks i hin
        dsimp only [upd]
        constructor
        · by_cases hIsLast : i = n - 1
          · have hEqPv0 : (((p0, pv0, nx0) :: tl)[i]'hin).1 = pv0 := by
              subst hIsLast; exact hpv0Eq.symm
            have hModN : (i + 1) % (n + 1) = n := by
              have : i + 1 = n := by omega
              rw [this]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [hEqPv0, beq_self_eq_true, ↓reduceIte, hModN]
            exact hFstAtN.symm
          · have hNePv0 : ((((p0, pv0, nx0) :: tl)[i]'hin).1 == pv0) = false := by
              apply beq_false_of_ne
              intro hEq
              exact hIsLast (hInj i (n - 1) hin (by omega) (hEq.trans hpv0Eq))
            have hModOld : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
            have hModNew : (i + 1) % (n + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
            simp only [hNePv0, Bool.false_eq_true, ↓reduceIte, hModNew]
            rw [hFstAtLt (i + 1) (by omega)]
            have hNxtOld : (((p0, pv0, nx0) :: tl)[i]'hin).2.2 =
                (((p0, pv0, nx0) :: tl)[(i + 1) % n]'(Nat.mod_lt _ hnPos)).1 := hOldLink.1
            simpa only [hModOld] using hNxtOld
        · by_cases hIsFirst : i = 0
          · subst hIsFirst
            have hModN : (0 + (n + 1) - 1) % (n + 1) = n := by
              have : 0 + (n + 1) - 1 = n := by omega
              rw [this]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [List.getElem_cons_zero, beq_self_eq_true, ↓reduceIte, hModN]
            exact hFstAtN.symm
          · have hNeP0 : ((((p0, pv0, nx0) :: tl)[i]'hin).1 == p0) = false := by
              apply beq_false_of_ne
              intro hEq
              exact hIsFirst (hInj i 0 hin hnPos hEq)
            have hModOld : (i + n - 1) % n = i - 1 := by
              have : i + n - 1 = (i - 1) + n := by omega
              rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            have hModNew : (i + (n + 1) - 1) % (n + 1) = i - 1 := by
              have : i + (n + 1) - 1 = (i - 1) + (n + 1) := by omega
              rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [hNeP0, Bool.false_eq_true, ↓reduceIte, hModNew]
            rw [hFstAtLt (i - 1) (by omega)]
            have hPrvOld : (((p0, pv0, nx0) :: tl)[i]'hin).2.1 =
                (((p0, pv0, nx0) :: tl)[(i + n - 1) % n]'(Nat.mod_lt _ hnPos)).1 := hOldLink.2
            simpa only [hModOld] using hPrvOld
      · have hiEq : i = n := by omega
        subst hiEq
        have hCurEq : res[n]'hi = (m, pv0, p0) := by
          simp [res, n]
        rw [hCurEq]
        have hModNxt : (n + 1) % (n + 1) = 0 := Nat.mod_self (n + 1)
        have hModPrv : (n + (n + 1) - 1) % (n + 1) = n - 1 := by
          have : n + (n + 1) - 1 = (n - 1) + (n + 1) := by omega
          rw [this, Nat.add_mod_right]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [hModNxt, hModPrv]
        rw [hFstAtLt 0 hnPos, hFstAtLt (n - 1) (by omega)]
        exact ⟨rfl, hpv0Eq⟩

/-- Removing the node at index `k < nodes.length` from a multi-element `CircularDllWf head nodes`
    (musl's `dequeue(&head, m)` when `m != m->next`). -/
theorem CircularDllWf.removeAt {head : BitVec 64}
    {nodes : List (BitVec 64 × BitVec 64 × BitVec 64)}
    {k : Nat} (hk : k < nodes.length) (hge2 : 2 ≤ nodes.length)
    (h : CircularDllWf head nodes) :
    let cur := nodes[k]'hk
    let m := cur.1
    let pvm := cur.2.1
    let nxm := cur.2.2
    let head' := if m == head then nxm else head
    let nodes' := (nodes.eraseIdx k).map fun d =>
      (d.1, if d.1 == nxm then pvm else d.2.1, if d.1 == pvm then nxm else d.2.2)
    m ≠ nxm ∧ pvm ≠ m ∧ nxm ≠ m ∧ CircularDllWf head' nodes' := by
  rcases nodes with _ | ⟨⟨p0, pv0, nx0⟩, _ | ⟨⟨p1, pv1, nx1⟩, tl1⟩⟩
  · simp at hk
  · simp at hge2
  · let L := (p0, pv0, nx0) :: (p1, pv1, nx1) :: tl1
    change k < L.length at hk
    change 2 ≤ L.length at hge2
    obtain ⟨hHead, hNd, hNonNull, hLinks⟩ := h
    let n := L.length
    have hnVal : n = tl1.length + 2 := rfl
    have hLLen : L.length = n := rfl
    have hnGe2 : 2 ≤ n := hge2
    have hInj : ∀ i j : Nat, (hi : i < n) → (hj : j < n) →
        (L[i]'hi).1 = (L[j]'hj).1 → i = j :=
      fun i j hi hj hEq => list_nodup_map_getElem_inj hNd hi hj hEq
    have hkLinks := hLinks k hk
    let kNext := (k + 1) % n
    let kPrev := (k + n - 1) % n
    have hkNextLt : kNext < n := Nat.mod_lt _ (by omega)
    have hkPrevLt : kPrev < n := Nat.mod_lt _ (by omega)
    have hNxmEq : (L[k]'hk).2.2 = (L[kNext]'hkNextLt).1 := hkLinks.1
    have hPvmEq : (L[k]'hk).2.1 = (L[kPrev]'hkPrevLt).1 := hkLinks.2
    have hkNeNext : k ≠ kNext := by
      intro hEq
      dsimp only [kNext] at hEq
      by_cases hkLast : k + 1 = n
      · rw [hkLast, Nat.mod_self] at hEq; omega
      · have : (k + 1) % n = k + 1 := Nat.mod_eq_of_lt (by omega)
        omega
    have hkNePrev : k ≠ kPrev := by
      intro hEq
      dsimp only [kPrev] at hEq
      by_cases hkZero : k = 0
      · subst hkZero
        have : (0 + n - 1) % n = n - 1 := by
          have h1 : 0 + n - 1 = n - 1 := by omega
          rw [h1]; exact Nat.mod_eq_of_lt (by omega)
        omega
      · have : (k + n - 1) % n = k - 1 := by
          have h1 : k + n - 1 = (k - 1) + n := by omega
          rw [h1, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
        omega
    have hmNeNxm : (L[k]'hk).1 ≠ (L[k]'hk).2.2 := by
      rw [hNxmEq]; intro hEq; exact hkNeNext (hInj k kNext hk hkNextLt hEq)
    have hpvmNeM : (L[k]'hk).2.1 ≠ (L[k]'hk).1 := by
      rw [hPvmEq]; intro hEq; exact hkNePrev (hInj k kPrev hk hkPrevLt hEq.symm)
    refine ⟨hmNeNxm, hpvmNeM, hmNeNxm.symm, ?_⟩
    by_cases hk0 : k = 0
    · subst hk0
      have hDeq := CircularDllWf.dequeue_head (head := head) ⟨hHead, hNd, hNonNull, hLinks⟩
      subst hHead
      simpa [L] using hDeq.2
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero hk0
      have hkLtN : k' + 1 < n := hk
      have hmNeHead : ((L[k' + 1]'hk).1 == head) = false := by
        subst hHead
        apply beq_false_of_ne
        intro hEq
        exact hk0 (hInj (k' + 1) 0 hk (by omega) hEq)
      let pvm := (L[k' + 1]'hk).2.1
      let nxm := (L[k' + 1]'hk).2.2
      let upd := fun d : BitVec 64 × BitVec 64 × BitVec 64 =>
        (d.1, if d.1 == nxm then pvm else d.2.1, if d.1 == pvm then nxm else d.2.2)
      let E := L.eraseIdx (k' + 1)
      let res := E.map upd
      have hELen : E.length = n - 1 := List.length_eraseIdx_of_lt hk
      have hResLen : res.length = n - 1 := by simp [res, hELen]
      let idxMap := fun j : Nat => if j < k' + 1 then j else j + 1
      have hIdxLt : ∀ j : Nat, j < n - 1 → idxMap j < L.length := by
        intro j hj
        dsimp only [idxMap]
        rw [hLLen]
        split <;> omega
      have hEAt : ∀ i : Nat, (hi : i < n - 1) →
          E[i]'(hELen.symm ▸ hi) = L[idxMap i]'(hIdxLt i hi) := by
        intro i hi
        dsimp only [E, idxMap]
        by_cases hik : i < k' + 1
        · simp only [hik, ↓reduceIte]
          exact List.getElem_eraseIdx_of_lt (hELen.symm ▸ hi) hik
        · simp only [hik, ↓reduceIte]
          exact List.getElem_eraseIdx_of_ge (hELen.symm ▸ hi) (by omega)
      change CircularDllWf (if (L[k' + 1]'hk).1 == head then nxm else head) res
      rw [hmNeHead]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨hHead, ?_, ?_, ?_⟩
      · change res.map Prod.fst |>.Nodup
        have hMapFst : res.map Prod.fst = E.map Prod.fst := by
          simp [res, upd, List.map_map, Function.comp_def]
        rw [hMapFst]
        have hSub : E.Sublist L := List.eraseIdx_sublist L (k' + 1)
        exact (hSub.map Prod.fst).nodup hNd
      · intro x hx
        change x ∈ res at hx
        obtain ⟨d, hdMem, rfl⟩ := List.mem_map.mp hx
        exact hNonNull d ((List.eraseIdx_sublist L (k' + 1)).subset hdMem)
      · intro i hi
        change i < res.length at hi
        have hiLt : i < n - 1 := hResLen ▸ hi
        have hCurEq : res[i]'hi = upd (L[idxMap i]'(hIdxLt i hiLt)) := by
          simp only [res, List.getElem_map]
          rw [hEAt i hiLt]
        have hResFst : ∀ j : Nat, (hj : j < res.length) →
            (res[j]'hj).1 = (L[idxMap j]'(hIdxLt j (hResLen ▸ hj))).1 := by
          intro j hj
          simp only [res, List.getElem_map, upd]
          rw [hEAt j (hResLen ▸ hj)]
        show (res[i]'hi).2.2 = (res[(i + 1) % res.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))).1 ∧
          (res[i]'hi).2.1 = (res[(i + res.length - 1) % res.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))).1
        rw [hCurEq,
            hResFst ((i + 1) % res.length) (Nat.mod_lt _ (Nat.zero_lt_of_lt hi)),
            hResFst ((i + res.length - 1) % res.length) (Nat.mod_lt _ (Nat.zero_lt_of_lt hi))]
        have hOldLink := hLinks (idxMap i) (hIdxLt i hiLt)
        have hFstCongr : ∀ a b : Nat, (ha : a < n) → (hb : b < n) → a = b →
            (L[a]'ha).1 = (L[b]'hb).1 := by
          rintro a _ ha _ rfl; rfl
        dsimp only [upd]
        constructor
        · by_cases hIsPrev : idxMap i = kPrev
          · have hEqPvm : (L[idxMap i]'(hIdxLt i hiLt)).1 = pvm := by
              dsimp only [pvm]; rw [hPvmEq]; exact hFstCongr _ _ _ _ hIsPrev
            simp only [hEqPvm, beq_self_eq_true, ↓reduceIte]
            have hkPrevVal : kPrev = k' := by
              dsimp only [kPrev]
              have : (k' + 1) + n - 1 = k' + n := by omega
              rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            have hiEqK' : i = k' := by
              dsimp only [idxMap] at hIsPrev
              split at hIsPrev <;> omega
            dsimp only [nxm]
            rw [hNxmEq]
            apply hFstCongr
            rw [hiEqK', hResLen]
            by_cases hkLast : k' + 1 = n - 1
            · have hMod0 : (k' + 1) % (n - 1) = 0 := by rw [hkLast, Nat.mod_self]
              have hkNext0 : kNext = 0 := by
                dsimp only [kNext]
                have : (k' + 1) + 1 = n := by omega
                rw [this, Nat.mod_self]
              rw [hMod0, hkNext0]
              simp [idxMap]
            · have hModNext : (k' + 1) % (n - 1) = k' + 1 := Nat.mod_eq_of_lt (by omega)
              have hkNextVal : kNext = k' + 2 := by
                dsimp only [kNext]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hModNext, hkNextVal]
              simp [idxMap]
          · have hNePvm : ((L[idxMap i]'(hIdxLt i hiLt)).1 == pvm) = false := by
              apply beq_false_of_ne
              intro hEq
              exact hIsPrev (hInj (idxMap i) kPrev (hIdxLt i hiLt) hkPrevLt
                (hEq.trans hPvmEq))
            simp only [hNePvm, Bool.false_eq_true, ↓reduceIte]
            have hkPrevVal : kPrev = k' := by
              dsimp only [kPrev]
              have : (k' + 1) + n - 1 = k' + n := by omega
              rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            have hiNeK' : i ≠ k' := by
              intro hEq; subst hEq
              exact hIsPrev (by simp [idxMap, hkPrevVal])
            have hNxtOld := hOldLink.1
            refine hNxtOld.trans (hFstCongr _ _ _ _ ?_)
            rw [hResLen, hLLen]
            by_cases hik : i < k' + 1
            · have hik' : i < k' := by omega
              have h1 : idxMap i = i := by simp [idxMap, hik]
              have hMod1 : (i + 1) % n = i + 1 := Nat.mod_eq_of_lt (by omega)
              have hMod2 : (i + 1) % (n - 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
              have h2 : idxMap (i + 1) = i + 1 := by
                dsimp [idxMap]; split <;> omega
              rw [h1, hMod1, hMod2]
              exact h2.symm
            · have h1 : idxMap i = i + 1 := by simp [idxMap, hik]
              by_cases hiLast : i + 1 = n - 1
              · have hMod1 : (i + 1 + 1) % n = 0 := by
                  have : i + 1 + 1 = n := by omega
                  rw [this, Nat.mod_self]
                have hMod2 : (i + 1) % (n - 1) = 0 := by rw [hiLast, Nat.mod_self]
                rw [h1, hMod1, hMod2]
                simp [idxMap]
              · have hMod1 : (i + 1 + 1) % n = i + 2 := Nat.mod_eq_of_lt (by omega)
                have hMod2 : (i + 1) % (n - 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
                rw [h1, hMod1, hMod2]
                dsimp [idxMap]; split <;> omega
        · by_cases hIsNext : idxMap i = kNext
          · have hEqNxm : (L[idxMap i]'(hIdxLt i hiLt)).1 = nxm := by
              dsimp only [nxm]; rw [hNxmEq]; exact hFstCongr _ _ _ _ hIsNext
            simp only [hEqNxm, beq_self_eq_true, ↓reduceIte]
            have hkPrevVal : kPrev = k' := by
              dsimp only [kPrev]
              have : (k' + 1) + n - 1 = k' + n := by omega
              rw [this, Nat.add_mod_right]
              exact Nat.mod_eq_of_lt (by omega)
            dsimp only [pvm]
            rw [hPvmEq]
            apply hFstCongr
            rw [hResLen, hkPrevVal]
            by_cases hkLast : k' + 1 = n - 1
            · have hkNext0 : kNext = 0 := by
                dsimp only [kNext]
                have : (k' + 1) + 1 = n := by omega
                rw [this, Nat.mod_self]
              have hi0 : i = 0 := by
                dsimp only [idxMap] at hIsNext
                split at hIsNext <;> omega
              have hModPrv : (0 + (n - 1) - 1) % (n - 1) = k' := by
                have h1 : 0 + (n - 1) - 1 = n - 2 := by omega
                rw [h1]
                have h2 : n - 2 = k' := by omega
                rw [h2]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hi0, hModPrv]
              simp [idxMap]
            · have hkNextVal : kNext = k' + 2 := by
                dsimp only [kNext]
                exact Nat.mod_eq_of_lt (by omega)
              have hiEq : i = k' + 1 := by
                dsimp only [idxMap] at hIsNext
                split at hIsNext <;> omega
              have hModPrv : ((k' + 1) + (n - 1) - 1) % (n - 1) = k' := by
                have h1 : (k' + 1) + (n - 1) - 1 = k' + (n - 1) := by omega
                rw [h1, Nat.add_mod_right]
                exact Nat.mod_eq_of_lt (by omega)
              rw [hiEq, hModPrv]
              simp [idxMap]
          · have hNeNxm : ((L[idxMap i]'(hIdxLt i hiLt)).1 == nxm) = false := by
              apply beq_false_of_ne
              intro hEq
              exact hIsNext (hInj (idxMap i) kNext (hIdxLt i hiLt) hkNextLt
                (hEq.trans hNxmEq))
            simp only [hNeNxm, Bool.false_eq_true, ↓reduceIte]
            have hPrvOld := hOldLink.2
            refine hPrvOld.trans (hFstCongr _ _ _ _ ?_)
            rw [hResLen, hLLen]
            by_cases hi0 : i = 0
            · have h1 : idxMap i = 0 := by rw [hi0]; simp [idxMap]
              have hMod1 : (0 + n - 1) % n = n - 1 := by
                have : 0 + n - 1 = n - 1 := by omega
                rw [this]; exact Nat.mod_eq_of_lt (by omega)
              have hMod2 : (0 + (n - 1) - 1) % (n - 1) = n - 2 := by
                have : 0 + (n - 1) - 1 = n - 2 := by omega
                rw [this]; exact Nat.mod_eq_of_lt (by omega)
              have hkNotLast : k' + 1 ≠ n - 1 := by
                intro hkL
                apply hIsNext
                rw [h1]
                dsimp [kNext]
                have : (k' + 1) + 1 = n := by omega
                rw [this, Nat.mod_self]
              rw [h1, hi0, hMod1, hMod2]
              dsimp [idxMap]; split <;> omega
            · have hMod2 : (i + (n - 1) - 1) % (n - 1) = i - 1 := by
                have : i + (n - 1) - 1 = (i - 1) + (n - 1) := by omega
                rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
              rw [hMod2]
              by_cases hik : i < k' + 1
              · have h1 : idxMap i = i := by simp [idxMap, hik]
                have hMod1 : (i + n - 1) % n = i - 1 := by
                  have : i + n - 1 = (i - 1) + n := by omega
                  rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
                rw [h1, hMod1]
                dsimp [idxMap]; split <;> omega
              · have hiNeK1 : i ≠ k' + 1 := by
                  intro hEq; subst hEq
                  apply hIsNext
                  have h1 : idxMap (k' + 1) = k' + 2 := by simp [idxMap]
                  have hkNotLast : k' + 1 < n - 1 := by omega
                  have h2 : kNext = k' + 2 := by
                    dsimp [kNext]; exact Nat.mod_eq_of_lt (by omega)
                  omega
                have h1 : idxMap i = i + 1 := by simp [idxMap, hik]
                have hMod1 : (i + 1 + n - 1) % n = i := by
                  have : i + 1 + n - 1 = i + n := by omega
                  rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
                rw [h1, hMod1]
                dsimp [idxMap]; split <;> omega

/-! ## Bitmask Lemmas for Slot Freeing and `activate_group` -/

open Arm64 ProofLib

private theorem bv32_add_eq_or_of_disj {x y : BitVec 32} (h : x &&& y = 0#32) :
    x + y = x ||| y := by
  revert h; bv_robdd

private theorem bv32_neg_eq_not_sub_one (x : BitVec 32) :
    -x = ~~~(x - 1#32) := by
  bv_robdd

private theorem bv32_mask_split (m x : BitVec 32) :
    (m &&& x) &&& (x &&& ~~~m) = 0#32 ∧ (m &&& x) ||| (x &&& ~~~m) = x := by
  bv_robdd

private theorem allMask32_getLsbD_fin :
    ∀ (k j : Fin 32), ((2#32 <<< k.val) - 1#32).getLsbD j.val = decide (j.val ≤ k.val) := by
  decide +kernel

private theorem oneShift32_getLsbD_fin :
    ∀ (k j : Fin 32), (1#32 <<< k.val).getLsbD j.val = decide (j.val = k.val) := by
  decide +kernel

private theorem allMask32_low_ones_fin :
    ∀ (k : Fin 32),
      ((2#32 <<< k.val) - 1#32).toNat = 2 ^ (k.val + 1) - 1 ∧
      (((2#32 <<< k.val) - 1#32) &&& (((2#32 <<< k.val) - 1#32) + 1#32)) = 0#32 := by
  decide +kernel

private theorem bv32_ule_low_ones_iff {m x : BitVec 32} (hm : m &&& (m + 1#32) = 0#32) :
    x.ule m = true ↔ (x ||| m) = m := by
  revert hm; bv_robdd

theorem freeSlot_mask_props {avail freed : BitVec 32} {idx lastIdx : Nat}
    (hIdx : idx ≤ lastIdx) (hLast : lastIdx ≤ 31)
    (hDisj : avail &&& freed = 0#32)
    (hBound : (avail ||| freed).toNat < 2 ^ (lastIdx + 1))
    (hAv0 : avail.getLsbD idx = false)
    (hFr0 : freed.getLsbD idx = false) :
    let self := 1#32 <<< idx
    let allMask := (2#32 <<< lastIdx) - 1#32
    self ≠ 0#32 ∧
    (avail ||| freed) &&& self = 0#32 ∧
    (avail ||| freed) + self = (avail ||| freed) ||| self ∧
    avail &&& (freed ||| self) = 0#32 ∧
    (avail ||| (freed ||| self)).toNat < 2 ^ (lastIdx + 1) ∧
    (∀ j : Nat, (freed ||| self).getLsbD j = (if j = idx then true else freed.getLsbD j)) ∧
    (((avail ||| freed) + self = allMask) ↔
      (∀ j : Nat, j ≤ lastIdx → j ≠ idx →
        avail.getLsbD j = true ∨ freed.getLsbD j = true)) := by
  dsimp only []
  have hIdxLt32 : idx < 32 := by omega
  have hLastLt32 : lastIdx < 32 := by omega
  have hSelfBit : ∀ j : Nat, j < 32 → (1#32 <<< idx).getLsbD j = decide (j = idx) :=
    fun j hj => oneShift32_getLsbD_fin ⟨idx, hIdxLt32⟩ ⟨j, hj⟩
  have hAllBit : ∀ j : Nat, j < 32 →
      ((2#32 <<< lastIdx) - 1#32).getLsbD j = decide (j ≤ lastIdx) :=
    fun j hj => allMask32_getLsbD_fin ⟨lastIdx, hLastLt32⟩ ⟨j, hj⟩
  obtain ⟨hAllToNat, hAllLowOnes⟩ := allMask32_low_ones_fin ⟨lastIdx, hLastLt32⟩
  dsimp only [] at hAllToNat hAllLowOnes
  have hPowPos : 0 < 2 ^ (lastIdx + 1) := Nat.two_pow_pos _
  have hUleOld : (avail ||| freed).ule ((2#32 <<< lastIdx) - 1#32) = true := by
    rw [BitVec.ule, decide_eq_true_eq, hAllToNat]; omega
  have hOrMaskOld : (avail ||| freed) ||| ((2#32 <<< lastIdx) - 1#32) = (2#32 <<< lastIdx) - 1#32 :=
    (bv32_ule_low_ones_iff hAllLowOnes).mp hUleOld
  have hOutBit : ∀ j : Nat, j < 32 → ¬ j ≤ lastIdx → (avail ||| freed).getLsbD j = false := by
    intro j hj32 hjNotLe
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD j) hOrMaskOld
    rw [BitVec.getLsbD_or, hAllBit j hj32] at hb
    simpa [hjNotLe] using hb
  have hSelfNe0 : (1#32 <<< idx) ≠ 0#32 := by
    intro h0
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD idx) h0
    rw [hSelfBit idx hIdxLt32] at hb
    simp at hb
  have hDisjSelf : (avail ||| freed) &&& (1#32 <<< idx) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero, hSelfBit j hj]
    by_cases hji : j = idx
    · subst hji; simp [hAv0, hFr0]
    · simp [hji]
  have hAddEqOr : (avail ||| freed) + (1#32 <<< idx) = (avail ||| freed) ||| (1#32 <<< idx) :=
    bv32_add_eq_or_of_disj hDisjSelf
  have hAvDisjNew : avail &&& (freed ||| (1#32 <<< idx)) = 0#32 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hd := congrArg (fun x : BitVec 32 => x.getLsbD j) hDisj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hd
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero, hSelfBit j hj]
    by_cases hji : j = idx
    · subst hji; simp [hAv0]
    · simp [hji, hd]
  have hGetNew : ∀ j : Nat,
      (freed ||| (1#32 <<< idx)).getLsbD j = (if j = idx then true else freed.getLsbD j) := by
    intro j
    by_cases hj32 : j < 32
    · simp only [BitVec.getLsbD_or, hSelfBit j hj32]
      by_cases hji : j = idx <;> simp [hji]
    · have hji : j ≠ idx := by omega
      have h1 : freed.getLsbD j = false := BitVec.getLsbD_of_ge freed j (by omega)
      have h2 : (freed ||| (1#32 <<< idx)).getLsbD j = false := BitVec.getLsbD_of_ge _ j (by omega)
      simp [hji, h1, h2]
  have hNewBound : (avail ||| (freed ||| (1#32 <<< idx))).toNat < 2 ^ (lastIdx + 1) := by
    have hOrMaskNew : (avail ||| (freed ||| (1#32 <<< idx))) ||| ((2#32 <<< lastIdx) - 1#32) =
        (2#32 <<< lastIdx) - 1#32 := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [← BitVec.or_assoc avail freed (1#32 <<< idx)]
      simp only [BitVec.getLsbD_or, hSelfBit j hj, hAllBit j hj]
      by_cases hjLe : j ≤ lastIdx
      · simp [hjLe]
      · have hOut := hOutBit j hj hjLe
        have hji : j ≠ idx := by omega
        simp only [BitVec.getLsbD_or] at hOut
        simp [hjLe, hji, hOut]
    have hUleNew : (avail ||| (freed ||| (1#32 <<< idx))).ule ((2#32 <<< lastIdx) - 1#32) = true :=
      (bv32_ule_low_ones_iff hAllLowOnes).mpr hOrMaskNew
    rw [BitVec.ule, decide_eq_true_eq, hAllToNat] at hUleNew
    omega
  refine ⟨hSelfNe0, hDisjSelf, hAddEqOr, hAvDisjNew, hNewBound, hGetNew, ?_⟩
  rw [hAddEqOr]
  constructor
  · intro hEqAll j hjLe hji
    have hj32 : j < 32 := by omega
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD j) hEqAll
    simp only [BitVec.getLsbD_or, hSelfBit j hj32, hAllBit j hj32, hji, hjLe,
      decide_false, decide_true, Bool.or_false, Bool.or_eq_true] at hb
    exact hb
  · intro hAllOther
    apply BitVec.eq_of_getLsbD_eq
    intro j hj32
    simp only [BitVec.getLsbD_or, hSelfBit j hj32, hAllBit j hj32]
    by_cases hjLe : j ≤ lastIdx
    · by_cases hji : j = idx
      · subst hji; simp [hjLe]
      · rcases hAllOther j hjLe hji with hA | hF
        · simp [hjLe, hji, hA]
        · simp [hjLe, hji, hF]
    · have hOut := hOutBit j hj32 hjLe
      have hji : j ≠ idx := by omega
      simp only [BitVec.getLsbD_or] at hOut
      simp [hjLe, hji, hOut]

theorem activateGroup_mask_props {freed : BitVec 32} {activeIdx lastIdx : Nat}
    (hActLe : activeIdx ≤ lastIdx) (hLast : lastIdx ≤ 31)
    (hBound : freed.toNat < 2 ^ (lastIdx + 1)) :
    let cntMask := (2#32 <<< activeIdx) - 1#32
    let negMask := -(2#32 <<< activeIdx)
    let avail' := cntMask &&& freed
    let freed' := freed &&& negMask
    negMask = ~~~cntMask ∧
    avail' &&& freed' = 0#32 ∧
    avail' ||| freed' = freed ∧
    (avail' ||| freed').toNat < 2 ^ (lastIdx + 1) ∧
    (∀ j : Nat, j < 32 →
      avail'.getLsbD j = (decide (j ≤ activeIdx) && freed.getLsbD j) ∧
      freed'.getLsbD j = (decide (activeIdx < j) && freed.getLsbD j)) := by
  dsimp only []
  have hNegEqNot : -(2#32 <<< activeIdx) = ~~~((2#32 <<< activeIdx) - 1#32) :=
    bv32_neg_eq_not_sub_one (2#32 <<< activeIdx)
  obtain ⟨hSplitDisj, hSplitOr⟩ := bv32_mask_split ((2#32 <<< activeIdx) - 1#32) freed
  have hDisj : (((2#32 <<< activeIdx) - 1#32) &&& freed) &&& (freed &&& -(2#32 <<< activeIdx)) = 0#32 := by
    rw [hNegEqNot]; exact hSplitDisj
  have hOr : (((2#32 <<< activeIdx) - 1#32) &&& freed) ||| (freed &&& -(2#32 <<< activeIdx)) = freed := by
    rw [hNegEqNot]; exact hSplitOr
  refine ⟨hNegEqNot, hDisj, hOr, hOr.symm ▸ hBound, ?_⟩
  intro j hj32
  have hCntBit : ((2#32 <<< activeIdx) - 1#32).getLsbD j = decide (j ≤ activeIdx) :=
    allMask32_getLsbD_fin ⟨activeIdx, by omega⟩ ⟨j, hj32⟩
  rw [hNegEqNot]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hCntBit]
  by_cases hjLe : j ≤ activeIdx
  · have hjNotGt : ¬ activeIdx < j := by omega
    simp [hj32, hjLe, hjNotGt]
  · have hjGt : activeIdx < j := by omega
    simp [hj32, hjLe, hjGt, Bool.and_comm]

/-! ## `CodeLoaded`-Preserving Sub-Word and Exclusive Store Steps -/

theorem step_str8_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg64 rt).truncate 8 = val) (hstore : SepStore8 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write8 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 1 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write8 _ _ _) (Memory.keepsFrozen_write8 hcan val)) hm'

theorem step_str16_perm_kf {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg64 rt).truncate 16 = val) (hstore : SepStore16 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  let m' := s.mem.write16 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 2 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .H16 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact SepWP.to_reaches_pc
    (hnext m' (Memory.perm_write16 _ _ _) (Memory.keepsFrozen_write16 hcan val)) hm'

theorem step_stxr32_either_perm {prog : Program} {target_pc pc ea : BitVec 64}
    {s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {v0 val : BitVec 32} {rel : Bool} {rs rn rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true) (hval : s.readReg32 rt = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm → s.mem.KeepsFrozen m' →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64)).setMem m')
        ((ea ↦₃₂ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true →
      SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 rs 1#64).setPC (pc + 4#64))
        ((ea ↦₃₂ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .W32 rel rs rn rt) s =
        ((s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64)).setMem (s.mem.write32 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, htrunc,
        MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, State.setMem, hpc]
    rw [hstep]
    refine SepWP.to_reaches_pc
      (hok hf _ (Memory.perm_write32 s.mem ea val) (Memory.keepsFrozen_write32 hcw val)) ?_
    rw [sepConj_assoc]
    exact (IsBlock.pointsTo32 ea v0).write32 hm' val
  · have hstep : prog.evalInst (.stxr .W32 rel rs rn rt) s =
        (s.stepExclOracle.writeReg .W32 rs 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf,
        MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, hpc]
    rw [hstep]
    exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)

theorem exclFails_tail_lt_free {s : State} {k : Nat}
    (hk : s.exclFails.length < k + 1) (hf : s.exclWillFail = true) :
    s.exclFails.tail.length < k := by
  cases h : s.exclFails with
  | nil => simp [State.exclWillFail_eq_headD, h] at hf
  | cons _ tl => simp [h] at hk ⊢; omega

end VerifiedLibraries.Mallocng.Proofs
