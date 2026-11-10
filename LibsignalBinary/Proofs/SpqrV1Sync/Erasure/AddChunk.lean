/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1Sync.Erasure.AddChunk

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.GF16Field
open CryptoVerification.SpqrV1Sync.Erasure
open Polynomial

/-! ## 1. `Ord.compare` on `Nat` and `insKey` / `insPt` -/

abbrev key (pt : Pt) : Nat := pt.x.value.toNat

theorem nat_compare_lt {a b : Nat} (h : a < b) : Ord.compare a b = .lt := by
  change compareOfLessAndEq a b = .lt
  simp [compareOfLessAndEq, h]

theorem nat_compare_eq {a b : Nat} (h : a = b) : Ord.compare a b = .eq := by
  subst h
  change compareOfLessAndEq a a = .eq
  simp [compareOfLessAndEq]

theorem nat_compare_gt {a b : Nat} (h : b < a) : Ord.compare a b = .gt := by
  change compareOfLessAndEq a b = .gt
  have h1 : ¬ a < b := by omega
  have h2 : ¬ a = b := by omega
  simp [compareOfLessAndEq, h1, h2]

theorem pt_cmp_eq (a b : Pt) : Pt.cmp a b = Ord.compare (key a) (key b) := rfl

def insKey (k : Nat) : List Nat → List Nat
  | [] => [k]
  | x :: xs =>
    match Ord.compare x k with
    | .lt => x :: insKey k xs
    | .eq => k :: xs
    | .gt => k :: x :: xs

def insPt (target : Pt) : List Pt → List Pt
  | [] => [target]
  | pt :: rest =>
    match Pt.cmp pt target with
    | .lt => pt :: insPt target rest
    | .eq => target :: rest
    | .gt => target :: pt :: rest

theorem map_key_insPt (target : Pt) :
    ∀ (xs : List Pt), (insPt target xs).map key = insKey (key target) (xs.map key)
  | [] => rfl
  | pt :: rest => by
    simp only [insPt, List.map_cons, insKey, pt_cmp_eq]
    cases Ord.compare (key pt) (key target) <;> simp [map_key_insPt target rest]

theorem mem_insPt {target p : Pt} :
    ∀ {xs : List Pt}, p ∈ insPt target xs → p = target ∨ p ∈ xs
  | [], h => by
    simp only [insPt, List.mem_singleton] at h
    exact .inl h
  | pt :: rest, h => by
    simp only [insPt] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h'
      · exact .inr (List.mem_cons_self ..)
      · rcases mem_insPt h' with rfl | h''
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem _ h'')
    · rcases List.mem_cons.mp h with rfl | h'
      · exact .inl rfl
      · exact .inr (List.mem_cons_of_mem _ h')
    · rcases List.mem_cons.mp h with rfl | h'
      · exact .inl rfl
      · exact .inr h'

theorem mem_insKey (k x : Nat) :
    ∀ (xs : List Nat), x ∈ insKey k xs ↔ x = k ∨ x ∈ xs
  | [] => by simp [insKey]
  | y :: rest => by
    rcases Nat.lt_trichotomy y k with hlt | rfl | hgt
    · rw [insKey, nat_compare_lt hlt, List.mem_cons, mem_insKey k x rest, List.mem_cons]
      tauto
    · rw [insKey, nat_compare_eq rfl, List.mem_cons]
      tauto
    · rw [insKey, nat_compare_gt hgt, List.mem_cons]

theorem pairwise_insKey (k : Nat) :
    ∀ {xs : List Nat}, xs.Pairwise (· < ·) → (insKey k xs).Pairwise (· < ·)
  | [], _ => by simp [insKey]
  | y :: rest, hs => by
    obtain ⟨hy, hrest⟩ := List.pairwise_cons.mp hs
    rcases Nat.lt_trichotomy y k with hlt | rfl | hgt
    · rw [insKey, nat_compare_lt hlt, List.pairwise_cons]
      refine ⟨fun z hz => ?_, pairwise_insKey k hrest⟩
      rcases (mem_insKey k z rest).mp hz with rfl | hz'
      · exact hlt
      · exact hy z hz'
    · rw [insKey, nat_compare_eq rfl]
      exact hs
    · rw [insKey, nat_compare_gt hgt, List.pairwise_cons]
      refine ⟨fun z hz => ?_, hs⟩
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact hgt
      · exact Nat.lt_trans hgt (hy z hz')

theorem length_insKey (k : Nat) :
    ∀ {xs : List Nat}, xs.Pairwise (· < ·) →
      (insKey k xs).length = if k ∈ xs then xs.length else xs.length + 1
  | [], _ => by simp [insKey]
  | y :: rest, hs => by
    obtain ⟨hy, hrest⟩ := List.pairwise_cons.mp hs
    rcases Nat.lt_trichotomy y k with hlt | rfl | hgt
    · rw [insKey, nat_compare_lt hlt, List.length_cons, length_insKey k hrest]
      have hne : k ≠ y := by omega
      simp [List.mem_cons, hne]
      split <;> omega
    · rw [insKey, nat_compare_eq rfl]
      simp
    · rw [insKey, nat_compare_gt hgt]
      have hnotmem : k ∉ y :: rest := by
        intro hm
        rcases List.mem_cons.mp hm with rfl | hm'
        · omega
        · have := hy k hm'; omega
      simp [hnotmem]

/-! ## 2. Connecting `SortedSetPt.replace` and `SortedSetPt.push` to `insPt` -/

def shiftExcept : Except Nat Nat → Except Nat Nat
  | .ok k => .ok (k + 1)
  | .error k => .error (k + 1)

theorem binarySearchAux_succ (target : Pt) :
    ∀ (xs : List Pt) (idx : Nat),
      SortedSetPt.binarySearchAux target (idx + 1) xs =
        shiftExcept (SortedSetPt.binarySearchAux target idx xs)
  | [], _ => rfl
  | pt :: rest, idx => by
    simp only [SortedSetPt.binarySearchAux]
    cases Pt.cmp pt target with
    | lt => exact binarySearchAux_succ target rest (idx + 1)
    | eq => rfl
    | gt => rfl

theorem replace_vec (target : Pt) :
    ∀ (xs : List Pt), (SortedSetPt.replace ⟨xs⟩ target).1.vec = insPt target xs
  | [] => rfl
  | pt :: rest => by
    have ih := replace_vec target rest
    simp only [SortedSetPt.replace, SortedSetPt.binarySearch] at ih ⊢
    simp only [SortedSetPt.binarySearchAux, insPt]
    cases Pt.cmp pt target with
    | eq => rfl
    | gt => rfl
    | lt =>
      rw [binarySearchAux_succ target rest 0]
      cases h : SortedSetPt.binarySearchAux target 0 rest with
      | ok k =>
        simp only [h] at ih
        simp [shiftExcept, ih]
      | error k =>
        simp only [h] at ih
        simp [shiftExcept, ih]

theorem insPt_append_last (target : Pt) :
    ∀ (ys : List Pt) (last : Pt),
      (∀ p ∈ ys, key p < key target) →
      insPt target (ys ++ [last]) = ys ++ insPt target [last]
  | [], _, _ => rfl
  | pt :: rest, last, hlt => by
    have hpt : key pt < key target := hlt pt (List.mem_cons_self ..)
    have hrest : ∀ p ∈ rest, key p < key target :=
      fun p hp => hlt p (List.mem_cons_of_mem _ hp)
    rw [List.cons_append, insPt, pt_cmp_eq, nat_compare_lt hpt]
    dsimp only
    rw [insPt_append_last target rest last hrest, List.cons_append]

theorem snoc_decomp : ∀ (xs : List Pt), xs = [] ∨ ∃ ys last, xs = ys ++ [last]
  | [] => .inl rfl
  | pt :: rest => by
    rcases snoc_decomp rest with rfl | ⟨ys, last, hrest⟩
    · exact .inr ⟨[], pt, rfl⟩
    · exact .inr ⟨pt :: ys, last, by simp [hrest]⟩

theorem getLast?_snoc : ∀ (ys : List Pt) (last : Pt), (ys ++ [last]).getLast? = some last
  | [], _ => rfl
  | _ :: rest, last => by
    cases rest with
    | nil => rfl
    | cons b bs => exact getLast?_snoc (b :: bs) last

theorem dropLast_snoc : ∀ (ys : List Pt) (last : Pt), (ys ++ [last]).dropLast = ys
  | [], _ => rfl
  | pt :: rest, last => by
    have hne : rest ++ [last] ≠ [] := by simp
    rw [List.cons_append, List.dropLast_cons_of_ne_nil hne, dropLast_snoc rest last]

theorem push_vec (xs : List Pt) (target : Pt) (hs : (xs.map key).Pairwise (· < ·)) :
    (SortedSetPt.push ⟨xs⟩ target).1.vec = insPt target xs := by
  rcases snoc_decomp xs with rfl | ⟨ys, last, rfl⟩
  · rfl
  · rw [List.map_append, List.map_singleton, List.pairwise_append] at hs
    obtain ⟨_, _, hlt_last⟩ := hs
    have hys_lt : ∀ p ∈ ys, key p < key last := by
      intro p hp
      exact hlt_last (key p) (List.mem_map_of_mem hp) (key last) (List.mem_singleton.mpr rfl)
    unfold SortedSetPt.push
    rw [getLast?_snoc, dropLast_snoc]
    dsimp only
    rcases Nat.lt_trichotomy (key target) (key last) with hlt | heq | hgt
    · rw [pt_cmp_eq, nat_compare_lt hlt]
      exact replace_vec target (ys ++ [last])
    · rw [pt_cmp_eq, nat_compare_eq heq]
      have hys_t : ∀ p ∈ ys, key p < key target := by
        intro p hp; have := hys_lt p hp; omega
      rw [insPt_append_last target ys last hys_t]
      simp [insPt, pt_cmp_eq, nat_compare_eq heq.symm]
    · rw [pt_cmp_eq, nat_compare_gt hgt]
      have hys_t : ∀ p ∈ ys, key p < key target := by
        intro p hp; have := hys_lt p hp; omega
      rw [insPt_append_last target ys last hys_t]
      simp [insPt, pt_cmp_eq, nat_compare_lt hgt]

/-! ## 3. Single-Set Update (`stepSet`) -/

def stepSet (nec : Nat) (idx : BitVec 16) (y : GF16) (s : SortedSetPt) : SortedSetPt :=
  if idx.toNat < nec || s.len < nec then
    (s.push { x := idxPt idx.toNat, y := y }).1
  else
    s

theorem key_idxPt {c : Nat} (hc : c < 2 ^ 16) : (idxPt c).value.toNat = c := by
  simp [idxPt, GF16.new]
  omega

theorem stepSet_sorted (nec : Nat) (idx : BitVec 16) (y : GF16) (s : SortedSetPt)
    (hs : (s.vec.map key).Pairwise (· < ·)) :
    ((stepSet nec idx y s).vec.map key).Pairwise (· < ·) := by
  unfold stepSet
  split
  · rw [push_vec s.vec _ hs, map_key_insPt]
    exact pairwise_insKey _ hs
  · exact hs

theorem stepSet_onPoly (msg : List (BitVec 8)) (j : Nat) (idx : BitVec 16) (s : SortedSetPt)
    (hs : (s.vec.map key).Pairwise (· < ·))
    (hpoly : ∀ pt ∈ s.vec, pt.y = (msgPoly msg j).eval pt.x) :
    ∀ pt ∈ (stepSet (needed msg.length j) idx (chunkVal msg idx j) s).vec,
      pt.y = (msgPoly msg j).eval pt.x := by
  intro pt hpt
  unfold stepSet at hpt
  split at hpt
  · rw [push_vec s.vec _ hs] at hpt
    rcases mem_insPt hpt with rfl | hmem
    · rfl
    · exact hpoly pt hmem
  · exact hpoly pt hpt

theorem stepSet_atNode (S : Finset Nat) (nec : Nat) (idx : BitVec 16) (y : GF16) (s : SortedSetPt)
    (hs : (s.vec.map key).Pairwise (· < ·))
    (hnode : ∀ pt ∈ s.vec, ∃ c ∈ S, c < 2 ^ 16 ∧ pt.x = idxPt c) :
    ∀ pt ∈ (stepSet nec idx y s).vec,
      ∃ c ∈ insert idx.toNat S, c < 2 ^ 16 ∧ pt.x = idxPt c := by
  intro pt hpt
  unfold stepSet at hpt
  split at hpt
  · rw [push_vec s.vec _ hs] at hpt
    rcases mem_insPt hpt with rfl | hmem
    · exact ⟨idx.toNat, Finset.mem_insert_self _ _, idx.isLt, rfl⟩
    · obtain ⟨c, hcS, hcLt, hcx⟩ := hnode pt hmem
      exact ⟨c, Finset.mem_insert_of_mem hcS, hcLt, hcx⟩
  · obtain ⟨c, hcS, hcLt, hcx⟩ := hnode pt hpt
    exact ⟨c, Finset.mem_insert_of_mem hcS, hcLt, hcx⟩

theorem stepSet_enough (S : Finset Nat) (nec : Nat) (idx : BitVec 16) (y : GF16) (s : SortedSetPt)
    (hs : (s.vec.map key).Pairwise (· < ·))
    (hnode : ∀ pt ∈ s.vec, ∃ c ∈ S, c < 2 ^ 16 ∧ pt.x = idxPt c)
    (henough : min S.card nec ≤ s.vec.length) :
    min (insert idx.toNat S).card nec ≤ (stepSet nec idx y s).vec.length := by
  unfold stepSet
  split
  · next hcond =>
    have hlen : ((s.push { x := idxPt idx.toNat, y := y }).1.vec).length =
        if key { x := idxPt idx.toNat, y := y } ∈ s.vec.map key then s.vec.length
        else s.vec.length + 1 := by
      rw [push_vec s.vec _ hs, ← List.length_map (f := key), map_key_insPt, length_insKey _ hs]
      simp [List.length_map]
    rw [hlen]
    have hkey0 : key { x := idxPt idx.toNat, y := y } = idx.toNat := key_idxPt idx.isLt
    rw [hkey0]
    split
    · next hmem_key =>
      obtain ⟨pt, hpt_mem, hpt_key⟩ := List.mem_map.mp hmem_key
      obtain ⟨c, hcS, hcLt, hcx⟩ := hnode pt hpt_mem
      have hkc : key pt = c := by
        simp [key, hcx, key_idxPt hcLt]
      have hidx_in_S : idx.toNat ∈ S := by
        rw [← hpt_key, hkc]; exact hcS
      rw [Finset.insert_eq_of_mem hidx_in_S]
      exact henough
    · next hnotmem_key =>
      have hcard : (insert idx.toNat S).card ≤ S.card + 1 := Finset.card_insert_le _ _
      omega
  · next hcond =>
    rw [SortedSetPt.len, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, not_or] at hcond
    omega

/-! ## 4. Chunk Byte Reassembly & `addChunkLoop` Induction -/

theorem recombine_u16 (v : BitVec 16) :
    (((v >>> 8).setWidth 8).zeroExtend 16 <<< 8) + (v.setWidth 8).zeroExtend 16 = v := by
  apply BitVec.eq_of_toNat_eq
  have hv := v.isLt
  simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
  omega

theorem chunkData_recombine (msg : List (BitVec 8)) (idx : BitVec 16) (i : Nat) (hi : i < 16) :
    let y1 := (chunkData msg idx).get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := (chunkData msg idx).get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16) = chunkVal msg idx i := by
  have h1 : (i * 2) % 32 / 2 = i := by omega
  have h2 : (i * 2) % 32 % 2 = 0 := by omega
  have h3 : (i * 2 + 1) % 32 / 2 = i := by omega
  have h4 : (i * 2 + 1) % 32 % 2 = 1 := by omega
  simp only [chunkData, List.Vector.get_ofFn, h1, h2, h3, h4, ↓reduceIte,
    Nat.one_ne_zero, recombine_u16]
  rfl

theorem addChunkLoop_spec (msg : List (BitVec 8)) (idx : BitVec 16) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      i + rem = 16 →
      (hlen : self.pts.length = 16) →
      self.ptsNeeded = msg.length / 2 →
      ∃ (dec' : PolyDecoder) (hlen' : dec'.pts.length = 16),
        PolyDecoder.addChunkLoop { index := idx, data := chunkData msg idx } i rem self = .ok dec' ∧
        dec'.ptsNeeded = self.ptsNeeded ∧
        dec'.isComplete = self.isComplete ∧
        ∀ j (hj : j < 16),
          dec'.pts[j]'(by omega) =
            if j < i then self.pts[j]'(by omega)
            else stepSet (needed msg.length j) idx (chunkVal msg idx j) (self.pts[j]'(by omega))
  | 0, i, self, hirem, hlen, hneeded => by
    refine ⟨self, hlen, rfl, rfl, rfl, fun j hj => ?_⟩
    have : j < i := by omega
    simp [this]
  | rem + 1, i, self, hirem, hlen, hneeded => by
    have hi : i < 16 := by omega
    have hmod : (idx.toNat * 16 + i) % 16 = i := by omega
    have hdiv : (idx.toNat * 16 + i) / 16 = idx.toNat := by omega
    have hget? : self.pts[i]? = some (self.pts[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hnec : self.necessaryPoints i = needed msg.length i :=
      necessaryPoints_eq self msg.length hneeded i
    have hy := chunkData_recombine msg idx i hi
    unfold PolyDecoder.addChunkLoop
    simp only [hmod, hdiv, hget?, hnec, hy]
    let s_i' := stepSet (needed msg.length i) idx (chunkVal msg idx i) (self.pts[i]'(by omega))
    let self' : PolyDecoder :=
      if idx.toNat < needed msg.length i || (self.pts[i]'(by omega)).len < needed msg.length i then
        let (polyPts', _, _) := (self.pts[i]'(by omega)).push
          { x := GF16.new (BitVec.ofNat 16 idx.toNat), y := chunkVal msg idx i }
        { self with pts := self.pts.set i polyPts' }
      else
        self
    have hself'_eq : self' = { self with pts := self.pts.set i s_i' } := by
      dsimp [self', s_i', stepSet, idxPt]
      split
      · rfl
      · cases self; simp [List.set_getElem_self]
    have hlen' : self'.pts.length = 16 := by
      rw [hself'_eq]; simp [hlen]
    have hneeded' : self'.ptsNeeded = msg.length / 2 := by
      rw [hself'_eq]; exact hneeded
    obtain ⟨dec', hlen'', hloop, hpn, hic, hpts⟩ :=
      addChunkLoop_spec msg idx rem (i + 1) self' (by omega) hlen' hneeded'
    refine ⟨dec', hlen'', hloop, ?_, ?_, fun j hj => ?_⟩
    · rw [hpn, hself'_eq]
    · rw [hic, hself'_eq]
    · rw [hpts j hj]
      by_cases hji : j < i
      · have hj1 : j < i + 1 := by omega
        have hij : i ≠ j := by omega
        simp [hji, hj1, hself'_eq, List.getElem_set_ne hij]
      · by_cases hjeq : j = i
        · subst hjeq
          have hj1 : j < j + 1 := by omega
          simp [hj1, hself'_eq, s_i']
        · have hj1 : ¬ j < i + 1 := by omega
          have hij : i ≠ j := by omega
          simp [hji, hj1, hself'_eq, List.getElem_set_ne hij]

theorem addChunk_spec_aux (msg : List (BitVec 8)) (S : Finset Nat) (dec : PolyDecoder)
    (hd : DecInv msg S dec) (_hlen : msg.length ≤ 2 ^ 20) (idx : BitVec 16) :
    ∃ dec', dec.addChunk { index := idx, data := chunkData msg idx } = .ok dec' ∧
      DecInv msg (insert idx.toNat S) dec' := by
  have hdec_len : dec.pts.length = 16 := hd.len
  obtain ⟨dec', hlen', hloop, hpn, hic, hpts⟩ :=
    addChunkLoop_spec msg idx 16 0 dec (by omega) hdec_len hd.ptsNeeded
  refine ⟨dec', hloop, ?_⟩
  have hpts0 : ∀ j (hj : j < 16),
      dec'.pts[j]'(by omega) =
        stepSet (needed msg.length j) idx (chunkVal msg idx j) (dec.pts[j]'(by omega)) := by
    intro j hj
    simpa using hpts j hj
  refine
    { ptsNeeded := hpn.trans hd.ptsNeeded
      notComplete := hic.trans hd.notComplete
      len := hlen'
      sorted := fun j hj => by
        have hj16 : j < 16 := by omega
        rw [hpts0 j hj16]
        exact stepSet_sorted _ _ _ _ (hd.sorted j (by omega))
      onPoly := fun j hj => by
        have hj16 : j < 16 := by omega
        rw [hpts0 j hj16]
        exact stepSet_onPoly msg j idx _ (hd.sorted j (by omega)) (hd.onPoly j (by omega))
      atNode := fun j hj => by
        have hj16 : j < 16 := by omega
        rw [hpts0 j hj16]
        exact stepSet_atNode S _ idx _ _ (hd.sorted j (by omega)) (hd.atNode j (by omega))
      enough := fun j hj => by
        have hj16 : j < 16 := by omega
        rw [hpts0 j hj16]
        exact stepSet_enough S _ idx _ _
          (hd.sorted j (by omega)) (hd.atNode j (by omega)) (hd.enough j (by omega)) }

end CryptoVerification.SpqrV1Sync.Erasure.AddChunk
