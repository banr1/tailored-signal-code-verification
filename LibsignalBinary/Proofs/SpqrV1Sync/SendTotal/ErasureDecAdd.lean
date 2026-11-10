/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import ProofLib

/-!
# Decoder Well-Formedness Under `addChunk`

Proves that `PolyDecoder.addChunk` preserves `DecWF n` on arbitrary chunks (`st_decAdd`), keeping
all `16` `SortedSetPt` lanes strictly sorted by `x : GF16`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1

private abbrev ptKey (pt : Pt) : ℕ := pt.x.value.toNat

private theorem pt_cmp_eq_lt {a b : Pt} : Pt.cmp a b = .lt ↔ ptKey a < ptKey b := by
  unfold Pt.cmp ptKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .lt ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all

private theorem pt_cmp_eq_eq {a b : Pt} : Pt.cmp a b = .eq ↔ ptKey a = ptKey b := by
  unfold Pt.cmp ptKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .eq ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all
  omega

private theorem pt_cmp_eq_gt {a b : Pt} : Pt.cmp a b = .gt ↔ ptKey b < ptKey a := by
  unfold Pt.cmp ptKey
  change compareOfLessAndEq a.x.value.toNat b.x.value.toNat = .gt ↔ _
  simp only [compareOfLessAndEq]
  split_ifs <;> simp_all <;> omega

private theorem binarySearchAux_spec (target : Pt) (idx : ℕ) (rest : List Pt)
    (hr : (rest.map ptKey).Pairwise (· < ·)) :
    (∃ k, ∃ _ : k < rest.length,
      SortedSetPt.binarySearchAux target idx rest = .ok (idx + k) ∧
      ptKey rest[k] = ptKey target) ∨
    (∃ k, k ≤ rest.length ∧
      SortedSetPt.binarySearchAux target idx rest = .error (idx + k) ∧
      (∀ p ∈ rest.take k, ptKey p < ptKey target) ∧
      (∀ p ∈ rest.drop k, ptKey target < ptKey p)) := by
  induction rest generalizing idx with
  | nil =>
    right
    exact ⟨0, Nat.le_refl 0, by simp [SortedSetPt.binarySearchAux], by simp, by simp⟩
  | cons pt tail ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hr
    unfold SortedSetPt.binarySearchAux
    cases hc : Pt.cmp pt target with
    | lt =>
      simp only []
      have hlt : ptKey pt < ptKey target := pt_cmp_eq_lt.mp hc
      rcases ih (idx + 1) hr.2 with ⟨k, hk, hok, heq⟩ | ⟨k, hk, herr, htake, hdrop⟩
      · left
        refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_⟩
        · rw [hok]; congr 1; omega
        · simpa using heq
      · right
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_, ?_, ?_⟩
        · rw [herr]; congr 1; omega
        · intro p hp
          simp only [List.take_succ_cons, List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact hlt
          · exact htake p hp
        · intro p hp
          simp only [List.drop_succ_cons] at hp
          exact hdrop p hp
    | eq =>
      simp only []
      have heq : ptKey pt = ptKey target := pt_cmp_eq_eq.mp hc
      left
      exact ⟨0, by simp, by simp, heq⟩
    | gt =>
      simp only []
      have hgt : ptKey target < ptKey pt := pt_cmp_eq_gt.mp hc
      right
      refine ⟨0, Nat.zero_le _, by simp, by simp, ?_⟩
      intro p hp
      simp only [List.drop_zero, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hgt
      · exact Nat.lt_trans hgt (hr.1 p hp)

private theorem replace_pairwise (s : SortedSetPt) (el : Pt)
    (hs : (s.vec.map ptKey).Pairwise (· < ·)) :
    ((s.replace el).1.vec.map ptKey).Pairwise (· < ·) := by
  unfold SortedSetPt.replace SortedSetPt.binarySearch
  rcases binarySearchAux_spec el 0 s.vec hs with ⟨k, hk, hok, heq⟩ | ⟨k, _, herr, htake, hdrop⟩
  · rw [Nat.zero_add] at hok
    simp only [hok]
    have hmap : (s.vec.set k el).map ptKey = s.vec.map ptKey := by
      apply List.ext_getElem
      · simp
      · intro m hm1 hm2
        simp only [List.getElem_map, List.getElem_set]
        split_ifs with hkm
        · subst hkm; exact heq.symm
        · rfl
    rw [hmap]
    exact hs
  · rw [Nat.zero_add] at herr
    simp only [herr, List.map_append, List.map_cons]
    have hsplit : (s.vec.take k).map ptKey ++ (s.vec.drop k).map ptKey = s.vec.map ptKey := by
      rw [← List.map_append, List.take_append_drop]
    rw [← hsplit] at hs
    rcases List.pairwise_append.mp hs with ⟨hs1, hs2, hs12⟩
    refine List.pairwise_append.mpr ⟨hs1, List.pairwise_cons.mpr ⟨?_, hs2⟩, ?_⟩
    · intro b hb
      rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
      exact hdrop p hp
    · intro a ha b hb
      rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact htake p hp
      · exact hs12 (ptKey p) ha b hb

private theorem eq_dropLast_append_of_getLast? :
    ∀ {l : List Pt} {last : Pt}, l.getLast? = some last → l = l.dropLast ++ [last]
  | [], _, h => by simp at h
  | [a], last, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h; rfl
  | a :: b :: tl, last, h => by
    have ih := eq_dropLast_append_of_getLast? (l := b :: tl) (by simpa using h)
    simp only [List.dropLast, List.cons_append]
    exact congrArg (a :: ·) ih

private theorem push_pairwise (s : SortedSetPt) (el : Pt)
    (hs : (s.vec.map ptKey).Pairwise (· < ·)) :
    ((s.push el).1.vec.map ptKey).Pairwise (· < ·) := by
  unfold SortedSetPt.push
  cases hlast : s.vec.getLast? with
  | none => simp
  | some last =>
    simp only
    have hsplit : s.vec = s.vec.dropLast ++ [last] := eq_dropLast_append_of_getLast? hlast
    have hdl : ((s.vec.dropLast ++ [last]).map ptKey).Pairwise (· < ·) := hsplit ▸ hs
    rw [List.map_append] at hdl
    rcases List.pairwise_append.mp hdl with ⟨_, _, hdl_lt⟩
    cases hc : Pt.cmp el last with
    | gt =>
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hgt : ptKey last < ptKey el := pt_cmp_eq_gt.mp hc
      refine List.pairwise_append.mpr ⟨hs, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      rw [hsplit, List.mem_map] at ha
      rcases ha with ⟨p, hp, rfl⟩
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact Nat.lt_trans (hdl_lt (ptKey p) (List.mem_map_of_mem hp) (ptKey last) (by simp)) hgt
      · exact hgt
    | eq =>
      simp only []
      have heq : ptKey el = ptKey last := pt_cmp_eq_eq.mp hc
      have hmap : (s.vec.dropLast ++ [el]).map ptKey = s.vec.map ptKey := by
        calc (s.vec.dropLast ++ [el]).map ptKey
            = s.vec.dropLast.map ptKey ++ [ptKey el] := by simp
          _ = s.vec.dropLast.map ptKey ++ [ptKey last] := by rw [heq]
          _ = (s.vec.dropLast ++ [last]).map ptKey := by simp
          _ = s.vec.map ptKey := by rw [← hsplit]
      rw [hmap]
      exact hs
    | lt =>
      simp only []
      exact replace_pairwise s el hs

private theorem addChunkLoop_wf (n : ℕ) (c : Chunk) (i rem : ℕ) (d d' : PolyDecoder)
    (hwf : DecWF n d) (h : d.addChunkLoop c i rem = .ok d') :
    DecWF n d' := by
  induction rem generalizing i d with
  | zero =>
    simp only [PolyDecoder.addChunkLoop, Except.ok.injEq] at h
    subst h
    exact hwf
  | succ rem ih =>
    unfold PolyDecoder.addChunkLoop at h
    have hmod : (c.index.toNat * 16 + i) % 16 = i % 16 := Nat.mul_add_mod_self_right _ _ _
    simp only [hmod] at h
    cases hpts : d.pts[i % 16]? with
    | none => simp [hpts] at h
    | some polyPts =>
      simp only [hpts] at h
      refine ih (i + 1) _ ?_ h
      split_ifs with hcond
      · refine ⟨hwf.1, by simp [hwf.2.1], ?_⟩
        intro j hj
        have hj' : j < d.pts.length := by simpa using hj
        simp only [List.getElem_set]
        split_ifs with hpj
        · subst hpj
          have hget : d.pts[i % 16] = polyPts := by
            rw [List.getElem?_eq_getElem hj'] at hpts
            exact Option.some.inj hpts
          rw [← hget]
          exact push_pairwise (d.pts[i % 16]) _ (hwf.2.2 (i % 16) hj')
        · exact hwf.2.2 j hj'
      · exact hwf

/-- `PolyDecoder.addChunk` preserves `DecWF n` for any input chunk. -/
theorem st_decAdd : DecAddStmt := by
  intro n d d' c hwf hadd
  exact addChunkLoop_wf n c 0 16 d d' hwf hadd

end CryptoVerification.SpqrV1Sync.SendTotal
