/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Concrete.ByteSpecs

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRTag
open ByteSpecs
theorem toBEBytes_length (n : ℕ) {w : ℕ} (x : BitVec w) : (toBEBytes n x).length = n := by simp [toBEBytes]
theorem sha256Pad_length (m : List (BitVec 8)) : (sha256Pad m).length = m.length + 9 + (119 - m.length % 64) % 64 := by simp only [sha256Pad, List.length_append, List.length_cons, List.length_nil, List.length_replicate, toBEBytes_length]; omega
theorem sha256Pad_length_mod (m : List (BitVec 8)) : (sha256Pad m).length % 64 = 0 := by rw [sha256Pad_length]; omega
theorem chunks64_length (bs : List (BitVec 8)) : (chunks64 bs).length = bs.length / 64 := by simp [chunks64]
theorem chunks64_sha256Pad_ne_nil (m : List (BitVec 8)) : chunks64 (sha256Pad m) ≠ [] := by intro h; have hl := congrArg List.length h; rw [chunks64_length, sha256Pad_length] at hl; simp only [List.length_nil] at hl; omega
theorem dropLast_append_getLast {α : Type} : ∀ {l : List α} (h : l ≠ []), l.dropLast ++ [l.getLast h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | x :: y :: zs, _ => congrArg (x :: ·) (dropLast_append_getLast (List.cons_ne_nil y zs))
theorem foldl_eq_getLast {α β : Type} (f : β → α → β) (b : β) (l : List α) (h : l ≠ []) : l.foldl f b = f (l.dropLast.foldl f b) (l.getLast h) := by
  conv_lhs => rw [← dropLast_append_getLast h]
  simp [List.foldl_append]
def lastBlock (m : List (BitVec 8)) : List (BitVec 8) := (chunks64 (sha256Pad m)).getLast (chunks64_sha256Pad_ne_nil m)
def stateBeforeLast (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) : ShaState := (chunks64 (sha256Pad m)).dropLast.foldl F sha256IV
theorem sha256With_eq_last (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) : sha256With F m = (F (stateBeforeLast F m) (lastBlock m)).toList.flatMap (toBEBytes 4) := by unfold sha256With stateBeforeLast lastBlock; rw [foldl_eq_getLast F sha256IV _ (chunks64_sha256Pad_ne_nil m)]
section Collapse
variable (onTable : ShaState → List (BitVec 8) → Prop) (tagState : List (BitVec 8) → ShaState)
end Collapse
theorem sha256With_take4 (F : ShaState → List (BitVec 8) → ShaState) (m : List (BitVec 8)) : (sha256With F m).take 4 = toBEBytes 4 (F (stateBeforeLast F m) (lastBlock m)).head := by
  rw [sha256With_eq_last]; obtain ⟨l, hl⟩ := F (stateBeforeLast F m) (lastBlock m)
  match l, hl with
  | w :: ws, _ =>
    simp [List.Vector.head, List.Vector.toList, List.flatMap_cons, toBEBytes_length]
theorem chunks64_append64 (x rest : List (BitVec 8)) (hx : x.length = 64) : chunks64 (x ++ rest) = x :: chunks64 rest := by
  apply List.ext_getElem
  · simp only [chunks64_length, List.length_append, List.length_cons, hx]; omega
  · intro i h1 h2
    cases i with
    | zero => simp [chunks64, hx]
    | succ j =>
      simp only [chunks64, List.getElem_ofFn, List.getElem_cons_succ]
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hx]; omega), hx,
        List.nil_append, show 64 * (j + 1) - 64 = 64 * j by omega]
def padTail64 (m : List (BitVec 8)) : List (BitVec 8) := m ++ [0x80] ++ List.replicate ((119 - (64 + m.length) % 64) % 64) 0 ++ toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + m.length)))
theorem sha256Pad_append64 (x m : List (BitVec 8)) (hx : x.length = 64) : sha256Pad (x ++ m) = x ++ padTail64 m := by simp [sha256Pad, padTail64, hx, List.append_assoc]
section Propagation
variable (onTable : ShaState → List (BitVec 8) → Prop) (tagWord : BitVec 32) (F : ShaState → List (BitVec 8) → ShaState) (hstep : ∀ s b, ¬ onTable s b → (F s b).head = tagWord) (hT1 : ∀ s b, s.head = tagWord → ¬ onTable s b)
include hstep hT1 in
theorem foldl_tagged : ∀ (l : List (List (BitVec 8))) (s : ShaState), s.head = tagWord → (l.foldl F s).head = tagWord := by
  intro l
  induction l with
  | nil => intro s hs; exact hs
  | cons b l ih => intro s hs; exact ih _ (hstep _ _ (hT1 _ _ hs))
theorem sha256With_take4_fold (m : List (BitVec 8)) : (sha256With F m).take 4 = toBEBytes 4 ((chunks64 (sha256Pad m)).foldl F sha256IV).head := by
  unfold sha256With; obtain ⟨l, hl⟩ := (chunks64 (sha256Pad m)).foldl F sha256IV
  match l, hl with
  | w :: ws, _ =>
    simp [List.Vector.head, List.Vector.toList, List.flatMap_cons, toBEBytes_length]
include hstep hT1 in
theorem sha256With_take4_of_offTable (m : List (BitVec 8)) (l₁ : List (List (BitVec 8))) (b : List (BitVec 8)) (l₂ : List (List (BitVec 8))) (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) (hoff : ¬ onTable (l₁.foldl F sha256IV) b) : (sha256With F m).take 4 = toBEBytes 4 tagWord := by rw [sha256With_take4_fold, hsplit, List.foldl_append, List.foldl_cons, foldl_tagged onTable tagWord F hstep hT1 l₂ _ (hstep _ _ hoff)]
theorem sha256With_length (m : List (BitVec 8)) : (sha256With F m).length = 32 := by
  unfold sha256With; obtain ⟨l, hl⟩ := (chunks64 (sha256Pad m)).foldl F sha256IV
  match l, hl with
  | [_, _, _, _, _, _, _, _], _ => simp [List.Vector.toList, toBEBytes_length]
theorem chunks64_padTail64_32 (h : List (BitVec 8)) (hh : h.length = 32) : chunks64 (padTail64 h) = [padTail64 h] := by
  have hlen : (padTail64 h).length = 64 := (by simp only [padTail64, List.length_append, List.length_cons, List.length_nil, List.length_replicate, toBEBytes_length, hh]); apply List.ext_getElem
  · simp [chunks64_length, hlen]
  · intro i h1 h2
    have hi : i = 0 := by simp at h2; omega
    subst hi; simp [chunks64, List.take_of_length_le, hlen]
theorem padTail64_take4 (h : List (BitVec 8)) (hh : h.length = 32) : (padTail64 h).take 4 = h.take 4 := by simp [padTail64, List.take_append_of_le_length, hh]
include hstep hT1 in
theorem hmacWith_take4_of_inner (hT2 : ∀ s b, b.take 4 = toBEBytes 4 tagWord → ¬ onTable s b) (k m : List (BitVec 8)) (hk : k.length ≤ 64) (hinner : (sha256With F ((k ++ List.replicate (64 - k.length) 0).map (· ^^^ 0x36) ++ m)).take 4 = toBEBytes 4 tagWord) : (hmacWith F k m).take 4 = toBEBytes 4 tagWord := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ite_false]
  set inner := sha256With F ((k ++ List.replicate (64 - k.length) 0).map (· ^^^ 0x36) ++ m)
  have hil : inner.length = 32 := sha256With_length F _
  have hx : ((k ++ List.replicate (64 - k.length) 0).map (· ^^^ 0x5c)).length = 64 := by simp; omega
  set x := (k ++ List.replicate (64 - k.length) 0).map (· ^^^ (0x5c : BitVec 8))
  have hsplit : chunks64 (sha256Pad (x ++ inner)) = [x] ++ padTail64 inner :: [] := (by rw [sha256Pad_append64 x inner hx, chunks64_append64 x _ hx, chunks64_padTail64_32 inner hil]; rfl); refine sha256With_take4_of_offTable onTable tagWord F hstep hT1 _ [x] (padTail64 inner) [] hsplit (hT2 _ _ ?_); rw [padTail64_take4 inner hil]; exact hinner
end Propagation
end Symbolic.BugInjection.Proofs.Common443.CompRTag
