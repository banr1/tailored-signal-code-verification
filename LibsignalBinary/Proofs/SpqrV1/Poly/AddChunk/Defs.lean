/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.PolyPart1CodeSym
public import LibsignalBinary.Proofs.SpqrV1.Alloc.GrowOne
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# `<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk`: Definitions and Specifications

Pure totality (`addChunkTotal`), hardware binary-search equivalence (`addChunkBsearch_eq_addChunkTotal`),
and separation-logic contracts (`addChunkBsearchSpec`, `addChunkSpec`, `addChunkSpecX`) for
`<PolyDecoder as Decoder>::add_chunk` (`0x6c420`, Block `419`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Poly.AddChunk

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Alloc CryptoVerification.CodeLayout

/-! ## Symbol Name, Decode Tree, and Stack Budgets -/

abbrev addChunkName : String :=
  "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"

theorem addChunk_fnOff : libsignalSessionCode.fnOff addChunkName = 0x67028 :=
  ls_lemma% fnOff "<spqr::encoding::polynomial::PolyDecoder as spqr::encoding::Decoder>::add_chunk"

gen_decodes libsignalSessionCode_tree addChunkBin [0x67028 → 0x6722c]

/-- Own stack frame of `add_chunk` (`0x60 = 96` bytes) + `growOneStack` (`4208` bytes) = `4304` bytes. -/
abbrev addChunkStack : Nat := 96 + growOneStack

/-- Own stack frame of `add_chunk` (`96` bytes) + `extHookStack` (`16384` bytes). -/
abbrev addChunkStackX : Nat := 96 + extHookStack

/-! ## Total Pure Characterization of `PolyDecoder.addChunk` -/

/-- Total version of `PolyDecoder.addChunkLoop` (`self.pts.length = 16`). -/
def addChunkLoopTotal (chunk : Chunk) : Nat → Nat → PolyDecoder → PolyDecoder
  | _, 0, self => self
  | i, rem + 1, self =>
    let totalIdx := chunk.index.toNat * 16 + i
    let poly := totalIdx % 16
    let polyIdx := totalIdx / 16
    let x := GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let polyPts := self.pts[poly]?.getD SortedSetPt.new
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set poly polyPts' }
      else
        self
    addChunkLoopTotal chunk (i + 1) rem self'

/-- Total pure result of `PolyDecoder.addChunk self chunk` when `self.pts.length = 16`. -/
def addChunkTotal (self : PolyDecoder) (chunk : Chunk) : PolyDecoder :=
  addChunkLoopTotal chunk 0 16 self

theorem addChunkLoop_eq_ok (chunk : Chunk) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      self.pts.length = 16 →
      PolyDecoder.addChunkLoop chunk i rem self = .ok (addChunkLoopTotal chunk i rem self) ∧
        (addChunkLoopTotal chunk i rem self).pts.length = 16 ∧
        (addChunkLoopTotal chunk i rem self).ptsNeeded = self.ptsNeeded ∧
        (addChunkLoopTotal chunk i rem self).isComplete = self.isComplete
  | 0, _, self, hlen => by
    simp [PolyDecoder.addChunkLoop, addChunkLoopTotal, hlen]
  | rem + 1, i, self, hlen => by
    have hpoly_lt : (chunk.index.toNat * 16 + i) % 16 < self.pts.length := by
      rw [hlen]
      exact Nat.mod_lt _ (by decide)
    have hget : self.pts[(chunk.index.toNat * 16 + i) % 16]? =
        some (self.pts[(chunk.index.toNat * 16 + i) % 16]'hpoly_lt) :=
      List.getElem?_eq_getElem hpoly_lt
    let polyPts := self.pts[(chunk.index.toNat * 16 + i) % 16]'hpoly_lt
    let polyIdx := (chunk.index.toNat * 16 + i) / 16
    let x := GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set ((chunk.index.toNat * 16 + i) % 16) polyPts' }
      else
        self
    have hlen' : self'.pts.length = 16 := by
      dsimp only [self']
      split <;> simp [hlen]
    have hneed' : self'.ptsNeeded = self.ptsNeeded := by
      dsimp only [self']
      split <;> rfl
    have hcomp' : self'.isComplete = self.isComplete := by
      dsimp only [self']
      split <;> rfl
    have ih := addChunkLoop_eq_ok chunk rem (i + 1) self' hlen'
    unfold PolyDecoder.addChunkLoop addChunkLoopTotal
    dsimp only
    rw [hget, Option.getD_some]
    exact ⟨ih.1, ih.2.1, ih.2.2.1.trans hneed', ih.2.2.2.trans hcomp'⟩

/-- When `self.pts.length = 16`, `PolyDecoder.addChunk self chunk` always returns
    `.ok (addChunkTotal self chunk)` (never `.error PolyPanic`). -/
@[simp] theorem addChunk_eq_ok (self : PolyDecoder) (chunk : Chunk)
    (hlen : self.pts.length = 16) :
    PolyDecoder.addChunk self chunk = .ok (addChunkTotal self chunk) :=
  (addChunkLoop_eq_ok chunk 16 0 self hlen).1

@[simp] theorem addChunkTotal_pts_length (self : PolyDecoder) (chunk : Chunk)
    (hlen : self.pts.length = 16) :
    (addChunkTotal self chunk).pts.length = 16 :=
  (addChunkLoop_eq_ok chunk 16 0 self hlen).2.1

@[simp] theorem addChunkTotal_ptsNeeded (self : PolyDecoder) (chunk : Chunk)
    (hlen : self.pts.length = 16) :
    (addChunkTotal self chunk).ptsNeeded = self.ptsNeeded :=
  (addChunkLoop_eq_ok chunk 16 0 self hlen).2.2.1

@[simp] theorem addChunkTotal_isComplete (self : PolyDecoder) (chunk : Chunk)
    (hlen : self.pts.length = 16) :
    (addChunkTotal self chunk).isComplete = self.isComplete :=
  (addChunkLoop_eq_ok chunk 16 0 self hlen).2.2.2

/-! ## Hardware Binary Search Mirror and Equivalence on Strictly Sorted `SortedSet<Pt>` -/

/-- Exact functional mirror of the hardware binary search loop at `0x6c524..0x6c544`. -/
def bsearchLoop (vec : List Pt) (xVal : BitVec 16) (base size : Nat) : Nat :=
  if _h : size > 1 then
    let half := size / 2
    let mid := base + half
    let size' := size - half
    let midX := (vec[mid]?.getD default).x.value
    let base' := if xVal.toNat < midX.toNat then base else mid
    bsearchLoop vec xVal base' size'
  else
    base
termination_by size
decreasing_by
  have : size / 2 > 0 := Nat.div_pos (by omega) (by decide)
  omega

theorem bsearchLoop_bounds (vec : List Pt) (xVal : BitVec 16) :
    ∀ (base size : Nat),
      1 ≤ size → base + size ≤ vec.length →
      base ≤ bsearchLoop vec xVal base size ∧ bsearchLoop vec xVal base size < base + size := by
  intro base size
  induction size using Nat.strongRecOn generalizing base with
  | ind size ih =>
    intro h1 hle
    rw [bsearchLoop]
    split_ifs with hgt
    · have hhalf_pos : 0 < size / 2 := Nat.div_pos (by omega) (by decide)
      have hsize'_lt : size - size / 2 < size := by omega
      have hsize'_ge1 : 1 ≤ size - size / 2 := by omega
      dsimp only
      split_ifs with hcmp
      · have ⟨hlo, hhi⟩ := ih (size - size / 2) hsize'_lt base hsize'_ge1 (by omega)
        exact ⟨hlo, by omega⟩
      · have ⟨hlo, hhi⟩ := ih (size - size / 2) hsize'_lt (base + size / 2) hsize'_ge1 (by omega)
        exact ⟨by omega, by omega⟩
    · exact ⟨Nat.le_refl _, by omega⟩

/-- Exact functional mirror of `0x6c50c..0x6c5a0` (`SortedSet::replace` when `element.x < last.x`). -/
def bsearchReplace (self : SortedSetPt) (element : Pt) : SortedSetPt :=
  let base := bsearchLoop self.vec element.x.value 0 self.vec.length
  let baseX := (self.vec[base]?.getD default).x.value
  if baseX == element.x.value then
    { vec := self.vec.set base element }
  else
    let insertIdx := if baseX.toNat < element.x.value.toNat then base + 1 else base
    { vec := self.vec.take insertIdx ++ (element :: self.vec.drop insertIdx) }

/-- Exact functional mirror of `0x6c4a0..0x6c5a0` (`SortedSet::push`). -/
def bsearchPush (self : SortedSetPt) (element : Pt) : SortedSetPt :=
  match self.vec.getLast? with
  | some last =>
    match Pt.cmp element last with
    | .gt => { vec := self.vec ++ [element] }
    | .eq => { vec := self.vec.dropLast ++ [element] }
    | .lt => bsearchReplace self element
  | none => { vec := [element] }

/-- Hardware loop mirror of `add_chunk` (`0x6c46c..0x6c5f8`), for `i` in `0..16`. -/
def addChunkBsearchLoop (chunk : Chunk) : Nat → Nat → PolyDecoder → PolyDecoder
  | _, 0, self => self
  | i, rem + 1, self =>
    let totalIdx := chunk.index.toNat * 16 + i
    let poly := totalIdx % 16
    let polyIdx := totalIdx / 16
    let x := GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let polyPts := self.pts[poly]?.getD SortedSetPt.new
    let nec := self.necessaryPoints i
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let polyPts' := bsearchPush polyPts { x := x, y := y }
        { self with pts := self.pts.set poly polyPts' }
      else
        self
    addChunkBsearchLoop chunk (i + 1) rem self'

/-- Hardware mirror of `<PolyDecoder as Decoder>::add_chunk` (`0x6c420..0x6c614`). -/
def addChunkBsearch (self : PolyDecoder) (chunk : Chunk) : PolyDecoder :=
  addChunkBsearchLoop chunk 0 16 self

/-- A `List Pt` is strictly sorted by `x` (`a.x.value.toNat < b.x.value.toNat`). -/
def PtListStrictSorted (pts : List Pt) : Prop :=
  pts.Pairwise (fun a b => a.x.value.toNat < b.x.value.toNat)

/-- A `SortedSetPt` is strictly sorted by `x`. -/
def SortedSetPtStrictSorted (s : SortedSetPt) : Prop :=
  PtListStrictSorted s.vec

/-- Every `SortedSetPt` in `dec.pts` is strictly sorted by `x`. -/
def PolyDecoderStrictSorted (dec : PolyDecoder) : Prop :=
  ∀ s ∈ dec.pts, SortedSetPtStrictSorted s

theorem ptListStrictSorted_getElem_lt {vec : List Pt} (hsort : PtListStrictSorted vec)
    {i j : Nat} (hi : i < vec.length) (hj : j < vec.length) (hij : i < j) :
    (vec[i]'hi).x.value.toNat < (vec[j]'hj).x.value.toNat :=
  List.pairwise_iff_getElem.mp hsort i j hi hj hij

theorem ptListStrictSorted_getElem_le {vec : List Pt} (hsort : PtListStrictSorted vec)
    {i j : Nat} (hi : i < vec.length) (hj : j < vec.length) (hij : i ≤ j) :
    (vec[i]'hi).x.value.toNat ≤ (vec[j]'hj).x.value.toNat := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (ptListStrictSorted_getElem_lt hsort hi hj hlt)

theorem ptListStrictSorted_idx_le_getElem {vec : List Pt} (hsort : PtListStrictSorted vec) :
    ∀ (i : Nat) (hi : i < vec.length), i ≤ (vec[i]'hi).x.value.toNat
  | 0, _ => Nat.zero_le _
  | i + 1, hi => by
    have hi0 : i < vec.length := Nat.lt_of_succ_lt hi
    have h1 := ptListStrictSorted_idx_le_getElem hsort i hi0
    have h2 := ptListStrictSorted_getElem_lt hsort hi0 hi (Nat.lt_succ_self i)
    omega

theorem ptListStrictSorted_length_le {vec : List Pt} (hsort : PtListStrictSorted vec) :
    vec.length ≤ 65536 := by
  by_cases hpos : 0 < vec.length
  · have hlast : vec.length - 1 < vec.length := by omega
    have h1 := ptListStrictSorted_idx_le_getElem hsort (vec.length - 1) hlast
    have h2 : (vec[vec.length - 1]'hlast).x.value.toNat < 65536 :=
      (vec[vec.length - 1]'hlast).x.value.isLt
    omega
  · omega

theorem bsearchReplace_length_le (s : SortedSetPt) (element : Pt) :
    (bsearchReplace s element).vec.length ≤ s.vec.length + 1 := by
  unfold bsearchReplace
  dsimp only
  split_ifs <;> simp only [List.length_set, List.length_append, List.length_cons,
    List.length_take, List.length_drop] <;> omega

theorem bsearchPush_length_le (s : SortedSetPt) (element : Pt) :
    (bsearchPush s element).vec.length ≤ s.vec.length + 1 := by
  unfold bsearchPush
  cases s.vec.getLast? with
  | none => simp
  | some last =>
    dsimp only
    cases Pt.cmp element last with
    | gt => simp
    | eq => rw [List.length_append, List.length_dropLast, List.length_singleton]; omega
    | lt => exact bsearchReplace_length_le s element

theorem bsearchLoop_sorted_inv {vec : List Pt} (hsort : PtListStrictSorted vec) (xVal : BitVec 16) :
    ∀ (base size : Nat),
      1 ≤ size →
      base + size ≤ vec.length →
      (base = 0 ∨ (vec[base]?.getD default).x.value.toNat ≤ xVal.toNat) →
      (∀ k (hk : k < vec.length), base + size ≤ k → xVal.toNat < (vec[k]'hk).x.value.toNat) →
      let b := bsearchLoop vec xVal base size
      (b = 0 ∨ (vec[b]?.getD default).x.value.toNat ≤ xVal.toNat) ∧
        (∀ k (hk : k < vec.length), b + 1 ≤ k → xVal.toNat < (vec[k]'hk).x.value.toNat) := by
  intro base size
  induction size using Nat.strongRecOn generalizing base with
  | ind size ih =>
    intro h1 hle hL hR
    rw [bsearchLoop]
    split_ifs with hgt
    · have hhalf_pos : 0 < size / 2 := Nat.div_pos (by omega) (by decide)
      have hsize'_lt : size - size / 2 < size := by omega
      have hsize'_ge1 : 1 ≤ size - size / 2 := by omega
      have hmid_lt : base + size / 2 < vec.length := by omega
      have hmid_get : vec[base + size / 2]?.getD default = vec[base + size / 2]'hmid_lt := by
        rw [List.getElem?_eq_getElem hmid_lt, Option.getD_some]
      dsimp only
      split_ifs with hcmp
      · refine ih (size - size / 2) hsize'_lt base hsize'_ge1 (by omega) hL ?_
        intro k hk hkle
        have hmid_le_k : base + size / 2 ≤ k := by omega
        have hle_k := ptListStrictSorted_getElem_le hsort hmid_lt hk hmid_le_k
        rw [hmid_get] at hcmp
        omega
      · refine ih (size - size / 2) hsize'_lt (base + size / 2) hsize'_ge1 (by omega)
          (Or.inr (by omega)) ?_
        intro k hk hkle
        exact hR k hk (by omega)
    · exact ⟨hL, fun k hk hkle => hR k hk (by omega)⟩

theorem binarySearchAux_eq_drop (vec : List Pt) (target : Pt) :
    ∀ (i : Nat) (hi : i ≤ vec.length),
      (∀ k (hk : k < i), (vec[k]'(Nat.lt_of_lt_of_le hk hi)).x.value.toNat < target.x.value.toNat) →
      SortedSetPt.binarySearchAux target 0 vec = SortedSetPt.binarySearchAux target i (vec.drop i)
  | 0, _, _ => rfl
  | i + 1, hi, hlt => by
    have hi_lt : i < vec.length := Nat.lt_of_succ_le hi
    rw [binarySearchAux_eq_drop vec target i (Nat.le_of_lt hi_lt)
      (fun k hk => hlt k (Nat.lt_succ_of_lt hk))]
    rw [List.drop_eq_getElem_cons hi_lt, SortedSetPt.binarySearchAux]
    have hcmp : Pt.cmp (vec[i]'hi_lt) target = .lt := by
      unfold Pt.cmp
      exact compare_lt_iff_lt.mpr (hlt i (Nat.lt_succ_self i))
    rw [hcmp]

theorem bsearchReplace_eq_replace (s : SortedSetPt) (element : Pt)
    (hsort : SortedSetPtStrictSorted s) (hne : s.vec ≠ []) :
    bsearchReplace s element = (s.replace element).1 ∧
      SortedSetPtStrictSorted (bsearchReplace s element) := by
  have hlen_ge1 : 1 ≤ s.vec.length := List.length_pos_iff.mpr hne
  let b := bsearchLoop s.vec element.x.value 0 s.vec.length
  have ⟨_, hb_lt0⟩ := bsearchLoop_bounds s.vec element.x.value 0 s.vec.length hlen_ge1 (by omega)
  have hb_lt : b < s.vec.length := by omega
  have hb_get : s.vec[b]?.getD default = s.vec[b]'hb_lt := by
    rw [List.getElem?_eq_getElem hb_lt, Option.getD_some]
  have ⟨hL, hR⟩ := bsearchLoop_sorted_inv hsort element.x.value 0 s.vec.length hlen_ge1 (by omega)
    (Or.inl rfl) (fun k hk hge => by omega)
  have hlt_before : ∀ k (hk : k < b),
      (s.vec[k]'(Nat.lt_trans hk hb_lt)).x.value.toNat < element.x.value.toNat := by
    intro k hk
    rcases hL with hb0 | hle_b
    · omega
    · rw [hb_get] at hle_b
      have hkb := ptListStrictSorted_getElem_lt hsort (Nat.lt_trans hk hb_lt) hb_lt hk
      omega
  have hbs_drop := binarySearchAux_eq_drop s.vec element b (Nat.le_of_lt hb_lt) hlt_before
  unfold bsearchReplace SortedSetPt.replace SortedSetPt.binarySearch
  change (if (s.vec[b]?.getD default).x.value == element.x.value then
      ({ vec := s.vec.set b element } : SortedSetPt)
    else
      let insertIdx := if (s.vec[b]?.getD default).x.value.toNat < element.x.value.toNat then b + 1 else b
      { vec := s.vec.take insertIdx ++ (element :: s.vec.drop insertIdx) }) = _ ∧
    SortedSetPtStrictSorted (if (s.vec[b]?.getD default).x.value == element.x.value then
      ({ vec := s.vec.set b element } : SortedSetPt)
    else
      let insertIdx := if (s.vec[b]?.getD default).x.value.toNat < element.x.value.toNat then b + 1 else b
      { vec := s.vec.take insertIdx ++ (element :: s.vec.drop insertIdx) })
  rw [hb_get, hbs_drop, List.drop_eq_getElem_cons hb_lt, SortedSetPt.binarySearchAux]
  by_cases heq : (s.vec[b]'hb_lt).x.value == element.x.value
  · have hnat_eq : (s.vec[b]'hb_lt).x.value.toNat = element.x.value.toNat := by
      rw [beq_iff_eq] at heq
      rw [heq]
    have hcmp : Pt.cmp (s.vec[b]'hb_lt) element = .eq := by
      unfold Pt.cmp
      exact compare_eq_iff_eq.mpr hnat_eq
    simp only [heq, ↓reduceIte, hcmp, true_and]
    unfold SortedSetPtStrictSorted PtListStrictSorted
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [List.length_set] at hi hj
    have hget_x : ∀ k (hk : k < s.vec.length),
        ((s.vec.set b element)[k]'(by rw [List.length_set]; exact hk)).x.value.toNat =
          (s.vec[k]'hk).x.value.toNat := by
      intro k hk
      rw [List.getElem_set]
      split_ifs with hbk
      · subst hbk; exact hnat_eq.symm
      · rfl
    rw [hget_x i hi, hget_x j hj]
    exact ptListStrictSorted_getElem_lt hsort hi hj hij
  · simp only [heq, Bool.false_eq_true, ↓reduceIte]
    have hnat_ne : (s.vec[b]'hb_lt).x.value.toNat ≠ element.x.value.toNat := by
      intro h
      exact heq (beq_iff_eq.mpr (BitVec.eq_of_toNat_eq h))
    have hsort_insert : ∀ (idx : Nat) (hidx : idx ≤ s.vec.length),
        (∀ k (hk : k < idx), (s.vec[k]'(Nat.lt_of_lt_of_le hk hidx)).x.value.toNat < element.x.value.toNat) →
        (∀ k (hk : k < s.vec.length), idx ≤ k → element.x.value.toNat < (s.vec[k]'hk).x.value.toNat) →
        SortedSetPtStrictSorted { vec := s.vec.take idx ++ (element :: s.vec.drop idx) } := by
      intro idx hidx hpre hsuf
      unfold SortedSetPtStrictSorted PtListStrictSorted
      rw [List.pairwise_append]
      refine ⟨hsort.take, List.pairwise_cons.mpr ⟨?_, hsort.drop⟩, ?_⟩
      · intro a ha
        rcases List.getElem_of_mem ha with ⟨k, hk, rfl⟩
        rw [List.getElem_drop]
        have hk_len : idx + k < s.vec.length := by
          rw [List.length_drop] at hk; omega
        exact hsuf (idx + k) hk_len (by omega)
      · intro a ha c hc
        rcases List.getElem_of_mem ha with ⟨k, hk, rfl⟩
        rw [List.getElem_take]
        have hk_idx : k < idx := by
          rw [List.length_take] at hk; omega
        have h1 := hpre k hk_idx
        rcases List.mem_cons.mp hc with rfl | hc_drop
        · exact h1
        · rcases List.getElem_of_mem hc_drop with ⟨m, hm, rfl⟩
          rw [List.getElem_drop]
          have hm_len : idx + m < s.vec.length := by
            rw [List.length_drop] at hm; omega
          have h2 := hsuf (idx + m) hm_len (by omega)
          omega
    by_cases hlt : (s.vec[b]'hb_lt).x.value.toNat < element.x.value.toNat
    · have hcmp : Pt.cmp (s.vec[b]'hb_lt) element = .lt := by
        unfold Pt.cmp
        exact compare_lt_iff_lt.mpr hlt
      have hbs_b1 : SortedSetPt.binarySearchAux element (b + 1) (s.vec.drop (b + 1)) = .error (b + 1) := by
        by_cases hb1 : b + 1 < s.vec.length
        · rw [List.drop_eq_getElem_cons hb1, SortedSetPt.binarySearchAux]
          have hgt1 : Pt.cmp (s.vec[b + 1]'hb1) element = .gt := by
            unfold Pt.cmp
            exact compare_gt_iff_gt.mpr (hR (b + 1) hb1 (Nat.le_refl _))
          rw [hgt1]
        · have hdrop_nil : s.vec.drop (b + 1) = [] := List.drop_eq_nil_of_le (by omega)
          rw [hdrop_nil, SortedSetPt.binarySearchAux]
      simp only [hlt, ↓reduceIte, hcmp, hbs_b1, true_and]
      refine hsort_insert (b + 1) (by omega) ?_ hR
      intro k hk
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hkb
      · exact hlt
      · exact hlt_before k hkb
    · have hgt : element.x.value.toNat < (s.vec[b]'hb_lt).x.value.toNat := by omega
      have hcmp : Pt.cmp (s.vec[b]'hb_lt) element = .gt := by
        unfold Pt.cmp
        exact compare_gt_iff_gt.mpr hgt
      simp only [hlt, ↓reduceIte, hcmp, true_and]
      refine hsort_insert b (by omega) hlt_before ?_
      intro k hk hbk
      rcases Nat.eq_or_lt_of_le hbk with rfl | hlt_k
      · exact hgt
      · exact hR k hk hlt_k

theorem bsearchPush_eq_push (s : SortedSetPt) (element : Pt) (hsort : SortedSetPtStrictSorted s) :
    bsearchPush s element = (s.push element).1 ∧
      SortedSetPtStrictSorted (bsearchPush s element) := by
  unfold bsearchPush SortedSetPt.push
  cases hlast : s.vec.getLast? with
  | none =>
    dsimp only
    exact ⟨rfl, List.pairwise_singleton _ _⟩
  | some last =>
    have hne : s.vec ≠ [] := fun h => by simp [h] at hlast
    have hpos : 0 < s.vec.length := List.length_pos_iff.mpr hne
    have hlast_lt : s.vec.length - 1 < s.vec.length := by omega
    have hlast_eq : last = s.vec[s.vec.length - 1]'hlast_lt := by
      rw [List.getLast?_eq_getElem?] at hlast
      rw [List.getElem?_eq_getElem hlast_lt] at hlast
      exact (Option.some.inj hlast).symm
    dsimp only
    cases hcmp : Pt.cmp element last with
    | gt =>
      dsimp only
      refine ⟨rfl, ?_⟩
      unfold SortedSetPtStrictSorted PtListStrictSorted
      rw [List.pairwise_append]
      refine ⟨hsort, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      rw [List.mem_singleton] at hc
      subst c
      rcases List.getElem_of_mem ha with ⟨k, hk, rfl⟩
      have hgt : last.x.value.toNat < element.x.value.toNat := by
        unfold Pt.cmp at hcmp
        exact compare_gt_iff_gt.mp hcmp
      rw [hlast_eq] at hgt
      have hle := ptListStrictSorted_getElem_le hsort hk hlast_lt (by omega)
      omega
    | eq =>
      dsimp only
      refine ⟨rfl, ?_⟩
      have heq_x : element.x.value.toNat = last.x.value.toNat := by
        unfold Pt.cmp at hcmp
        exact compare_eq_iff_eq.mp hcmp
      rw [hlast_eq] at heq_x
      have hdrop : s.vec.dropLast = s.vec.take (s.vec.length - 1) := List.dropLast_eq_take
      unfold SortedSetPtStrictSorted PtListStrictSorted
      rw [hdrop, List.pairwise_append]
      refine ⟨hsort.take, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      rw [List.mem_singleton] at hc
      subst c
      rcases List.getElem_of_mem ha with ⟨k, hk, rfl⟩
      rw [List.getElem_take]
      have hk_lt : k < s.vec.length - 1 := by
        rw [List.length_take] at hk; omega
      have hlt := ptListStrictSorted_getElem_lt hsort (by omega) hlast_lt hk_lt
      omega
    | lt =>
      dsimp only
      exact bsearchReplace_eq_replace s element hsort hne

theorem addChunkBsearchLoop_eq_total (chunk : Chunk) :
    ∀ (rem i : Nat) (self : PolyDecoder),
      self.pts.length = 16 →
      PolyDecoderStrictSorted self →
      addChunkBsearchLoop chunk i rem self = addChunkLoopTotal chunk i rem self ∧
        PolyDecoderStrictSorted (addChunkLoopTotal chunk i rem self)
  | 0, _, self, _, hsort => ⟨rfl, hsort⟩
  | rem + 1, i, self, hlen, hsort => by
    let totalIdx := chunk.index.toNat * 16 + i
    let poly := totalIdx % 16
    have hpoly_lt : poly < self.pts.length := by
      rw [hlen]; exact Nat.mod_lt _ (by decide)
    have hget : self.pts[poly]? = some (self.pts[poly]'hpoly_lt) :=
      List.getElem?_eq_getElem hpoly_lt
    let polyPts := self.pts[poly]'hpoly_lt
    have hsort_poly : SortedSetPtStrictSorted polyPts :=
      hsort polyPts (List.getElem_mem hpoly_lt)
    let polyIdx := totalIdx / 16
    let x := GF16.new (BitVec.ofNat 16 polyIdx)
    let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
    let nec := self.necessaryPoints i
    have ⟨hpush_eq, hpush_sort⟩ := bsearchPush_eq_push polyPts { x := x, y := y } hsort_poly
    unfold addChunkBsearchLoop addChunkLoopTotal
    dsimp only
    rw [hget, Option.getD_some, hpush_eq]
    let self' :=
      if polyIdx < nec || polyPts.len < nec then
        let (polyPts', _, _) := polyPts.push { x := x, y := y }
        { self with pts := self.pts.set poly polyPts' }
      else
        self
    have hlen' : self'.pts.length = 16 := by
      dsimp only [self']; split <;> simp [hlen]
    have hsort' : PolyDecoderStrictSorted self' := by
      dsimp only [self']
      split
      · intro s hs
        rcases List.mem_or_eq_of_mem_set hs with hmem | rfl
        · exact hsort s hmem
        · rw [← hpush_eq]; exact hpush_sort
      · exact hsort
    exact addChunkBsearchLoop_eq_total chunk rem (i + 1) self' hlen' hsort'

/-- When `self.pts.length = 16` and `PolyDecoderStrictSorted self`, the hardware binary-search
    result `addChunkBsearch self chunk` equals `addChunkTotal self chunk` and preserves
    `PolyDecoderStrictSorted`. -/
theorem addChunkBsearch_eq_addChunkTotal (self : PolyDecoder) (chunk : Chunk)
    (hlen : self.pts.length = 16) (hsort : PolyDecoderStrictSorted self) :
    addChunkBsearch self chunk = addChunkTotal self chunk ∧
      PolyDecoderStrictSorted (addChunkTotal self chunk) :=
  addChunkBsearchLoop_eq_total chunk 16 0 self hlen hsort

/-! ## Separation-Logic Helpers for `ptSliceAt`, `sortedSetPtListOf`, and `chunkAt` -/

/-- Little-endian 4-byte encoding of a `Pt` in memory (`x` at `+0..+2`, `y` at `+2..+4`). -/
def ptLeBytes (pt : Pt) : List (BitVec 8) :=
  [pt.x.value.extractLsb' 0 8, pt.x.value.extractLsb' 8 8,
   pt.y.value.extractLsb' 0 8, pt.y.value.extractLsb' 8 8]

/-- Little-endian byte list of a `List Pt` in memory. -/
def ptListBytes (pts : List Pt) : List (BitVec 8) :=
  pts.flatMap ptLeBytes

@[simp] theorem ptLeBytes_length (pt : Pt) : (ptLeBytes pt).length = 4 := rfl

@[simp] theorem ptListBytes_length :
    ∀ (pts : List Pt), (ptListBytes pts).length = 4 * pts.length
  | [] => rfl
  | pt :: pts => by
    change (ptLeBytes pt ++ ptListBytes pts).length = 4 * (pts.length + 1)
    rw [List.length_append, ptListBytes_length pts, ptLeBytes_length]
    omega

theorem ptAt_eq_pointsToBytes (pt : Pt) (a : BitVec 64) :
    ptAt pt a = (a ↦ₛ ptLeBytes pt) := by
  unfold ptAt ptLeBytes
  rw [pointsTo16_split8 a pt.x.value, pointsTo16_split8 (a + 2#64) pt.y.value]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have h3 : a + 1#64 + 1#64 + 1#64 = a + 2#64 + 1#64 := by bv_omega
  rw [h3, h2, sepConj_assoc]

theorem ptSliceAt_eq_pointsToBytes :
    ∀ (pts : List Pt) (ptr : BitVec 64),
      ptSliceAt ptr pts = (ptr ↦ₛ ptListBytes pts)
  | [], ptr => by
    simp [ptSliceAt, arrayAt, ptListBytes, pointsToBytes_nil]
  | pt :: pts, ptr => by
    change ptAt pt ptr ∗ ptSliceAt (ptr + 4#64) pts =
      (ptr ↦ₛ (ptLeBytes pt ++ ptListBytes pts))
    rw [pointsToBytes_append, ptAt_eq_pointsToBytes, ptSliceAt_eq_pointsToBytes pts (ptr + 4#64)]
    rfl

theorem ptSliceAt_append :
    ∀ (xs ys : List Pt) (ptr : BitVec 64),
      ptSliceAt ptr (xs ++ ys) =
        ptSliceAt ptr xs ∗ ptSliceAt (ptr + BitVec.ofNat 64 (4 * xs.length)) ys
  | [], ys, ptr => by
    simp [ptSliceAt, arrayAt]
  | x :: xs, ys, ptr => by
    change ptAt x ptr ∗ ptSliceAt (ptr + 4#64) (xs ++ ys) =
      (ptAt x ptr ∗ ptSliceAt (ptr + 4#64) xs) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (xs.length + 1))) ys
    rw [ptSliceAt_append xs ys (ptr + 4#64), ← sepConj_assoc]
    have haddr : ptr + 4#64 + BitVec.ofNat 64 (4 * xs.length) =
        ptr + BitVec.ofNat 64 (4 * (xs.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    rw [haddr]

theorem ptSliceAt_append_singleton (pts : List Pt) (pt : Pt) (ptr : BitVec 64) :
    ptSliceAt ptr (pts ++ [pt]) =
      ptSliceAt ptr pts ∗ ptAt pt (ptr + BitVec.ofNat 64 (4 * pts.length)) := by
  rw [ptSliceAt_append]
  simp [ptSliceAt, arrayAt]

theorem ptSliceAt_split_take_drop (pts : List Pt) (i : Nat) (ptr : BitVec 64)
    (hi : i ≤ pts.length) :
    ptSliceAt ptr pts =
      ptSliceAt ptr (pts.take i) ∗ ptSliceAt (ptr + BitVec.ofNat 64 (4 * i)) (pts.drop i) := by
  conv_lhs => rw [← List.take_append_drop i pts]
  rw [ptSliceAt_append, List.length_take_of_le hi]

theorem ptSliceAt_focus (pts : List Pt) (i : Nat) (ptr : BitVec 64) (hi : i < pts.length) :
    ptSliceAt ptr pts =
      ptSliceAt ptr (pts.take i) ∗
        ptAt (pts[i]'hi) (ptr + BitVec.ofNat 64 (4 * i)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (i + 1))) (pts.drop (i + 1)) := by
  rw [ptSliceAt_split_take_drop pts i ptr (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi]
  change ptSliceAt ptr (pts.take i) ∗
    (ptAt (pts[i]'hi) (ptr + BitVec.ofNat 64 (4 * i)) ∗
      ptSliceAt (ptr + BitVec.ofNat 64 (4 * i) + 4#64) (pts.drop (i + 1))) = _
  have haddr : ptr + BitVec.ofNat 64 (4 * i) + 4#64 = ptr + BitVec.ofNat 64 (4 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [haddr, ← sepConj_assoc]

theorem ptSliceAt_set (pts : List Pt) (i : Nat) (pt : Pt) (ptr : BitVec 64) (hi : i < pts.length) :
    ptSliceAt ptr (pts.set i pt) =
      ptSliceAt ptr (pts.take i) ∗
        ptAt pt (ptr + BitVec.ofNat 64 (4 * i)) ∗
        ptSliceAt (ptr + BitVec.ofNat 64 (4 * (i + 1))) (pts.drop (i + 1)) := by
  have hi' : i < (pts.set i pt).length := by rw [List.length_set]; exact hi
  rw [ptSliceAt_focus (pts.set i pt) i ptr hi']
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

theorem sortedSetPtListOf_append (A : RustAlloc) :
    ∀ (xs ys : List SortedSetPt) (base : BitVec 64),
      sortedSetPtListOf A base (xs ++ ys) =
        sortedSetPtListOf A base xs ∗ sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * xs.length)) ys
  | [], ys, base => by
    simp [sortedSetPtListOf, arrayAt]
  | x :: xs, ys, base => by
    change sortedSetPtOf A base x ∗ sortedSetPtListOf A (base + 24#64) (xs ++ ys) =
      (sortedSetPtOf A base x ∗ sortedSetPtListOf A (base + 24#64) xs) ∗
        sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * (xs.length + 1))) ys
    rw [sortedSetPtListOf_append A xs ys (base + 24#64), ← sepConj_assoc]
    have haddr : base + 24#64 + BitVec.ofNat 64 (24 * xs.length) =
        base + BitVec.ofNat 64 (24 * (xs.length + 1)) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    rw [haddr]

theorem sortedSetPtListOf_split_take_drop (A : RustAlloc) (ss : List SortedSetPt) (i : Nat)
    (base : BitVec 64) (hi : i ≤ ss.length) :
    sortedSetPtListOf A base ss =
      sortedSetPtListOf A base (ss.take i) ∗
        sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * i)) (ss.drop i) := by
  conv_lhs => rw [← List.take_append_drop i ss]
  rw [sortedSetPtListOf_append, List.length_take_of_le hi]

theorem sortedSetPtListOf_focus (A : RustAlloc) (ss : List SortedSetPt) (i : Nat)
    (base : BitVec 64) (hi : i < ss.length) :
    sortedSetPtListOf A base ss =
      sortedSetPtListOf A base (ss.take i) ∗
        sortedSetPtOf A (base + BitVec.ofNat 64 (24 * i)) (ss[i]'hi) ∗
        sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (ss.drop (i + 1)) := by
  rw [sortedSetPtListOf_split_take_drop A ss i base (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi]
  change sortedSetPtListOf A base (ss.take i) ∗
    (sortedSetPtOf A (base + BitVec.ofNat 64 (24 * i)) (ss[i]'hi) ∗
      sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * i) + 24#64) (ss.drop (i + 1))) = _
  have haddr : base + BitVec.ofNat 64 (24 * i) + 24#64 = base + BitVec.ofNat 64 (24 * (i + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [haddr, ← sepConj_assoc]

theorem sortedSetPtListOf_set (A : RustAlloc) (ss : List SortedSetPt) (i : Nat) (s : SortedSetPt)
    (base : BitVec 64) (hi : i < ss.length) :
    sortedSetPtListOf A base (ss.set i s) =
      sortedSetPtListOf A base (ss.take i) ∗
        sortedSetPtOf A (base + BitVec.ofNat 64 (24 * i)) s ∗
        sortedSetPtListOf A (base + BitVec.ofNat 64 (24 * (i + 1))) (ss.drop (i + 1)) := by
  have hi' : i < (ss.set i s).length := by rw [List.length_set]; exact hi
  rw [sortedSetPtListOf_focus A (ss.set i s) i base hi']
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

/-- Pure `listMove` equation for shifting `4 * n` bytes right by `4` bytes inside `bs ++ slotBs`. -/
theorem listMove_insert_pt {bs slotBs : List (BitVec 8)} {n : Nat}
    (hbs : bs.length = 4 * n) (hslot : slotBs.length = 4) :
    listMove (bs ++ slotBs) 4 0 (4 * n) =
      (bs ++ slotBs).take 4 ++ bs := by
  unfold listMove
  simp only [List.drop_zero]
  have htake : (bs ++ slotBs).take (4 * n) = bs := by
    rw [← hbs, List.take_left]
  have hdrop : (bs ++ slotBs).drop (4 + 4 * n) = [] := by
    apply List.drop_eq_nil_of_le
    rw [List.length_append, hbs, hslot]
    omega
  rw [htake, hdrop, List.append_nil]

/-- Splits `memmove(x22 + 4, x22, 4 * suffix.length)` into a 4-byte writable slot at `x22` and `ptSliceAt (x22 + 4#64) suffix`. -/
theorem pointsToBytes_listMove_insert_pt (x22 : BitVec 64) (suffix : List Pt)
    {slotBs : List (BitVec 8)} (hslot : slotBs.length = 4) :
    (x22 ↦ₛ listMove (ptListBytes suffix ++ slotBs) 4 0 (4 * suffix.length)) ⊢
      (∃∗ v1 : BitVec 16, ∃∗ v0 : BitVec 16, (x22 ↦₁₆ v0) ∗ ((x22 + 2#64) ↦₁₆ v1)) ∗
        ptSliceAt (x22 + 4#64) suffix := by
  have hbs : (ptListBytes suffix).length = 4 * suffix.length := ptListBytes_length suffix
  rw [listMove_insert_pt hbs hslot, pointsToBytes_append, ptSliceAt_eq_pointsToBytes]
  have hlen4 : ((ptListBytes suffix ++ slotBs).take 4).length = 4 := by
    rw [List.length_take, List.length_append, hbs, hslot]
    omega
  rw [hlen4]
  apply sepConj_mono_left
  refine Entails.trans (pointsToBytes_entails_memRegion x22 ((ptListBytes suffix ++ slotBs).take 4)) ?_
  rw [hlen4, show (4 : Nat) = 2 + 2 from rfl, memRegion_split x22 2 2 (by decide),
    memRegion_two x22, memRegion_two (x22 + 2#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem pointsTo8_pair_eq_pointsTo16 (a : BitVec 64) (b0 b1 : BitVec 8) :
    ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1)) = (a ↦₁₆ (b1 ++ b0)) := by
  rw [pointsTo16_split8 a (b1 ++ b0)]
  have h0 : (b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have h1 : (b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  rw [h0, h1]

theorem chunk_data_focus16 (a : BitVec 64) (c : Chunk) (i : Nat) (hi : i < 16) :
    let y1 := c.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
    let y2 := c.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
    (a ↦ₛ c.data.toList) =
      (a ↦ₛ c.data.toList.take (i * 2)) ∗
        ((a + BitVec.ofNat 64 (i * 2)) ↦₁₆ (y2 ++ y1)) ∗
        ((a + BitVec.ofNat 64 (i * 2 + 2)) ↦ₛ c.data.toList.drop (i * 2 + 2)) := by
  dsimp only
  have hlen : c.data.toList.length = 32 := c.data.2
  have hi0 : i * 2 < c.data.toList.length := by omega
  have hi1 : i * 2 + 1 < c.data.toList.length := by omega
  have hmod0 : (i * 2) % 32 = i * 2 := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (i * 2 + 1) % 32 = i * 2 + 1 := Nat.mod_eq_of_lt (by omega)
  have hsplit : c.data.toList =
      c.data.toList.take (i * 2) ++
        (c.data.toList[i * 2]'hi0 :: c.data.toList[i * 2 + 1]'hi1 :: c.data.toList.drop (i * 2 + 2)) := by
    conv_lhs => rw [← List.take_append_drop (i * 2) c.data.toList]
    rw [List.drop_eq_getElem_cons hi0, List.drop_eq_getElem_cons hi1]
  conv_lhs => rw [hsplit]
  rw [pointsToBytes_append, List.length_take_of_le (by omega),
    pointsToBytes_cons, pointsToBytes_cons]
  have hpair :
      (((a + BitVec.ofNat 64 (i * 2)) ↦₈ c.data.toList[i * 2]) ∗
        (((a + BitVec.ofNat 64 (i * 2) + 1#64) ↦₈ c.data.toList[i * 2 + 1]) ∗
          ((a + BitVec.ofNat 64 (i * 2) + 1#64 + 1#64) ↦ₛ c.data.toList.drop (i * 2 + 2)))) =
      (((a + BitVec.ofNat 64 (i * 2)) ↦₁₆ (c.data.toList[i * 2 + 1] ++ c.data.toList[i * 2])) ∗
        ((a + BitVec.ofNat 64 (i * 2) + 1#64 + 1#64) ↦ₛ c.data.toList.drop (i * 2 + 2))) := by
    rw [← sepConj_assoc, pointsTo8_pair_eq_pointsTo16]
  rw [hpair]
  have haddr : a + BitVec.ofNat 64 (i * 2) + 1#64 + 1#64 = a + BitVec.ofNat 64 (i * 2 + 2) := by
    rw [BitVec.add_assoc, BitVec.add_assoc]
    change a + (BitVec.ofNat 64 (i * 2) + 2#64) = a + BitVec.ofNat 64 (i * 2 + 2)
    rw [← BitVec.ofNat_add]
  have hy1 : c.data.toList[i * 2]'hi0 = c.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩ := by
    simp only [List.Vector.toList, List.Vector.get, List.get_eq_getElem, Fin.val_cast, hmod0]
  have hy2 : c.data.toList[i * 2 + 1]'hi1 = c.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩ := by
    simp only [List.Vector.toList, List.Vector.get, List.get_eq_getElem, Fin.val_cast, hmod1]
  rw [haddr, hy1, hy2, ← sepConj_assoc]

theorem addChunk_poly_eq (c : Chunk) {i : Nat} (hi : i < 16) :
    (c.index.toNat * 16 + i) % 16 = i := by omega

theorem addChunk_polyIdx_eq (c : Chunk) {i : Nat} (hi : i < 16) :
    (c.index.toNat * 16 + i) / 16 = c.index.toNat := by omega

theorem addChunk_x_eq (c : Chunk) {i : Nat} (hi : i < 16) :
    GF16.new (BitVec.ofNat 16 ((c.index.toNat * 16 + i) / 16)) = GF16.new c.index := by
  rw [addChunk_polyIdx_eq c hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem bv64_madd24_ofNat (base : BitVec 64) {i : Nat} (hi : i < 16) :
    base + BitVec.ofNat 64 i * 24#64 = base + BitVec.ofNat 64 (24 * i) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  change (i * 24) % 2 ^ 64 = (BitVec.ofNat 64 (24 * i)).toNat
  rw [BitVec.toNat_ofNat, Nat.mul_comm i 24]

theorem bv64_lsl1_ofNat {i : Nat} (hi : i < 16) :
    (BitVec.ofNat 64 i) <<< 1 = BitVec.ofNat 64 (i * 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem bv64_lsr4_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem bv64_and15_ofNat {n : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n) &&& 15#64 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  have h15 : (15#64 : BitVec 64).toNat = 2 ^ 4 - 1 := rfl
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h15,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n % 16 < 2 ^ 64)]

theorem necessaryPoints_lt (dec : PolyDecoder) (i : Nat) (hneed : dec.ptsNeeded < 2 ^ 64) :
    dec.necessaryPoints i < 2 ^ 64 := by
  unfold PolyDecoder.necessaryPoints
  dsimp only [NUM_POLYS]
  split_ifs <;> omega

theorem cinc_necessaryPoints_eq (dec : PolyDecoder) {i : Nat} (hi : i < 16)
    (_hneed : dec.ptsNeeded < 2 ^ 64) :
    (if (BitVec.ofNat 64 (dec.ptsNeeded % 16)).ule (BitVec.ofNat 64 i) = true then
      BitVec.ofNat 64 (dec.ptsNeeded / 16)
    else BitVec.ofNat 64 (dec.ptsNeeded / 16 + 1)) =
      BitVec.ofNat 64 (dec.necessaryPoints i) := by
  have hule :
      (BitVec.ofNat 64 (dec.ptsNeeded % 16)).ule (BitVec.ofNat 64 i) =
        decide (dec.ptsNeeded % 16 ≤ i) := by
    simp only [BitVec.ule, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : dec.ptsNeeded % 16 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  rw [hule]
  unfold PolyDecoder.necessaryPoints
  dsimp only [NUM_POLYS]
  by_cases hlt : i < dec.ptsNeeded % 16
  · have hle : ¬ dec.ptsNeeded % 16 ≤ i := by omega
    simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte, hlt]
  · have hle : dec.ptsNeeded % 16 ≤ i := by omega
    simp only [hle, decide_true, ↓reduceIte, hlt]

theorem bv32_bne_zeroExtend16 (a b : BitVec 16) :
    (BitVec.zeroExtend 32 a != BitVec.zeroExtend 32 b) = (!(a == b)) := by
  bv_bits

theorem bv32_ule_zeroExtend16 (x y : BitVec 16) :
    (BitVec.zeroExtend 32 x).ule (BitVec.zeroExtend 32 y) = decide (x.toNat ≤ y.toNat) := by
  simp only [BitVec.ule, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 32)]

theorem cinc_insertIdx_eq (baseX xVal : BitVec 16) (base : Nat) :
    (if (BitVec.zeroExtend 32 xVal).ule (BitVec.zeroExtend 32 baseX) = true then
      BitVec.ofNat 64 base
    else BitVec.ofNat 64 (base + 1)) =
      BitVec.ofNat 64 (if baseX.toNat < xVal.toNat then base + 1 else base) := by
  rw [bv32_ule_zeroExtend16]
  by_cases hlt : baseX.toNat < xVal.toNat
  · have hle : ¬ xVal.toNat ≤ baseX.toNat := by omega
    simp only [hle, decide_false, Bool.false_eq_true, ↓reduceIte, hlt]
  · have hle : xVal.toNat ≤ baseX.toNat := by omega
    simp only [hle, decide_true, ↓reduceIte, hlt]

theorem bv64_beq_cap_ofNat {n : Nat} {cap : BitVec 64} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == cap) = decide (n = cap.toNat) := by
  by_cases h : n = cap.toNat
  · subst h
    simp only [decide_true, BitVec.ofNat_toNat, BitVec.setWidth_eq, beq_self_eq_true]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    apply h
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hto
    exact hto

theorem ptr_add_len_sub4 (ptr : BitVec 64) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 65536) :
    ptr + BitVec.ofNat 64 (4 * n) + 18446744073709551612#64 =
      ptr + BitVec.ofNat 64 (4 * (n - 1)) := by
  have h4 : BitVec.ofNat 64 (4 * n) = BitVec.ofNat 64 (4 * (n - 1)) + 4#64 := by
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1; omega
  rw [h4]; bv_omega

theorem ptr_add_len_sub2 (ptr : BitVec 64) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 65536) :
    ptr + BitVec.ofNat 64 (4 * n) + 18446744073709551614#64 =
      ptr + BitVec.ofNat 64 (4 * (n - 1)) + 2#64 := by
  have h4 : BitVec.ofNat 64 (4 * n) = BitVec.ofNat 64 (4 * (n - 1)) + 4#64 := by
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1; omega
  rw [h4]; bv_omega

theorem bv64_ne_zero_of_pos {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 65536) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have hto := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
  change n = 0 at hto; omega

theorem dropLast_append_singleton_eq_set {α : Type*} (l : List α) (x : α)
    (h : 0 < l.length) :
    l.dropLast ++ [x] = l.set (l.length - 1) x := by
  have hlt : l.length - 1 < l.length := by omega
  have hdrop : l.drop (l.length - 1 + 1) = [] := by
    rw [Nat.sub_add_cancel h, List.drop_length]
  rw [List.dropLast_eq_take, List.set_eq_take_append_cons_drop]
  simp only [hlt, ↓reduceIte, hdrop]

theorem bv64_ule_succ {n : Nat} (hn : n + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 n).ule (BitVec.ofNat 64 (n + 1)) = true := by
  simp only [BitVec.ule, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64),
    Nat.mod_eq_of_lt hn, decide_eq_true_eq]
  omega

theorem addChunk_skip_cond_eq (idx : BitVec 16) {nec len : Nat}
    (hnec : nec < 2 ^ 64) (hlen : len < 2 ^ 64) :
    (if (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 idx) = true then
      (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 len)
    else false) = !(decide (idx.toNat < nec) || decide (len < nec)) := by
  have h1 : (BitVec.ofNat 64 nec).ule (BitVec.zeroExtend 64 idx) = decide (nec ≤ idx.toNat) := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnec,
      BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : idx.toNat < 2 ^ 64)]
  have h2 : (BitVec.ofNat 64 nec).ule (BitVec.ofNat 64 len) = decide (nec ≤ len) := by
    simp only [BitVec.ule, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnec, Nat.mod_eq_of_lt hlen]
  rw [h1, h2]
  by_cases ha : idx.toNat < nec <;> by_cases hb : len < nec
  · have hna : ¬ nec ≤ idx.toNat := by omega
    simp [ha, hb, hna]
  · have hna : ¬ nec ≤ idx.toNat := by omega
    simp [ha, hb, hna]
  · have hna : nec ≤ idx.toNat := by omega
    have hnb : ¬ nec ≤ len := by omega
    simp [ha, hb, hna, hnb]
  · have hna : nec ≤ idx.toNat := by omega
    have hnb : nec ≤ len := by omega
    simp [ha, hb, hna, hnb]

theorem bv64_add1_beq16 {i : Nat} (hi : i < 16) :
    (BitVec.ofNat 64 (i + 1) == 16#64) = decide (i + 1 = 16) := by
  by_cases h : i + 1 = 16
  · rw [h]; rfl
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro heq
    apply h
    have hto := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hto
    exact hto

theorem sortedSetPtOf_expose (A : RustAlloc) (v : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A v s ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr s.vec ∗
           memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader vecBuf ptStride ptAlign
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  change (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ∗
      (⌜s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr s.vec ∗
           memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)))) ⊢ _
  exact Entails.of_eq (by ac_rfl)

theorem sortedSetPtOf_eq_len_sep (A : RustAlloc) (v : BitVec 64) (s : SortedSetPt) :
    sortedSetPtOf A v s =
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr)) ∗
        (⌜s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
          (if cap = 0#64 then emp
           else A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr s.vec ∗
             memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)))) := by
  unfold sortedSetPtOf vecOf vecAt vecHeader vecBuf ptStride ptAlign
  simp only [sepExists_sepConj_right]
  congr; funext cap; congr; funext ptr
  change (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length)) ∗
      (⌜s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr s.vec ∗
           memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4)))) =
    ((v + 16#64) ↦₆₄ BitVec.ofNat 64 s.vec.length) ∗ (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr)) ∗
      (⌜s.vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (if cap = 0#64 then emp
         else A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr s.vec ∗
           memRegion (ptr + BitVec.ofNat 64 (s.vec.length * 4)) ((cap.toNat - s.vec.length) * 4))))
  ac_rfl

theorem sortedSetPtOf_intro_nonempty (A : RustAlloc) (v cap ptr : BitVec 64) (vec : List Pt)
    (hle : vec.length ≤ cap.toNat) (hcap : cap.toNat * 4 < 2 ^ 63)
    (hptr : ptr ≠ 0#64) (hcap_ne : cap ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
      A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
      memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) ⊢
      sortedSetPtOf A v { vec := vec } := by
  unfold sortedSetPtOf vecOf vecAt vecHeader vecBuf ptStride ptAlign
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  have hcap0 : (cap = 0) ↔ False := ⟨hcap_ne, False.elim⟩
  simp only [hcap0, ↓reduceIte]
  rw [show ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length)) ∗
      (⌜vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (A.live ptr (cap.toNat * 4) 2 ∗ arrayAt ptAt 4 ptr vec ∗
          memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4))) =
      ⌜vec.length ≤ cap.toNat ∧ cap.toNat * 4 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 vec.length) ∗
        A.live ptr (cap.toNat * 4) 2 ∗ ptSliceAt ptr vec ∗
        memRegion (ptr + BitVec.ofNat 64 (vec.length * 4)) ((cap.toNat - vec.length) * 4)) by
    change _ = ⌜_⌝ ∗ (_ ∗ _ ∗ _ ∗ _ ∗ arrayAt ptAt 4 ptr vec ∗ _)
    ac_rfl]
  exact Entails.pure_right ⟨hle, hcap, hptr⟩ (Entails.refl _)

theorem memRegion_spare_split_one (ptr : BitVec 64) {len cap : Nat}
    (hlt : len < cap) (hcap : cap * 4 < 2 ^ 63) :
    memRegion (ptr + BitVec.ofNat 64 (len * 4)) ((cap - len) * 4) =
      (∃∗ v1 : BitVec 16, ∃∗ v0 : BitVec 16,
        ((ptr + BitVec.ofNat 64 (4 * len)) ↦₁₆ v0) ∗
        ((ptr + BitVec.ofNat 64 (4 * len) + 2#64) ↦₁₆ v1)) ∗
      memRegion (ptr + BitVec.ofNat 64 ((len + 1) * 4)) ((cap - (len + 1)) * 4) := by
  have hmul : (cap - len) * 4 = 4 + (cap - (len + 1)) * 4 := by omega
  have hcomm : len * 4 = 4 * len := Nat.mul_comm len 4
  have hadd4 : ptr + BitVec.ofNat 64 (4 * len) + 4#64 = ptr + BitVec.ofNat 64 ((len + 1) * 4) := by
    rw [BitVec.add_assoc, show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 2; omega
  have h4 : ∀ a : BitVec 64, memRegion a 4 =
      (∃∗ v1 : BitVec 16, ∃∗ v0 : BitVec 16, (a ↦₁₆ v0) ∗ ((a + 2#64) ↦₁₆ v1)) := by
    intro a
    rw [show (4 : Nat) = 2 + 2 from rfl,
      memRegion_split a 2 2 (by decide),
      ProofLib.memRegion_two, ProofLib.memRegion_two]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  rw [hcomm, hmul, memRegion_split (ptr + BitVec.ofNat 64 (4 * len)) 4 ((cap - (len + 1)) * 4) (by omega),
    hadd4, h4 (ptr + BitVec.ofNat 64 (4 * len))]

/-- Single iteration `i` of `addChunkBsearchLoop`. -/
def addChunkBsearchStep (chunk : Chunk) (i : Nat) (self : PolyDecoder) : PolyDecoder :=
  let totalIdx := chunk.index.toNat * 16 + i
  let poly := totalIdx % 16
  let polyIdx := totalIdx / 16
  let x := GF16.new (BitVec.ofNat 16 polyIdx)
  let y1 := chunk.data.get ⟨(i * 2) % 32, Nat.mod_lt _ (by decide)⟩
  let y2 := chunk.data.get ⟨(i * 2 + 1) % 32, Nat.mod_lt _ (by decide)⟩
  let y := GF16.new ((y1.zeroExtend 16 <<< 8) + y2.zeroExtend 16)
  let polyPts := self.pts[poly]?.getD SortedSetPt.new
  let nec := self.necessaryPoints i
  if polyIdx < nec || polyPts.len < nec then
    let polyPts' := bsearchPush polyPts { x := x, y := y }
    { self with pts := self.pts.set poly polyPts' }
  else
    self

@[simp] theorem addChunkBsearchStep_pts_length (chunk : Chunk) (i : Nat) (self : PolyDecoder) :
    (addChunkBsearchStep chunk i self).pts.length = self.pts.length := by
  unfold addChunkBsearchStep; dsimp only; split <;> simp

@[simp] theorem addChunkBsearchStep_ptsNeeded (chunk : Chunk) (i : Nat) (self : PolyDecoder) :
    (addChunkBsearchStep chunk i self).ptsNeeded = self.ptsNeeded := by
  unfold addChunkBsearchStep; dsimp only; split <;> rfl

@[simp] theorem addChunkBsearchStep_isComplete (chunk : Chunk) (i : Nat) (self : PolyDecoder) :
    (addChunkBsearchStep chunk i self).isComplete = self.isComplete := by
  unfold addChunkBsearchStep; dsimp only; split <;> rfl

theorem addChunkBsearchStep_getElem_after (chunk : Chunk) {i j : Nat} (self : PolyDecoder)
    (hi : i < 16) (hij : i < j) (hj : j < self.pts.length) :
    (addChunkBsearchStep chunk i self).pts[j]'(by rw [addChunkBsearchStep_pts_length]; exact hj) =
      self.pts[j]'hj := by
  unfold addChunkBsearchStep
  dsimp only
  split
  · rw [List.getElem_set_ne]
    rw [addChunk_poly_eq chunk hi]
    omega
  · rfl

/-! ## Specifications of `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`) -/

/-- Ghost arguments of `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`). -/
structure AddChunkGhost where
  /-- Pointer to `self : &mut PolyDecoder` (`x0`, 400 bytes). -/
  decA : BitVec 64
  /-- Pointer to `chunk : &Chunk` (`x1`, 34 bytes). -/
  chunkA : BitVec 64
  /-- Logical `PolyDecoder` value at `decA`. -/
  dec : PolyDecoder
  /-- Logical `Chunk` value at `chunkA`. -/
  chunk : Chunk

/-- Hardware specification of `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`, 129 instructions)
    without requiring `PolyDecoderStrictSorted` in the precondition (outputs `addChunkBsearch`). -/
def addChunkBsearchSpec (A : RustAlloc) : Spec AddChunkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      (∀ s ∈ x.dec.pts, s.vec.length ≤ 65536)⌝ ∗
      polyDecoderAt A x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s.sp addChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      polyDecoderAt A x.decA (addChunkBsearch x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s0.sp addChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Specification of `<PolyDecoder as Decoder>::add_chunk` (`0x6c420`, 129 instructions) on a
    strictly sorted `PolyDecoder` (`PolyDecoderStrictSorted x.dec`), outputting
    `addChunkTotal x.dec x.chunk` (`PolyDecoder.addChunk x.dec x.chunk = .ok (addChunkTotal x.dec x.chunk)`)
    and preserving `PolyDecoderStrictSorted`. -/
def addChunkSpec (A : RustAlloc) : Spec AddChunkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      PolyDecoderStrictSorted x.dec⌝ ∗
      polyDecoderAt A x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s.sp addChunkStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ PolyDecoderStrictSorted (addChunkTotal x.dec x.chunk)⌝ ∗
      polyDecoderAt A x.decA (addChunkTotal x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s0.sp addChunkStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Extended-stack variant of `addChunkSpec` (`addChunkStackX = 96 + extHookStack`). -/
def addChunkSpecX (A : RustAlloc) : Spec AddChunkGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.decA ∧ s.readReg64 .x1 = x.chunkA ∧
      PolyDecoderStrictSorted x.dec⌝ ∗
      polyDecoderAt A x.decA x.dec ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s.sp addChunkStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ PolyDecoderStrictSorted (addChunkTotal x.dec x.chunk)⌝ ∗
      polyDecoderAt A x.decA (addChunkTotal x.dec x.chunk) ∗
      chunkAt x.chunkA x.chunk ∗
      A.pool ∗ stackAt s0.sp addChunkStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def AddChunkOkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr addChunkName)
    (addChunkSpec A)

def AddChunkOkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr addChunkName)
    ((addChunkSpecX A).inImage img)

def AddChunkPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
    (blkPl_419).base
    (addChunkSpec A)

def AddChunkPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_419).rebase (blkPl_419).base (Rust.withPanics ext))
    (blkPl_419).base
    (addChunkSpecX A)

def addChunkOnPanic (s0 sf : State) : SepProp :=
  ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  unfold allocFailedIn at *
  rwa [htr] at h

end CryptoVerification.SpqrV1.Poly.AddChunk
