/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.ImageData
import ProofLib.SepLogic.Model

/-!
# Per-Byte View of Image Data Segments After a Run

Converses to `ProofLib.SepLogic.ImageData` relating whole-segment assertions (`imageDataBss`,
`imageInitialDataBss`) to per-byte `byteCells` slices, and read-only duplication lemmas
(`imageDataBss_dup_pointsTo8RO`, `imageDataBss_dup_pointsToBytesRO`,
`imageDataBss_dup_pointsTo64RO`, and initial-segment counterparts) that frame out `↦ᵣ` atoms
without splitting the segment assertion.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib

open Arm64

/-! ## Heap-Level Characterization -/

section HeapLevel

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union
  regionHeap

private theorem toNat_sub_eq_succ' {x a : BitVec 64} (h : x ≠ a) :
    (x - a).toNat = (x - (a + 1#64)).toNat + 1 := by
  bv_omega

private theorem getElem_cons_of_sub' {x a : BitVec 64} (h : x ≠ a) (v : BitVec 8)
    (vs : List (BitVec 8)) (hi : (x - a).toNat < (v :: vs).length)
    (hi' : (x - (a + 1#64)).toNat < vs.length) :
    (v :: vs)[(x - a).toNat] = vs[(x - (a + 1#64)).toNat] := by
  simp only [toNat_sub_eq_succ' h, List.getElem_cons_succ]

private theorem byteCells_phys' {C : BitVec 64 → BitVec 8 → SepProp}
    {R : BitVec 64 → BitVec 8 → HeapCell → Prop}
    (hC : ∀ a v h, (C a v).holds h →
      ∃ c, R a v c ∧ h = { phys := fun x => if x = a then some c else none }) :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap), (byteCells C a bs).holds h →
      h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
      ∀ x, if hx : (x - a).toNat < bs.length then
             ∃ c, R x bs[(x - a).toNat] c ∧ h.phys x = some c
           else h.phys x = none := by
  intro bs
  induction bs with
  | nil =>
    intro a h hh
    have e : h = Heap.empty := SepProp.holds_emp_iff.mp hh
    subst e
    exact ⟨rfl, rfl, rfl, fun x => by simp [Heap.empty]⟩
  | cons v vs ih =>
    intro a h hh
    obtain ⟨h1, h2, _, rfl, hh1, hh2⟩ := SepProp.holds_sepConj_iff.mp hh
    obtain ⟨c, hR, rfl⟩ := hC a v h1 hh1
    obtain ⟨ha2, hf2, hm2, hp2⟩ := ih (a + 1#64) h2 hh2
    refine ⟨?_, ?_, ?_, fun x => ?_⟩
    · funext γ k; simp [Heap.union, ha2]
    · funext γ k; simp [Heap.union, hf2]
    · funext x; simp [Heap.union, hm2]
    · by_cases hxa : x = a
      · subst hxa
        rw [dite_eq_left (by simp)]
        refine ⟨c, ?_, by simp [Heap.union]⟩
        simpa using hR
      · have hux : (Heap.union { phys := fun y => if y = a then some c else none } h2).phys x =
            h2.phys x := by simp [Heap.union, hxa]
        rw [hux]
        have hs := toNat_sub_eq_succ' hxa
        have h2x := hp2 x
        by_cases hlt : (x - (a + 1#64)).toNat < vs.length
        · have hlt' : (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_left hlt] at h2x
          rw [dite_eq_left hlt', getElem_cons_of_sub' hxa v vs hlt' hlt]
          exact h2x
        · have hlt' : ¬ (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_right hlt] at h2x
          rw [dite_eq_right hlt']
          exact h2x

private theorem byteCells_of_phys' {C : BitVec 64 → BitVec 8 → SepProp}
    {R : BitVec 64 → BitVec 8 → HeapCell → Prop}
    (hC : ∀ a v c, R a v c → (C a v).holds { phys := fun x => if x = a then some c else none }) :
    ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap), bs.length ≤ 2 ^ 64 →
      h.auth = (fun _ _ => none) → h.frag = (fun _ _ => none) → h.mapped = (fun _ => false) →
      (∀ x, if hx : (x - a).toNat < bs.length then
             ∃ c, R x bs[(x - a).toNat] c ∧ h.phys x = some c
           else h.phys x = none) →
      (byteCells C a bs).holds h := by
  intro bs
  induction bs with
  | nil =>
    intro a h _ ha hf hm hp
    rw [byteCells_nil, SepProp.holds_emp_iff]
    apply Heap.ext
    · funext x
      have := hp x
      simpa [Heap.empty] using this
    · exact ha
    · exact hf
    · exact hm
  | cons v vs ih =>
    intro a h hlen ha hf hm hp
    have h0 := hp a
    rw [dite_eq_left (by simp)] at h0
    obtain ⟨c, hR, hpa⟩ := h0
    simp only [BitVec.sub_self, BitVec.toNat_zero, List.getElem_cons_zero] at hR
    rw [byteCells_cons, SepProp.holds_sepConj_iff]
    refine ⟨{ phys := fun x => if x = a then some c else none },
      { phys := fun x => if x = a then none else h.phys x }, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun x => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun _ => Or.inl rfl⟩
      · by_cases hx : x = a
        · exact Or.inr (Or.inl (by simp [hx]))
        · exact Or.inl (by simp [hx])
      · intro γ k oa w hh
        simp at hh
    · apply Heap.ext
      · funext x
        by_cases hx : x = a
        · subst hx; simp [Heap.union, hpa]
        · simp [Heap.union, hx]
      · funext γ k; simp [Heap.union, ha]
      · funext γ k; simp [Heap.union, hf]
      · funext x; simp [Heap.union, hm]
    · exact hC a v c hR
    · refine ih (a + 1#64) _ (by simp at hlen; omega) rfl rfl rfl fun x => ?_
      by_cases hxa : x = a
      · subst hxa
        have hne : ¬ (x - (x + 1#64)).toNat < vs.length := by
          have e : (x - (x + 1#64)).toNat = 2 ^ 64 - 1 := by bv_omega
          simp at hlen; omega
        rw [dite_eq_right hne]
        simp
      · have hs := toNat_sub_eq_succ' hxa
        have hx := hp x
        simp only [hxa, ↓reduceIte]
        by_cases hlt : (x - (a + 1#64)).toNat < vs.length
        · have hlt' : (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_left hlt', getElem_cons_of_sub' hxa v vs hlt' hlt] at hx
          rw [dite_eq_left hlt]
          exact hx
        · have hlt' : ¬ (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_right hlt'] at hx
          rw [dite_eq_right hlt]
          exact hx

private theorem dataCell_holds_eq (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8)
    (h : Heap) (hh : (dataCell isRo a v).holds h) :
    ∃ c, c = (if isRo a then HeapCell.ro v else HeapCell.rw v) ∧
      h = { phys := fun x => if x = a then some c else none } := by
  refine ⟨_, rfl, ?_⟩
  cases hro : isRo a <;> simp only [dataCell, hro, Bool.false_eq_true, ↓reduceIte] at hh ⊢
  · exact holds_pointsTo8_iff.mp hh
  · exact holds_pointsTo8RO_iff.mp hh

private theorem dataCellAny_holds_of (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8)
    (c : HeapCell) (hc : if isRo a then c = .ro v else ∃ v', c = .rw v') :
    (dataCellAny isRo a v).holds { phys := fun x => if x = a then some c else none } := by
  cases hro : isRo a <;> simp only [hro, Bool.false_eq_true, ↓reduceIte] at hc <;>
    simp only [dataCellAny, hro, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨v', rfl⟩ := hc
    exact SepProp.holds_sepExists_iff.mpr ⟨v', holds_pointsTo8_iff.mpr rfl⟩
  · subst hc
    exact holds_pointsTo8RO_iff.mpr rfl

/-- The segment after a run as per-byte cells: read-only bytes of the loaded image, arbitrary
    writable bytes. -/
theorem imageDataBss_entails_byteCells_dataCellAny {obj : Obj.LinkedImage} {base : BitVec 64}
    {img : Obj.Image} (hload : obj.load base = .ok img) :
    imageDataBss obj base ⊢ byteCells (dataCellAny img.isRoData) img.dataAddr img.data := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨ha, hf, hm, img', hload', hp⟩ := (imageDataBss_holds obj base h).1 hh
  rw [hload, Except.ok.injEq] at hload'
  subst hload'
  refine byteCells_of_phys'
    (R := fun a v c => if img.isRoData a then c = HeapCell.ro v else ∃ v', c = HeapCell.rw v')
    (fun a v c hc => dataCellAny_holds_of _ a v c hc)
    img.data img.dataAddr h (load_data_length_le hload) ha hf hm fun x => ?_
  have hx := hp x
  by_cases hlt : (x - img.dataAddr).toNat < img.data.length
  · rw [dite_eq_left hlt] at hx ⊢
    dsimp only at hx ⊢
    cases hro : img.isRoData x <;> simp only [hro, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    · obtain ⟨b', hb'⟩ := hx
      exact ⟨_, ⟨b', rfl⟩, hb'⟩
    · exact ⟨_, rfl, hx⟩
  · rw [dite_eq_right hlt] at hx ⊢
    exact hx

/-- Per-byte cells with the exact contents of the loaded image give back the freshly loaded
    segment. -/
theorem byteCells_dataCell_entails_imageInitialDataBss {obj : Obj.LinkedImage}
    {base : BitVec 64} {img : Obj.Image} (hload : obj.load base = .ok img) :
    byteCells (dataCell img.isRoData) img.dataAddr img.data ⊢ imageInitialDataBss obj base := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := byteCells_phys'
    (R := fun a v c => c = if img.isRoData a then HeapCell.ro v else HeapCell.rw v)
    (fun a v h hh => dataCell_holds_eq _ a v h hh) img.data img.dataAddr h hh
  refine (imageInitialDataBss_holds obj base h).2 ⟨ha, hf, hm, img, hload, fun x => ?_⟩
  have hx := hp x
  by_cases hlt : (x - img.dataAddr).toNat < img.data.length
  · rw [dite_eq_left hlt] at hx ⊢
    obtain ⟨c, rfl, hpx⟩ := hx
    exact hpx
  · rw [dite_eq_right hlt] at hx ⊢
    exact hx

/-! ## Whole-Segment Wrappers -/

/-- `imageDataBss obj base ⊢ P` from `P` for every successful load of `obj` at `base`
    (when `obj` does not load at `base`, `imageDataBss obj base` is unsatisfiable). -/
theorem imageDataBss_entails {obj : Obj.LinkedImage} {base : BitVec 64} {P : SepProp}
    (hP : ∀ img, obj.load base = .ok img →
      byteCells (dataCellAny img.isRoData) img.dataAddr img.data ⊢ P) :
    imageDataBss obj base ⊢ P := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨-, -, -, img, hload, -⟩ := (imageDataBss_holds obj base h).1 hh
  exact SepProp.entails_iff.mp (hP img hload) h
    (SepProp.entails_iff.mp (imageDataBss_entails_byteCells_dataCellAny hload) h hh)

end HeapLevel

/-- A byte that is read-only in every heap satisfying `imageInitialDataBss obj base` is a
    read-only byte of the loaded image. -/
theorem imageInitialDataBss_roByte {obj : Obj.LinkedImage} {base : BitVec 64}
    {img : Obj.Image} (hload : obj.load base = .ok img) {a : BitVec 64} {v : BitVec 8}
    (hro : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v)) :
    ∃ hi : (a - img.dataAddr).toNat < img.data.length,
      img.isRoData a = true ∧ img.data[(a - img.dataAddr).toNat] = v := by
  let h : Heap :=
    { phys := fun x => if hx : (x - img.dataAddr).toNat < img.data.length then
        some (if img.isRoData x then HeapCell.ro img.data[(x - img.dataAddr).toNat]
          else HeapCell.rw img.data[(x - img.dataAddr).toNat])
      else none }
  have hh : (imageInitialDataBss obj base).holds h :=
    (imageInitialDataBss_holds obj base h).2 ⟨rfl, rfl, rfl, img, hload, fun x => by
      by_cases hx : (x - img.dataAddr).toNat < img.data.length
      · rw [dite_eq_left hx]; simp only [h, dite_eq_left hx]
      · rw [dite_eq_right hx]; simp only [h, dite_eq_right hx]⟩
  have hp := hro h hh
  by_cases hx : (a - img.dataAddr).toNat < img.data.length
  · simp only [h, dite_eq_left hx] at hp
    refine ⟨hx, ?_⟩
    cases hr : img.isRoData a <;>
      simp only [hr, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq,
        HeapCell.ro.injEq] at hp
    exact ⟨rfl, hp⟩
  · simp only [h, dite_eq_right hx] at hp
    cases hp

/-! ## Read-Only Duplication -/

private theorem byteCells_dup_pointsTo8RO {C : BitVec 64 → BitVec 8 → SepProp}
    (a : BitVec 64) (bs : List (BitVec 8)) (i : Nat) (hi : i < bs.length)
    (hC : C (a + BitVec.ofNat 64 i) bs[i] = ((a + BitVec.ofNat 64 i) ↦₈ᵣ bs[i])) :
    byteCells C a bs ⊢ byteCells C a bs ∗ ((a + BitVec.ofNat 64 i) ↦₈ᵣ bs[i]) := by
  rw [byteCells_take_drop C a bs i (Nat.le_of_lt hi), ← List.getElem_cons_drop hi,
    byteCells_cons, hC]
  conv => lhs; rw [← pointsTo8RO_dup (a + BitVec.ofNat 64 i) bs[i]]
  exact Entails.of_eq

/-- Duplicate a read-only byte out of the segment after a run. -/
theorem imageDataBss_dup_pointsTo8RO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {v : BitVec 8}
    (hro : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v)) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₈ᵣ v) :=
  imageDataBss_entails fun img hload => by
    obtain ⟨hi, hr, hv⟩ := imageInitialDataBss_roByte hload hro
    have ha : img.dataAddr + BitVec.ofNat 64 (a - img.dataAddr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hd := byteCells_dup_pointsTo8RO (C := dataCellAny img.isRoData) img.dataAddr img.data
      _ hi (by simp only [dataCellAny, ha, hr, ↓reduceIte])
    rw [ha, hv] at hd
    exact Entails.trans hd
      (sepConj_mono_left (byteCells_dataCellAny_entails_imageDataBss hload))

/-- Duplicate a read-only byte out of the freshly loaded segment. -/
theorem imageInitialDataBss_dup_pointsTo8RO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {v : BitVec 8}
    (hro : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v)) :
    imageInitialDataBss obj base ⊢ imageInitialDataBss obj base ∗ (a ↦₈ᵣ v) :=
  imageInitialDataBss_entails fun img hload => by
    obtain ⟨hi, hr, hv⟩ := imageInitialDataBss_roByte hload hro
    have ha : img.dataAddr + BitVec.ofNat 64 (a - img.dataAddr).toNat = a := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hd := byteCells_dup_pointsTo8RO (C := dataCell img.isRoData) img.dataAddr img.data
      _ hi (by simp only [dataCell, ha, hr, ↓reduceIte])
    rw [ha, hv] at hd
    exact Entails.trans hd
      (sepConj_mono_left (byteCells_dataCell_entails_imageInitialDataBss hload))

private theorem dup_pointsToBytesRO_of_dup8 {obj : Obj.LinkedImage} {base : BitVec 64}
    {S : SepProp} (a : BitVec 64)
    (hdup : ∀ (x : BitVec 64) (v : BitVec 8),
      (∀ h, (imageInitialDataBss obj base).holds h → h.phys x = some (.ro v)) →
      S ⊢ S ∗ (x ↦₈ᵣ v)) :
    ∀ (bs : List (BitVec 8)),
      (∀ (j : Nat) (hj : j < bs.length) h, (imageInitialDataBss obj base).holds h →
        h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])) →
      S ⊢ S ∗ (a ↦ᵣ bs) := by
  intro bs
  induction bs generalizing a with
  | nil =>
    intro _
    rw [pointsToBytesRO_nil, sepConj_emp]
    exact Entails.refl _
  | cons v vs ih =>
    intro hro
    have h0 : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v) := by
      intro h hh
      have := hro 0 (by simp) h hh
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getElem_cons_zero] using this
    have ht := ih (a + 1#64) fun j hj h hh => by
      have := hro (j + 1) (by simp; omega) h hh
      rwa [show a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j by bv_omega,
        List.getElem_cons_succ] at this
    refine Entails.trans (hdup a v h0) (Entails.trans (sepConj_mono_left ht) ?_)
    rw [pointsToBytesRO_cons]
    exact Entails.of_eq

/-- Duplicate a read-only byte slice out of the segment after a run. -/
theorem imageDataBss_dup_pointsToBytesRO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {bs : List (BitVec 8)}
    (hro : ∀ (j : Nat) (hj : j < bs.length) h, (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦ᵣ bs) :=
  dup_pointsToBytesRO_of_dup8 a (fun _ _ h => imageDataBss_dup_pointsTo8RO h) bs hro

/-- Duplicate a read-only byte slice out of the freshly loaded segment. -/
theorem imageInitialDataBss_dup_pointsToBytesRO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {bs : List (BitVec 8)}
    (hro : ∀ (j : Nat) (hj : j < bs.length) h, (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])) :
    imageInitialDataBss obj base ⊢ imageInitialDataBss obj base ∗ (a ↦ᵣ bs) :=
  dup_pointsToBytesRO_of_dup8 a (fun _ _ h => imageInitialDataBss_dup_pointsTo8RO h) bs hro

/-- Duplicate a read-only 64-bit word (little-endian bytes `unpack64 w`) out of the segment after
    a run. -/
theorem imageDataBss_dup_pointsTo64RO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {w : BitVec 64}
    (hro : ∀ (j : Nat) (hj : j < (unpack64 w).length) h,
      (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro (unpack64 w)[j])) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₆₄ᵣ w) := by
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact imageDataBss_dup_pointsToBytesRO hro

/-- Duplicate a read-only 64-bit word (little-endian bytes `unpack64 w`) out of the freshly loaded
    segment. -/
theorem imageInitialDataBss_dup_pointsTo64RO {obj : Obj.LinkedImage} {base : BitVec 64}
    {a : BitVec 64} {w : BitVec 64}
    (hro : ∀ (j : Nat) (hj : j < (unpack64 w).length) h,
      (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro (unpack64 w)[j])) :
    imageInitialDataBss obj base ⊢ imageInitialDataBss obj base ∗ (a ↦₆₄ᵣ w) := by
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact imageInitialDataBss_dup_pointsToBytesRO hro

end ProofLib
