/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Exists
public import ProofLib.ObjectLoad
public import ProofLib.SepLogic.Region
import ProofLib.SepLogic.Model

/-!
# Per-Byte Decomposition of Image Data Segments

Decomposes the whole-segment assertions `imageInitialDataBss` and `imageDataBss` into per-byte
separating conjunctions `byteCells (dataCell img.isRoData)` and
`byteCells (dataCellAny img.isRoData)`, bridging loaded `.rodata`, `.data`, and `.bss` sections to
byte-slice (`↦ᵣ`, `↦ₛ`) and `memRegion` assertions.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## `byteCells` -/

/-- `C (a + i) bs[i]` for each byte `bs[i]`, joined by `∗` (`emp` for `[]`). -/
def byteCells (C : BitVec 64 → BitVec 8 → SepProp) (a : BitVec 64) : List (BitVec 8) → SepProp
  | [] => emp
  | v :: vs => C a v ∗ byteCells C (a + 1#64) vs

@[simp] theorem byteCells_nil (C : BitVec 64 → BitVec 8 → SepProp) (a : BitVec 64) :
    byteCells C a [] = emp := rfl

theorem byteCells_cons (C : BitVec 64 → BitVec 8 → SepProp) (a : BitVec 64) (v : BitVec 8)
    (vs : List (BitVec 8)) :
    byteCells C a (v :: vs) = (C a v ∗ byteCells C (a + 1#64) vs) := rfl

private theorem add_one_add_ofNat (a : BitVec 64) (i : Nat) :
    a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
  bv_omega

theorem byteCells_append (C : BitVec 64 → BitVec 8 → SepProp) (a : BitVec 64)
    (xs ys : List (BitVec 8)) :
    byteCells C a (xs ++ ys) =
      (byteCells C a xs ∗ byteCells C (a + BitVec.ofNat 64 xs.length) ys) := by
  induction xs generalizing a with
  | nil => simp [emp_sepConj]
  | cons x xs ih =>
    rw [List.cons_append, byteCells_cons, byteCells_cons, ih, sepConj_assoc,
      add_one_add_ofNat, List.length_cons]

theorem byteCells_take_drop (C : BitVec 64 → BitVec 8 → SepProp) (a : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat) (hn : n ≤ bs.length) :
    byteCells C a bs =
      (byteCells C a (bs.take n) ∗ byteCells C (a + BitVec.ofNat 64 n) (bs.drop n)) := by
  conv => lhs; rw [← List.take_append_drop n bs]
  rw [byteCells_append, List.length_take, Nat.min_eq_left hn]

/-- `byteCells_append` at an offset `p + k`, with the split point given as `p + m`. -/
theorem byteCells_append_off (C : BitVec 64 → BitVec 8 → SepProp) (p : BitVec 64) (k m : Nat)
    (xs ys : List (BitVec 8)) (h : k + xs.length = m) :
    byteCells C (p + BitVec.ofNat 64 k) (xs ++ ys) =
      (byteCells C (p + BitVec.ofNat 64 k) xs ∗ byteCells C (p + BitVec.ofNat 64 m) ys) := by
  subst h
  rw [byteCells_append, BitVec.add_assoc, BitVec.ofNat_add]

theorem byteCells_entails {C D : BitVec 64 → BitVec 8 → SepProp} (a : BitVec 64)
    (bs : List (BitVec 8))
    (h : ∀ (i : Nat) (hi : i < bs.length),
      C (a + BitVec.ofNat 64 i) bs[i] ⊢ D (a + BitVec.ofNat 64 i) bs[i]) :
    byteCells C a bs ⊢ byteCells D a bs := by
  induction bs generalizing a with
  | nil => exact Entails.refl _
  | cons v vs ih =>
    rw [byteCells_cons, byteCells_cons]
    have h0 := h 0 (by simp)
    simp only [BitVec.add_zero, List.getElem_cons_zero] at h0
    refine sepConj_mono h0 (ih (a + 1#64) fun i hi => ?_)
    have := h (i + 1) (by simp; omega)
    simpa only [add_one_add_ofNat, List.getElem_cons_succ] using this

theorem byteCells_congr {C D : BitVec 64 → BitVec 8 → SepProp} (a : BitVec 64)
    (bs : List (BitVec 8))
    (h : ∀ (i : Nat) (hi : i < bs.length),
      C (a + BitVec.ofNat 64 i) bs[i] = D (a + BitVec.ofNat 64 i) bs[i]) :
    byteCells C a bs = byteCells D a bs :=
  Entails.antisymm
    (byteCells_entails a bs fun i hi => by rw [h i hi]; exact Entails.refl _)
    (byteCells_entails a bs fun i hi => by rw [h i hi]; exact Entails.refl _)

/-! ## Data-segment cells -/

/-- One byte of a loaded data segment: `a ↦₈ᵣ v` in a read-only section, `a ↦₈ v` elsewhere. -/
def dataCell (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8) : SepProp :=
  if isRo a then a ↦₈ᵣ v else a ↦₈ v

/-- One byte of a data segment after execution: `a ↦₈ᵣ v` in a read-only section, arbitrary value
    elsewhere. -/
def dataCellAny (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8) : SepProp :=
  if isRo a then a ↦₈ᵣ v else ∃∗ v' : BitVec 8, a ↦₈ v'

/-! ## Heap-level characterization -/

set_option allowUnsafeReducibility true in
attribute [local semireducible]
  Heap.empty Heap.singleton Heap.singletonRO Heap.Disjoint Heap.union
  regionHeap

private def OneCell (h : Heap) (a : BitVec 64) (c : HeapCell) : Prop :=
  h.auth = (fun _ _ => none) ∧ h.frag = (fun _ _ => none) ∧ h.mapped = (fun _ => false) ∧
    h.phys a = some c ∧ ∀ x, x ≠ a → h.phys x = none

private theorem oneCell_iff (h : Heap) (a : BitVec 64) (c : HeapCell) :
    OneCell h a c ↔ h = { phys := fun x => if x = a then some c else none } := by
  constructor
  · rintro ⟨ha, hf, hm, hp, hn⟩
    apply Heap.ext
    · funext x
      by_cases hx : x = a
      · simp [hx, ← hp]
      · simp [hx, hn x hx]
    · exact ha
    · exact hf
    · exact hm
  · rintro rfl
    exact ⟨rfl, rfl, rfl, by simp, fun x hx => by simp [hx]⟩

private theorem dataCell_holds (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8)
    (h : Heap) :
    (dataCell isRo a v).holds h ↔ OneCell h a (if isRo a then .ro v else .rw v) := by
  rw [oneCell_iff]
  cases hro : isRo a <;> simp only [dataCell, hro, Bool.false_eq_true, ↓reduceIte]
  · exact holds_pointsTo8_iff
  · exact holds_pointsTo8RO_iff

private theorem dataCellAny_holds (isRo : BitVec 64 → Bool) (a : BitVec 64) (v : BitVec 8)
    (h : Heap) :
    (dataCellAny isRo a v).holds h ↔
      ∃ c, (if isRo a then c = .ro v else ∃ v', c = .rw v') ∧ OneCell h a c := by
  cases hro : isRo a <;> simp only [dataCellAny, hro, Bool.false_eq_true, ↓reduceIte,
    SepProp.holds_sepExists_iff, holds_pointsTo8_iff, holds_pointsTo8RO_iff]
  · constructor
    · rintro ⟨v', rfl⟩
      exact ⟨.rw v', ⟨v', rfl⟩, (oneCell_iff _ _ _).2 rfl⟩
    · rintro ⟨c, ⟨v', rfl⟩, hc⟩
      exact ⟨v', (oneCell_iff _ _ _).1 hc⟩
  · constructor
    · intro hh
      exact ⟨.ro v, rfl, (oneCell_iff _ _ _).2 hh⟩
    · rintro ⟨c, rfl, hc⟩
      exact (oneCell_iff _ _ _).1 hc

private theorem toNat_sub_eq_succ {x a : BitVec 64} (h : x ≠ a) :
    (x - a).toNat = (x - (a + 1#64)).toNat + 1 := by
  bv_omega

private theorem getElem_cons_of_sub {x a : BitVec 64} (h : x ≠ a) (v : BitVec 8)
    (vs : List (BitVec 8)) (hi : (x - a).toNat < (v :: vs).length)
    (hi' : (x - (a + 1#64)).toNat < vs.length) :
    (v :: vs)[(x - a).toNat] = vs[(x - (a + 1#64)).toNat] := by
  simp only [toNat_sub_eq_succ h, List.getElem_cons_succ]

private theorem byteCells_phys {C : BitVec 64 → BitVec 8 → SepProp}
    {R : BitVec 64 → BitVec 8 → HeapCell → Prop}
    (hC : ∀ a v h, (C a v).holds h → ∃ c, R a v c ∧ OneCell h a c) :
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
    obtain ⟨c, hR, ha1, hf1, hm1, hp1, hn1⟩ := hC a v h1 hh1
    obtain ⟨ha2, hf2, hm2, hp2⟩ := ih (a + 1#64) h2 hh2
    refine ⟨?_, ?_, ?_, fun x => ?_⟩
    · funext γ k; simp [Heap.union, ha1, ha2]
    · funext γ k; simp [Heap.union, hf1, hf2]
    · funext x; simp [Heap.union, hm1, hm2]
    · by_cases hxa : x = a
      · subst hxa
        rw [dite_eq_left (by simp)]
        refine ⟨c, ?_, by simp [Heap.union, hp1]⟩
        simpa using hR
      · have hux : (h1.union h2).phys x = h2.phys x := by simp [Heap.union, hn1 x hxa]
        rw [hux]
        have hs := toNat_sub_eq_succ hxa
        have h2x := hp2 x
        by_cases hlt : (x - (a + 1#64)).toNat < vs.length
        · have hlt' : (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_left hlt] at h2x
          rw [dite_eq_left hlt', getElem_cons_of_sub hxa v vs hlt' hlt]
          exact h2x
        · have hlt' : ¬ (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_right hlt] at h2x
          rw [dite_eq_right hlt']
          exact h2x

private theorem byteCells_of_phys {C : BitVec 64 → BitVec 8 → SepProp}
    {R : BitVec 64 → BitVec 8 → HeapCell → Prop}
    (hC : ∀ a v h c, R a v c → OneCell h a c → (C a v).holds h) :
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
    · exact hC a v _ c hR ((oneCell_iff _ _ _).2 rfl)
    · refine ih (a + 1#64) _ (by simp at hlen; omega) rfl rfl rfl fun x => ?_
      by_cases hxa : x = a
      · subst hxa
        have hne : ¬ (x - (x + 1#64)).toNat < vs.length := by
          have e : (x - (x + 1#64)).toNat = 2 ^ 64 - 1 := by bv_omega
          simp at hlen; omega
        rw [dite_eq_right hne]
        simp
      · have hs := toNat_sub_eq_succ hxa
        have hx := hp x
        simp only [hxa, ↓reduceIte]
        by_cases hlt : (x - (a + 1#64)).toNat < vs.length
        · have hlt' : (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_left hlt', getElem_cons_of_sub hxa v vs hlt' hlt] at hx
          rw [dite_eq_left hlt]
          exact hx
        · have hlt' : ¬ (x - a).toNat < (v :: vs).length := by simp only [List.length_cons]; omega
          rw [dite_eq_right hlt'] at hx
          rw [dite_eq_right hlt]
          exact hx

/-! ## Image segments -/

/-- The data segment of a loaded image fits in the address space. -/
theorem load_data_length_le {obj : Obj.LinkedImage} {base : BitVec 64} {img : Obj.Image}
    (hload : obj.load base = .ok img) : img.data.length ≤ 2 ^ 64 := by
  obtain ⟨data, hfold, -, hwf, hwrap, rfl⟩ := ObjectLoad.load_eq_ok hload
  simp only [Obj.LinkedImage.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hwf
  have hrel : obj.relocs.all (fun r => decide (r.off + r.width ≤ obj.data.length)) = true := by
    rw [List.all_eq_true]
    intro r hr
    have := List.all_eq_true.mp hwf.1.1.2 r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    simpa using this.2
  have hdlen := ObjectLoad.RoDataFactsAux.foldlM_dataReloc_length obj.relocs _ data hfold hrel
    (by simp only [List.length_append]; omega)
  simp only [List.length_append, List.length_replicate] at hdlen
  have hdg := hwf.1.1.1.1.1.1.2
  have hde : obj.dataEnd = obj.dataOff + obj.data.length + obj.bss := rfl
  show data.length ≤ 2 ^ 64
  omega

/-- Decomposes the freshly loaded `.rodata`/`.data`/`.bss` segment into per-byte `dataCell`s. -/
theorem imageInitialDataBss_entails_byteCells {obj : Obj.LinkedImage} {base : BitVec 64}
    {img : Obj.Image} (hload : obj.load base = .ok img) :
    imageInitialDataBss obj base ⊢ byteCells (dataCell img.isRoData) img.dataAddr img.data := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨ha, hf, hm, img', hload', hp⟩ := (imageInitialDataBss_holds obj base h).1 hh
  rw [hload, Except.ok.injEq] at hload'
  subst hload'
  refine byteCells_of_phys
    (R := fun a v c => c = if img.isRoData a then HeapCell.ro v else HeapCell.rw v)
    (fun a v h c hR hc => by subst hR; exact (dataCell_holds _ _ _ _).2 hc)
    img.data img.dataAddr h (load_data_length_le hload) ha hf hm fun x => ?_
  have hx := hp x
  by_cases hlt : (x - img.dataAddr).toNat < img.data.length
  · rw [dite_eq_left hlt] at hx ⊢
    exact ⟨_, rfl, hx⟩
  · rw [dite_eq_right hlt] at hx ⊢
    exact hx

/-- Eliminates `imageInitialDataBss obj base` into `P` via per-byte `dataCell`s over every
    successful load of `obj` at `base`. -/
theorem imageInitialDataBss_entails {obj : Obj.LinkedImage} {base : BitVec 64} {P : SepProp}
    (hP : ∀ img, obj.load base = .ok img →
      byteCells (dataCell img.isRoData) img.dataAddr img.data ⊢ P) :
    imageInitialDataBss obj base ⊢ P := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨-, -, -, img, hload, -⟩ := (imageInitialDataBss_holds obj base h).1 hh
  exact SepProp.entails_iff.mp (hP img hload) h
    (SepProp.entails_iff.mp (imageInitialDataBss_entails_byteCells hload) h hh)

/-- Reassembles `imageDataBss obj base` from per-byte `dataCellAny` cells. -/
theorem byteCells_dataCellAny_entails_imageDataBss {obj : Obj.LinkedImage} {base : BitVec 64}
    {img : Obj.Image} (hload : obj.load base = .ok img) :
    byteCells (dataCellAny img.isRoData) img.dataAddr img.data ⊢ imageDataBss obj base := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨ha, hf, hm, hp⟩ := byteCells_phys
    (R := fun a v c => if img.isRoData a then c = HeapCell.ro v else ∃ v', c = HeapCell.rw v')
    (fun a v h hh => (dataCellAny_holds _ _ _ _).1 hh) img.data img.dataAddr h hh
  refine (imageDataBss_holds obj base h).2 ⟨ha, hf, hm, img, hload, fun x => ?_⟩
  have hx := hp x
  by_cases hlt : (x - img.dataAddr).toNat < img.data.length
  · rw [dite_eq_left hlt] at hx ⊢
    obtain ⟨c, hR, hpx⟩ := hx
    dsimp only
    by_cases hro : img.isRoData x = true
    · rw [ite_eq_left hro] at hR ⊢
      rw [hpx, hR]
    · rw [ite_eq_right hro] at hR ⊢
      obtain ⟨v', rfl⟩ := hR
      exact ⟨v', hpx⟩
  · rw [dite_eq_right hlt] at hx ⊢
    exact hx

/-! ## Slices -/

/-- `byteCells (dataCell isRo)` on an entirely read-only slice equals `a ↦ᵣ bs`. -/
theorem byteCells_dataCell_ro {isRo : BitVec 64 → Bool} {a : BitVec 64} {bs : List (BitVec 8)}
    (hro : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = true) :
    byteCells (dataCell isRo) a bs = (a ↦ᵣ bs) := by
  induction bs generalizing a with
  | nil => rw [byteCells_nil, pointsToBytesRO_nil]
  | cons v vs ih =>
    have h0 : isRo a = true := by simpa using hro 0 (by simp)
    rw [byteCells_cons, pointsToBytesRO_cons, ih fun i hi => ?_]
    · simp [dataCell, h0]
    · rw [add_one_add_ofNat]; exact hro (i + 1) (by simp; omega)

/-- `byteCells (dataCell isRo)` on an entirely writable slice equals `a ↦ₛ bs`. -/
theorem byteCells_dataCell_rw {isRo : BitVec 64 → Bool} {a : BitVec 64} {bs : List (BitVec 8)}
    (hrw : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = false) :
    byteCells (dataCell isRo) a bs = (a ↦ₛ bs) := by
  induction bs generalizing a with
  | nil => rw [byteCells_nil, pointsToBytes_nil]
  | cons v vs ih =>
    have h0 : isRo a = false := by simpa using hrw 0 (by simp)
    rw [byteCells_cons, pointsToBytes_cons, ih fun i hi => ?_]
    · simp [dataCell, h0]
    · rw [add_one_add_ofNat]; exact hrw (i + 1) (by simp; omega)

/-- `byteCells (dataCellAny isRo)` on an entirely read-only slice equals `a ↦ᵣ bs`. -/
theorem byteCells_dataCellAny_ro {isRo : BitVec 64 → Bool} {a : BitVec 64}
    {bs : List (BitVec 8)}
    (hro : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = true) :
    byteCells (dataCellAny isRo) a bs = (a ↦ᵣ bs) := by
  induction bs generalizing a with
  | nil => rw [byteCells_nil, pointsToBytesRO_nil]
  | cons v vs ih =>
    have h0 : isRo a = true := by simpa using hro 0 (by simp)
    rw [byteCells_cons, pointsToBytesRO_cons, ih fun i hi => ?_]
    · simp [dataCellAny, h0]
    · rw [add_one_add_ofNat]; exact hro (i + 1) (by simp; omega)

/-- `byteCells (dataCellAny isRo)` on an entirely writable slice equals `memRegion a bs.length`. -/
theorem byteCells_dataCellAny_rw {isRo : BitVec 64 → Bool} {a : BitVec 64}
    {bs : List (BitVec 8)}
    (hrw : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = false)
    (hlen : bs.length ≤ 2 ^ 64) :
    byteCells (dataCellAny isRo) a bs = memRegion a bs.length := by
  induction bs generalizing a with
  | nil => rw [byteCells_nil, List.length_nil, memRegion_zero]
  | cons v vs ih =>
    have h0 : isRo a = false := by simpa using hrw 0 (by simp)
    simp only [List.length_cons] at hlen
    rw [byteCells_cons, ih (fun i hi => ?_) (by omega), List.length_cons,
      show vs.length + 1 = 1 + vs.length from Nat.add_comm _ _,
      memRegion_split a 1 vs.length (by omega), memRegion_one]
    · simp only [dataCellAny, h0, Bool.false_eq_true, ↓reduceIte]
    · rw [add_one_add_ofNat]; exact hrw (i + 1) (by simp; omega)

/-- `memRegion a bs.length` entails `byteCells (dataCellAny isRo) a bs` on an entirely writable
    slice. -/
theorem memRegion_entails_byteCells_dataCellAny {isRo : BitVec 64 → Bool} {a : BitVec 64}
    {bs : List (BitVec 8)}
    (hrw : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = false)
    (hlen : bs.length ≤ 2 ^ 64) :
    memRegion a bs.length ⊢ byteCells (dataCellAny isRo) a bs := by
  rw [SepProp.entails_iff]
  intro h hh
  obtain ⟨m, rfl⟩ := holds_memRegion_iff.mp hh
  refine byteCells_of_phys
    (R := fun x v c => if isRo x then c = HeapCell.ro v else ∃ v', c = HeapCell.rw v')
    (fun x v h c hR hc => (dataCellAny_holds _ _ _ _).2 ⟨c, hR, hc⟩) bs a _ hlen rfl rfl rfl
    fun x => ?_
  by_cases hlt : (x - a).toNat < bs.length
  · rw [dite_eq_left hlt]
    have e : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have hro : isRo x = false := by have := hrw _ hlt; rwa [e] at this
    refine ⟨.rw (m.read8 x), ?_, ?_⟩
    · rw [hro]; exact ⟨_, rfl⟩
    · show (if InRegion a bs.length x then _ else _) = _
      rw [ite_eq_left (show InRegion a bs.length x from hlt)]
  · rw [dite_eq_right hlt]
    show (if InRegion a bs.length x then _ else _) = _
    rw [ite_eq_right (show ¬ InRegion a bs.length x from hlt)]

/-- `a ↦ₛ xs` entails `byteCells (dataCellAny isRo) a bs` on an entirely writable slice of equal
    length. -/
theorem pointsToBytes_entails_byteCells_dataCellAny {isRo : BitVec 64 → Bool} {a : BitVec 64}
    {xs bs : List (BitVec 8)} (hl : xs.length = bs.length)
    (hrw : ∀ i, i < bs.length → isRo (a + BitVec.ofNat 64 i) = false)
    (hlen : bs.length ≤ 2 ^ 64) :
    (a ↦ₛ xs) ⊢ byteCells (dataCellAny isRo) a bs :=
  Entails.trans (pointsToBytes_entails_memRegion a xs)
    (by rw [hl]; exact memRegion_entails_byteCells_dataCellAny hrw hlen)

end ProofLib
