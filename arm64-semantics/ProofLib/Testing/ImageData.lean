/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Arm64
import ProofLib.SepLogic.ImageData

/-!
# Per-Byte Image Data Segment Regressions

Tests `byteCells_append_off`, `byteCells_dataCell_ro`, `byteCells_dataCell_rw`,
`byteCells_dataCellAny_ro`, `byteCells_dataCellAny_rw`, `imageInitialDataBss_entails`, and
`byteCells_dataCellAny_entails_imageDataBss`, including negative rejection of writable slices
coerced to read-only `↦ᵣ` assertions.
-/

namespace Examples.Testing.ProofLib.ImageData

open Arm64 _root_.ProofLib

/-- Two-section segment `[ro ro | rw rw rw]` at `p + 0x10`. -/
private def twoSec (p : BitVec 64) (a : BitVec 64) : Bool := decide ((a - (p + 0x10#64)).toNat < 2)

example (p : BitVec 64) (x y : BitVec 8) (zs : List (BitVec 8)) (h : zs.length = 3) :
    byteCells (dataCell (twoSec p)) (p + BitVec.ofNat 64 0x10) ([x, y] ++ zs) =
      ((p + BitVec.ofNat 64 0x10) ↦ᵣ [x, y]) ∗ ((p + BitVec.ofNat 64 0x12) ↦ₛ zs) := by
  rw [byteCells_append_off _ p 0x10 0x12 [x, y] zs rfl, byteCells_dataCell_ro, byteCells_dataCell_rw]
  · intro i hi
    simp only [twoSec, decide_eq_false_iff_not, Nat.not_lt]
    bv_omega
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    simp only [twoSec, decide_eq_true_eq]
    bv_omega

example (p : BitVec 64) (x y : BitVec 8) (zs : List (BitVec 8)) (h : zs.length = 3) :
    byteCells (dataCellAny (twoSec p)) (p + BitVec.ofNat 64 0x10) ([x, y] ++ zs) =
      ((p + BitVec.ofNat 64 0x10) ↦ᵣ [x, y]) ∗ memRegion (p + BitVec.ofNat 64 0x12) 3 := by
  rw [byteCells_append_off _ p 0x10 0x12 [x, y] zs rfl, byteCells_dataCellAny_ro,
    byteCells_dataCellAny_rw, h]
  · intro i hi
    simp only [twoSec, decide_eq_false_iff_not, Nat.not_lt]
    bv_omega
  · omega
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    simp only [twoSec, decide_eq_true_eq]
    bv_omega

example (a : BitVec 64) (xs : List (BitVec 8)) (h : xs.length ≤ 2 ^ 64) :
    byteCells (dataCell fun _ => false) a xs ⊢ byteCells (dataCellAny fun _ => false) a xs := by
  rw [byteCells_dataCell_rw (fun _ _ => rfl), byteCells_dataCellAny_rw (fun _ _ => rfl) h]
  exact pointsToBytes_entails_memRegion a xs

example (obj : Obj.LinkedImage) (base : BitVec 64) (P : SepProp)
    (h : ∀ img, obj.load base = .ok img →
      byteCells (dataCell img.isRoData) img.dataAddr img.data ⊢ P) :
    imageInitialDataBss obj base ⊢ P :=
  imageInitialDataBss_entails h

example (obj : Obj.LinkedImage) (base : BitVec 64) (img : Obj.Image)
    (hload : obj.load base = .ok img) :
    imageInitialDataBss obj base ⊢ imageDataBss obj base :=
  imageInitialDataBss_entails fun img' hload' => by
    rw [hload] at hload'
    cases hload'
    refine Entails.trans (byteCells_entails _ _ fun i _ => ?_)
      (byteCells_dataCellAny_entails_imageDataBss hload)
    simp only [dataCell, dataCellAny]
    split
    · exact Entails.refl _
    · exact Entails.sepExists_intro _

/--
error: Tactic `decide` proved that the proposition
  false = true
is false
-/
#guard_msgs in
example (a : BitVec 64) (v : BitVec 8) :
    byteCells (dataCell fun _ => false) a [v] = (a ↦ᵣ [v]) :=
  byteCells_dataCell_ro fun i _ => by decide

end Examples.Testing.ProofLib.ImageData
