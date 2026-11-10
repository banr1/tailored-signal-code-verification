/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Arm64
import ProofLib.SepLogic.ImageDataAny

/-!
# Image Segment Per-Byte View Tests

Regression tests for `imageDataBss` and `imageInitialDataBss` per-byte round trips and read-only
duplication lemmas.
-/

set_option autoImplicit false

namespace Examples.Testing.ProofLib.ImageDataAny

open Arm64 _root_.ProofLib

/-! ## Round Trips -/

example (obj : Obj.LinkedImage) (base : BitVec 64) (img : Obj.Image)
    (hload : obj.load base = .ok img) :
    imageDataBss obj base ⊢ imageDataBss obj base :=
  Entails.trans (imageDataBss_entails_byteCells_dataCellAny hload)
    (byteCells_dataCellAny_entails_imageDataBss hload)

example (obj : Obj.LinkedImage) (base : BitVec 64) (img : Obj.Image)
    (hload : obj.load base = .ok img) :
    imageInitialDataBss obj base ⊢ imageInitialDataBss obj base :=
  Entails.trans (imageInitialDataBss_entails_byteCells hload)
    (byteCells_dataCell_entails_imageInitialDataBss hload)

example (obj : Obj.LinkedImage) (base : BitVec 64) (P : SepProp)
    (h : ∀ img, obj.load base = .ok img →
      byteCells (dataCellAny img.isRoData) img.dataAddr img.data ⊢ P) :
    imageDataBss obj base ⊢ P :=
  imageDataBss_entails h

/-! ## Read-Only Duplication -/

example (obj : Obj.LinkedImage) (base a : BitVec 64) (v : BitVec 8)
    (hro : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v)) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₈ᵣ v) :=
  imageDataBss_dup_pointsTo8RO hro

example (obj : Obj.LinkedImage) (base a w : BitVec 64)
    (hro : ∀ (j : Nat) (hj : j < (unpack64 w).length) h,
      (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro (unpack64 w)[j])) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₆₄ᵣ w) :=
  imageDataBss_dup_pointsTo64RO hro

/-- Two read-only atoms from the same segment, framed with an extra assertion `Q`. -/
example (obj : Obj.LinkedImage) (base a b : BitVec 64) (x y : BitVec 8) (Q : SepProp)
    (hx : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro x))
    (hy : ∀ h, (imageInitialDataBss obj base).holds h → h.phys b = some (.ro y)) :
    imageDataBss obj base ∗ Q ⊢ ((imageDataBss obj base ∗ (a ↦₈ᵣ x)) ∗ (b ↦₈ᵣ y)) ∗ Q :=
  sepConj_mono_left (Entails.trans (Entails.trans (imageDataBss_dup_pointsTo8RO hx)
    (sepConj_mono_left (imageDataBss_dup_pointsTo8RO hy))) Entails.of_eq)

example (obj : Obj.LinkedImage) (base a : BitVec 64) (bs : List (BitVec 8))
    (hro : ∀ (j : Nat) (hj : j < bs.length) h, (imageInitialDataBss obj base).holds h →
      h.phys (a + BitVec.ofNat 64 j) = some (.ro bs[j])) :
    imageInitialDataBss obj base ⊢ imageInitialDataBss obj base ∗ (a ↦ᵣ bs) :=
  imageInitialDataBss_dup_pointsToBytesRO hro

/-! ## Negative Tests -/

-- Duplication only produces read-only atoms: the writable form is rejected.

/--
error: Type mismatch
  imageDataBss_dup_pointsTo8RO hro
has type
  imageDataBss obj base ⊢ imageDataBss obj base ∗ a ↦₈ᵣ v
but is expected to have type
  imageDataBss obj base ⊢ imageDataBss obj base ∗ a ↦₈ v

Note: The following definitions were not unfolded because their definition is not exposed:
  pointsTo8 ↦ 2
  pointsTo8RO ↦ 2
  Entails ↦ 4
  sepConj ↦ 4
-/
#guard_msgs in
example (obj : Obj.LinkedImage) (base a : BitVec 64) (v : BitVec 8)
    (hro : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.ro v)) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₈ v) :=
  imageDataBss_dup_pointsTo8RO hro

-- A writable byte of the loaded segment is not a read-only fact.

/--
error: Application type mismatch: The argument
  hrw
has type
  ∀ (h : Heap), (imageInitialDataBss obj base).holds h → h.phys a = some (HeapCell.rw v)
but is expected to have type
  ∀ (h : Heap), (imageInitialDataBss obj base).holds h → h.phys a = some (HeapCell.ro v)
in the application
  imageDataBss_dup_pointsTo8RO hrw

Note: The following definitions were not unfolded because their definition is not exposed:
  imageInitialDataBss ↦ 1
-/
#guard_msgs in
example (obj : Obj.LinkedImage) (base a : BitVec 64) (v : BitVec 8)
    (hrw : ∀ h, (imageInitialDataBss obj base).holds h → h.phys a = some (.rw v)) :
    imageDataBss obj base ⊢ imageDataBss obj base ∗ (a ↦₈ᵣ v) :=
  imageDataBss_dup_pointsTo8RO hrw

end Examples.Testing.ProofLib.ImageDataAny
