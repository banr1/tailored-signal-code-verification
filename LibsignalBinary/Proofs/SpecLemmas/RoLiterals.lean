/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ObjectLoad
public import ProofLib.SepLogic
import ProofLib.SepLogic.WP.Access

@[expose] public section

set_option autoImplicit false

/-!
# Read-only literals of a loaded image

**Checked by Lean.**

A *read-only literal* of a linked image `li` is a byte range `[off, off + bs.length)` of its data
object that lies inside one of `li.roData`'s ranges, that no data relocation touches, and whose
bytes are `bs` (`LinkedImage.RoLitAt`). Wherever `img.FrozenLoaded s` holds (`Obj.Loads li img`),
`(img.base + off) ↦ᵣ bs` can be added to any assertion `s.mem` satisfies
(`Image.FrozenLoaded.sat_roLit`, `roLits`, `sepWPp_roLits_intro`).
-/

namespace Arm64.Obj

open Arm64 ProofLib ProofLib.ObjectLoad

/-- `bs` is a read-only literal of `li` at data offset `off` (image-relative): the range is inside
`li.data`, no data relocation overlaps it, it lies inside one of `li.roData`'s ranges, and its
bytes are `bs`. -/
def LinkedImage.RoLitAt (li : LinkedImage) (off : Nat) (bs : List (BitVec 8)) : Bool :=
  decide (li.dataOff ≤ off) &&
  decide ((off - li.dataOff) + bs.length ≤ li.data.length) &&
  noRelocInRange li.relocs (li.data.length + li.bss) (off - li.dataOff) bs.length &&
  inLiRoData li off bs.length &&
  decide ((li.data.drop (off - li.dataOff)).take bs.length = bs)

theorem LinkedImage.RoLitAt.length_le {li : LinkedImage} {off : Nat} {bs : List (BitVec 8)}
    (h : li.RoLitAt off bs = true) : bs.length ≤ 2 ^ 64 := by
  simp only [LinkedImage.RoLitAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨_, hro⟩, _⟩ := h
  simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hro
  obtain ⟨_, _, _, _, _⟩ := hro
  omega

/-- A read-only literal is in memory, read-only, wherever the image's frozen parts are. -/
theorem LinkedImage.RoLitAt.holdsBytes {li : LinkedImage} {img : Image} {s : State}
    {off : Nat} {bs : List (BitVec 8)} (h : li.RoLitAt off bs = true)
    (himg : Loads li img) (hF : img.FrozenLoaded s) :
    HoldsBytes s.mem (img.base + BitVec.ofNat 64 off) bs (fun _ => .ro) := by
  simp only [LinkedImage.RoLitAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hoff, hk⟩, hno⟩, hro⟩, hbs⟩ := h
  exact loads_rodata_holdsBytes himg hF hoff hk hno hro rfl hbs

/-- A read-only literal from `FrozenLoaded`: wherever the frozen parts of `img` (loaded from
`li`) are in memory, the literal `bs` at `off` can be added to anything `s.mem` satisfies. -/
theorem Image.FrozenLoaded.sat_roLit {li : LinkedImage} {img : Image} {s : State}
    (hF : img.FrozenLoaded s) (himg : Loads li img)
    {off : Nat} {bs : List (BitVec 8)} (h : li.RoLitAt off bs = true)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + BitVec.ofNat 64 off) ↦ᵣ bs) ∗ P :=
  Satisfies.of_holdsBytes_ro (LinkedImage.RoLitAt.holdsBytes h himg hF)
    (LinkedImage.RoLitAt.length_le h) hP

/-- The read-only points-to facts of the literals `ls` (`(offset, bytes)`, image-relative) of an
image based at `base`. -/
def roLits (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) : SepProp :=
  ls.foldr (fun l P => ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ P) emp

@[simp] theorem roLits_nil (base : BitVec 64) : roLits base [] = emp := rfl

@[simp] theorem roLits_cons (base : BitVec 64) (l : Nat × List (BitVec 8))
    (ls : List (Nat × List (BitVec 8))) :
    roLits base (l :: ls) = ((base + BitVec.ofNat 64 l.1) ↦ᵣ l.2) ∗ roLits base ls := rfl

/-- Read-only literals from `FrozenLoaded`, for a list (`sat_roLit` for each). -/
theorem Image.FrozenLoaded.sat_roLits {li : LinkedImage} {img : Image} {s : State}
    (hF : img.FrozenLoaded s) (himg : Loads li img)
    {ls : List (Nat × List (BitVec 8))} (h : ls.all (fun l => li.RoLitAt l.1 l.2) = true)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ roLits img.base ls ∗ P := by
  induction ls with
  | nil => rw [roLits_nil, emp_sepConj]; exact hP
  | cons l ls ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [roLits_cons, sepConj_assoc]
    exact hF.sat_roLit himg h.1 (ih h.2)

/-- Read-only literals duplicate. -/
@[simp] theorem roLits_dup (base : BitVec 64) (ls : List (Nat × List (BitVec 8))) :
    (roLits base ls ∗ roLits base ls) = roLits base ls := by
  induction ls with
  | nil => rw [roLits_nil, emp_sepConj]
  | cons l ls ih =>
    rw [roLits_cons, sepConj_assoc, sepConj_left_comm (roLits base ls), ← sepConj_assoc,
      pointsToBytesRO_dup, ih]

/-- Add read-only literals of a frozen-loaded image to a `SepWPp` precondition. -/
theorem sepWPp_roLits_intro {li : LinkedImage} {img : Image} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hF : img.FrozenLoaded s) (himg : Loads li img)
    {ls : List (Nat × List (BitVec 8))} (h : ls.all (fun l => li.RoLitAt l.1 l.2) = true)
    (hwp : SepWPp prog ret s (roLits img.base ls ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm
  apply hwp R
  rw [sepConj_assoc]
  exact hF.sat_roLits himg h hm

end Arm64.Obj
