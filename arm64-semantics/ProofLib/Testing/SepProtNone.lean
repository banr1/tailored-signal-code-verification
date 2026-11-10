/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.Hoare.SubroutineHook
public import ProofLib.Process

/-!
# `PROT_NONE` Separation-Logic Primitives and Permission-Transition Tests

Tests `HeapCell.protNone`, `↦₈ₙ`, `↦ₙ`, `regionBlockProtNone`, `memRegionProtNone`, and their
`mmap`, `mprotect`, and `munmap` permission-transition bridges (`Satisfies.mapZeroProtNone_mapped`,
`Satisfies.setPermProtNone_of_pointsToBytes`, `Satisfies.setPermRw_of_pointsToBytesProtNone`,
`Satisfies.mmapFixedProtNone_owned`, `Satisfies.unmapNonFrozen_protNone`, `SepProp.NoProtNone`,
and `Satisfies.frame_perm_view`), along with negative `#guard_msgs` checks confirming that
`PROT_NONE` cells reject direct loads, stores, and read-write aliasing.
-/

@[expose] public section

set_option autoImplicit false

namespace Examples.Testing.SepProtNoneTest

open Arm64 ProofLib

/-! ## `mmap(PROT_NONE)` and `mprotect(PROT_RW)` -/

example {m : Memory} {P : SepProp} {base : BitVec 64} {len : Nat}
    (hP : m ⊨ P) (hmap : m.canMap base len = true) (hlen : len ≤ 2 ^ 64) :
    let m₁ := (m.mapZero base len).setPermNonFrozen base len Perm.protNone
    let m₂ := m₁.setPermNonFrozen base len Perm.rw
    m₁.allPerm (fun p => !p.frozen) base len = true ∧
    m₁.allPerm (·.mapped) base len = true ∧
    (m₂ ⊨ (base ↦ₛ List.replicate len 0#8) ∗ memMapped base len ∗ P) ∧
    m₂.readBytes base len = List.replicate len 0#8 := by
  intro m₁ m₂
  have hm₁ : m₁ ⊨ (base ↦ₙ List.replicate len 0#8) ∗ (memMapped base len ∗ P) :=
    Satisfies.mapZeroProtNone_mapped hP hmap hlen
  have hnf : m₁.allPerm (fun p => !p.frozen) base len = true := by
    simpa [List.length_replicate] using
      Satisfies.allPerm_not_frozen_of_pointsToBytesProtNone hm₁
  have hmp : m₁.allPerm (·.mapped) base len = true := by
    simpa [List.length_replicate] using
      Satisfies.allPerm_mapped_of_pointsToBytesProtNone hm₁
  have hm₂ : m₂ ⊨ (base ↦ₛ List.replicate len 0#8) ∗ (memMapped base len ∗ P) := by
    simpa [m₂, List.length_replicate] using
      Satisfies.setPermRw_of_pointsToBytesProtNone hm₁
  have hread : m₂.readBytes base len = List.replicate len 0#8 := by
    have ⟨_, hr⟩ := (IsBlock.pointsToBytes base (List.replicate len 0#8)).read hm₂
    simpa [List.length_replicate] using hr
  exact ⟨hnf, hmp, hm₂, hread⟩

/-! ## Round-Trip Byte Preservation (`Perm.rw` -> `Perm.protNone` -> `Perm.rw`) -/

example {m : Memory} {P : SepProp} {a : BitVec 64}
    (hm : m ⊨ (a ↦₈ 0x5a#8) ∗ P) :
    let m₁ := m.setPermNonFrozen a 1 Perm.protNone
    let m₂ := m₁.setPermNonFrozen a 1 Perm.rw
    m₁.perm a = some Perm.protNone ∧
    m₁.read8 a = 0x5a#8 ∧
    (m₂ ⊨ (a ↦₈ 0x5a#8) ∗ P) ∧
    m₂.perm a = some Perm.rw ∧
    m₂.read8 a = 0x5a#8 := by
  intro m₁ m₂
  have hm_slice : m ⊨ (a ↦ₛ [0x5a#8]) ∗ P := by simpa using hm
  have hm₁_slice : m₁ ⊨ (a ↦ₙ [0x5a#8]) ∗ P :=
    Satisfies.setPermProtNone_of_pointsToBytes hm_slice
  have hm₁ : m₁ ⊨ (a ↦₈ₙ 0x5a#8) ∗ P := by simpa using hm₁_slice
  have ⟨hr₁, hp₁⟩ := satisfies_pointsTo8ProtNone_frame hm₁
  have hm₂_slice : m₂ ⊨ (a ↦ₛ [0x5a#8]) ∗ P :=
    Satisfies.setPermRw_of_pointsToBytesProtNone hm₁_slice
  have hm₂ : m₂ ⊨ (a ↦₈ 0x5a#8) ∗ P := by simpa using hm₂_slice
  have ⟨hr₂, hp₂⟩ := satisfies_pointsTo8_frame hm₂
  exact ⟨hp₁, hr₁, hm₂, hp₂, hr₂⟩

/-! ## Exclusivity, Disjointness, `NoRO`, and `MAP_FIXED` / `munmap` -/

example (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) :
    ((a₁ ↦₈ₙ v₁) ∗ (a₂ ↦₈ₙ v₂)) ⊢ ⌜a₁ ≠ a₂⌝ ∗ (a₁ ↦₈ₙ v₁) ∗ (a₂ ↦₈ₙ v₂) :=
  pointsTo8ProtNone_disjoint a₁ a₂ v₁ v₂

example {m : Memory} {a : BitVec 64} {v₁ v₂ : BitVec 8} {R : SepProp}
    (h : m ⊨ ((a ↦₈ₙ v₁) ∗ (a ↦₈ₙ v₂)) ∗ R) : False :=
  not_satisfies_false_sepConj
    (Satisfies.mono (sepConj_mono_left (pointsTo8ProtNone_conflict a v₁ v₂)) h)

example {m : Memory} {a : BitVec 64} {v₁ v₂ : BitVec 8} {R : SepProp}
    (h : m ⊨ ((a ↦₈ₙ v₁) ∗ (a ↦₈ v₂)) ∗ R) : False :=
  not_satisfies_false_sepConj
    (Satisfies.mono (sepConj_mono_left (pointsTo8ProtNone_pointsTo8_conflict a v₁ v₂)) h)

example {m : Memory} {a b : BitVec 64} {v w : BitVec 8} {R : SepProp}
    (h : m ⊨ (a ↦₈ₙ v) ∗ (R ∗ (b ↦₈ w))) :
    m ⊨ (b ↦₈ w) ∗ ((a ↦₈ₙ v) ∗ R) := by
  sep_entail

example (a b c : BitVec 64) (v : BitVec 8) (bs : List (BitVec 8)) (n : Nat) :
    SepProp.NoRO ((a ↦₈ₙ v) ∗ (b ↦ₙ bs) ∗ memRegionProtNone c n) := by
  simp

example {m : Memory} {P : SepProp} {base : BitVec 64} {len : Nat}
    (h : m ⊨ memRegion base len ∗ (memMapped base len ∗ P)) (hlen : len ≤ 2 ^ 64) :
    let m_guard := ((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone
    m_guard.unmapNonFrozen base len ⊨ P := by
  intro m_guard
  have hguard : m_guard ⊨ (base ↦ₙ List.replicate len 0#8) ∗ (memMapped base len ∗ P) :=
    Satisfies.mmapFixedProtNone_owned h hlen
  have hreg : m_guard ⊨ memRegionProtNone base len ∗ (memMapped base len ∗ P) := by
    have hent := pointsToBytesProtNone_entails_memRegionProtNone base (List.replicate len 0#8)
    simpa [List.length_replicate] using Satisfies.mono (sepConj_mono_left hent) hguard
  exact Satisfies.unmapNonFrozen_protNone hreg

/-! ## Negative Checks: No Direct Loads, Stores, or RW Aliasing on `PROT_NONE` -/

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
example (a : BitVec 64) (v : BitVec 8) :
    SepBlock (a ↦₈ₙ v) a 1 (fun m => m.read8 a = v) :=
  inferInstance

/-- error: wp_sep_access -/
#guard_msgs (error, substring := true) in
example {a : BitVec 64} {v : BitVec 8} {R : SepProp} :
    SepLoad8 a ((a ↦₈ₙ v) ∗ R) v := by
  wp_sep_access

/-- error: wp_sep_access -/
#guard_msgs (error, substring := true) in
example {a : BitVec 64} {v w : BitVec 8} {R : SepProp} :
    SepStore8 a w ((a ↦₈ₙ v) ∗ R) ((a ↦₈ₙ w) ∗ R) := by
  wp_sep_access

/-- error: frame_split: no match -/
#guard_msgs (error, substring := true) in
example {m : Memory} {a : BitVec 64} {v : BitVec 8} {R : SepProp}
    (h : m ⊨ (a ↦₈ₙ v) ∗ R) :
    m ⊨ (a ↦₈ v) ∗ R := by
  sep_entail

/-! ## `SepProp.NoProtNone` and `Satisfies.frame_perm_view` -/

example (a b c d : BitVec 64) (v : BitVec 8) (w : BitVec 64) (bs : List (BitVec 8)) (n : Nat) :
    SepProp.NoProtNone
      ((a ↦₈ v) ∗ (b ↦₆₄ w) ∗ (c ↦ₛ bs) ∗ (d ↦ᵣ bs) ∗
       memRegion a n ∗ memMapped b n) := by
  simp (maxDischargeDepth := 64)

example (a b c d : BitVec 64) (v : BitVec 8) (w : BitVec 64) (bs : List (BitVec 8)) (n : Nat) :
    SepProp.NoProtNone
      ((a ↦₈ v) ∗ (b ↦₆₄ w) ∗ (c ↦ₛ bs) ∗ (d ↦ᵣ bs) ∗
       memRegion a n ∗ memMapped b n ∗ (∃∗ x : Nat, ⌜x = n⌝ ∗ emp)) := by
  simp (maxDischargeDepth := 64)

example (a : BitVec 64) (v : BitVec 8) : ¬ SepProp.NoProtNone (a ↦₈ₙ v) := by
  simp

example {m0 mf : Memory} {a g : BitVec 64} {v0 vf gv : BitVec 8} {R : SepProp}
    (hpre : m0 ⊨ (a ↦₈ v0) ∗ ((g ↦₈ₙ gv) ∗ R))
    (hperm : ∀ x, mf.perm x = m0.perm x)
    (hexec : ∀ F : SepProp, (m0 ⊨ (a ↦₈ v0) ∗ F) → (mf ⊨ (a ↦₈ vf) ∗ F)) :
    mf ⊨ (a ↦₈ vf) ∗ ((g ↦₈ₙ gv) ∗ R) := by
  obtain ⟨R_view, hpre_view, hrestore⟩ := Satisfies.frame_perm_view hpre
  exact hrestore (by simp) hperm (fun _ => rfl) (fun _ h => h) (fun _ h => h) (fun _ h => h)
    (fun _ h => h) (fun _ h => h) (hexec R_view hpre_view)

/-- error: `simp` made no progress -/
#guard_msgs (error, substring := true) in
example (a : BitVec 64) (v : BitVec 8) : SepProp.NoProtNone (a ↦₈ₙ v) := by
  simp only [SepProp.NoProtNone.pointsTo8]

end Examples.Testing.SepProtNoneTest
