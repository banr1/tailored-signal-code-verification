/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Tactic.BVDecide
public import Arm64
public import Arm64.Trusted.Process
public import ProofLib.SimpAttrs
public import ProofLib.Exec
public import ProofLib.BV.Arith
public import ProofLib.ReadWritevFrame
import Arm64.Trusted.Spec.SepLogic

/-!
# Frozen-Memory Invariant and Base Memory Interface

Establishes the base `Memory` representation lemmas over `read8`, `perm`, `isLazyFree`, and
`isAnon`, proves that every `Step` preserves frozen bytes (`Memory.KeepsFrozen`) and `symtab`, and
bridges dynamic `Program.fetchMem` from loaded `r-x` memory to static `Program.fetch`.
-/

@[expose] public section

namespace Arm64

/-- Convert `PState` to the 4-bit `nzcv` value (`[N, Z, C, V]`), inverse to `PState.ofBits4`. -/
def PState.toBits4 (ps : PState) : BitVec 4 :=
  (if ps.n then 8#4 else 0#4) |||
  (if ps.z then 4#4 else 0#4) |||
  (if ps.c then 2#4 else 0#4) |||
  (if ps.v then 1#4 else 0#4)

namespace Perm

@[simp] theorem rwx_protNone : Perm.protNone.rwx = Perm.protNone := rfl
@[simp] theorem rwx_ro : Perm.ro.rwx = Perm.ro := rfl
@[simp] theorem rwx_rw : Perm.rw.rwx = Perm.rw := rfl
@[simp] theorem rwx_rx : Perm.rx.rwx = Perm.rx := rfl
@[simp] theorem rwx_rwx (p : Perm) : p.rwx.rwx = p.rwx := rfl
@[simp] theorem rwx_r (p : Perm) : p.rwx.r = p.r := rfl
@[simp] theorem rwx_w (p : Perm) : p.rwx.w = p.w := rfl
@[simp] theorem rwx_x (p : Perm) : p.rwx.x = p.x := rfl
@[simp] theorem rwx_frozen (p : Perm) : p.rwx.frozen = p.frozen := rfl

end Perm

@[simp] theorem _root_.Option.map_rwx_some (p : Perm) : (some p).map Perm.rwx = some p.rwx := rfl
@[simp] theorem _root_.Option.map_rwx_none : (none : Option Perm).map Perm.rwx = none := rfl

namespace Memory

/-! ## Base interface of the representation -/

@[simp] theorem perm_map_rwx (m : Memory) (a : BitVec 64) : (m.perm a).map Perm.rwx = m.perm a := by
  unfold perm
  rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl

@[simp] theorem read8_write8 (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).read8 a2 = if a2 = a1 then v else m.read8 a2 := by
  unfold read8 write8
  by_cases h : a2 = a1 <;> simp [h]

@[simp] theorem perm_write8_apply (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).perm a2 = m.perm a2 := by
  unfold write8 rawPerm perm
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | p, _⟩ <;> rfl
  · simp [h]

@[simp] theorem isLazyFree_write8 (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).isLazyFree a2 = if a2 = a1 then false else m.isLazyFree a2 := by
  unfold write8 rawPerm isLazyFree
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
    · rfl
    · rfl
    · cases r <;> cases w <;> cases x <;> cases lf <;> rfl
  · simp [h]

@[simp] theorem isAnon_write8_apply (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8) :
    (m.write8 a1 v).isAnon a2 = m.isAnon a2 := by
  unfold write8 rawPerm isAnon
  by_cases h : a2 = a1
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells a2 with _ | ⟨_ | p, _⟩ <;> rfl
  · simp [h]

@[simp] theorem read8_empty (a : BitVec 64) : empty.read8 a = 0#8 := rfl
@[simp] theorem perm_empty (a : BitVec 64) : empty.perm a = none := rfl
@[simp] theorem isLazyFree_empty (a : BitVec 64) : empty.isLazyFree a = false := rfl
@[simp] theorem isAnon_empty (a : BitVec 64) : empty.isAnon a = false := rfl

@[simp] theorem read8_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).read8 a = bytes a := rfl
@[simp] theorem perm_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).perm a = (p a).map Perm.rwx := by
  unfold ofFn perm
  dsimp only
  cases p a <;> rfl
@[simp] theorem isLazyFree_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).isLazyFree a = match p a with | some q => q.lazyFree | none => false := by
  unfold ofFn isLazyFree
  dsimp only
  cases p a <;> rfl
@[simp] theorem isAnon_ofFn (bytes : BitVec 64 → BitVec 8) (p : BitVec 64 → Option Perm) (a : BitVec 64) :
    (ofFn bytes p).isAnon a = match p a with | some q => q.anon | none => false := by
  unfold ofFn isAnon
  dsimp only
  cases p a <;> rfl

theorem perm_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    perm ⟨f⟩ a = match f a with | some (some p, _) => some p.rwx | _ => none := rfl
theorem read8_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    read8 ⟨f⟩ a = match f a with | some (_, b) => b | none => 0#8 := rfl
theorem isLazyFree_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    isLazyFree ⟨f⟩ a = match f a with | some (some p, _) => p.lazyFree | _ => false := rfl
theorem isAnon_mk (f : BitVec 64 → Option (Option Perm × BitVec 8)) (a : BitVec 64) :
    isAnon ⟨f⟩ a = match f a with | some (some p, _) => p.anon | _ => false := rfl

theorem isLazyFree_eq_false_of_unmapped {m : Memory} {a : BitVec 64}
    (hu : (m.perm a).mapped = false) : m.isLazyFree a = false := by
  unfold perm at hu
  unfold isLazyFree
  cases hca : m.cells a with
  | none => rfl
  | some pb =>
    rcases pb with ⟨po, _⟩
    cases po with
    | none => rfl
    | some _ => simp [hca] at hu

theorem permNoLazy_eq_some_rw_iff {m : Memory} {a : BitVec 64} :
    m.permNoLazy a = some Perm.rw ↔ m.perm a = some Perm.rw ∧ m.isLazyFree a = false := by
  unfold permNoLazy perm isLazyFree Perm.rw Perm.rwx
  cases m.cells a with
  | none => simp
  | some pb =>
    rcases pb with ⟨po, _⟩
    cases po with
    | none => simp
    | some p =>
      cases p with
      | mk r w x lf an =>
        cases r <;> cases w <;> cases x <;> cases lf <;> simp

@[simp] theorem write8_write8_same (m : Memory) (a : BitVec 64) (x y : BitVec 8) :
    (m.write8 a x).write8 a y = m.write8 a y := by
  ext addr
  unfold write8 rawPerm
  by_cases h : addr = a
  · subst h
    dsimp only
    simp only [↓reduceIte]
    rcases m.cells addr with _ | ⟨_ | ⟨r, w, xv, lf, an⟩, _⟩
    · rfl
    · rfl
    · cases r <;> cases w <;> cases xv <;> cases lf <;> rfl
  · simp [h]

theorem write8_write8_comm (m : Memory) (a₁ a₂ : BitVec 64) (v₁ v₂ : BitVec 8) (hne : a₁ ≠ a₂) :
    (m.write8 a₁ v₁).write8 a₂ v₂ = (m.write8 a₂ v₂).write8 a₁ v₁ := by
  ext addr
  unfold write8 rawPerm
  by_cases h2 : addr = a₂ <;> by_cases h1 : addr = a₁ <;> simp_all

@[simp] theorem read8_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm)
    (a : BitVec 64) : (m.mapFresh base len p).read8 a = m.read8 a := by
  rw [mapFresh, read8_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem perm_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.mapFresh base len p).perm a =
      if (a - base).toNat < len && !(m.perm a).mapped then some p.rwx else m.perm a := by
  rw [mapFresh, perm_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isLazyFree_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.mapFresh base len p).isLazyFree a =
      if (a - base).toNat < len && !(m.perm a).mapped then p.lazyFree else m.isLazyFree a := by
  rw [mapFresh, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isAnon_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.mapFresh base len p).isAnon a =
      if (a - base).toNat < len && !(m.perm a).mapped then p.anon else m.isAnon a := by
  rw [mapFresh, isAnon_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem perm_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapWritable base len).perm a =
      if (a - base).toNat < len && (m.perm a).w then none else m.perm a := by
  rw [unmapWritable, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).w) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem read8_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapWritable base len).read8 a =
      if (a - base).toNat < len && (m.perm a).w then 0#8 else m.read8 a := by
  rw [unmapWritable, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).w) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isLazyFree_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapWritable base len).isLazyFree a =
      if (a - base).toNat < len && (m.perm a).w then false else m.isLazyFree a := by
  rw [unmapWritable, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).w) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isAnon_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapWritable base len).isAnon a =
      if (a - base).toNat < len && (m.perm a).w then false else m.isAnon a := by
  rw [unmapWritable, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).w) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem perm_mapZero (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).perm a =
      if (a - base).toNat < len && !(m.perm a).mapped then some Perm.rw else m.perm a := by
  rw [mapZero, perm_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem read8_mapZero (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).read8 a =
      if (a - base).toNat < len && !(m.perm a).mapped then 0#8 else m.read8 a := by
  rw [mapZero, read8_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_mapZero (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).isLazyFree a = m.isLazyFree a := by
  rw [mapZero, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [h.1, h.2, Bool.not_false, Bool.and_self, ↓reduceIte]
    exact (isLazyFree_eq_false_of_unmapped h.2).symm
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isAnon_mapZero (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.mapZero base len).isAnon a =
      if (a - base).toNat < len && !(m.perm a).mapped then true else m.isAnon a := by
  rw [mapZero, isAnon_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).mapped) = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem perm_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapNonFrozen base len).perm a =
      if (a - base).toNat < len && !(m.perm a).frozen then none else m.perm a := by
  rw [unmapNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem read8_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapNonFrozen base len).read8 a =
      if (a - base).toNat < len && !(m.perm a).frozen then 0#8 else m.read8 a := by
  rw [unmapNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isLazyFree_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapNonFrozen base len).isLazyFree a =
      if (a - base).toNat < len && !(m.perm a).frozen then false else m.isLazyFree a := by
  rw [unmapNonFrozen, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isAnon_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.unmapNonFrozen base len).isAnon a =
      if (a - base).toNat < len && !(m.perm a).frozen then false else m.isAnon a := by
  rw [unmapNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem perm_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).perm a =
      if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then some p.rwx else m.perm a := by
  rw [setPermNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem read8_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).read8 a = m.read8 a := by
  rw [setPermNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_setPermNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).isLazyFree a = m.isLazyFree a := by
  rw [setPermNonFrozen, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isLazyFree_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    (m.setPermNonFrozen base len p).isLazyFree = m.isLazyFree :=
  funext (isLazyFree_setPermNonFrozen_apply m base len p)

@[simp] theorem isAnon_setPermNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) (a : BitVec 64) :
    (m.setPermNonFrozen base len p).isAnon a = m.isAnon a := by
  rw [setPermNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    (m.setPermNonFrozen base len p).isAnon = m.isAnon :=
  funext (isAnon_setPermNonFrozen_apply m base len p)

theorem perm_zeroNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).perm a = m.perm a := by
  rw [zeroNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    unfold perm
    rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem perm_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.zeroNonFrozen base len).perm = m.perm :=
  funext (perm_zeroNonFrozen_apply m base len)

theorem read8_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).read8 a =
      if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then 0#8 else m.read8 a := by
  rw [zeroNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isLazyFree_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).isLazyFree a =
      if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then false else m.isLazyFree a := by
  rw [zeroNonFrozen, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    unfold perm at hm ⊢
    rcases hca : m.cells a with _ | ⟨_ | p, _⟩
    · simp [hca] at hm
    · simp [hca] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_zeroNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.zeroNonFrozen base len).isAnon a = m.isAnon a := by
  rw [zeroNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    unfold perm at hm ⊢
    unfold isAnon
    rcases hca : m.cells a with _ | ⟨_ | p, _⟩
    · simp [hca] at hm
    · simp [hca] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.zeroNonFrozen base len).isAnon = m.isAnon :=
  funext (isAnon_zeroNonFrozen_apply m base len)

theorem perm_madvFreeNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).perm a = m.perm a := by
  rw [madvFreeNonFrozen, perm_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    unfold perm
    rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem perm_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.madvFreeNonFrozen base len).perm = m.perm :=
  funext (perm_madvFreeNonFrozen_apply m base len)

@[simp] theorem read8_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).read8 a = m.read8 a := by
  rw [madvFreeNonFrozen, read8_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

theorem isLazyFree_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).isLazyFree a =
      if (a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen then true else m.isLazyFree a := by
  rw [madvFreeNonFrozen, isLazyFree_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    rcases hpa : m.perm a with _ | p
    · simp [hpa, Option.mapped] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_madvFreeNonFrozen_apply (m : Memory) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (m.madvFreeNonFrozen base len).isAnon a = m.isAnon a := by
  rw [madvFreeNonFrozen, isAnon_mk]
  by_cases h : ((a - base).toNat < len && (m.perm a).mapped && !(m.perm a).frozen) = true
  · simp only [h, ↓reduceIte]
    have hm : (m.perm a).mapped = true := by simp only [Bool.and_eq_true] at h; exact h.1.2
    unfold perm at hm ⊢
    unfold isAnon
    rcases hca : m.cells a with _ | ⟨_ | p, _⟩
    · simp [hca] at hm
    · simp [hca] at hm
    · rfl
  · simp only [h, ↓reduceIte, Bool.false_eq_true]; rfl

@[simp] theorem isAnon_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    (m.madvFreeNonFrozen base len).isAnon = m.isAnon :=
  funext (isAnon_madvFreeNonFrozen_apply m base len)

theorem perm_remapRw_raw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).perm a =
      if (m.perm a).frozen then m.perm a
      else if (a - newBase).toNat < newSize then some Perm.rw
      else if (a - oldBase).toNat < oldSize then none
      else m.perm a := by
  rw [remapRw, perm_mk]
  by_cases hf : (m.perm a).frozen = true
  · simp only [hf, ↓reduceIte]; rfl
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte]
      split <;> rfl
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - oldBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl

theorem read8_remapRw_raw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).read8 a =
      if (m.perm a).frozen then m.read8 a
      else if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.read8 (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else 0#8
      else if (a - oldBase).toNat < oldSize then 0#8
      else m.read8 a := by
  rw [remapRw, read8_mk]
  by_cases hf : (m.perm a).frozen = true
  · simp only [hf, ↓reduceIte]; rfl
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte]
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - oldBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl

theorem isLazyFree_remapRw_raw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).isLazyFree a =
      if (m.perm a).frozen then m.isLazyFree a
      else if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.isLazyFree (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else false
      else if (a - oldBase).toNat < oldSize then false
      else m.isLazyFree a := by
  rw [remapRw, isLazyFree_mk]
  by_cases hf : (m.perm a).frozen = true
  · simp only [hf, ↓reduceIte]; rfl
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - newBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - oldBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl

theorem isAnon_remapRw_raw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).isAnon a =
      if (m.perm a).frozen then m.isAnon a
      else if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.isAnon (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else true
      else if (a - oldBase).toNat < oldSize then false
      else m.isAnon a := by
  rw [remapRw, isAnon_mk]
  by_cases hf : (m.perm a).frozen = true
  · simp only [hf, ↓reduceIte]; rfl
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    by_cases hn : (a - newBase).toNat < newSize
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - newBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl
    · simp only [hn, ↓reduceIte]
      by_cases ho : (a - oldBase).toNat < oldSize
      · simp only [ho, ↓reduceIte]
      · simp only [ho, ↓reduceIte]; rfl

/-! ## Permissions are unchanged by writes -/

@[simp] theorem perm_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).perm = m.perm := funext fun b => perm_write8_apply m a b v
@[simp] theorem perm_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).perm = m.perm := by simp only [write16, perm_write8]
@[simp] theorem perm_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).perm = m.perm := by simp only [write32, perm_write8]
@[simp] theorem perm_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).perm = m.perm := by simp only [write64, perm_write8]
@[simp] theorem perm_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).perm = m.perm := by simp only [write128, perm_write64]
@[simp] theorem perm_writeSized (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (m.writeSized sz a v).perm = m.perm := by
  cases sz <;> simp only [writeSized, perm_write8, perm_write16, perm_write32, perm_write64]
@[simp] theorem perm_writeSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) : (m.writeSimdSized sz a v).perm = m.perm := by
  cases sz <;> simp only [writeSimdSized, perm_write8, perm_write16, perm_write32, perm_write64,
    perm_write128]
@[simp] theorem perm_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).perm = m.perm := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => exact (ih _ _).trans (perm_write8 _ _ _)

@[simp] theorem isAnon_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon = m.isAnon := funext fun b => isAnon_write8_apply m a b v
@[simp] theorem isAnon_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).isAnon = m.isAnon := by simp only [write16, isAnon_write8]
@[simp] theorem isAnon_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).isAnon = m.isAnon := by simp only [write32, isAnon_write8]
@[simp] theorem isAnon_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).isAnon = m.isAnon := by simp only [write64, isAnon_write8]
@[simp] theorem isAnon_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128) :
    (m.write128 a v).isAnon = m.isAnon := by simp only [write128, isAnon_write64]
@[simp] theorem isAnon_writeSized (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (m.writeSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [writeSized, isAnon_write8, isAnon_write16, isAnon_write32, isAnon_write64]
@[simp] theorem isAnon_writeSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) : (m.writeSimdSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [writeSimdSized, isAnon_write8, isAnon_write16, isAnon_write32,
    isAnon_write64, isAnon_write128]
@[simp] theorem isAnon_writeBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) :
    (m.writeBytes a bs).isAnon = m.isAnon := by
  induction bs generalizing m a with
  | nil => rfl
  | cons b bs ih => exact (ih _ _).trans (isAnon_write8 _ _ _)

theorem isLazyFree_write8_of_false {m : Memory} (a : BitVec 64) (v : BitVec 8) {b : BitVec 64}
    (hb : m.isLazyFree b = false) : (m.write8 a v).isLazyFree b = false := by
  rw [isLazyFree_write8]
  split
  · rfl
  · exact hb
theorem isLazyFree_write16_of_false {m : Memory} (a : BitVec 64) (v : BitVec 16) {b : BitVec 64}
    (hb : m.isLazyFree b = false) : (m.write16 a v).isLazyFree b = false := by
  unfold write16; exact isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _ hb)
theorem isLazyFree_write32_of_false {m : Memory} (a : BitVec 64) (v : BitVec 32) {b : BitVec 64}
    (hb : m.isLazyFree b = false) : (m.write32 a v).isLazyFree b = false := by
  unfold write32
  exact isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _
    (isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _ hb)))
theorem isLazyFree_write64_of_false {m : Memory} (a : BitVec 64) (v : BitVec 64) {b : BitVec 64}
    (hb : m.isLazyFree b = false) : (m.write64 a v).isLazyFree b = false := by
  unfold write64
  exact isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _
    (isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _
      (isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _
        (isLazyFree_write8_of_false _ _ (isLazyFree_write8_of_false _ _ hb)))))))
theorem isLazyFree_write128_of_false {m : Memory} (a : BitVec 64) (v : BitVec 128) {b : BitVec 64}
    (hb : m.isLazyFree b = false) : (m.write128 a v).isLazyFree b = false := by
  unfold write128; exact isLazyFree_write64_of_false _ _ (isLazyFree_write64_of_false _ _ hb)
theorem isLazyFree_writeBytes_of_false {m : Memory} (a : BitVec 64) (bs : List (BitVec 8))
    {b : BitVec 64} (hb : m.isLazyFree b = false) : (m.writeBytes a bs).isLazyFree b = false := by
  induction bs generalizing m a with
  | nil => exact hb
  | cons x xs ih => exact ih _ (isLazyFree_write8_of_false _ _ hb)

/-- `allPerm` only depends on `perm`. -/
theorem allPerm_congr {m m' : Memory} (h : m'.perm = m.perm) (p : Option Perm → Bool)
    (a : BitVec 64) (n : Nat) : m'.allPerm p a n = m.allPerm p a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [allPerm, h, ih]

theorem allNoLazyFree_congr {m m' : Memory} (h : m'.isLazyFree = m.isLazyFree)
    (a : BitVec 64) (n : Nat) : m'.allNoLazyFree a n = m.allNoLazyFree a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [allNoLazyFree, h, ih]

theorem allAnon_congr {m m' : Memory} (h : m'.isAnon = m.isAnon)
    (a : BitVec 64) (n : Nat) : m'.allAnon a n = m.allAnon a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [allAnon, h, ih]

theorem canRead_congr {m m' : Memory} (hp : m'.perm = m.perm) (hlf : m'.isLazyFree = m.isLazyFree)
    (a : BitVec 64) (n : Nat) : m'.canRead a n = m.canRead a n := by
  unfold canRead; rw [allPerm_congr hp, allNoLazyFree_congr hlf]
theorem canWrite_congr {m m' : Memory} (h : m'.perm = m.perm) (a : BitVec 64) (n : Nat) :
    m'.canWrite a n = m.canWrite a n := allPerm_congr h _ a n
theorem canMap_congr {m m' : Memory} (h : m'.perm = m.perm) (a : BitVec 64) (n : Nat) :
    m'.canMap a n = m.canMap a n := allPerm_congr h _ a n

@[simp] theorem canMap_write8 (m : Memory) (a : BitVec 64) (v : BitVec 8)
    (b : BitVec 64) (n : Nat) : (m.write8 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write8 m a v) b n
@[simp] theorem canMap_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16)
    (b : BitVec 64) (n : Nat) : (m.write16 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write16 m a v) b n
@[simp] theorem canMap_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32)
    (b : BitVec 64) (n : Nat) : (m.write32 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write32 m a v) b n
@[simp] theorem canMap_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64)
    (b : BitVec 64) (n : Nat) : (m.write64 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write64 m a v) b n
@[simp] theorem canMap_write128 (m : Memory) (a : BitVec 64) (v : BitVec 128)
    (b : BitVec 64) (n : Nat) : (m.write128 a v).canMap b n = m.canMap b n :=
  canMap_congr (perm_write128 m a v) b n

/-- `allPerm` as a bounded quantifier. -/
theorem allPerm_iff (m : Memory) (p : Option Perm → Bool) (a : BitVec 64) (n : Nat) :
    m.allPerm p a n = true ↔ ∀ i < n, p (m.perm (a + BitVec.ofNat 64 i)) = true := by
  induction n generalizing a with
  | zero => simp [allPerm]
  | succ n ih =>
    simp only [allPerm, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := hs i (by omega)
        have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rwa [e] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (i + 1) (by omega)

theorem allPerm_mono {m m' : Memory} {p : Option Perm → Bool}
    (hp : ∀ a, p (m.perm a) = true → p (m'.perm a) = true) (a : BitVec 64) (n : Nat)
    (h : m.allPerm p a n = true) : m'.allPerm p a n = true := by
  rw [allPerm_iff] at h ⊢
  exact fun i hi => hp _ (h i hi)

theorem allNoLazyFree_iff (m : Memory) (a : BitVec 64) (n : Nat) :
    m.allNoLazyFree a n = true ↔ ∀ i < n, m.isLazyFree (a + BitVec.ofNat 64 i) = false := by
  induction n generalizing a with
  | zero => simp [allNoLazyFree]
  | succ n ih =>
    simp only [allNoLazyFree, Bool.and_eq_true, Bool.not_eq_true', ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := hs i (by omega)
        have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rwa [e] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (i + 1) (by omega)

theorem allAnon_iff (m : Memory) (a : BitVec 64) (n : Nat) :
    m.allAnon a n = true ↔ ∀ i < n, m.isAnon (a + BitVec.ofNat 64 i) = true := by
  induction n generalizing a with
  | zero => simp [allAnon]
  | succ n ih =>
    simp only [allAnon, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      rcases i with _ | i
      · simpa using h0
      · have := hs i (by omega)
        have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
          apply BitVec.eq_of_toNat_eq; simp; omega
        rwa [e] at this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have e : a + 1#64 + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (i + 1) (by omega)

theorem allNoLazyFree_mono {m m' : Memory}
    (hlf : ∀ a, m.isLazyFree a = false → m'.isLazyFree a = false) (a : BitVec 64) (n : Nat)
    (h : m.allNoLazyFree a n = true) : m'.allNoLazyFree a n = true := by
  rw [allNoLazyFree_iff] at h ⊢
  exact fun i hi => hlf _ (h i hi)

theorem allAnon_mono {m m' : Memory}
    (han : ∀ a, m.isAnon a = true → m'.isAnon a = true) (a : BitVec 64) (n : Nat)
    (h : m.allAnon a n = true) : m'.allAnon a n = true := by
  rw [allAnon_iff] at h ⊢
  exact fun i hi => han _ (h i hi)

theorem canRead_of_perm_eq_mono {m m' : Memory} (hp : m'.perm = m.perm)
    (hlf : ∀ x, m.isLazyFree x = false → m'.isLazyFree x = false)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : m'.canRead a n = true := by
  unfold canRead at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  exact ⟨(allPerm_congr hp _ a n).trans h.1, allNoLazyFree_mono hlf a n h.2⟩

theorem canRead_write8_of_canRead {m : Memory} (wAddr : BitVec 64) (wVal : BitVec 8)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : (m.write8 wAddr wVal).canRead a n = true :=
  canRead_of_perm_eq_mono (perm_write8 m wAddr wVal) (fun _ => isLazyFree_write8_of_false wAddr wVal) h
theorem canRead_write16_of_canRead {m : Memory} (wAddr : BitVec 64) (wVal : BitVec 16)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : (m.write16 wAddr wVal).canRead a n = true :=
  canRead_of_perm_eq_mono (perm_write16 m wAddr wVal) (fun _ => isLazyFree_write16_of_false wAddr wVal) h
theorem canRead_write32_of_canRead {m : Memory} (wAddr : BitVec 64) (wVal : BitVec 32)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : (m.write32 wAddr wVal).canRead a n = true :=
  canRead_of_perm_eq_mono (perm_write32 m wAddr wVal) (fun _ => isLazyFree_write32_of_false wAddr wVal) h
theorem canRead_write64_of_canRead {m : Memory} (wAddr : BitVec 64) (wVal : BitVec 64)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : (m.write64 wAddr wVal).canRead a n = true :=
  canRead_of_perm_eq_mono (perm_write64 m wAddr wVal) (fun _ => isLazyFree_write64_of_false wAddr wVal) h
theorem canRead_write128_of_canRead {m : Memory} (wAddr : BitVec 64) (wVal : BitVec 128)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) : (m.write128 wAddr wVal).canRead a n = true :=
  canRead_of_perm_eq_mono (perm_write128 m wAddr wVal) (fun _ => isLazyFree_write128_of_false wAddr wVal) h

theorem canRead_mapZero_of_canRead {m : Memory} (base : BitVec 64) (len : Nat)
    {a : BitVec 64} {n : Nat} (h : m.canRead a n = true) :
    (m.mapZero base len).canRead a n = true := by
  unfold canRead at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨allPerm_mono (fun x hx => ?_) a n h.1,
    (allNoLazyFree_congr (funext (isLazyFree_mapZero m base len)) a n).trans h.2⟩
  rw [perm_mapZero]
  split
  · rfl
  · exact hx

theorem canWrite_mapZero_of_canWrite {m : Memory} (base : BitVec 64) (len : Nat)
    {a : BitVec 64} {n : Nat} (h : m.canWrite a n = true) :
    (m.mapZero base len).canWrite a n = true := by
  refine allPerm_mono (fun x hx => ?_) a n h
  rw [perm_mapZero]
  split
  · rfl
  · exact hx

/-- Split `allPerm` over `[a, a + (n + k))` into `[a, a + n)` and `[a + n, a + n + k)`. -/
theorem allPerm_add (m : Memory) (p : Option Perm → Bool) (a : BitVec 64) (n k : Nat) :
    m.allPerm p a (n + k) = (m.allPerm p a n && m.allPerm p (a + BitVec.ofNat 64 n) k) := by
  induction n generalizing a with
  | zero => simp [allPerm]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [allPerm, ih, Bool.and_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]

theorem allNoLazyFree_add (m : Memory) (a : BitVec 64) (n k : Nat) :
    m.allNoLazyFree a (n + k) = (m.allNoLazyFree a n && m.allNoLazyFree (a + BitVec.ofNat 64 n) k) := by
  induction n generalizing a with
  | zero => simp [allNoLazyFree]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [allNoLazyFree, ih, Bool.and_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]

theorem allAnon_add (m : Memory) (a : BitVec 64) (n k : Nat) :
    m.allAnon a (n + k) = (m.allAnon a n && m.allAnon (a + BitVec.ofNat 64 n) k) := by
  induction n generalizing a with
  | zero => simp [allAnon]
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [allAnon, ih, Bool.and_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 n = a + BitVec.ofNat 64 (n + 1) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [e]

/-- Split the first byte off a `canRead` check (automation for ranges spanning several blocks). -/
theorem canRead_succ_of (m : Memory) (a : BitVec 64) (n : Nat)
    (h1 : m.canRead a 1 = true) (h2 : m.canRead (a + 1#64) n = true) :
    m.canRead a (n + 1) = true := by
  unfold canRead at *
  rw [Bool.and_eq_true] at h1 h2 ⊢
  rw [Nat.add_comm, allPerm_add, allNoLazyFree_add]
  simp [h1, h2]

theorem canWrite_succ_of (m : Memory) (a : BitVec 64) (n : Nat)
    (h1 : m.canWrite a 1 = true) (h2 : m.canWrite (a + 1#64) n = true) :
    m.canWrite a (n + 1) = true := by
  unfold canWrite at *
  rw [Nat.add_comm, allPerm_add]; simp [h1, h2]

/-! ## `KeepsFrozen` -/

@[simp, arm64_norm, wp_norm]
theorem KeepsFrozen.refl (m : Memory) : m.KeepsFrozen m := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsFrozen.trans {m₁ m₂ m₃ : Memory} (h₁ : m₁.KeepsFrozen m₂) (h₂ : m₂.KeepsFrozen m₃) :
    m₁.KeepsFrozen m₃ := by
  intro a ha
  obtain ⟨hb₁, hp₁, hlf₁, ha₁⟩ := h₁ a ha
  have ha₂ : m₂.Frozen a := by unfold Frozen at *; rw [hp₁]; exact ha
  obtain ⟨hb₂, hp₂, hlf₂, h_an₂⟩ := h₂ a ha₂
  exact ⟨hb₂.trans hb₁, hp₂.trans hp₁, hlf₂.trans hlf₁, h_an₂.trans ha₁⟩

/-- Same permissions and anonymous bits, and the contents / `isLazyFree` only differ at writable bytes. -/
theorem KeepsFrozen.of_perm_eq {m m' : Memory} (hp : m'.perm = m.perm)
    (hb : ∀ a, m.Frozen a → m'.read8 a = m.read8 a)
    (hlf : ∀ a, m.Frozen a → m'.isLazyFree a = m.isLazyFree a := by intros; rfl)
    (hanon : m'.isAnon = m.isAnon := by simp) : m.KeepsFrozen m' :=
  fun a ha => ⟨hb a ha, by rw [hp], hlf a ha, by rw [hanon]⟩

/-- A byte whose permission allows a store (`w && !x`) is not frozen. -/
theorem not_frozen_of_writable {m : Memory} {a : BitVec 64}
    (h : ((m.perm a).w && !(m.perm a).x) = true) : ¬ m.Frozen a := by
  unfold Frozen
  rcases hperm : m.perm a with _ | p <;>
    simp [hperm, Option.w, Option.x, Option.frozen, Perm.frozen] at h ⊢
  intro _; exact h.1

/-- If `[a, a + n)` is writable, every frozen byte lies outside it. -/
theorem ne_of_canWrite {m : Memory} {a : BitVec 64} {n : Nat} (h : m.canWrite a n = true)
    {b : BitVec 64} (hb : m.Frozen b) {i : Nat} (hi : i < n) : b ≠ a + BitVec.ofNat 64 i := by
  rintro rfl
  exact not_frozen_of_writable ((allPerm_iff m _ a n).1 h i hi) hb

theorem keepsFrozen_write8 {m : Memory} {a : BitVec 64} (h : m.canWrite a 1 = true)
    (v : BitVec 8) : m.KeepsFrozen (m.write8 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp)
    (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    simp only [BitVec.add_zero] at h0; simp [h0]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    simp only [BitVec.add_zero] at h0; simp [h0]

theorem keepsFrozen_write16 {m : Memory} {a : BitVec 64} (h : m.canWrite a 2 = true)
    (v : BitVec 16) : m.KeepsFrozen (m.write16 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    simp only [write16, read8_write8, h0, h1, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    simp only [write16, isLazyFree_write8, h0, h1, ↓reduceIte]

theorem keepsFrozen_write32 {m : Memory} {a : BitVec 64} (h : m.canWrite a 4 = true)
    (v : BitVec 32) : m.KeepsFrozen (m.write32 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    simp only [write32, read8_write8, h0, h1, h2, h3, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    simp only [write32, isLazyFree_write8, h0, h1, h2, h3, ↓reduceIte]

theorem keepsFrozen_write64 {m : Memory} {a : BitVec 64} (h : m.canWrite a 8 = true)
    (v : BitVec 64) : m.KeepsFrozen (m.write64 a v) := by
  refine KeepsFrozen.of_perm_eq (by simp) (fun b hb => ?_) (fun b hb => ?_)
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    have h4 := ne_of_canWrite h hb (i := 4) (by omega)
    have h5 := ne_of_canWrite h hb (i := 5) (by omega)
    have h6 := ne_of_canWrite h hb (i := 6) (by omega)
    have h7 := ne_of_canWrite h hb (i := 7) (by omega)
    simp only [write64, read8_write8, h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]
  · have h0 := ne_of_canWrite h hb (i := 0) (by omega)
    have h1 := ne_of_canWrite h hb (i := 1) (by omega)
    have h2 := ne_of_canWrite h hb (i := 2) (by omega)
    have h3 := ne_of_canWrite h hb (i := 3) (by omega)
    have h4 := ne_of_canWrite h hb (i := 4) (by omega)
    have h5 := ne_of_canWrite h hb (i := 5) (by omega)
    have h6 := ne_of_canWrite h hb (i := 6) (by omega)
    have h7 := ne_of_canWrite h hb (i := 7) (by omega)
    simp only [write64, isLazyFree_write8, h0, h1, h2, h3, h4, h5, h6, h7, ↓reduceIte]

theorem keepsFrozen_write128 {m : Memory} {a : BitVec 64} (h : m.canWrite a 16 = true)
    (v : BitVec 128) : m.KeepsFrozen (m.write128 a v) := by
  have h' := h
  unfold canWrite at h'
  rw [show (16 : Nat) = 8 + 8 from rfl, allPerm_add, Bool.and_eq_true] at h'
  refine (keepsFrozen_write64 h'.1 _).trans (keepsFrozen_write64 ?_ _)
  rw [canWrite_congr (perm_write64 _ _ _)]
  exact h'.2

theorem keepsFrozen_writeSized {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : m.canWrite a sz.bytes = true) (v : BitVec 64) : m.KeepsFrozen (m.writeSized sz a v) := by
  cases sz
  · exact keepsFrozen_write8 h _
  · exact keepsFrozen_write16 h _
  · exact keepsFrozen_write32 h _
  · exact keepsFrozen_write64 h _

theorem keepsFrozen_writeSimdSized {m : Memory} {sz : SimdMemSize} {a : BitVec 64}
    (h : m.canWrite a sz.bytes = true) (v : BitVec 128) :
    m.KeepsFrozen (m.writeSimdSized sz a v) := by
  cases sz
  · exact keepsFrozen_write8 h _
  · exact keepsFrozen_write16 h _
  · exact keepsFrozen_write32 h _
  · exact keepsFrozen_write64 h _
  · exact keepsFrozen_write128 h _

theorem keepsFrozen_writeBytes {m : Memory} {a : BitVec 64} (bs : List (BitVec 8))
    (h : m.canWrite a bs.length = true) : m.KeepsFrozen (m.writeBytes a bs) := by
  induction bs generalizing m a with
  | nil => exact KeepsFrozen.refl m
  | cons b bs ih =>
    unfold canWrite allPerm at h
    simp only [List.length_cons, Bool.and_eq_true] at h
    have h1 : m.canWrite a 1 = true := by simp [canWrite, allPerm, h.1]
    have h2 : (m.write8 a b).canWrite (a + 1#64) bs.length = true := by
      rw [canWrite_congr (perm_write8 _ _ _)]
      exact h.2
    exact (keepsFrozen_write8 h1 b).trans (ih h2)

theorem keepsFrozen_getrandom {m : Memory} {buf : BitVec 64} {n : Nat}
    (h : ¬(!m.canWrite buf n) = true) (f : Nat → BitVec 8) :
    m.KeepsFrozen (m.writeBytes buf ((List.range n).map f)) := by
  apply keepsFrozen_writeBytes
  simpa using h

theorem canWrite_take_of_le {m : Memory} {a : BitVec 64} {k n : Nat}
    (h : m.canWrite a n = true) (hle : k ≤ n) : m.canWrite a k = true := by
  induction k generalizing a n with
  | zero => simp [canWrite, allPerm]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      unfold canWrite allPerm at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih h.2 (by omega)⟩

theorem keepsFrozen_writeBytes_le {m : Memory} {buf : BitVec 64} {n : Nat}
    (bs : List (BitVec 8)) (h : ¬(!m.canWrite buf n) = true) (hle : bs.length ≤ n) :
    m.KeepsFrozen (m.writeBytes buf bs) :=
  keepsFrozen_writeBytes bs (canWrite_take_of_le (by simpa using h) hle)

theorem keepsFrozen_writeBytes_take {m : Memory} {buf : BitVec 64} {n : Nat}
    (xs : List (BitVec 8)) (h : ¬(!m.canWrite buf n) = true) :
    m.KeepsFrozen (m.writeBytes buf (xs.take n)) :=
  keepsFrozen_writeBytes_le (xs.take n) h (List.length_take_le n xs)

theorem keepsFrozen_writeStat {m : Memory} {statbuf : BitVec 64} (e : FsEntry)
    (h : ¬(!m.canWrite statbuf 128) = true) :
    m.KeepsFrozen (m.writeBytes statbuf (encodeLinuxStat e)) :=
  keepsFrozen_writeBytes_le (encodeLinuxStat e) h
    (by cases e <;> simp [encodeLinuxStat, leBytes64, leBytes32])

theorem keepsFrozen_writeAffinity {m : Memory} {mask : BitVec 64}
    (h : ¬(!m.canWrite mask 8) = true) :
    m.KeepsFrozen (m.writeBytes mask SCHED_AFFINITY_MASK) :=
  keepsFrozen_writeBytes_le SCHED_AFFINITY_MASK h (by simp [SCHED_AFFINITY_MASK])

theorem keepsFrozen_writeClock {m : Memory} {tp : BitVec 64} (ts : Timespec)
    (h : ¬(!m.canWrite tp 16) = true) :
    m.KeepsFrozen (m.writeBytes tp (encodeTimespec ts)) :=
  keepsFrozen_writeBytes_le (encodeTimespec ts) h (Nat.le_refl _)

theorem mapped_of_frozen {m : Memory} {a : BitVec 64} (ha : m.Frozen a) :
    (m.perm a).mapped = true := by
  unfold Frozen at ha
  rcases hperm : m.perm a with _ | p <;>
    simp [hperm, Option.frozen, Option.mapped] at ha ⊢

theorem keepsFrozen_mapFresh (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    m.KeepsFrozen (m.mapFresh base len p) := by
  intro a ha
  have hm := mapped_of_frozen ha
  have hne : m.perm a ≠ none := by intro h; simp [h, Option.mapped] at hm
  have hcell : (m.mapFresh base len p).cells a = m.cells a := by simp [mapFresh, hne]
  simp [read8, perm, isLazyFree, isAnon, hcell]

theorem keepsFrozen_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen (m.unmapWritable base len) := by
  intro a ha
  have hw : (m.perm a).w = false := by
    unfold Frozen at ha
    rcases hperm : m.perm a with _ | p <;>
      simp [hperm, Option.frozen, Perm.frozen, Option.w] at ha ⊢
    exact ha.2
  have hcell : (m.unmapWritable base len).cells a = m.cells a := by simp [unmapWritable, hw]
  simp [read8, perm, isLazyFree, isAnon, hcell]

theorem keepsFrozen_mapZero (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen (m.mapZero base len) := by
  intro a ha
  have hm := mapped_of_frozen ha
  have hne : m.perm a ≠ none := by intro h; simp [h, Option.mapped] at hm
  have hcell : (m.mapZero base len).cells a = m.cells a := by simp [mapZero, hne]
  simp [read8, perm, isLazyFree, isAnon, hcell]

theorem keepsFrozen_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen (m.unmapNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  have hcell : (m.unmapNonFrozen base len).cells a = m.cells a := by simp [unmapNonFrozen, hf]
  simp [read8, perm, isLazyFree, isAnon, hcell]

theorem keepsFrozen_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    m.KeepsFrozen (m.setPermNonFrozen base len p) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  have hcell : (m.setPermNonFrozen base len p).cells a = m.cells a := by simp [setPermNonFrozen, hf]
  simp [read8, perm, isLazyFree, isAnon, hcell]

theorem keepsFrozen_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen (m.zeroNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [read8_zeroNonFrozen, perm_zeroNonFrozen_apply, isLazyFree_zeroNonFrozen, isAnon_zeroNonFrozen_apply, hf]

theorem keepsFrozen_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen (m.madvFreeNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [read8_madvFreeNonFrozen, perm_madvFreeNonFrozen_apply, isLazyFree_madvFreeNonFrozen,
    isAnon_madvFreeNonFrozen_apply, hf]

/-- The memory of a `MAP_FIXED` `PROT_NONE` `mmap` (`execMmap`) keeps frozen bytes. -/
theorem keepsFrozen_mmapFixedProtNone (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen
      (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone) :=
  ((keepsFrozen_unmapNonFrozen m base len).trans (keepsFrozen_mapZero _ base len)).trans
    (keepsFrozen_setPermNonFrozen _ base len _)

/-- The memory of a non-`MAP_FIXED` `PROT_NONE` `mmap` (`execMmap`) keeps frozen bytes. -/
theorem keepsFrozen_mapZero_protNone (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozen ((m.mapZero base len).setPermNonFrozen base len Perm.protNone) :=
  (keepsFrozen_mapZero m base len).trans (keepsFrozen_setPermNonFrozen _ base len _)

/-- `Memory.remapRw` unconditionally preserves all frozen bytes. -/
theorem keepsFrozen_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) :
    m.KeepsFrozen (m.remapRw oldBase oldSize newBase newSize) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  have hcell : (m.remapRw oldBase oldSize newBase newSize).cells a = m.cells a := by simp [remapRw, hf]
  simp [read8, perm, isLazyFree, isAnon, hcell]

private theorem not_frozen_of_allPerm_in_range {m : Memory} {base : BitVec 64} {size : Nat}
    (h : m.allPerm (fun p => !p.frozen) base size = true) {a : BitVec 64}
    (ha : (a - base).toNat < size) : (m.perm a).frozen = false := by
  have hi := (allPerm_iff m (fun p => !p.frozen) base size).1 h (a - base).toNat ha
  have heq : base + BitVec.ofNat 64 (a - base).toNat = a := by
    have h1 : BitVec.ofNat 64 (a - base).toNat = a - base := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [h1]
    bv_arith
  rw [heq, Bool.not_eq_true'] at hi
  exact hi

/-- Pointwise permission of `Memory.remapRw` when neither the source nor destination range
    intersects frozen memory. -/
theorem perm_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat)
    (hOld : m.allPerm (fun p => !p.frozen) oldBase oldSize = true)
    (hNew : m.allPerm (fun p => !p.frozen) newBase newSize = true) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).perm a =
      if (a - newBase).toNat < newSize then some Perm.rw
      else if (a - oldBase).toNat < oldSize then none
      else m.perm a := by
  rw [perm_remapRw_raw]
  by_cases hn : (a - newBase).toNat < newSize
  · simp only [hn, ↓reduceIte, not_frozen_of_allPerm_in_range hNew hn, Bool.false_eq_true]
  · by_cases ho : (a - oldBase).toNat < oldSize
    · simp only [hn, ho, ↓reduceIte, not_frozen_of_allPerm_in_range hOld ho, Bool.false_eq_true]
    · simp only [hn, ho, ↓reduceIte]
      split <;> rfl

/-- Pointwise byte value of `Memory.remapRw` when neither the source nor destination range
    intersects frozen memory. -/
theorem read8_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat)
    (hOld : m.allPerm (fun p => !p.frozen) oldBase oldSize = true)
    (hNew : m.allPerm (fun p => !p.frozen) newBase newSize = true) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).read8 a =
      if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.read8 (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else 0#8
      else if (a - oldBase).toNat < oldSize then 0#8
      else m.read8 a := by
  rw [read8_remapRw_raw]
  by_cases hn : (a - newBase).toNat < newSize
  · simp only [hn, ↓reduceIte, not_frozen_of_allPerm_in_range hNew hn, Bool.false_eq_true]
  · by_cases ho : (a - oldBase).toNat < oldSize
    · simp only [hn, ho, ↓reduceIte, not_frozen_of_allPerm_in_range hOld ho, Bool.false_eq_true]
    · simp only [hn, ho, ↓reduceIte]
      split <;> rfl

/-- Any range unmapped in `m.unmapNonFrozen oldBase oldSize` contains no frozen bytes in `m`. -/
theorem allPerm_not_frozen_of_canMap_unmapNonFrozen {m : Memory}
    {oldBase : BitVec 64} {oldSize : Nat} {newBase : BitVec 64} {newSize : Nat}
    (hmap : (m.unmapNonFrozen oldBase oldSize).canMap newBase newSize = true) :
    m.allPerm (fun p => !p.frozen) newBase newSize = true := by
  rw [allPerm_iff]
  unfold canMap at hmap
  rw [allPerm_iff] at hmap
  intro i hi
  have hu := hmap i hi
  cases hfz : (m.perm (newBase + BitVec.ofNat 64 i)).frozen
  · rfl
  · have hp := (keepsFrozen_unmapNonFrozen m oldBase oldSize (newBase + BitVec.ofNat 64 i) hfz).2.1
    have hm := mapped_of_frozen (m := m) (a := newBase + BitVec.ofNat 64 i) hfz
    rw [hp, hm] at hu
    exact Bool.noConfusion hu
theorem isLazyFree_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat)
    (hOld : m.allPerm (fun p => !p.frozen) oldBase oldSize = true)
    (hNew : m.allPerm (fun p => !p.frozen) newBase newSize = true) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).isLazyFree a =
      if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.isLazyFree (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else false
      else if (a - oldBase).toNat < oldSize then false
      else m.isLazyFree a := by
  rw [isLazyFree_remapRw_raw]
  by_cases hn : (a - newBase).toNat < newSize
  · simp only [hn, ↓reduceIte, not_frozen_of_allPerm_in_range hNew hn, Bool.false_eq_true]
  · by_cases ho : (a - oldBase).toNat < oldSize
    · simp only [hn, ho, ↓reduceIte, not_frozen_of_allPerm_in_range hOld ho, Bool.false_eq_true]
    · simp only [hn, ho, ↓reduceIte]
      split <;> rfl

theorem isAnon_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat)
    (hOld : m.allPerm (fun p => !p.frozen) oldBase oldSize = true)
    (hNew : m.allPerm (fun p => !p.frozen) newBase newSize = true) (a : BitVec 64) :
    (m.remapRw oldBase oldSize newBase newSize).isAnon a =
      if (a - newBase).toNat < newSize then
        if (a - newBase).toNat < oldSize then
          m.isAnon (oldBase + BitVec.ofNat 64 (a - newBase).toNat)
        else true
      else if (a - oldBase).toNat < oldSize then false
      else m.isAnon a := by
  rw [isAnon_remapRw_raw]
  by_cases hn : (a - newBase).toNat < newSize
  · simp only [hn, ↓reduceIte, not_frozen_of_allPerm_in_range hNew hn, Bool.false_eq_true]
  · by_cases ho : (a - oldBase).toNat < oldSize
    · simp only [hn, ho, ↓reduceIte, not_frozen_of_allPerm_in_range hOld ho, Bool.false_eq_true]
    · simp only [hn, ho, ↓reduceIte]
      split <;> rfl

/-- Raw cell preservation on frozen bytes (stronger than `KeepsFrozen`, preserving `anon` as well). -/
def KeepsFrozenCells (m m' : Memory) : Prop :=
  ∀ a, m.Frozen a → m'.cells a = m.cells a

theorem KeepsFrozenCells.refl (m : Memory) : m.KeepsFrozenCells m := fun _ _ => rfl

theorem KeepsFrozenCells.keepsFrozen {m m' : Memory} (h : m.KeepsFrozenCells m') : m.KeepsFrozen m' :=
  fun a ha => by unfold read8 perm isLazyFree isAnon; rw [h a ha]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem KeepsFrozenCells.trans {m₁ m₂ m₃ : Memory}
    (h₁ : m₁.KeepsFrozenCells m₂) (h₂ : m₂.KeepsFrozenCells m₃) : m₁.KeepsFrozenCells m₃ := by
  intro a ha
  have ha₂ : m₂.Frozen a := by unfold Frozen at *; rw [(h₁.keepsFrozen a ha).2.1]; exact ha
  exact (h₂ a ha₂).trans (h₁ a ha)

theorem keepsFrozenCells_write8 {m : Memory} {a : BitVec 64} (h : m.canWrite a 1 = true)
    (v : BitVec 8) : m.KeepsFrozenCells (m.write8 a v) := by
  intro b hb
  have h0 := ne_of_canWrite h hb (i := 0) (by omega)
  simp only [BitVec.add_zero] at h0
  simp [write8, h0]

theorem keepsFrozenCells_write16 {m : Memory} {a : BitVec 64} (h : m.canWrite a 2 = true)
    (v : BitVec 16) : m.KeepsFrozenCells (m.write16 a v) := by
  intro b hb
  have h0 := ne_of_canWrite h hb (i := 0) (by omega)
  have h1 := ne_of_canWrite h hb (i := 1) (by omega)
  simp only [write16, write8, h0, h1, ↓reduceIte]

theorem keepsFrozenCells_writeBytes {m : Memory} {a : BitVec 64} (bs : List (BitVec 8))
    (h : m.canWrite a bs.length = true) : m.KeepsFrozenCells (m.writeBytes a bs) := by
  induction bs generalizing m a with
  | nil => exact KeepsFrozenCells.refl m
  | cons b bs ih =>
    unfold canWrite allPerm at h
    simp only [List.length_cons, Bool.and_eq_true] at h
    have h1 : m.canWrite a 1 = true := by simp [canWrite, allPerm, h.1]
    have h2 : (m.write8 a b).canWrite (a + 1#64) bs.length = true := by
      rw [canWrite_congr (perm_write8 _ _ _)]; exact h.2
    exact (keepsFrozenCells_write8 h1 b).trans (ih h2)

theorem keepsFrozenCells_writeBytes_le {m : Memory} {buf : BitVec 64} {n : Nat}
    (bs : List (BitVec 8)) (h : ¬(!m.canWrite buf n) = true) (hle : bs.length ≤ n) :
    m.KeepsFrozenCells (m.writeBytes buf bs) :=
  keepsFrozenCells_writeBytes bs (canWrite_take_of_le (by simpa using h) hle)

theorem keepsFrozenCells_writeBytes_take {m : Memory} {buf : BitVec 64} {n : Nat}
    (xs : List (BitVec 8)) (h : ¬(!m.canWrite buf n) = true) :
    m.KeepsFrozenCells (m.writeBytes buf (xs.take n)) :=
  keepsFrozenCells_writeBytes_le (xs.take n) h (List.length_take_le n xs)

theorem keepsFrozenCells_writeStat {m : Memory} {statbuf : BitVec 64} (e : FsEntry)
    (h : ¬(!m.canWrite statbuf 128) = true) :
    m.KeepsFrozenCells (m.writeBytes statbuf (encodeLinuxStat e)) :=
  keepsFrozenCells_writeBytes_le (encodeLinuxStat e) h
    (by cases e <;> simp [encodeLinuxStat, leBytes64, leBytes32])

theorem keepsFrozenCells_writeAffinity {m : Memory} {mask : BitVec 64}
    (h : ¬(!m.canWrite mask 8) = true) :
    m.KeepsFrozenCells (m.writeBytes mask SCHED_AFFINITY_MASK) :=
  keepsFrozenCells_writeBytes_le SCHED_AFFINITY_MASK h (by simp [SCHED_AFFINITY_MASK])

theorem keepsFrozenCells_writeClock {m : Memory} {tp : BitVec 64} (ts : Timespec)
    (h : ¬(!m.canWrite tp 16) = true) :
    m.KeepsFrozenCells (m.writeBytes tp (encodeTimespec ts)) :=
  keepsFrozenCells_writeBytes_le (encodeTimespec ts) h (Nat.le_refl _)

theorem keepsFrozenCells_getrandom {m : Memory} {buf : BitVec 64} {n : Nat}
    (h : ¬(!m.canWrite buf n) = true) (f : Nat → BitVec 8) :
    m.KeepsFrozenCells (m.writeBytes buf ((List.range n).map f)) :=
  keepsFrozenCells_writeBytes _ (by simpa using h)

theorem keepsFrozenCells_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells (m.unmapWritable base len) := by
  intro a ha
  have hw : (m.perm a).w = false := by
    unfold Frozen at ha
    rcases hperm : m.perm a with _ | p <;>
      simp [hperm, Option.frozen, Perm.frozen, Option.w] at ha ⊢
    exact ha.2
  simp [unmapWritable, hw]

theorem keepsFrozenCells_mapZero (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells (m.mapZero base len) := by
  intro a ha
  have hm := mapped_of_frozen ha
  unfold mapZero
  dsimp only
  split
  · rename_i h
    rw [hm] at h
    simp at h
  · rfl

theorem keepsFrozenCells_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells (m.unmapNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [unmapNonFrozen, hf]

theorem keepsFrozenCells_setPermNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm) :
    m.KeepsFrozenCells (m.setPermNonFrozen base len p) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [setPermNonFrozen, hf]

theorem keepsFrozenCells_zeroNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells (m.zeroNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [zeroNonFrozen, hf]

theorem keepsFrozenCells_madvFreeNonFrozen (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells (m.madvFreeNonFrozen base len) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [madvFreeNonFrozen, hf]

theorem keepsFrozenCells_mmapFixedProtNone (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells
      (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone) :=
  ((keepsFrozenCells_unmapNonFrozen m base len).trans (keepsFrozenCells_mapZero _ base len)).trans
    (keepsFrozenCells_setPermNonFrozen _ base len _)

theorem keepsFrozenCells_mapZero_protNone (m : Memory) (base : BitVec 64) (len : Nat) :
    m.KeepsFrozenCells ((m.mapZero base len).setPermNonFrozen base len Perm.protNone) :=
  (keepsFrozenCells_mapZero m base len).trans (keepsFrozenCells_setPermNonFrozen _ base len _)

theorem keepsFrozenCells_remapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) :
    m.KeepsFrozenCells (m.remapRw oldBase oldSize newBase newSize) := by
  intro a ha
  have hf : (m.perm a).frozen = true := ha
  simp [remapRw, hf]

end Memory

/-- `evalPpollEntries` preserves frozen cells whenever the remaining `pollfd` slice is writable. -/
theorem evalPpollEntries_keepsFrozenCells (fs : FsState) (m m' : Memory) (ufds : BitVec 64)
    (rem idx count count' : Nat)
    (heval : evalPpollEntries fs m ufds rem idx count = some (m', count'))
    (hcw : m.canWrite (ufds + BitVec.ofNat 64 (idx * 8)) (rem * 8) = true) :
    m.KeepsFrozenCells m' := by
  induction rem generalizing m idx count with
  | zero =>
    simp [evalPpollEntries] at heval
    obtain ⟨rfl, _⟩ := heval
    exact Memory.KeepsFrozenCells.refl m
  | succ rem ih =>
    unfold evalPpollEntries at heval
    dsimp (config := { zetaHave := true }) only at heval
    have hsplit : m.canWrite (ufds + BitVec.ofNat 64 (idx * 8)) 8 = true ∧
        m.canWrite (ufds + BitVec.ofNat 64 (idx * 8) + 8#64) (rem * 8) = true := by
      unfold Memory.canWrite at hcw ⊢
      rw [show (rem + 1) * 8 = 8 + rem * 8 by omega, Memory.allPerm_add, Bool.and_eq_true] at hcw
      exact hcw
    have hw2 : m.canWrite (ufds + BitVec.ofNat 64 (idx * 8) + 6#64) 2 = true := by
      have h8 := hsplit.1
      unfold Memory.canWrite at h8 ⊢
      rw [show (8 : Nat) = 6 + 2 from rfl, Memory.allPerm_add, Bool.and_eq_true] at h8
      exact h8.2
    have hnext : ufds + BitVec.ofNat 64 (idx * 8) + 8#64 =
        ufds + BitVec.ofNat 64 ((idx + 1) * 8) := by
      rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
        ← BitVec.ofNat_add, show idx * 8 + 8 = (idx + 1) * 8 by omega]
    split at heval
    · cases heval
    · split at heval
      · refine (Memory.keepsFrozenCells_write16 hw2 _).trans (ih _ (idx + 1) _ heval ?_)
        rw [Memory.canWrite_congr (Memory.perm_write16 _ _ _), ← hnext]
        exact hsplit.2
      · split at heval
        · refine (Memory.keepsFrozenCells_write16 hw2 _).trans (ih _ (idx + 1) _ heval ?_)
          rw [Memory.canWrite_congr (Memory.perm_write16 _ _ _), ← hnext]
          exact hsplit.2
        · cases heval

theorem evalPpollEntries_keepsFrozen (fs : FsState) (m m' : Memory) (ufds : BitVec 64)
    (rem idx count count' : Nat)
    (heval : evalPpollEntries fs m ufds rem idx count = some (m', count'))
    (hcw : m.canWrite (ufds + BitVec.ofNat 64 (idx * 8)) (rem * 8) = true) :
    m.KeepsFrozen m' :=
  (evalPpollEntries_keepsFrozenCells fs m m' ufds rem idx count count' heval hcw).keepsFrozen

/-! ## Every step keeps frozen memory -/

private abbrev StateKeepsFrozen (m : Memory) (s' : State) : Prop := m.KeepsFrozenCells s'.mem

private theorem execFcntl_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execFcntl s) := by
  dsimp (config := { zetaHave := true }) only [execFcntl]
  (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem execIoctl_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execIoctl s) := by
  dsimp (config := { zetaHave := true }) only [execIoctl]
  repeat' split
  all_goals first
    | exact Memory.KeepsFrozenCells.refl _
    | (change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
       exact Memory.keepsFrozenCells_writeBytes_le _ (by assumption) (by simp [leBytes32]))

private theorem execOpenat_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execOpenat s) := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem execClose_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execClose s) := by
  dsimp (config := { zetaHave := true }) only [execClose]
  (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem stateKeepsFrozen_ite {m : Memory} {c : Prop} [Decidable c] {s₁ s₂ : State}
    (h₁ : c → StateKeepsFrozen m s₁) (h₂ : ¬c → StateKeepsFrozen m s₂) :
    StateKeepsFrozen m (if c then s₁ else s₂) := by
  by_cases hc : c <;> simp [hc, h₁, h₂]

private theorem execLseek_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execLseek s) := by
  dsimp (config := { zetaHave := true }) only [execLseek]
  repeat' (apply stateKeepsFrozen_ite <;> intro)
  any_goals exact Memory.KeepsFrozenCells.refl _
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    all_goals exact Memory.KeepsFrozenCells.refl _
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    any_goals exact Memory.KeepsFrozenCells.refl _
    (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem execReadCommon_keepsFrozen (s : State) (b : Bool) :
    StateKeepsFrozen s.mem (execReadCommon s b) := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]
  repeat' (apply stateKeepsFrozen_ite <;> intro)
  any_goals exact Memory.KeepsFrozenCells.refl _
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    all_goals exact Memory.KeepsFrozenCells.refl _
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    all_goals first
      | exact Memory.KeepsFrozenCells.refl _
      | (cases b <;> (change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _); apply Memory.keepsFrozenCells_writeBytes; assumption))

private theorem execWrite_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execWrite s) := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  repeat' (apply stateKeepsFrozen_ite <;> intro)
  any_goals exact Memory.KeepsFrozenCells.refl _
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    all_goals exact Memory.KeepsFrozenCells.refl _
  · dsimp only; repeat' (apply stateKeepsFrozen_ite <;> intro)
    all_goals exact Memory.KeepsFrozenCells.refl _

private theorem execFstat_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execFstat s) := by
  dsimp (config := { zetaHave := true }) only [execFstat]
  repeat' split
  all_goals first
    | (change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _); apply Memory.keepsFrozenCells_writeStat; assumption)
    | exact Memory.KeepsFrozenCells.refl _

private theorem execPpoll_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execPpoll s) := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  by_cases h1 : (s.readReg64 Reg.x2 == 0#64) = true
  · simp only [h1, ↓reduceIte]; exact Memory.KeepsFrozenCells.refl _
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (!decide ((s.readReg64 Reg.x2).toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm Option.r (s.readReg64 Reg.x2) 16) = true
  · simp only [h2, ↓reduceIte]; exact Memory.KeepsFrozenCells.refl _
  simp only [eq_false h2, ↓reduceIte]
  by_cases h3 : (!s.mem.canRead (s.readReg64 Reg.x2) 16) = true
  · simp only [h3, ↓reduceIte]; exact Memory.KeepsFrozenCells.refl _
  simp only [eq_false h3, ↓reduceIte]
  by_cases h4 : ((s.mem.read64 (s.readReg64 Reg.x2)).slt 0#64 || (s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).slt 0#64 || !decide ((s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).toNat < 1000000000)) = true
  · simp only [h4, ↓reduceIte]; exact Memory.KeepsFrozenCells.refl _
  simp only [eq_false h4, ↓reduceIte]
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  · rename_i m' count heval
    split
    · exact Memory.KeepsFrozenCells.refl _
    · rename_i hcw
      exact evalPpollEntries_keepsFrozenCells _ _ _ _ _ _ _ _ heval (by simpa using hcw)

private theorem execSetTidAddress_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execSetTidAddress s) := by
  exact Memory.KeepsFrozenCells.refl _

private theorem execGetpid_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execGetpid s) := by
  exact Memory.KeepsFrozenCells.refl _

private theorem execRtSigprocmask_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execRtSigprocmask s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]
  repeat' split
  all_goals first
    | (next h =>
        change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
        exact Memory.keepsFrozenCells_writeBytes_le (List.replicate 8 0#8) h (by simp))
    | exact Memory.KeepsFrozenCells.refl _

private theorem execSigaltstack_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execSigaltstack s) := by
  have hmem0 : ∀ sas, (s.setSigAltStack sas).mem = s.mem :=
    fun _ => by cases s; rfl
  have hmem1 : ∀ sas r v, (((s.setSigAltStack sas).writeReg64 r v).advancePC).mem = s.mem :=
    fun _ r _ => by cases s; cases r <;> rfl
  have hmem2 : ∀ sas m' r v,
      ((((s.setSigAltStack sas).setMem m').writeReg64 r v).advancePC).mem = m' :=
    fun _ _ r _ => by cases s; cases r <;> rfl
  unfold StateKeepsFrozen
  dsimp (config := { zetaHave := true }) only [execSigaltstack]
  by_cases huss : (s.readReg64 Reg.x0 == 0#64) = true
  · simp only [huss, ↓reduceIte]
    (repeat' split) <;> first
      | exact Memory.KeepsFrozenCells.refl _
      | (next h =>
          have hcw : ¬(!s.mem.canWrite (s.readReg64 Reg.x1) 24) = true := by
            intro hc; exact h (by simp [hc])
          change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
          exact Memory.keepsFrozenCells_writeBytes_le _ hcw
            (by simp [SigAltStack.toBytes, leBytes64, leBytes32]))
  · simp only [huss, ↓reduceIte, Bool.false_eq_true]
    (repeat' split) <;> first
      | exact Memory.KeepsFrozenCells.refl _
      | (rw [hmem1]; exact Memory.KeepsFrozenCells.refl _)
      | (next h =>
          rw [hmem0] at h
          rw [hmem2]
          have hcw : ¬(!s.mem.canWrite (s.readReg64 Reg.x1) 24) = true := by
            intro hc; exact h (by simp [hc])
          exact Memory.keepsFrozenCells_writeBytes_le _ hcw
            (by simp [SigAltStack.toBytes, leBytes64, leBytes32]))

private theorem execRtSigaction_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execRtSigaction s) := by
  have hmem0 : ∀ signum act, (s.setSigAction signum act).mem = s.mem :=
    fun _ _ => by cases s; rfl
  have hmem1 : ∀ signum act r v, (((s.setSigAction signum act).writeReg64 r v).advancePC).mem = s.mem :=
    fun _ _ r _ => by cases s; cases r <;> rfl
  have hmem2 : ∀ signum act m' r v,
      ((((s.setSigAction signum act).setMem m').writeReg64 r v).advancePC).mem = m' :=
    fun _ _ _ r _ => by cases s; cases r <;> rfl
  unfold StateKeepsFrozen
  dsimp (config := { zetaHave := true }) only [execRtSigaction]
  by_cases hact : (s.readReg64 Reg.x1 == 0#64) = true
  · simp only [hact, ↓reduceIte]
    (repeat' split) <;> first
      | exact Memory.KeepsFrozenCells.refl _
      | (next h =>
          have hcw : ¬(!s.mem.canWrite (s.readReg64 Reg.x2) 32) = true := by
            intro hc; exact h (by simp [hc])
          change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
          exact Memory.keepsFrozenCells_writeBytes_le _ hcw (by simp [SigAction.toBytes, leBytes64]))
  · simp only [hact, ↓reduceIte, Bool.false_eq_true, hmem0]
    (repeat' split) <;> first
      | exact Memory.KeepsFrozenCells.refl _
      | (rw [hmem1]; exact Memory.KeepsFrozenCells.refl _)
      | (next h =>
          rw [hmem2]
          have hcw : ¬(!s.mem.canWrite (s.readReg64 Reg.x2) 32) = true := by
            intro hc; exact h (by simp [hc])
          exact Memory.keepsFrozenCells_writeBytes_le _ hcw (by simp [SigAction.toBytes, leBytes64]))

private theorem execTkill_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execTkill s) := by
  dsimp (config := { zetaHave := true }) only [execTkill]
  (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem execTgkill_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execTgkill s) := by
  dsimp (config := { zetaHave := true }) only [execTgkill]
  (repeat' split) <;> exact Memory.KeepsFrozenCells.refl _

private theorem execSchedGetaffinity_keepsFrozen (s : State) :
    StateKeepsFrozen s.mem (execSchedGetaffinity s) := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]
  repeat' split
  all_goals first
    | (next h =>
        change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
        exact Memory.keepsFrozenCells_writeAffinity h)
    | exact Memory.KeepsFrozenCells.refl _

private theorem execClockGettime_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execClockGettime s) := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]
  split
  · exact Memory.KeepsFrozenCells.refl _
  · split
    · exact Memory.KeepsFrozenCells.refl _
    · next h =>
      change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _)
      exact Memory.keepsFrozenCells_writeClock (s.oracle.clockGettime s.oracleIdx) h

private theorem execMmap_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execMmap s) := by
  dsimp (config := { zetaHave := true }) only [execMmap]
  -- Case split explicitly: a failing `exact` of the nested `MAP_FIXED` lemma on another branch
  -- unfolds `Memory` operations and times out.
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  ·
    split
    · exact Memory.KeepsFrozenCells.refl _
    split
    · exact Memory.KeepsFrozenCells.refl _
    split
    · exact Memory.keepsFrozenCells_mmapFixedProtNone _ _ _
    · split
      · exact Memory.KeepsFrozenCells.refl _
      · exact (Memory.keepsFrozenCells_unmapNonFrozen _ _ _).trans
          (Memory.keepsFrozenCells_mapZero _ _ _)
  ·
    split
    · split
      · exact Memory.keepsFrozenCells_mapZero_protNone _ _ _
      · split
        · exact Memory.KeepsFrozenCells.refl _
        · exact Memory.keepsFrozenCells_mapZero _ _ _
    · exact Memory.KeepsFrozenCells.refl _

private theorem execBrk_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execBrk s) := by
  dsimp (config := { zetaHave := true }) only [execBrk]
  repeat' split
  all_goals first
    | exact Memory.keepsFrozenCells_mapZero _ _ _
    | exact Memory.keepsFrozenCells_unmapWritable _ _ _
    | exact Memory.KeepsFrozenCells.refl _

private theorem execMunmap_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execMunmap s) := by
  dsimp (config := { zetaHave := true }) only [execMunmap]
  repeat' split
  all_goals first
    | exact Memory.keepsFrozenCells_unmapNonFrozen _ _ _
    | exact Memory.KeepsFrozenCells.refl _

private theorem execMremap_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execMremap s) := by
  dsimp (config := { zetaHave := true }) only [execMremap]
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  split
  · exact Memory.KeepsFrozenCells.refl _
  · split
    · exact Memory.KeepsFrozenCells.refl _
    · split
      · exact Memory.KeepsFrozenCells.refl _
      · exact Memory.keepsFrozenCells_remapRw _ _ _ _ _

private theorem execMprotect_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execMprotect s) := by
  dsimp (config := { zetaHave := true }) only [execMprotect]
  repeat' split
  all_goals first
    | exact Memory.keepsFrozenCells_setPermNonFrozen _ _ _ _
    | exact Memory.KeepsFrozenCells.refl _

private theorem execMadvise_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execMadvise s) := by
  dsimp (config := { zetaHave := true }) only [execMadvise]
  repeat' split
  all_goals first
    | exact Memory.keepsFrozenCells_zeroNonFrozen _ _ _
    | exact Memory.keepsFrozenCells_madvFreeNonFrozen _ _ _
    | exact Memory.KeepsFrozenCells.refl _

private theorem execGetrandom_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execGetrandom s) := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]
  repeat' split
  all_goals first
    | (next h => change s.mem.KeepsFrozenCells (s.mem.writeBytes _ _); exact Memory.keepsFrozenCells_getrandom h _)
    | exact Memory.KeepsFrozenCells.refl _

theorem evalSvc_keepsFrozen (svc : State → State) (s : State) :
    s.mem.KeepsFrozen (evalSvc svc s).mem := by
  intro a hf
  have hf' : (s.mem.perm a).frozen = true := hf
  have hcell : (evalSvc svc s).mem.cells a = s.mem.cells a := by simp [evalSvc, hf']
  simp [Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, hcell]

@[simp, arm64_norm]
theorem evalSvc_tpidrEl0 (svc : State → State) (s : State) :
    (evalSvc svc s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm]
theorem evalSvc_symtab (svc : State → State) (s : State) :
    (evalSvc svc s).symtab = s.symtab := by
  cases s; rfl

private theorem execExit_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execExit s) :=
  Memory.KeepsFrozenCells.refl s.mem
private theorem execRead_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execRead s) :=
  execReadCommon_keepsFrozen s false
private theorem execPread64_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execPread64 s) :=
  execReadCommon_keepsFrozen s true

theorem dispatch_keepsFrozenCells
    (table : List (BitVec 64 × (State → State))) (s : State)
    (htab : ∀ p ∈ table, s.mem.KeepsFrozenCells (p.2 s).mem) :
    s.mem.KeepsFrozenCells (Syscall.dispatch table s).mem := by
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · exact Memory.KeepsFrozenCells.refl s.mem

theorem dispatch_keepsFrozen
    (table : List (BitVec 64 × (State → State))) (s : State)
    (htab : ∀ p ∈ table, s.mem.KeepsFrozen (p.2 s).mem) :
    s.mem.KeepsFrozen (Syscall.dispatch table s).mem := by
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · exact Memory.KeepsFrozen.refl s.mem

private theorem keepsFrozen_rwvFrame :
    ProofLib.RwvFrame (fun a b => a.mem.KeepsFrozenCells b.mem) where
  refl _ := Memory.KeepsFrozenCells.refl _
  trans _ _ _ h1 h2 := h1.trans h2
  reg _ _ _ := Memory.KeepsFrozenCells.refl _
  pc _ := Memory.KeepsFrozenCells.refl _
  status _ _ := Memory.KeepsFrozenCells.refl _
  regsPc _ _ _ := Memory.KeepsFrozenCells.refl _

private theorem execReadv_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execReadv s) :=
  ProofLib.execReadv_preserves keepsFrozen_rwvFrame execRead_keepsFrozen s
private theorem execWritev_keepsFrozen (s : State) : StateKeepsFrozen s.mem (execWritev s) :=
  ProofLib.execWritev_preserves keepsFrozen_rwvFrame execWrite_keepsFrozen s

private theorem standardEntry_keepsFrozen (s : State) :
    ∀ p ∈ Syscall.standardTable, s.mem.KeepsFrozenCells (p.2 s).mem := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact execRead_keepsFrozen s
  · exact execWrite_keepsFrozen s
  · exact execReadv_keepsFrozen s
  · exact execWritev_keepsFrozen s
  · exact execExit_keepsFrozen s
  · exact execExit_keepsFrozen s
  · exact execFcntl_keepsFrozen s
  · exact execIoctl_keepsFrozen s
  · exact execOpenat_keepsFrozen s
  · exact execClose_keepsFrozen s
  · exact execLseek_keepsFrozen s
  · exact execPread64_keepsFrozen s
  · exact execFstat_keepsFrozen s
  · exact execPpoll_keepsFrozen s
  · exact execBrk_keepsFrozen s
  · exact execMunmap_keepsFrozen s
  · exact execMremap_keepsFrozen s
  · exact execMmap_keepsFrozen s
  · exact execMprotect_keepsFrozen s
  · exact execMadvise_keepsFrozen s
  · exact execTkill_keepsFrozen s
  · exact execTgkill_keepsFrozen s
  · exact execSigaltstack_keepsFrozen s
  · exact execRtSigaction_keepsFrozen s
  · exact execRtSigprocmask_keepsFrozen s
  · exact execClockGettime_keepsFrozen s
  · exact execGetrandom_keepsFrozen s
  · exact execSetTidAddress_keepsFrozen s
  · exact execSchedGetaffinity_keepsFrozen s
  · exact execGetpid_keepsFrozen s
  · exact execGetpid_keepsFrozen s

theorem execSyscall_keepsFrozen (s : State) : s.mem.KeepsFrozen (execSyscall s).mem :=
  (dispatch_keepsFrozenCells Syscall.standardTable s (standardEntry_keepsFrozen s)).keepsFrozen

namespace Memory

theorem keepsFrozen_writeSized' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!m.canWrite a sz.bytes) = true) (v : BitVec 64) : m.KeepsFrozen (m.writeSized sz a v) :=
  keepsFrozen_writeSized (by simpa using h) v

theorem keepsFrozen_writeSimdSized' {m : Memory} {sz : SimdMemSize} {a : BitVec 64}
    (h : ¬(!m.canWrite a sz.bytes) = true) (v : BitVec 128) :
    m.KeepsFrozen (m.writeSimdSized sz a v) :=
  keepsFrozen_writeSimdSized (by simpa using h) v

theorem keepsFrozen_writeSized2' {m : Memory} {sz : MemWidth} {a b : BitVec 64}
    (h : ¬(!(m.canWrite a sz.bytes && m.canWrite b sz.bytes)) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz b w) := by
  have h : m.canWrite a sz.bytes = true ∧ m.canWrite b sz.bytes = true := by simpa using h
  refine (keepsFrozen_writeSized h.1 v).trans (keepsFrozen_writeSized ?_ w)
  rw [canWrite_congr (perm_writeSized _ _ _ _)]; exact h.2

theorem keepsFrozen_writeSimdSized2' {m : Memory} {sz : SimdMemSize} {a b : BitVec 64}
    (h : ¬(!(m.canWrite a sz.bytes && m.canWrite b sz.bytes)) = true) (v w : BitVec 128) :
    m.KeepsFrozen ((m.writeSimdSized sz a v).writeSimdSized sz b w) := by
  have h : m.canWrite a sz.bytes = true ∧ m.canWrite b sz.bytes = true := by simpa using h
  refine (keepsFrozen_writeSimdSized h.1 v).trans (keepsFrozen_writeSimdSized ?_ w)
  rw [canWrite_congr (perm_writeSimdSized _ _ _ _)]; exact h.2

/-- The memory written by `st1` (single structure, post-index): one lane of 1/2/4/8 bytes. -/
theorem keepsFrozen_st1 {m : Memory} {ea : BitVec 64} {c1 c2 c3 : Bool} {b8 : BitVec 8}
    {h16 : BitVec 16} {w32 : BitVec 32} {d64 : BitVec 64}
    (h : ¬(!m.canWrite ea (if c1 = true then 1 else if c2 = true then 2
      else if c3 = true then 4 else 8)) = true) :
    m.KeepsFrozen (if c1 = true then (m.write8 ea b8, 1#64)
      else if c2 = true then (m.write16 ea h16, 2#64)
      else if c3 = true then (m.write32 ea w32, 4#64)
      else (m.write64 ea d64, 8#64)).fst := by
  simp only [Bool.not_eq_true'] at h
  cases c1 <;> cases c2 <;> cases c3 <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals first
    | exact keepsFrozen_write8 (by simpa using h) _ | exact keepsFrozen_write16 (by simpa using h) _
    | exact keepsFrozen_write32 (by simpa using h) _ | exact keepsFrozen_write64 (by simpa using h) _

/-- Two adjacent `sz` stores at `a`, `a + sz` guarded by one `canWrite a (2 * sz)` check
    (`STXP`, `CASP`). -/
theorem keepsFrozen_writeSizedPair {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : m.canWrite a (2 * sz.bytes) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) := by
  unfold canWrite at h
  rw [show 2 * sz.bytes = sz.bytes + sz.bytes by omega, allPerm_add, Bool.and_eq_true] at h
  refine (keepsFrozen_writeSized h.1 v).trans (keepsFrozen_writeSized ?_ w)
  rw [canWrite_congr (perm_writeSized _ _ _ _)]; exact h.2

theorem keepsFrozen_writeSizedPair' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!m.canWrite a (2 * sz.bytes)) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) :=
  keepsFrozen_writeSizedPair (by simpa using h) v w

theorem keepsFrozen_writeSizedPairRW' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!(m.canRead a (2 * sz.bytes) && m.canWrite a (2 * sz.bytes))) = true) (v w : BitVec 64) :
    m.KeepsFrozen ((m.writeSized sz a v).writeSized sz (a + BitVec.ofNat 64 sz.bytes) w) :=
  keepsFrozen_writeSizedPair (by simp at h; exact h.2) v w

/-- A store guarded by a combined read-and-write check (`CAS`, LSE atomics). -/
theorem keepsFrozen_writeSizedRW' {m : Memory} {sz : MemWidth} {a : BitVec 64}
    (h : ¬(!(m.canRead a sz.bytes && m.canWrite a sz.bytes)) = true) (v : BitVec 64) :
    m.KeepsFrozen (m.writeSized sz a v) :=
  keepsFrozen_writeSized (by simp at h; exact h.2) v

end Memory

/-- `simdStoreRegs` (ST1 multiple structures, DC ZVA) writes only inside `[ea, ea + k * sz)`. -/
theorem keepsFrozen_simdStoreRegs (sz : SimdMemSize) (rd : BitVec 5 → BitVec 128) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      m.canWrite ea (k * sz.bytes) = true → m.KeepsFrozen (simdStoreRegs sz rd k vt ea m)
  | 0, _, _, m, _ => Memory.KeepsFrozen.refl m
  | k + 1, vt, ea, m, h => by
    unfold Memory.canWrite at h
    rw [Nat.succ_mul, Nat.add_comm, Memory.allPerm_add, Bool.and_eq_true] at h
    simp only [simdStoreRegs]
    refine (Memory.keepsFrozen_writeSimdSized h.1 _).trans
      (keepsFrozen_simdStoreRegs sz rd k _ _ _ ?_)
    rw [Memory.canWrite_congr (Memory.perm_writeSimdSized _ _ _ _)]; exact h.2

theorem keepsFrozen_simdStoreRegs' {sz : SimdMemSize} {rd : BitVec 5 → BitVec 128} {k n : Nat}
    {vt : BitVec 5} {ea : BitVec 64} {m : Memory} (hn : k * sz.bytes = n)
    (h : ¬(!m.canWrite ea n) = true) : m.KeepsFrozen (simdStoreRegs sz rd k vt ea m) :=
  keepsFrozen_simdStoreRegs sz rd k vt ea m (by subst hn; simpa using h)

/-- `simdLoadRegs` (LD1 multiple structures) only writes vector registers. -/
@[simp] theorem mem_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), (simdLoadRegs sz m k vt ea s).mem = s.mem
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]; rw [mem_simdLoadRegs]; rfl

@[simp] theorem symtab_simdLoadRegs (sz : SimdMemSize) (m : Memory) :
    ∀ (k : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m k vt ea s).symtab = s.symtab
  | 0, _, _, _ => rfl
  | k + 1, vt, ea, s => by
    simp only [simdLoadRegs]; rw [symtab_simdLoadRegs]; rfl

/-! ## Instruction helpers -/

section ExecHelpers

local macro "mem_helper" : tactic =>
  `(tactic| (repeat' split) <;> rfl)

theorem mem_execAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (shift12 : Bool) (s : State) : (execAddSubImm w op rd rn imm12 shift12 s).mem = s.mem := by
  simp only [execAddSubImm]; mem_helper
theorem mem_execAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amt : Nat) (s : State) : (execAddSubExt w op rd rn rm ext amt s).mem = s.mem := by
  simp only [execAddSubExt]; mem_helper
theorem mem_execAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execAddSubShift w op rd rn rm sh amt s).mem = s.mem := by
  simp only [execAddSubShift]; mem_helper
theorem mem_execAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : State) :
    (execAddSubCarry w op rd rn rm s).mem = s.mem := by
  simp only [execAddSubCarry]; mem_helper
theorem mem_execLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64)
    (s : State) : (execLogicalImm w op rd rn imm s).mem = s.mem := by
  simp only [execLogicalImm]; mem_helper
theorem mem_execLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execLogicalShift w op rd rn rm sh amt s).mem = s.mem := by
  simp only [execLogicalShift]; mem_helper
theorem mem_execCondCompare (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64)
    (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) :
    (execCondCompare w isSub isImm rn rhs rm nzcv cond s).mem = s.mem := by
  simp only [execCondCompare]; mem_helper
theorem mem_execLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
    (s : State) : (execLdr w size signed rt addr s).mem = s.mem := by
  simp only [execLdr]; mem_helper
theorem mem_execLdrLit (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) (s : State) : (execLdrLit w size signed rt offset s).mem = s.mem := by
  simp only [execLdrLit]; mem_helper
theorem mem_execLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    (execLdp w signed rt1 rt2 addr s).mem = s.mem := by
  simp only [execLdp]; mem_helper

theorem execStr_keepsFrozen (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) :
    s.mem.KeepsFrozen (execStr size rt addr s).mem := by
  simp only [execStr]
  repeat' split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | exact Memory.keepsFrozen_writeSized' ‹_› _

theorem execStp_keepsFrozen (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    s.mem.KeepsFrozen (execStp w rt1 rt2 addr s).mem := by
  simp only [execStp]
  repeat' split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | exact Memory.keepsFrozen_writeSized2' ‹_› _ _

end ExecHelpers

theorem keepsFrozen_ite {m : Memory} {c : Prop} [Decidable c] {s1 s2 : State}
    (h1 : c → m.KeepsFrozen s1.mem) (h2 : ¬c → m.KeepsFrozen s2.mem) :
    m.KeepsFrozen (if c then s1 else s2).mem := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

theorem KeepsFrozen_of_mem_eq {m : Memory} {s : State} (h : s.mem = m) : m.KeepsFrozen s.mem :=
  h ▸ Memory.KeepsFrozen.refl _

theorem keepsFrozen_applySimdResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    s.mem.KeepsFrozen (applySimdResult s rd r).mem := by
  cases r <;> exact Memory.KeepsFrozen.refl _

theorem keepsFrozen_applySimdSatResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) :
    s.mem.KeepsFrozen (applySimdSatResult s rd r satFlags).mem := by
  cases r <;> cases satFlags <;> exact Memory.KeepsFrozen.refl _

set_option maxHeartbeats 1600000 in
theorem evalInst_keepsFrozen (prog : Program) (inst : Instr) (s : State) :
    s.mem.KeepsFrozen (prog.evalInst inst s).mem := by
  unfold Program.evalInst execInstWithSvc
  split
  all_goals first
    | exact Memory.KeepsFrozen.refl _
    | (first
        | rw [mem_execAddSubImm] | rw [mem_execAddSubExt] | rw [mem_execAddSubShift]
        | rw [mem_execAddSubCarry] | rw [mem_execLogicalImm] | rw [mem_execLogicalShift]
        | rw [mem_execCondCompare] | rw [mem_execLdr] | rw [mem_execLdrLit] | rw [mem_execLdp]
       exact Memory.KeepsFrozen.refl _)
    | with_reducible exact execStr_keepsFrozen _ _ _ _
    | with_reducible exact execStp_keepsFrozen _ _ _ _ _
    | (try dsimp only
       repeat' (first
         | exact Memory.KeepsFrozen.refl _
         | exact keepsFrozen_applySimdResult _ _ _
         | exact keepsFrozen_applySimdSatResult _ _ _ _
         | exact evalSvc_keepsFrozen _ _
         | exact Memory.keepsFrozen_writeSized' ‹_› _
         | exact Memory.keepsFrozen_writeSimdSized' ‹_› _
         | exact Memory.keepsFrozen_writeSimdSized2' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedPair' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedPairRW' ‹_› _ _
         | exact Memory.keepsFrozen_writeSizedRW' ‹_› _
         | exact Memory.keepsFrozen_st1 ‹_›
         | exact keepsFrozen_simdStoreRegs' (by first | rfl | decide) ‹_›
         | exact KeepsFrozen_of_mem_eq (mem_simdLoadRegs _ _ _ _ _ _)
         | refine keepsFrozen_ite (fun _ => ?_) (fun _ => ?_)
         | split))

/-! ## Steps keep frozen memory and the symbol table, so loaded code stays loaded -/

namespace State

@[simp, arm64_norm] theorem symtab_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by
  cases s; cases r <;> rfl
@[simp, arm64_norm] theorem symtab_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab :=
  symtab_writeReg64 s r (v.zeroExtend 64)
@[simp, arm64_norm] theorem symtab_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).symtab = s.symtab := by
  cases w <;> exact symtab_writeReg64 s r _
@[simp, arm64_norm] theorem symtab_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).symtab = s.symtab :=
  symtab_writeVReg128 s i (v.zeroExtend 128)
@[simp, arm64_norm] theorem symtab_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).symtab = s.symtab :=
  symtab_writeVReg128 s i (v.zeroExtend 128)
@[simp, arm64_norm] theorem symtab_advancePC (s : State) : (s.advancePC).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_setPState (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_setMem (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_nextOracle (s : State) : (s.nextOracle).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_stepExclOracle (s : State) : (s.stepExclOracle).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem symtab_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).symtab = s.symtab := by
  cases s; rfl

@[simp, arm64_norm] theorem sym_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (o n : String) :
    (s.writeReg64 r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg64]
@[simp, arm64_norm] theorem sym_writeReg32 (s : State) (r : Reg) (v : BitVec 32) (o n : String) :
    (s.writeReg32 r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg32]
@[simp, arm64_norm] theorem sym_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) (o n : String) :
    (s.writeReg w r v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeReg]
@[simp, arm64_norm] theorem sym_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) (o n : String) :
    (s.writeVReg128 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg128]
@[simp, arm64_norm] theorem sym_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) (o n : String) :
    (s.writeVReg64 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg64]
@[simp, arm64_norm] theorem sym_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) (o n : String) :
    (s.writeVReg32 i v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_writeVReg32]
@[simp, arm64_norm] theorem sym_advancePC (s : State) (o n : String) :
    (s.advancePC).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_advancePC]
@[simp, arm64_norm] theorem sym_setPC (s : State) (pc : BitVec 64) (o n : String) :
    (s.setPC pc).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPC]
@[simp, arm64_norm] theorem sym_setPState (s : State) (ps : PState) (o n : String) :
    (s.setPState ps).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPState]
@[simp, arm64_norm] theorem sym_setMem (s : State) (m : Memory) (o n : String) :
    (s.setMem m).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setMem]
@[simp, arm64_norm] theorem sym_setStatus (s : State) (st : ExecStatus) (o n : String) :
    (s.setStatus st).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setStatus]
@[simp, arm64_norm] theorem sym_setBrk (s : State) (b : BitVec 64) (o n : String) :
    (s.setBrk b).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setBrk]
@[simp, arm64_norm] theorem sym_nextOracle (s : State) (o n : String) :
    (s.nextOracle).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_nextOracle]
@[simp, arm64_norm] theorem sym_stepExclOracle (s : State) (o n : String) :
    (s.stepExclOracle).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_stepExclOracle]
@[simp, arm64_norm] theorem sym_appendTrace (s : State) (evs : List TraceEvent) (o n : String) :
    (s.appendTrace evs).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_appendTrace]
@[simp, arm64_norm] theorem symtab_setFs (s : State) (fs : FsState) :
    (s.setFs fs).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_setFs (s : State) (fs : FsState) (o n : String) :
    (s.setFs fs).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setFs]
@[simp, arm64_norm] theorem symtab_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_setFpsr (s : State) (f : BitVec 32) (o n : String) :
    (s.setFpsr f).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setFpsr]
@[simp, arm64_norm] theorem symtab_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_orFpsr (s : State) (f : BitVec 32) (o n : String) :
    (s.orFpsr f).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_orFpsr]
@[simp, arm64_norm] theorem symtab_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_setSigAction (s : State) (sig : BitVec 32) (act : SigAction)
    (o n : String) :
    (s.setSigAction sig act).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigAction]
@[simp, arm64_norm] theorem symtab_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_setSigAltStack (s : State) (sas : SigAltStack)
    (o n : String) :
    (s.setSigAltStack sas).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setSigAltStack]
@[simp, arm64_norm] theorem symtab_setPhysMemAvail (s : State) (v : Nat) :
    (s.setPhysMemAvail v).symtab = s.symtab := by
  cases s; rfl
@[simp, arm64_norm] theorem sym_setPhysMemAvail (s : State) (v : Nat) (o n : String) :
    (s.setPhysMemAvail v).sym o n = s.sym o n := by
  unfold State.sym; rw [symtab_setPhysMemAvail]

end State

theorem symtab_ite {s : State} {c : Prop} [Decidable c] {s1 s2 : State}
    (h1 : c → s1.symtab = s.symtab) (h2 : ¬c → s2.symtab = s.symtab) :
    (if c then s1 else s2).symtab = s.symtab := by
  split
  · exact h1 ‹_›
  · exact h2 ‹_›

private def StateSymtabEq (t : String → String → Option (BitVec 64)) (s' : State) : Prop :=
  s'.symtab = t

private theorem symtab_execFcntl (s : State) : StateSymtabEq s.symtab (execFcntl s) := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; (repeat' split) <;> rfl
private theorem symtab_execIoctl (s : State) : StateSymtabEq s.symtab (execIoctl s) := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; (repeat' split) <;> rfl
private theorem symtab_execOpenat (s : State) : StateSymtabEq s.symtab (execOpenat s) := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;> rfl
private theorem symtab_execClose (s : State) : StateSymtabEq s.symtab (execClose s) := by
  dsimp (config := { zetaHave := true }) only [execClose]; (repeat' split) <;> rfl
private theorem symtab_execLseek (s : State) : StateSymtabEq s.symtab (execLseek s) := by
  dsimp (config := { zetaHave := true }) only [execLseek, StateSymtabEq]
  repeat' (apply symtab_ite <;> intro)
  any_goals rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    all_goals rfl
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    any_goals rfl
    (repeat' split) <;> rfl
private theorem symtab_execReadCommon (s : State) (b : Bool) :
    StateSymtabEq s.symtab (execReadCommon s b) := by
  dsimp (config := { zetaHave := true }) only [execReadCommon, StateSymtabEq]
  repeat' (apply symtab_ite <;> intro)
  any_goals rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    all_goals rfl
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    all_goals (try cases b) <;> rfl
private theorem symtab_execWrite (s : State) : StateSymtabEq s.symtab (execWrite s) := by
  dsimp (config := { zetaHave := true }) only [execWrite, StateSymtabEq]
  repeat' (apply symtab_ite <;> intro)
  any_goals rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    all_goals rfl
  · dsimp only; repeat' (apply symtab_ite <;> intro)
    all_goals rfl
private theorem symtab_execFstat (s : State) : StateSymtabEq s.symtab (execFstat s) := by
  dsimp (config := { zetaHave := true }) only [execFstat]; (repeat' split) <;> rfl
private theorem symtab_execPpoll (s : State) : StateSymtabEq s.symtab (execPpoll s) := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  by_cases h1 : (s.readReg64 Reg.x2 == 0#64) = true
  · simp only [h1, ↓reduceIte]; rfl
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (!decide ((s.readReg64 Reg.x2).toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm Option.r (s.readReg64 Reg.x2) 16) = true
  · simp only [h2, ↓reduceIte]; rfl
  simp only [eq_false h2, ↓reduceIte]
  by_cases h3 : (!s.mem.canRead (s.readReg64 Reg.x2) 16) = true
  · simp only [h3, ↓reduceIte]; rfl
  simp only [eq_false h3, ↓reduceIte]
  by_cases h4 : ((s.mem.read64 (s.readReg64 Reg.x2)).slt 0#64 || (s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).slt 0#64 || !decide ((s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).toNat < 1000000000)) = true
  · simp only [h4, ↓reduceIte]; rfl
  simp only [eq_false h4, ↓reduceIte]
  (repeat' split) <;> rfl
private theorem symtab_execSetTidAddress (s : State) :
    StateSymtabEq s.symtab (execSetTidAddress s) := rfl
private theorem symtab_execGetpid (s : State) :
    StateSymtabEq s.symtab (execGetpid s) := rfl
private theorem symtab_execRtSigprocmask (s : State) :
    StateSymtabEq s.symtab (execRtSigprocmask s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; (repeat' split) <;> rfl
private theorem symtab_execSigaltstack (s : State) :
    StateSymtabEq s.symtab (execSigaltstack s) := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; (repeat' split) <;> rfl
private theorem symtab_execRtSigaction (s : State) :
    StateSymtabEq s.symtab (execRtSigaction s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; (repeat' split) <;> rfl
private theorem symtab_execTkill (s : State) :
    StateSymtabEq s.symtab (execTkill s) := by
  dsimp (config := { zetaHave := true }) only [execTkill]; (repeat' split) <;> rfl
private theorem symtab_execTgkill (s : State) :
    StateSymtabEq s.symtab (execTgkill s) := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; (repeat' split) <;> rfl
private theorem symtab_execSchedGetaffinity (s : State) :
    StateSymtabEq s.symtab (execSchedGetaffinity s) := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; (repeat' split) <;> rfl
private theorem symtab_execClockGettime (s : State) : StateSymtabEq s.symtab (execClockGettime s) := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; (repeat' split) <;> rfl
private theorem symtab_execMmap (s : State) : StateSymtabEq s.symtab (execMmap s) := by
  dsimp (config := { zetaHave := true }) only [execMmap]; (repeat' split) <;> rfl
private theorem symtab_execBrk (s : State) : StateSymtabEq s.symtab (execBrk s) := by
  dsimp (config := { zetaHave := true }) only [execBrk]; (repeat' split) <;> rfl
private theorem symtab_execMunmap (s : State) : StateSymtabEq s.symtab (execMunmap s) := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; (repeat' split) <;> rfl
private theorem symtab_execMremap (s : State) : StateSymtabEq s.symtab (execMremap s) := by
  dsimp (config := { zetaHave := true }) only [execMremap]; (repeat' split) <;> rfl
private theorem symtab_execMprotect (s : State) : StateSymtabEq s.symtab (execMprotect s) := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; (repeat' split) <;> rfl
private theorem symtab_execMadvise (s : State) : StateSymtabEq s.symtab (execMadvise s) := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; (repeat' split) <;> rfl
private theorem symtab_execGetrandom (s : State) : StateSymtabEq s.symtab (execGetrandom s) := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; (repeat' split) <;> rfl

private theorem symtab_setStatus (s : State) (st : ExecStatus) :
    StateSymtabEq s.symtab (s.setStatus st) := rfl

private theorem symtab_execExit (s : State) :
    StateSymtabEq s.symtab (execExit s) := rfl
private theorem symtab_execRead (s : State) :
    StateSymtabEq s.symtab (execRead s) := symtab_execReadCommon s false
private theorem symtab_execPread64 (s : State) :
    StateSymtabEq s.symtab (execPread64 s) := symtab_execReadCommon s true

theorem dispatch_symtab
    (table : List (BitVec 64 × (State → State))) (s : State)
    (htab : ∀ p ∈ table, (p.2 s).symtab = s.symtab) :
    (Syscall.dispatch table s).symtab = s.symtab := by
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · rfl

private theorem symtab_rwvFrame : ProofLib.RwvFrame (fun a b => b.symtab = a.symtab) where
  refl _ := rfl
  trans _ _ _ h1 h2 := h2.trans h1
  reg _ _ _ := rfl
  pc _ := rfl
  status _ _ := rfl
  regsPc _ _ _ := rfl

private theorem symtab_execReadv (s : State) : StateSymtabEq s.symtab (execReadv s) :=
  ProofLib.execReadv_preserves symtab_rwvFrame symtab_execRead s
private theorem symtab_execWritev (s : State) : StateSymtabEq s.symtab (execWritev s) :=
  ProofLib.execWritev_preserves symtab_rwvFrame symtab_execWrite s

private theorem standardEntry_symtab (s : State) :
    ∀ p ∈ Syscall.standardTable, (p.2 s).symtab = s.symtab := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact symtab_execRead s
  · exact symtab_execWrite s
  · exact symtab_execReadv s
  · exact symtab_execWritev s
  · exact symtab_execExit s
  · exact symtab_execExit s
  · exact symtab_execFcntl s
  · exact symtab_execIoctl s
  · exact symtab_execOpenat s
  · exact symtab_execClose s
  · exact symtab_execLseek s
  · exact symtab_execPread64 s
  · exact symtab_execFstat s
  · exact symtab_execPpoll s
  · exact symtab_execBrk s
  · exact symtab_execMunmap s
  · exact symtab_execMremap s
  · exact symtab_execMmap s
  · exact symtab_execMprotect s
  · exact symtab_execMadvise s
  · exact symtab_execTkill s
  · exact symtab_execTgkill s
  · exact symtab_execSigaltstack s
  · exact symtab_execRtSigaction s
  · exact symtab_execRtSigprocmask s
  · exact symtab_execClockGettime s
  · exact symtab_execGetrandom s
  · exact symtab_execSetTidAddress s
  · exact symtab_execSchedGetaffinity s
  · exact symtab_execGetpid s
  · exact symtab_execGetpid s

theorem execSyscall_symtab (s : State) : (execSyscall s).symtab = s.symtab :=
  dispatch_symtab Syscall.standardTable s (standardEntry_symtab s)

section ExecSymtabHelpers

local macro "symtab_helper" : tactic =>
  `(tactic| (repeat' split) <;> rfl)

theorem symtab_execAddSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12)
    (shift12 : Bool) (s : State) : (execAddSubImm w op rd rn imm12 shift12 s).symtab = s.symtab := by
  simp only [execAddSubImm]; symtab_helper
theorem symtab_execAddSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType)
    (amt : Nat) (s : State) : (execAddSubExt w op rd rn rm ext amt s).symtab = s.symtab := by
  simp only [execAddSubExt]; symtab_helper
theorem symtab_execAddSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execAddSubShift w op rd rn rm sh amt s).symtab = s.symtab := by
  simp only [execAddSubShift]; symtab_helper
theorem symtab_execAddSubCarry (w : Width) (op : AddSubOp) (rd rn rm : Reg) (s : State) :
    (execAddSubCarry w op rd rn rm s).symtab = s.symtab := by
  simp only [execAddSubCarry]; symtab_helper
theorem symtab_execLogicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64)
    (s : State) : (execLogicalImm w op rd rn imm s).symtab = s.symtab := by
  simp only [execLogicalImm]; symtab_helper
theorem symtab_execLogicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType)
    (amt : Nat) (s : State) : (execLogicalShift w op rd rn rm sh amt s).symtab = s.symtab := by
  simp only [execLogicalShift]; symtab_helper
theorem symtab_execCondCompare (w : Width) (isSub isImm : Bool) (rn : Reg) (rhs : BitVec 64)
    (rm : Reg) (nzcv : BitVec 4) (cond : CondCode) (s : State) :
    (execCondCompare w isSub isImm rn rhs rm nzcv cond s).symtab = s.symtab := by
  simp only [execCondCompare]; symtab_helper
theorem symtab_execLdr (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg) (addr : AddrMode)
    (s : State) : (execLdr w size signed rt addr s).symtab = s.symtab := by
  simp only [execLdr]; symtab_helper
theorem symtab_execLdrLit (w : Width) (size : MemWidth) (signed : Bool) (rt : Reg)
    (offset : BitVec 64) (s : State) : (execLdrLit w size signed rt offset s).symtab = s.symtab := by
  simp only [execLdrLit]; symtab_helper
theorem symtab_execLdp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    (execLdp w signed rt1 rt2 addr s).symtab = s.symtab := by
  simp only [execLdp]; symtab_helper
theorem symtab_execStr (size : MemWidth) (rt : Reg) (addr : AddrMode) (s : State) :
    (execStr size rt addr s).symtab = s.symtab := by
  simp only [execStr]; symtab_helper
theorem symtab_execStp (w : Width) (rt1 rt2 : Reg) (addr : AddrMode) (s : State) :
    (execStp w rt1 rt2 addr s).symtab = s.symtab := by
  simp only [execStp]; symtab_helper

end ExecSymtabHelpers

theorem symtab_applySimdResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    (applySimdResult s rd r).symtab = s.symtab := by
  cases r <;> rfl

theorem symtab_applySimdSatResult (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (satFlags : Option (BitVec 32)) :
    (applySimdSatResult s rd r satFlags).symtab = s.symtab := by
  cases r <;> cases satFlags <;> rfl

set_option maxHeartbeats 1600000 in
theorem evalInst_symtab (prog : Program) (inst : Instr) (s : State) :
    (prog.evalInst inst s).symtab = s.symtab := by
  unfold Program.evalInst execInstWithSvc
  split
  all_goals first
    | with_reducible rfl
    | with_reducible exact symtab_execAddSubImm _ _ _ _ _ _ _
    | with_reducible exact symtab_execAddSubExt _ _ _ _ _ _ _ _
    | with_reducible exact symtab_execAddSubShift _ _ _ _ _ _ _ _
    | with_reducible exact symtab_execAddSubCarry _ _ _ _ _ _
    | with_reducible exact symtab_execLogicalImm _ _ _ _ _ _
    | with_reducible exact symtab_execLogicalShift _ _ _ _ _ _ _ _
    | with_reducible exact symtab_execCondCompare _ _ _ _ _ _ _ _ _
    | with_reducible exact symtab_execLdr _ _ _ _ _ _
    | with_reducible exact symtab_execLdrLit _ _ _ _ _ _
    | with_reducible exact symtab_execLdp _ _ _ _ _ _
    | with_reducible exact symtab_execStr _ _ _ _
    | with_reducible exact symtab_execStp _ _ _ _ _
    | (try dsimp only
       repeat' (first
         | with_reducible exact evalSvc_symtab _ _
         | exact symtab_applySimdResult _ _ _
         | exact symtab_applySimdSatResult _ _ _ _
         | exact symtab_simdLoadRegs _ _ _ _ _ _
         | with_reducible rfl
         | with_reducible refine symtab_ite (fun _ => ?_) (fun _ => ?_)
         | split
         | rfl))

/-- Every step keeps every frozen byte. -/
theorem Step.keepsFrozen {prog : Program} {s s' : State} (h : Step prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  cases h with
  | exec _ _ => exact evalInst_keepsFrozen _ _ _
  | halt_unmapped _ _ _ => exact Memory.KeepsFrozen.refl _
  | extern _ _ hk _ => exact hk
  | extern_fault _ _ _ => exact Memory.KeepsFrozen.refl _

theorem Steps.keepsFrozen {prog : Program} {s s' : State} (h : Steps prog s s') :
    s.mem.KeepsFrozen s'.mem := by
  induction h with
  | refl _ => exact Memory.KeepsFrozen.refl _
  | step h1 _ ih => exact h1.keepsFrozen.trans ih

/-- Every step preserves `s.symtab`. -/
theorem Step.symtab_eq {prog : Program} {s s' : State} (h : Step prog s s') :
    s'.symtab = s.symtab := by
  cases h with
  | exec _ _ => exact evalInst_symtab _ _ _
  | halt_unmapped _ _ _ => rfl
  | extern _ _ _ hsym => exact hsym
  | extern_fault _ _ _ => rfl

theorem Steps.symtab_eq {prog : Program} {s s' : State} (h : Steps prog s s') :
    s'.symtab = s.symtab := by
  induction h with
  | refl _ => rfl
  | step h1 _ ih => exact ih.trans h1.symtab_eq

/-! ## Interface of the loaded-code predicates -/

theorem Program.codeLoaded_iff {prog : Program} {m : Memory} :
    prog.CodeLoaded m ↔
      prog.base.toNat % 4 = 0 ∧ prog.base.toNat + prog.code.length ≤ 2 ^ 64 ∧
      ∀ (i : Nat) (hi : i < prog.code.length),
        m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
        m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx ∧
        m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false := by
  unfold Program.CodeLoaded; exact Iff.rfl

theorem Program.CodeLoaded.intro {prog : Program} {m : Memory}
    (h_al : prog.base.toNat % 4 = 0) (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64)
    (h : ∀ (i : Nat) (hi : i < prog.code.length),
      m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] ∧
      m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx ∧
      m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false) : prog.CodeLoaded m :=
  Program.codeLoaded_iff.2 ⟨h_al, h_len, h⟩

theorem Program.CodeLoaded.aligned {prog : Program} {m : Memory} (h : prog.CodeLoaded m) :
    prog.base.toNat % 4 = 0 := (Program.codeLoaded_iff.1 h).1

theorem Program.CodeLoaded.no_wrap {prog : Program} {m : Memory} (h : prog.CodeLoaded m) :
    prog.base.toNat + prog.code.length ≤ 2 ^ 64 := (Program.codeLoaded_iff.1 h).2.1

theorem Program.CodeLoaded.byte_eq {prog : Program} {m : Memory} (h : prog.CodeLoaded m)
    (i : Nat) (hi : i < prog.code.length) :
    m.read8 (prog.base + BitVec.ofNat 64 i) = prog.code[i] := ((Program.codeLoaded_iff.1 h).2.2 i hi).1

theorem Program.CodeLoaded.perm_eq {prog : Program} {m : Memory} (h : prog.CodeLoaded m)
    (i : Nat) (hi : i < prog.code.length) :
    m.perm (prog.base + BitVec.ofNat 64 i) = some Perm.rx := ((Program.codeLoaded_iff.1 h).2.2 i hi).2.1

theorem Program.CodeLoaded.isLazyFree_eq {prog : Program} {m : Memory} (h : prog.CodeLoaded m)
    (i : Nat) (hi : i < prog.code.length) :
    m.isLazyFree (prog.base + BitVec.ofNat 64 i) = false := ((Program.codeLoaded_iff.1 h).2.2 i hi).2.2

/-- `CodeLoaded` only depends on `base` and `code`. -/
theorem Program.CodeLoaded.of_base_code {prog prog' : Program} {m : Memory}
    (h : prog.CodeLoaded m) (hb : prog'.base = prog.base) (hc : prog'.code = prog.code) :
    prog'.CodeLoaded m := by
  rw [Program.codeLoaded_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hb ▸ h1, hb ▸ hc ▸ h2, fun i hi => ?_⟩
  have hi' : i < prog.code.length := hc ▸ hi
  have e : prog'.code[i] = prog.code[i]'hi' := by simp only [hc]
  rw [hb, e]; exact h3 i hi'

theorem Program.codeLoaded_loadCode (prog : Program) (m : Memory)
    (h_al : prog.base.toNat % 4 = 0) (h_len : prog.base.toNat + prog.code.length ≤ 2 ^ 64) :
    prog.CodeLoaded (prog.loadCode m) := by
  refine Program.CodeLoaded.intro h_al h_len fun i hi => ?_
  have hi' : (prog.base + BitVec.ofNat 64 i - prog.base).toNat = i := by
    have : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel]
    rw [this, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [Program.loadCode, Memory.read8_ofFn, Memory.perm_ofFn, Memory.isLazyFree_ofFn, hi',
    List.size_toArray, hi, ite_true]
  exact ⟨by simp [hi], rfl, rfl⟩

/-- Loaded code is frozen, so it stays loaded under any `KeepsFrozen` change. -/
theorem Program.CodeLoaded.of_keepsFrozen {prog : Program} {m m' : Memory}
    (hL : prog.CodeLoaded m) (hk : m.KeepsFrozen m') : prog.CodeLoaded m' := by
  obtain ⟨h1, h2, h3⟩ := Program.codeLoaded_iff.1 hL
  refine Program.CodeLoaded.intro h1 h2 fun i hi => ?_
  obtain ⟨hb, hp, hlf⟩ := h3 i hi
  have hf : m.Frozen (prog.base + BitVec.ofNat 64 i) := by
    unfold Memory.Frozen; rw [hp]; rfl
  obtain ⟨hb', hp', hlf', _⟩ := hk _ hf
  exact ⟨hb'.trans hb, hp'.trans hp, hlf'.trans hlf⟩

theorem Step.codeLoaded {prog prog' : Program} {s s' : State} (h : Step prog s s')
    (hL : prog'.CodeLoaded s.mem) : prog'.CodeLoaded s'.mem :=
  hL.of_keepsFrozen h.keepsFrozen

theorem Steps.codeLoaded {prog prog' : Program} {s s' : State} (h : Steps prog s s')
    (hL : prog'.CodeLoaded s.mem) : prog'.CodeLoaded s'.mem :=
  hL.of_keepsFrozen h.keepsFrozen

/-- `fetchMem` returns `none` at an extern entry point. -/
theorem Program.fetchMem_eq_none_of_externs {prog : Program} {m : Memory} {pc : BitVec 64}
    {f : State → State} (h : prog.externAt? pc = some f) : prog.fetchMem m pc = none := by
  simp [Program.fetchMem, h]

/-! ## Fetching from loaded memory -/

namespace Program

/-- Fetching from memory agrees with fetching from the code image when the code is loaded. -/
theorem fetchMem_of_fetch {prog : Program} {m : Memory} {pc : BitVec 64} {i : Instr}
    (hL : prog.CodeLoaded m) (h : prog.fetch pc = some i) : prog.fetchMem m pc = some i := by
  obtain ⟨hbase, hlen, hcode⟩ := Program.codeLoaded_iff.1 hL
  unfold fetch at h
  unfold fetchMem
  split at h
  · contradiction
  rename_i hext
  simp only [hext]
  generalize hoff : (pc - prog.base).toNat = off at h
  have hpc : pc = prog.base + BitVec.ofNat 64 off := by
    rw [← hoff, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_arith
  unfold readWordOff at h
  split at h
  · contradiction
  rename_i hal
  split at h
  rotate_left
  · contradiction
  rename_i b0 b1 b2 b3 tl hdrop
  have hlen4 : off + 4 ≤ prog.code.length := by
    have := congrArg List.length hdrop
    simp at this; omega
  have hb : ∀ k (hk : k < 4), m.read8 (pc + BitVec.ofNat 64 k) = prog.code[off + k] ∧
      m.perm (pc + BitVec.ofNat 64 k) = some Perm.rx ∧
      m.isLazyFree (pc + BitVec.ofNat 64 k) = false := by
    intro k hk
    have e : pc + BitVec.ofNat 64 k = prog.base + BitVec.ofNat 64 (off + k) := by
      rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
    rw [e]; exact hcode _ (by omega)
  have hget : ∀ k (hk : k < 4), prog.code[off + k] = (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
    intro k hk
    simp only [← hdrop, List.getElem_drop]
  have hpcn : pc.toNat = prog.base.toNat + off := by
    rw [hpc, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hal' : ¬ pc.toNat % 4 ≠ 0 := by omega
  simp only [hal', ↓reduceIte]
  have hx : m.canExec pc 4 = true := by
    unfold Memory.canExec
    rw [Memory.allPerm_iff]
    intro k hk
    rw [(hb k hk).2.1]; rfl
  rw [hx]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hr : m.read32 pc = b3 ++ b2 ++ b1 ++ b0 := by
    have h0 := hb 0 (by omega); have h1 := hb 1 (by omega)
    have h2 := hb 2 (by omega); have h3 := hb 3 (by omega)
    have g0 := hget 0 (by omega); have g1 := hget 1 (by omega)
    have g2 := hget 2 (by omega); have g3 := hget 3 (by omega)
    simp only [Memory.read32]
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
    rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0.1, g0,
      show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1.1, g1,
      show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2.1, g2,
      show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3.1, g3]
  rw [hr]; exact h

end Program

/-! ## Frozen-memory preservation for hooks and supervisor calls -/

/-- Every hook of `prog` keeps frozen memory (`Memory.KeepsFrozen`) and preserves `symtab`, so
    `Step.extern_fault` never applies. -/
def Program.HooksKeepFrozen (prog : Program) : Prop :=
  ∀ (pc : BitVec 64) (f : State → State) (s : State),
    prog.externAt? pc = some f → s.mem.KeepsFrozen (f s).mem ∧ (f s).symtab = s.symtab

/-- Supervisor-call handler `svc` preserves frozen memory cells (`Memory.KeepsFrozenCells`),
    `tpidrEl0`, and `symtab`, so `evalSvc svc s = svc s`. -/
def SvcKeepsFrozen (svc : State → State) : Prop :=
  ∀ s : State,
    s.mem.KeepsFrozenCells (svc s).mem ∧
    (svc s).tpidrEl0 = s.tpidrEl0 ∧
    (svc s).symtab = s.symtab

theorem evalSvc_eq_of_svcKeepsFrozen {svc : State → State}
    (h : SvcKeepsFrozen svc) (s : State) : evalSvc svc s = svc s := by
  obtain ⟨hk, ht, hs⟩ := h s
  have hmem :
      ({ cells := fun a => if (s.mem.perm a).frozen then s.mem.cells a else (svc s).mem.cells a } :
        Memory) = (svc s).mem := by
    congr 1; funext a
    by_cases hf : (s.mem.perm a).frozen = true
    · simp [hf, hk a hf]
    · simp [hf]
  unfold evalSvc
  dsimp only
  rw [hmem, ← ht, ← hs]

theorem dispatch_tpidrEl0
    (table : List (BitVec 64 × (State → State))) (s : State)
    (htab : ∀ p ∈ table, (p.2 s).tpidrEl0 = s.tpidrEl0) :
    (Syscall.dispatch table s).tpidrEl0 = s.tpidrEl0 := by
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · rfl

private abbrev StateTpidrEq (tp : BitVec 64) (s : State) : Prop := s.tpidrEl0 = tp

private theorem stateTpidrEq_ite {tp : BitVec 64} {c : Prop} [Decidable c] {s₁ s₂ : State}
    (h₁ : c → StateTpidrEq tp s₁) (h₂ : ¬c → StateTpidrEq tp s₂) :
    StateTpidrEq tp (if c then s₁ else s₂) := by
  split
  · exact h₁ ‹_›
  · exact h₂ ‹_›

private theorem tpidr_execReadCommon (s : State) (isPread : Bool) :
    StateTpidrEq s.tpidrEl0 (execReadCommon s isPread) := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]
  repeat' (apply stateTpidrEq_ite <;> intro)
  any_goals rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply stateTpidrEq_ite <;> intro)
    all_goals rfl
  · dsimp only; repeat' (apply stateTpidrEq_ite <;> intro)
    all_goals (try cases isPread) <;> rfl
private theorem tpidr_execRead (s : State) :
    StateTpidrEq s.tpidrEl0 (execRead s) := tpidr_execReadCommon s false
private theorem tpidr_execPread64 (s : State) :
    StateTpidrEq s.tpidrEl0 (execPread64 s) := tpidr_execReadCommon s true
private theorem tpidr_execWrite (s : State) :
    StateTpidrEq s.tpidrEl0 (execWrite s) := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  repeat' (apply stateTpidrEq_ite <;> intro)
  any_goals rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply stateTpidrEq_ite <;> intro)
    all_goals rfl
  · dsimp only; repeat' (apply stateTpidrEq_ite <;> intro)
    all_goals rfl
private theorem tpidr_execExit (s : State) :
    StateTpidrEq s.tpidrEl0 (execExit s) := rfl
private theorem tpidr_execFcntl (s : State) :
    StateTpidrEq s.tpidrEl0 (execFcntl s) := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; (repeat' split) <;> rfl
private theorem tpidr_execIoctl (s : State) :
    StateTpidrEq s.tpidrEl0 (execIoctl s) := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; (repeat' split) <;> rfl
private theorem tpidr_execOpenat (s : State) :
    StateTpidrEq s.tpidrEl0 (execOpenat s) := by
  dsimp (config := { zetaHave := true }) only [execOpenat, applyOpenVerdict]
  (repeat' split) <;> rfl
private theorem tpidr_execClose (s : State) :
    StateTpidrEq s.tpidrEl0 (execClose s) := by
  dsimp (config := { zetaHave := true }) only [execClose]; (repeat' split) <;> rfl
private theorem tpidr_execLseek (s : State) :
    StateTpidrEq s.tpidrEl0 (execLseek s) := by
  dsimp (config := { zetaHave := true }) only [execLseek]; (repeat' split) <;> rfl
private theorem tpidr_execFstat (s : State) :
    StateTpidrEq s.tpidrEl0 (execFstat s) := by
  dsimp (config := { zetaHave := true }) only [execFstat]; (repeat' split) <;> rfl
private theorem tpidr_execPpoll (s : State) :
    StateTpidrEq s.tpidrEl0 (execPpoll s) := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  by_cases h1 : (s.readReg64 Reg.x2 == 0#64) = true
  · simp only [h1, ↓reduceIte]; rfl
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (!decide ((s.readReg64 Reg.x2).toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm Option.r (s.readReg64 Reg.x2) 16) = true
  · simp only [h2, ↓reduceIte]; rfl
  simp only [eq_false h2, ↓reduceIte]
  by_cases h3 : (!s.mem.canRead (s.readReg64 Reg.x2) 16) = true
  · simp only [h3, ↓reduceIte]; rfl
  simp only [eq_false h3, ↓reduceIte]
  by_cases h4 : ((s.mem.read64 (s.readReg64 Reg.x2)).slt 0#64 || (s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).slt 0#64 || !decide ((s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).toNat < 1000000000)) = true
  · simp only [h4, ↓reduceIte]; rfl
  simp only [eq_false h4, ↓reduceIte]
  (repeat' split) <;> rfl
private theorem tpidr_execBrk (s : State) :
    StateTpidrEq s.tpidrEl0 (execBrk s) := by
  dsimp (config := { zetaHave := true }) only [execBrk]; (repeat' split) <;> rfl
private theorem tpidr_execMunmap (s : State) :
    StateTpidrEq s.tpidrEl0 (execMunmap s) := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; (repeat' split) <;> rfl
private theorem tpidr_execMremap (s : State) :
    StateTpidrEq s.tpidrEl0 (execMremap s) := by
  dsimp (config := { zetaHave := true }) only [execMremap]; (repeat' split) <;> rfl
private theorem tpidr_execMmap (s : State) :
    StateTpidrEq s.tpidrEl0 (execMmap s) := by
  dsimp (config := { zetaHave := true }) only [execMmap]; (repeat' split) <;> rfl
private theorem tpidr_execMprotect (s : State) :
    StateTpidrEq s.tpidrEl0 (execMprotect s) := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; (repeat' split) <;> rfl
private theorem tpidr_execMadvise (s : State) :
    StateTpidrEq s.tpidrEl0 (execMadvise s) := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; (repeat' split) <;> rfl
private theorem tpidr_execSigaltstack (s : State) :
    StateTpidrEq s.tpidrEl0 (execSigaltstack s) := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; (repeat' split) <;> rfl
private theorem tpidr_execRtSigaction (s : State) :
    StateTpidrEq s.tpidrEl0 (execRtSigaction s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; (repeat' split) <;> rfl
private theorem tpidr_execRtSigprocmask (s : State) :
    StateTpidrEq s.tpidrEl0 (execRtSigprocmask s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; (repeat' split) <;> rfl
private theorem tpidr_execTkill (s : State) :
    StateTpidrEq s.tpidrEl0 (execTkill s) := by
  dsimp (config := { zetaHave := true }) only [execTkill]; (repeat' split) <;> rfl
private theorem tpidr_execTgkill (s : State) :
    StateTpidrEq s.tpidrEl0 (execTgkill s) := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; (repeat' split) <;> rfl
private theorem tpidr_execClockGettime (s : State) :
    StateTpidrEq s.tpidrEl0 (execClockGettime s) := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; (repeat' split) <;> rfl
private theorem tpidr_execGetrandom (s : State) :
    StateTpidrEq s.tpidrEl0 (execGetrandom s) := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; (repeat' split) <;> rfl
private theorem tpidr_execSetTidAddress (s : State) :
    StateTpidrEq s.tpidrEl0 (execSetTidAddress s) := rfl
private theorem tpidr_execSchedGetaffinity (s : State) :
    StateTpidrEq s.tpidrEl0 (execSchedGetaffinity s) := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; (repeat' split) <;> rfl
private theorem tpidr_execGetpid (s : State) :
    StateTpidrEq s.tpidrEl0 (execGetpid s) := rfl

private theorem tpidr_rwvFrame : ProofLib.RwvFrame (fun a b => b.tpidrEl0 = a.tpidrEl0) where
  refl _ := rfl
  trans _ _ _ h1 h2 := h2.trans h1
  reg _ _ _ := rfl
  pc _ := rfl
  status _ _ := rfl
  regsPc _ _ _ := rfl

private theorem tpidr_execReadv (s : State) : StateTpidrEq s.tpidrEl0 (execReadv s) :=
  ProofLib.execReadv_preserves tpidr_rwvFrame tpidr_execRead s
private theorem tpidr_execWritev (s : State) : StateTpidrEq s.tpidrEl0 (execWritev s) :=
  ProofLib.execWritev_preserves tpidr_rwvFrame tpidr_execWrite s

private theorem standardEntry_tpidrEl0 (s : State) :
    ∀ p ∈ Syscall.standardTable, (p.2 s).tpidrEl0 = s.tpidrEl0 := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact tpidr_execRead s
  · exact tpidr_execWrite s
  · exact tpidr_execReadv s
  · exact tpidr_execWritev s
  · exact tpidr_execExit s
  · exact tpidr_execExit s
  · exact tpidr_execFcntl s
  · exact tpidr_execIoctl s
  · exact tpidr_execOpenat s
  · exact tpidr_execClose s
  · exact tpidr_execLseek s
  · exact tpidr_execPread64 s
  · exact tpidr_execFstat s
  · exact tpidr_execPpoll s
  · exact tpidr_execBrk s
  · exact tpidr_execMunmap s
  · exact tpidr_execMremap s
  · exact tpidr_execMmap s
  · exact tpidr_execMprotect s
  · exact tpidr_execMadvise s
  · exact tpidr_execTkill s
  · exact tpidr_execTgkill s
  · exact tpidr_execSigaltstack s
  · exact tpidr_execRtSigaction s
  · exact tpidr_execRtSigprocmask s
  · exact tpidr_execClockGettime s
  · exact tpidr_execGetrandom s
  · exact tpidr_execSetTidAddress s
  · exact tpidr_execSchedGetaffinity s
  · exact tpidr_execGetpid s
  · exact tpidr_execGetpid s

private theorem subset_standardTable_keepsFrozen {table : List (BitVec 64 × (State → State))}
    (hsub : ∀ p ∈ table, p ∈ Syscall.standardTable) :
    SvcKeepsFrozen (Syscall.dispatch table) :=
  fun s =>
    ⟨dispatch_keepsFrozenCells table s (fun p hp => standardEntry_keepsFrozen s p (hsub p hp)),
     dispatch_tpidrEl0 table s (fun p hp => standardEntry_tpidrEl0 s p (hsub p hp)),
     dispatch_symtab table s (fun p hp => standardEntry_symtab s p (hsub p hp))⟩

theorem svcKeepsFrozen_noSyscalls : SvcKeepsFrozen noSyscalls :=
  fun s => ⟨Memory.KeepsFrozenCells.refl s.mem, rfl, rfl⟩

theorem svcKeepsFrozen_none : SvcKeepsFrozen Syscall.none :=
  fun s => ⟨Memory.KeepsFrozenCells.refl s.mem, rfl, rfl⟩

theorem svcKeepsFrozen_stdioWrite : SvcKeepsFrozen Syscall.stdioWrite :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.stdioWriteTable, Syscall.standardTable, Syscall.stdioTable] at hp ⊢
    subst hp; simp

theorem svcKeepsFrozen_stdioCli : SvcKeepsFrozen Syscall.stdioCli :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable] at hp ⊢; exact Or.inl hp

theorem svcKeepsFrozen_fileIo : SvcKeepsFrozen Syscall.fileIo :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.fileIoTable, Syscall.standardTable] at hp ⊢
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (Or.inl hp)

theorem svcKeepsFrozen_poll : SvcKeepsFrozen Syscall.poll :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; left; exact hp

theorem svcKeepsFrozen_alloc : SvcKeepsFrozen Syscall.alloc :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; right; left; exact hp

theorem svcKeepsFrozen_signals : SvcKeepsFrozen Syscall.signals :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; right; right; left; exact hp

theorem svcKeepsFrozen_time : SvcKeepsFrozen Syscall.time :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; right; right; right; left; exact hp

theorem svcKeepsFrozen_random : SvcKeepsFrozen Syscall.random :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; right; right; right; right; left; exact hp

theorem svcKeepsFrozen_misc : SvcKeepsFrozen Syscall.misc :=
  subset_standardTable_keepsFrozen fun p hp => by
    simp [Syscall.standardTable]; right; right; right; right; right; right; right; exact hp

theorem svcKeepsFrozen_standard : SvcKeepsFrozen Syscall.standard :=
  subset_standardTable_keepsFrozen fun _ hp => hp

@[simp, arm64_norm]
theorem evalSvc_noSyscalls (s : State) : evalSvc noSyscalls s = noSyscalls s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_noSyscalls s

@[simp, arm64_norm]
theorem evalSvc_none (s : State) : evalSvc Syscall.none s = Syscall.none s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_none s

@[simp, arm64_norm]
theorem evalSvc_stdioWrite (s : State) : evalSvc Syscall.stdioWrite s = Syscall.stdioWrite s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_stdioWrite s

@[simp, arm64_norm]
theorem evalSvc_stdioCli (s : State) : evalSvc Syscall.stdioCli s = Syscall.stdioCli s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_stdioCli s

@[simp, arm64_norm]
theorem evalSvc_fileIo (s : State) : evalSvc Syscall.fileIo s = Syscall.fileIo s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_fileIo s

@[simp, arm64_norm]
theorem evalSvc_poll (s : State) : evalSvc Syscall.poll s = Syscall.poll s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_poll s

@[simp, arm64_norm]
theorem evalSvc_alloc (s : State) : evalSvc Syscall.alloc s = Syscall.alloc s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_alloc s

@[simp, arm64_norm]
theorem evalSvc_signals (s : State) : evalSvc Syscall.signals s = Syscall.signals s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_signals s

@[simp, arm64_norm]
theorem evalSvc_time (s : State) : evalSvc Syscall.time s = Syscall.time s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_time s

@[simp, arm64_norm]
theorem evalSvc_random (s : State) : evalSvc Syscall.random s = Syscall.random s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_random s

@[simp, arm64_norm]
theorem evalSvc_misc (s : State) : evalSvc Syscall.misc s = Syscall.misc s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_misc s

@[simp, arm64_norm]
theorem evalSvc_standard (s : State) : evalSvc Syscall.standard s = Syscall.standard s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_standard s

@[simp, arm64_norm]
theorem evalInst_eq_execInstWithSvc {prog : Program} (h : SvcKeepsFrozen prog.svc)
    (inst : Instr) (s : State) :
    prog.evalInst inst s = execInstWithSvc prog.svc inst s := by
  unfold Program.evalInst
  have heq : evalSvc prog.svc = prog.svc := funext (evalSvc_eq_of_svcKeepsFrozen h)
  rw [heq]

theorem Program.evalInst_eq_execInst {prog : Program}
    (inst : Instr) (s : State) (h : prog.svc = Syscall.standard := by rfl) :
    prog.evalInst inst s = execInst inst s := by
  rw [evalInst_eq_execInstWithSvc (h ▸ svcKeepsFrozen_standard), h]

@[simp, arm64_norm]
theorem evalInst_pureMem (inst : Instr) (s : State) :
    Program.pureMem.evalInst inst s = execInst inst s :=
  Program.evalInst_eq_execInst inst s rfl

theorem execInst_keepsFrozen (inst : Instr) (s : State) : s.mem.KeepsFrozen (execInst inst s).mem := by
  rw [← evalInst_pureMem]
  exact evalInst_keepsFrozen Program.pureMem inst s

@[simp, arm64_norm]
theorem Program.svc_rebase (prog : Program) (b : BitVec 64)
    (X O : String → Option (State → State)) :
    (prog.rebase b X O).svc = prog.svc := by
  funext s; cases s; rfl

@[simp, arm64_norm]
theorem Program.svc_ofWords (b : BitVec 64) (ws : List (BitVec 32))
    (syms : List (String × BitVec 64)) (svc : State → State) :
    (Program.ofWords b ws syms svc).svc = svc := by
  funext s; cases s; rfl

@[simp, arm64_norm]
theorem Program.svc_pureWithSvc (svc : State → State) :
    (Program.pureWithSvc svc).svc = svc := by
  funext s; cases s; rfl

end Arm64
