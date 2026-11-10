/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Region
public import ProofLib.BV.Bits
import Arm64.Trusted.Spec.SepLogic

/-!
# Stack Regions and 8-Byte Cell Decomposition

Defines `stackAt sp n` (`memRegion (sp - n) n`), `cells a k` (`k` consecutive 8-byte existential
cells), the `cells_unfold` macro, stack-frame splitting lemmas, and 16-byte stack-pointer
alignment preservation across downward frame allocation.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- `n` bytes of stack below `sp` (`memRegion (sp - n) n`). -/
abbrev stackAt (sp : BitVec 64) (n : Nat) : SepProp :=
  memRegion (sp - BitVec.ofNat 64 n) n

/-- Equivalence between `stackAt sp n` (`memRegion (sp - BitVec.ofNat 64 n) n`) and
    `stackFrameAt sp n` (`n ≤ 2 ^ 64`). -/
theorem stackAt_eq_stackFrameAt (sp : BitVec 64) (n : Nat)
    (hn : n ≤ 2 ^ 64 := by first | decide | omega) :
    stackAt sp n = stackFrameAt sp n :=
  (stackFrameAt_eq_memRegion sp n hn).symm

/-- `k` consecutive owned 8-byte cells starting at `a`. -/
def cells (a : BitVec 64) : Nat → SepProp
  | 0 => emp
  | k + 1 => ∃∗ v : BitVec 64, (a ↦₆₄ v) ∗ cells (a + 8#64) k

theorem cells_zero (a : BitVec 64) : cells a 0 = emp := rfl

theorem cells_succ (a : BitVec 64) (k : Nat) :
    cells a (k + 1) = ∃∗ v : BitVec 64, (a ↦₆₄ v) ∗ cells (a + 8#64) k := rfl

/-- Split `cells a (m + n)` into `cells a m ∗ cells (a + 8 * m) n`. -/
theorem cells_split (a : BitVec 64) (m n : Nat) :
    cells a (m + n) = cells a m ∗ cells (a + BitVec.ofNat 64 (8 * m)) n := by
  induction m generalizing a with
  | zero =>
    simp only [Nat.zero_add, cells_zero, emp_sepConj, Nat.mul_zero, BitVec.add_zero]
  | succ m ih =>
    rw [Nat.succ_add, cells_succ, cells_succ, ih (a + 8#64)]
    simp only [sepExists_sepConj_left]
    congr 1; funext v
    rw [sepConj_assoc]
    congr 2
    have : a + 8#64 + BitVec.ofNat 64 (8 * m) = a + BitVec.ofNat 64 (8 * (m + 1)) := by
      rw [show 8 * (m + 1) = 8 + 8 * m by omega, BitVec.ofNat_add, BitVec.add_assoc]
    rw [this]

/-- Split `cells (sp - BitVec.ofNat 64 a) (k1 + k2)` into
    `cells (sp - BitVec.ofNat 64 a) k1 ∗ cells (sp - BitVec.ofNat 64 b) k2`
    when `a = b + 8 * k1`. -/
theorem cells_split_sub (sp : BitVec 64) (a b k1 k2 : Nat)
    (ha : a = b + 8 * k1 := by omega) :
    cells (sp - BitVec.ofNat 64 a) (k1 + k2) =
      cells (sp - BitVec.ofNat 64 a) k1 ∗ cells (sp - BitVec.ofNat 64 b) k2 := by
  subst ha
  rw [cells_split]
  have h_add : sp - BitVec.ofNat 64 (b + 8 * k1) + BitVec.ofNat 64 (8 * k1) =
      sp - BitVec.ofNat 64 b := by
    rw [BitVec.ofNat_add, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  rw [h_add]

/-- Unfold one cell of `cells (sp - a) _` keeping literal offsets (`sp - 48#64`, `sp - 40#64`, ...). -/
theorem cells_sub_succ (sp : BitVec 64) (a k : Nat) (hk : k ≠ 0) (h : 8 ≤ a) :
    cells (sp - BitVec.ofNat 64 a) k =
      ∃∗ v : BitVec 64, ((sp - BitVec.ofNat 64 a) ↦₆₄ v) ∗
        cells (sp - BitVec.ofNat 64 (a - 8)) (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [cells_succ]
  congr 1; funext v; congr 2
  have : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - 8) + 8#64 := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [this, ← BitVec.sub_sub, BitVec.sub_add_cancel]

/-- Entailment step peeling one concrete cell `(sp - a) ↦₆₄ v` off `cells (sp - a) k`. -/
theorem cells_sub_succ_entails {sp : BitVec 64} (a k : Nat) {v : BitVec 64} {R : SepProp}
    (h : R ⊢ cells (sp - BitVec.ofNat 64 (a - 8)) (k - 1))
    (hk : k ≠ 0 := by decide) (ha : 8 ≤ a := by decide) :
    (((sp - BitVec.ofNat 64 a) ↦₆₄ v) ∗ R) ⊢ cells (sp - BitVec.ofNat 64 a) k := by
  rw [cells_sub_succ sp a k hk ha]
  exact Entails.sepExists_right v (sepConj_mono_right h)

/-- Unfold `cells (sp - N#64) k` (literal `N`, `k`) everywhere into explicit `∃∗` cells at
    literal offsets `sp - N#64`, `sp - (N-8)#64`, ... -/
macro "cells_unfold" : tactic =>
  `(tactic| simp (disch := decide) only [ProofLib.cells_sub_succ, Nat.reduceSub,
    ProofLib.cells_zero, sepConj_emp,
    sepExists_sepConj_right] at *)

theorem memRegion_cells (a : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64) :
    memRegion a (8 * k) = cells a k := by
  induction k generalizing a with
  | zero => exact memRegion_zero a
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, memRegion_split a 8 (8 * k) (by omega),
      memRegion_eight, ih _ (by omega), cells_succ, sepExists_sepConj_left]

/-- Convert `stackAt sp (8 * k)` directly into `cells (sp - 8 * k) k`. -/
theorem stackAt_eq_cells (sp : BitVec 64) (k : Nat) (h : 8 * k ≤ 2 ^ 64 := by decide) :
    stackAt sp (8 * k) = cells (sp - BitVec.ofNat 64 (8 * k)) k :=
  memRegion_cells (sp - BitVec.ofNat 64 (8 * k)) k h

/-- Split the top `8 * k` bytes of a stack region into cells. -/
theorem stackAt_split_cells (sp : BitVec 64) (n k : Nat) (h : n + 8 * k ≤ 2 ^ 64) :
    stackAt sp (n + 8 * k) =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) n ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  simp only [stackAt]
  rw [memRegion_split _ n (8 * k) h, memRegion_cells _ k (by omega)]
  generalize hj : 8 * k = j at *
  have e1 : sp - BitVec.ofNat 64 (n + j) = sp - BitVec.ofNat 64 j - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + j) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 j := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

/-- Split off the unused bottom `d` bytes of a stack region. -/
theorem stackAt_split_bottom (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n := by
  simp only [stackAt]
  rw [show n + d = d + n by omega, memRegion_split _ d n (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

/-- Carve the top `8 * k` bytes of a stack region into cells. -/
theorem stackAt_frame (sp : BitVec 64) (n k : Nat) (h : 8 * k ≤ n) (hn : n ≤ 2 ^ 64 := by decide) :
    stackAt sp n =
      stackAt (sp - BitVec.ofNat 64 (8 * k)) (n - 8 * k) ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  have := stackAt_split_cells sp (n - 8 * k) k (by omega)
  rwa [show n - 8 * k + 8 * k = n by omega] at this

/-- Keep only the top `m` bytes of a stack region. -/
theorem stackAt_shrink (sp : BitVec 64) (n m : Nat) (h : m ≤ n) (hn : n ≤ 2 ^ 64 := by decide) :
    stackAt sp n = memRegion (sp - BitVec.ofNat 64 n) (n - m) ∗ stackAt sp m := by
  have := stackAt_split_bottom sp m (n - m) (by omega)
  rwa [show m + (n - m) = n by omega] at this

/-- Entailment form of `stackAt_shrink`: keep the top `m` bytes and frame out the bottom `n - m` bytes. -/
theorem stackAt_shrink_entails (sp : BitVec 64) (n m : Nat) (h : m ≤ n)
    (hn : n ≤ 2 ^ 64 := by decide) :
    stackAt sp n ⊢ stackAt sp m ∗ memRegion (sp - BitVec.ofNat 64 n) (n - m) := by
  rw [stackAt_shrink sp n m h hn, sepConj_comm]
  exact Entails.refl _

/-- Carve the top `b` bytes of a stack region as a raw region. -/
theorem stackAt_region (sp : BitVec 64) (n b : Nat) (h : n + b ≤ 2 ^ 64) :
    stackAt sp (n + b) =
      stackAt (sp - BitVec.ofNat 64 b) n ∗ memRegion (sp - BitVec.ofNat 64 b) b := by
  simp only [stackAt]
  rw [memRegion_split _ n b h]
  have e1 : sp - BitVec.ofNat 64 (n + b) = sp - BitVec.ofNat 64 b - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  rw [e1, BitVec.sub_add_cancel]

/-- Split the top of a stack region (from the top down) into `k` cells, a `bl`-byte raw region and
    `a` cells; the rest stays a stack region. -/
theorem stackAt_frame3 (sp : BitVec 64) (N a bl k : Nat) (h : 8 * a + bl + 8 * k ≤ N)
    (hN : N ≤ 2 ^ 64 := by decide) :
    stackAt sp N =
      stackAt (sp - BitVec.ofNat 64 (8 * k) - BitVec.ofNat 64 bl - BitVec.ofNat 64 (8 * a))
          (N - (8 * a + bl + 8 * k)) ∗
        cells (sp - BitVec.ofNat 64 (8 * k) - BitVec.ofNat 64 bl - BitVec.ofNat 64 (8 * a)) a ∗
        memRegion (sp - BitVec.ofNat 64 (8 * k) - BitVec.ofNat 64 bl) bl ∗
        cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  rw [stackAt_frame sp N k (by omega) hN]
  rw [show N - 8 * k = (N - (8 * a + bl + 8 * k) + 8 * a) + bl by omega,
    stackAt_region _ _ bl (by omega), stackAt_split_cells _ _ a (by omega)]
  simp only [sepConj_assoc]

/-- Parametric wrapper-frame split: a `wrapperStack`-byte stack region below `sp` splits into
    its unused bottom (`wrapperStack - hookStack - 8 * k` bytes), a `hookStack`-byte inner stack
    frame below `sp - 8 * k`, and `k` 8-byte local frame cells starting at `sp - 8 * k`. -/
theorem wrapperFrame_split (sp : BitVec 64) {wrapperStack hookStack : Nat} (k : Nat)
    (hk : hookStack + 8 * k ≤ wrapperStack) (hw : wrapperStack ≤ 2 ^ 64 := by decide) :
    stackAt sp wrapperStack =
      memRegion (sp - BitVec.ofNat 64 wrapperStack) (wrapperStack - hookStack - 8 * k) ∗
        stackAt (sp - BitVec.ofNat 64 (8 * k)) hookStack ∗ cells (sp - BitVec.ofNat 64 (8 * k)) k := by
  have h1 := stackAt_split_bottom sp (hookStack + 8 * k) (wrapperStack - hookStack - 8 * k) (by omega)
  rw [show hookStack + 8 * k + (wrapperStack - hookStack - 8 * k) = wrapperStack by omega] at h1
  rw [h1, stackAt_split_cells sp hookStack k (by omega)]

/-- Subtracting any 16-byte-aligned offset `n` from a 16-byte-aligned stack pointer `sp`
    preserves 16-byte alignment (`(sp - n) &&& 15#64 == 0#64`). -/
theorem spAligned_sub (sp : BitVec 64) (n : BitVec 64)
    (hsp : (sp &&& 15#64 == 0#64) = true)
    (hn : (n &&& 15#64 == 0#64) = true := by rfl) :
    ((sp - n) &&& 15#64 == 0#64) = true := by
  revert hsp hn; bv_bits

/-- Boolean-equality form of `spAligned_sub` with `sp` and `off` implicit. -/
theorem spAligned_sub_beq {sp off : BitVec 64}
    (hsp : (sp &&& 15#64 == 0#64) = true)
    (hoff : (off &&& 15#64 == 0#64) = true := by rfl) :
    ((sp - off) &&& 15#64 == 0#64) = true :=
  spAligned_sub sp off hsp hoff

/-- Subtracting any 16-byte-aligned offset `n` from `s.sp` when `s.spAligned = true`
    preserves 16-byte alignment. -/
theorem _root_.Arm64.State.spAligned_sub (s : State) (n : BitVec 64)
    (hsp : s.spAligned = true)
    (hn : (n &&& 15#64 == 0#64) = true := by rfl) :
    ((s.sp - n) &&& 15#64 == 0#64) = true :=
  ProofLib.spAligned_sub s.sp n hsp hn

end ProofLib
