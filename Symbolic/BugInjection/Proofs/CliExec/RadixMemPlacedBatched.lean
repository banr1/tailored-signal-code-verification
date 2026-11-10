/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

/-!
# 64-Byte Line-Batched VM Operations

Defines 64-byte cache-line-batched counterparts (`allPermB`, `canMapB`, `allAnonB`, `countPermB`,
`countRwB`, `unmapWritableB`, `unmapNonFrozenB`, `mapZeroB`, `setPermNonFrozenB`, and
`sanitizeMmapAddrFastB`) of the per-byte `FastMem` VM operations in `RadixMem` and
`RadixMemPlaced`, and proves value-level equality (`=`) with each per-byte definition.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched

set_option autoImplicit false

open Arm64 Arm64.Memory
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

theorem btSet_twig_same {α : Type} (d k : Nat) (v1 v2 : α) :
    btSet d (.twig k v1) k v2 = .twig k v2 := by
  cases d <;> simp [btSet, mkTwig_eq, Nat.beq_refl]

theorem btSet_btSet_same {α : Type} :
    ∀ (d : Nat) (tr : BinTree α) (k : Nat) (v1 v2 : α),
      btSet d (btSet d tr k v1) k v2 = btSet d tr k v2
  | 0, _, _, _, _ => rfl
  | d + 1, .empty, k, v1, v2 => by
    simp [btSet, mkTwig_eq, Nat.beq_refl]
  | d + 1, .twig kj u, k, v1, v2 => by
    dsimp only [btSet]
    cases hk : Nat.beq k kj
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hkj2 : Nat.beq (Nat.mod kj 2) 0 <;> cases hk2 : Nat.beq (Nat.mod k 2) 0 <;>
        simp [mkTwig_eq, mkBranchL_eq, mkBranchR_eq, btSet, hk2, btSet_twig_same, btSet_btSet_same d]
    · have heq : k = kj := Nat.beq_eq.mp hk
      subst heq
      simp [btSet, Nat.beq_refl]
  | d + 1, .branch lo hi, k, v1, v2 => by
    dsimp only [btSet]
    cases hk2 : Nat.beq (Nat.mod k 2) 0 <;>
      simp [mkBranchL_eq, mkBranchR_eq, btSet, hk2, btSet_btSet_same d]

theorem btSet_of_btGet_eq_some {α : Type} :
    ∀ (d : Nat) (tr : BinTree α) (k : Nat) (v : α),
      btGet d tr k = some v → btSet d tr k v = tr
  | _, .empty, _, _, h => by simp at h
  | d, .twig kj u, k, v, h => by
    rw [btGet_twig] at h
    cases hk : Nat.beq k kj
    · simp [hk] at h
    · simp only [hk, ↓reduceIte, Option.some.injEq] at h
      have heq : k = kj := Nat.beq_eq.mp hk
      subst heq h
      cases d <;> simp [btSet, mkTwig_eq, Nat.beq_refl]
  | 0, .branch _ _, _, _, h => by simp [btGet] at h
  | d + 1, .branch lo hi, k, v, h => by
    dsimp only [btGet, btSet] at h ⊢
    cases hk2 : Nat.beq (Nat.mod k 2) 0
    · simp only [hk2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [mkBranchR_eq, btSet_of_btGet_eq_some d hi (Nat.div k 2) v h]
    · simp only [hk2, ↓reduceIte] at h ⊢
      rw [mkBranchL_eq, btSet_of_btGet_eq_some d lo (Nat.div k 2) v h]

theorem btDel_btSet_of_btGet_eq_some {α : Type} :
    ∀ (d : Nat) (tr : BinTree α) (k : Nat) (v0 v1 : α),
      btGet d tr k = some v0 → btDel d (btSet d tr k v1) k = btDel d tr k
  | _, .empty, _, _, _, h => by simp at h
  | d, .twig kj u, k, _, v1, h => by
    rw [btGet_twig] at h
    cases hk : Nat.beq k kj
    · simp [hk] at h
    · have heq : k = kj := Nat.beq_eq.mp hk
      subst heq
      cases d <;> simp [btSet, btDel, mkTwig_eq, Nat.beq_refl]
  | 0, .branch _ _, _, _, _, h => by simp [btGet] at h
  | d + 1, .branch lo hi, k, v0, v1, h => by
    dsimp only [btGet, btSet] at h ⊢
    cases hk2 : Nat.beq (Nat.mod k 2) 0
    · simp only [hk2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      rw [mkBranchR_eq]
      dsimp only [btDel]
      simp only [hk2, Bool.false_eq_true, ↓reduceIte,
        btDel_btSet_of_btGet_eq_some d hi (Nat.div k 2) v0 v1 h]
    · simp only [hk2, ↓reduceIte] at h ⊢
      rw [mkBranchL_eq]
      dsimp only [btDel]
      simp only [hk2, ↓reduceIte,
        btDel_btSet_of_btGet_eq_some d lo (Nat.div k 2) v0 v1 h]

/-- Number of 64-byte cache-line slices spanned by `[addr, addr + rem)`. -/
@[inline] def lineSpanFuel (addr rem : Nat) : Nat :=
  Nat.div (Nat.add (Nat.add (Nat.mod addr 64) rem) 63) 64

theorem lineSpanFuel_pos {addr rem : Nat} (hpos : 0 < rem) :
    1 ≤ lineSpanFuel addr rem := by
  unfold lineSpanFuel
  change 1 ≤ (addr % 64 + rem + 63) / 64
  omega

theorem lineSpanFuel_step {addr rem f : Nat} (_hpos : 0 < rem)
    (hf : lineSpanFuel addr rem ≤ f + 1) :
    let step := min rem (64 - addr % 64)
    rem - step = 0 ∨ lineSpanFuel (addr + step) (rem - step) ≤ f := by
  dsimp only
  unfold lineSpanFuel at hf ⊢
  change (addr % 64 + rem + 63) / 64 ≤ f + 1 at hf
  by_cases hle : rem ≤ 64 - addr % 64
  · left; omega
  · right
    have hstep : min rem (64 - addr % 64) = 64 - addr % 64 := by omega
    rw [hstep]
    have hmod : (addr + (64 - addr % 64)) % 64 = 0 := by omega
    change ((addr + (64 - addr % 64)) % 64 + (rem - (64 - addr % 64)) + 63) / 64 ≤ f
    rw [hmod]
    omega

theorem bv_ofNat_add (a k : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 k = BitVec.ofNat 64 (a + k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]

theorem bv_ofNat_succ (a : Nat) :
    BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) :=
  bv_ofNat_add a 1

private theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]

private theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]

theorem memory_allPerm_add (m : Memory) (pred : Option Perm → Bool) :
    ∀ (n1 n2 : Nat) (a : BitVec 64),
      m.allPerm pred a (n1 + n2) =
        (m.allPerm pred a n1 && m.allPerm pred (a + BitVec.ofNat 64 n1) n2)
  | 0, n2, a => by simp [Memory.allPerm]
  | n1 + 1, n2, a => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [Memory.allPerm]
    rw [memory_allPerm_add m pred n1 n2 (a + 1#64), Bool.and_assoc]
    have hbv : a + 1#64 + BitVec.ofNat 64 n1 = a + BitVec.ofNat 64 (n1 + 1) := by bv_omega
    rw [hbv]

theorem memory_allAnon_add (m : Memory) :
    ∀ (n1 n2 : Nat) (a : BitVec 64),
      m.allAnon a (n1 + n2) =
        (m.allAnon a n1 && m.allAnon (a + BitVec.ofNat 64 n1) n2)
  | 0, n2, a => by simp [Memory.allAnon]
  | n1 + 1, n2, a => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [Memory.allAnon]
    rw [memory_allAnon_add m n1 n2 (a + 1#64), Bool.and_assoc]
    have hbv : a + 1#64 + BitVec.ofNat 64 n1 = a + BitVec.ofNat 64 (n1 + 1) := by bv_omega
    rw [hbv]

theorem memory_countPerm_add (m : Memory) (pred : Option Perm → Bool) :
    ∀ (n1 n2 : Nat) (a : BitVec 64),
      m.countPerm pred a (n1 + n2) =
        m.countPerm pred a n1 + m.countPerm pred (a + BitVec.ofNat 64 n1) n2
  | 0, n2, a => by simp [Memory.countPerm]
  | n1 + 1, n2, a => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [Memory.countPerm]
    rw [memory_countPerm_add m pred n1 n2 (a + 1#64), ← Nat.add_assoc]
    have hbv : a + 1#64 + BitVec.ofNat 64 n1 = a + BitVec.ofNat 64 (n1 + 1) := by bv_omega
    rw [hbv]

@[inline] def optCellPerm (sb top addr : Nat) (lnOpt : Option Line64) (lo : Nat) : Option Perm :=
  match lnOpt with
  | some ln =>
    match btGet 6 ln lo with
    | some (some q, _) => some q.rwx
    | some (none, _) => none
    | none => if Nat.ble sb addr && Nat.blt addr top then some Perm.rw else none
  | none =>
    if Nat.ble sb addr && Nat.blt addr top then some Perm.rw else none

theorem optCellPerm_eq (fm : FastMem) (addr : Nat) (had : addr < 2 ^ 64) :
    optCellPerm fm.stackBase fm.stackTop addr (btGet 58 fm.lines (addr / 64)) (addr % 64) =
      fm.perm (BitVec.ofNat 64 addr) := by
  have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
  simp only [optCellPerm, FastMem.perm, FastMem.cellAt, rawCellAt, hto, ble_eq_decide, blt_eq_decide]
  cases h58 : btGet 58 fm.lines (addr / 64) with
  | none =>
    dsimp only
    cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
  | some ln =>
    dsimp only
    cases h6 : btGet 6 ln (addr % 64) with
    | none =>
      dsimp only
      cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
    | some c => rcases c with ⟨_ | q, _⟩ <;> rfl

@[inline] def optCellAnon (sb top addr : Nat) (lnOpt : Option Line64) (lo : Nat) : Bool :=
  match lnOpt with
  | some ln =>
    match btGet 6 ln lo with
    | some (some q, _) => q.anon
    | some (none, _) => false
    | none => if Nat.ble sb addr && Nat.blt addr top then Perm.rw.anon else false
  | none =>
    if Nat.ble sb addr && Nat.blt addr top then Perm.rw.anon else false

theorem optCellAnon_eq (fm : FastMem) (addr : Nat) (had : addr < 2 ^ 64) :
    optCellAnon fm.stackBase fm.stackTop addr (btGet 58 fm.lines (addr / 64)) (addr % 64) =
      fm.isAnon (BitVec.ofNat 64 addr) := by
  have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
  simp only [optCellAnon, FastMem.isAnon, FastMem.cellAt, rawCellAt, hto, ble_eq_decide, blt_eq_decide]
  cases h58 : btGet 58 fm.lines (addr / 64) with
  | none =>
    dsimp only
    cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
  | some ln =>
    dsimp only
    cases h6 : btGet 6 ln (addr % 64) with
    | none =>
      dsimp only
      cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
    | some c => rcases c with ⟨_ | q, _⟩ <;> rfl

def lineSliceAllPerm (sb top : Nat) (pred : Option Perm → Bool) (lnOpt : Option Line64)
    (addr lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    if pred (optCellPerm sb top addr lnOpt lo) then
      lineSliceAllPerm sb top pred lnOpt (Nat.add addr 1) (Nat.add lo 1) k
    else
      false

theorem lineSliceAllPerm_eq (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (k addr : Nat) (lnOpt : Option Line64),
      lnOpt = btGet 58 fm.lines (addr / 64) →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      lineSliceAllPerm fm.stackBase fm.stackTop pred lnOpt addr (addr % 64) k =
        Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) k
  | 0, _, _, _, _, _ => rfl
  | k + 1, addr, lnOpt, hln, hlo, hwrap => by
    dsimp only [lineSliceAllPerm, Memory.allPerm]
    have had : addr < 2 ^ 64 := by omega
    rw [hln, optCellPerm_eq fm addr had]
    have hperm_self : (⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr) = fm.perm (BitVec.ofNat 64 addr) :=
      (fm.perm_eq (fun _ => rfl) (BitVec.ofNat 64 addr)).symm
    rw [hperm_self]
    cases hp : pred (fm.perm (BitVec.ofNat 64 addr))
    · simp
    · simp only [↓reduceIte, Bool.true_and]
      by_cases hk0 : k = 0
      · subst hk0; rfl
      · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
        have hmod : (addr + 1) % 64 = addr % 64 + 1 := by omega
        change lineSliceAllPerm fm.stackBase fm.stackTop pred (btGet 58 fm.lines (addr / 64))
            (addr + 1) (addr % 64 + 1) k =
          Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr + 1#64) k
        rw [← hmod, bv_ofNat_succ]
        exact lineSliceAllPerm_eq fm pred k (addr + 1) _
          (congrArg (btGet 58 fm.lines) hdiv.symm) (by omega) (by omega)

theorem memory_allPerm_unmapped_slice (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (k addr : Nat),
      0 < k →
      btGet 58 fm.lines (addr / 64) = none →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (addr + k ≤ fm.stackBase ∨ fm.stackTop ≤ addr) →
      Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) k = pred none
  | 0, _, hpos, _, _, _, _ => absurd hpos (Nat.lt_irrefl 0)
  | 1, addr, _, hnone, _, hwrap, hdisj => by
    dsimp only [Memory.allPerm]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hp : (⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr) = none := by
      rw [← fm.perm_eq (fun _ => rfl)]
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, hnone]
      have hst : (decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hst]
    simp [hp]
  | k + 2, addr, _, hnone, hlo, hwrap, hdisj => by
    change (pred ((⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr)) &&
      Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr + 1#64) (k + 1)) = pred none
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hp : (⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr) = none := by
      rw [← fm.perm_eq (fun _ => rfl)]
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, hnone]
      have hst : (decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hst]
    have hdiv : (addr + 1) / 64 = addr / 64 := by omega
    rw [hp, bv_ofNat_succ,
      memory_allPerm_unmapped_slice fm pred (k + 1) (addr + 1) (by omega)
        (by rw [hdiv]; exact hnone) (by omega) (by omega) (by omega)]
    cases pred none <;> rfl

def allPermLinesLoop (fm : FastMem) (pred : Option Perm → Bool) (predNone : Bool) :
    Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | 0, _, _ + 1 => true
  | fuel + 1, addr, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    let lnOpt := btGet 58 fm.lines hi
    let sliceOk :=
      match lnOpt with
      | none =>
        if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
          predNone
        else
          lineSliceAllPerm fm.stackBase fm.stackTop pred none addr lo step
      | some ln =>
        lineSliceAllPerm fm.stackBase fm.stackTop pred (some ln) addr lo step
    if sliceOk then
      withForcedNat (Nat.add addr step) fun addr' =>
      withForcedNat (Nat.sub rem step) fun rem' =>
        allPermLinesLoop fm pred predNone fuel addr' rem'
    else
      false

theorem allPermLinesLoop_eq (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (fuel addr rem : Nat),
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      allPermLinesLoop fm pred (pred none) fuel addr rem =
        Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) rem
  | _, addr, 0, _, _ => by simp [allPermLinesLoop, Memory.allPerm]
  | 0, addr, rem + 1, hf, _ => absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, addr, rem + 1, hf, hwrap => by
    unfold allPermLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hstep_pos : 0 < step := by omega
    have hstep_le : step ≤ rem + 1 := Nat.min_le_left _ _
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hslice_eq :
        (match btGet 58 fm.lines (addr / 64) with
         | none =>
           if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
             pred none
           else
             lineSliceAllPerm fm.stackBase fm.stackTop pred none addr (addr % 64) step
         | some ln =>
           lineSliceAllPerm fm.stackBase fm.stackTop pred (some ln) addr (addr % 64) step) =
        Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) step := by
      cases h58 : btGet 58 fm.lines (addr / 64) with
      | some ln =>
        exact lineSliceAllPerm_eq fm pred step addr (some ln) h58.symm hlo_le (by omega)
      | none =>
        dsimp only
        have ha_add : Nat.add addr step = addr + step := rfl
        rw [ha_add, ble_eq_decide, ble_eq_decide]
        by_cases hdisj : (decide (addr + step ≤ fm.stackBase) || decide (fm.stackTop ≤ addr)) = true
        · simp only [hdisj, ↓reduceIte]
          have hdisj' : addr + step ≤ fm.stackBase ∨ fm.stackTop ≤ addr := by
            simpa [Bool.or_eq_true, decide_eq_true_eq] using hdisj
          exact (memory_allPerm_unmapped_slice fm pred step addr hstep_pos h58 hlo_le
            (by omega) hdisj').symm
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact lineSliceAllPerm_eq fm pred step addr none h58.symm hlo_le (by omega)
    rw [hslice_eq]
    conv_rhs => rw [hrem_split]
    rw [memory_allPerm_add ⟨fm.cellAt⟩ pred step (rem + 1 - step) (BitVec.ofNat 64 addr)]
    cases Memory.allPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) step
    · simp
    · simp only [↓reduceIte, Bool.true_and, withForcedNat_eq]
      have ha_add : Nat.add addr step = addr + step := rfl
      have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
      rw [ha_add, hr_sub, bv_ofNat_add]
      rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
      · have hz : rem + 1 - step = 0 := hzero
        rw [hz]
        cases fuel <;> rfl
      · exact allPermLinesLoop_eq fm pred fuel (addr + step) (rem + 1 - step) hnext (by omega)

def lineSliceAllAnon (sb top : Nat) (lnOpt : Option Line64) (addr lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
    if optCellAnon sb top addr lnOpt lo then
      lineSliceAllAnon sb top lnOpt (Nat.add addr 1) (Nat.add lo 1) k
    else
      false

theorem lineSliceAllAnon_eq (fm : FastMem) :
    ∀ (k addr : Nat) (lnOpt : Option Line64),
      lnOpt = btGet 58 fm.lines (addr / 64) →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      lineSliceAllAnon fm.stackBase fm.stackTop lnOpt addr (addr % 64) k =
        Memory.allAnon ⟨fm.cellAt⟩ (BitVec.ofNat 64 addr) k
  | 0, _, _, _, _, _ => rfl
  | k + 1, addr, lnOpt, hln, hlo, hwrap => by
    dsimp only [lineSliceAllAnon, Memory.allAnon]
    have had : addr < 2 ^ 64 := by omega
    rw [hln, optCellAnon_eq fm addr had]
    have han_self : (⟨fm.cellAt⟩ : Memory).isAnon (BitVec.ofNat 64 addr) = fm.isAnon (BitVec.ofNat 64 addr) :=
      (fm.isAnon_eq (fun _ => rfl) (BitVec.ofNat 64 addr)).symm
    rw [han_self]
    cases fm.isAnon (BitVec.ofNat 64 addr)
    · simp
    · simp only [↓reduceIte, Bool.true_and]
      by_cases hk0 : k = 0
      · subst hk0; rfl
      · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
        have hmod : (addr + 1) % 64 = addr % 64 + 1 := by omega
        change lineSliceAllAnon fm.stackBase fm.stackTop (btGet 58 fm.lines (addr / 64))
            (addr + 1) (addr % 64 + 1) k =
          Memory.allAnon ⟨fm.cellAt⟩ (BitVec.ofNat 64 addr + 1#64) k
        rw [← hmod, bv_ofNat_succ]
        exact lineSliceAllAnon_eq fm k (addr + 1) _
          (congrArg (btGet 58 fm.lines) hdiv.symm) (by omega) (by omega)

def allAnonLinesLoop (fm : FastMem) : Nat → Nat → Nat → Bool
  | _, _, 0 => true
  | 0, _, _ + 1 => true
  | fuel + 1, addr, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    let lnOpt := btGet 58 fm.lines hi
    let sliceOk :=
      match lnOpt with
      | none =>
        if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
          false
        else
          lineSliceAllAnon fm.stackBase fm.stackTop none addr lo step
      | some ln =>
        lineSliceAllAnon fm.stackBase fm.stackTop (some ln) addr lo step
    if sliceOk then
      withForcedNat (Nat.add addr step) fun addr' =>
      withForcedNat (Nat.sub rem step) fun rem' =>
        allAnonLinesLoop fm fuel addr' rem'
    else
      false

theorem allAnonLinesLoop_eq (fm : FastMem) :
    ∀ (fuel addr rem : Nat),
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      allAnonLinesLoop fm fuel addr rem =
        Memory.allAnon ⟨fm.cellAt⟩ (BitVec.ofNat 64 addr) rem
  | _, _, 0, _, _ => by simp [allAnonLinesLoop, Memory.allAnon]
  | 0, _, rem + 1, hf, _ => absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, addr, rem + 1, hf, hwrap => by
    unfold allAnonLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hstep_pos : 0 < step := by omega
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hslice_eq :
        (match btGet 58 fm.lines (addr / 64) with
         | none =>
           if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
             false
           else
             lineSliceAllAnon fm.stackBase fm.stackTop none addr (addr % 64) step
         | some ln =>
           lineSliceAllAnon fm.stackBase fm.stackTop (some ln) addr (addr % 64) step) =
        Memory.allAnon ⟨fm.cellAt⟩ (BitVec.ofNat 64 addr) step := by
      cases h58 : btGet 58 fm.lines (addr / 64) with
      | some ln =>
        exact lineSliceAllAnon_eq fm step addr (some ln) h58.symm hlo_le (by omega)
      | none =>
        dsimp only
        have ha_add : Nat.add addr step = addr + step := rfl
        rw [ha_add, ble_eq_decide, ble_eq_decide]
        by_cases hdisj : (decide (addr + step ≤ fm.stackBase) || decide (fm.stackTop ≤ addr)) = true
        · simp only [hdisj, ↓reduceIte]
          have hdisj' : addr + step ≤ fm.stackBase ∨ fm.stackTop ≤ addr := by
            simpa [Bool.or_eq_true, decide_eq_true_eq] using hdisj
          obtain ⟨step1, hstep1⟩ : ∃ s, step = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
          rw [hstep1]
          dsimp only [Memory.allAnon]
          have had : addr < 2 ^ 64 := by omega
          have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
          have han0 : (⟨fm.cellAt⟩ : Memory).isAnon (BitVec.ofNat 64 addr) = false := by
            rw [← fm.isAnon_eq (fun _ => rfl)]
            simp only [FastMem.isAnon, FastMem.cellAt, rawCellAt, hto, h58]
            have hst : (decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop)) = false := by
              simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
            simp [hst]
          simp [han0]
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact lineSliceAllAnon_eq fm step addr none h58.symm hlo_le (by omega)
    rw [hslice_eq]
    conv_rhs => rw [hrem_split]
    rw [memory_allAnon_add ⟨fm.cellAt⟩ step (rem + 1 - step) (BitVec.ofNat 64 addr)]
    cases Memory.allAnon ⟨fm.cellAt⟩ (BitVec.ofNat 64 addr) step
    · simp
    · simp only [↓reduceIte, Bool.true_and, withForcedNat_eq]
      have ha_add : Nat.add addr step = addr + step := rfl
      have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
      rw [ha_add, hr_sub, bv_ofNat_add]
      rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
      · have hz : rem + 1 - step = 0 := hzero
        rw [hz]
        cases fuel <;> rfl
      · exact allAnonLinesLoop_eq fm fuel (addr + step) (rem + 1 - step) hnext (by omega)

def lineSliceCountPerm (sb top : Nat) (pred : Option Perm → Bool) (lnOpt : Option Line64)
    (addr lo : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc =>
    let inc := if pred (optCellPerm sb top addr lnOpt lo) then 1 else 0
    withForcedNat (Nat.add acc inc) fun acc' =>
      lineSliceCountPerm sb top pred lnOpt (Nat.add addr 1) (Nat.add lo 1) k acc'

theorem lineSliceCountPerm_eq (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (k addr acc : Nat) (lnOpt : Option Line64),
      lnOpt = btGet 58 fm.lines (addr / 64) →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      lineSliceCountPerm fm.stackBase fm.stackTop pred lnOpt addr (addr % 64) k acc =
        acc + Memory.countPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) k
  | 0, _, acc, _, _, _, _ => by simp [lineSliceCountPerm, Memory.countPerm]
  | k + 1, addr, acc, lnOpt, hln, hlo, hwrap => by
    dsimp only [lineSliceCountPerm, Memory.countPerm]
    simp only [withForcedNat_eq]
    have had : addr < 2 ^ 64 := by omega
    rw [hln, optCellPerm_eq fm addr had]
    have hperm_self : (⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr) = fm.perm (BitVec.ofNat 64 addr) :=
      (fm.perm_eq (fun _ => rfl) (BitVec.ofNat 64 addr)).symm
    rw [hperm_self]
    set inc := if pred (fm.perm (BitVec.ofNat 64 addr)) then 1 else 0
    have hacc_add : Nat.add acc inc = acc + inc := rfl
    rw [hacc_add]
    by_cases hk0 : k = 0
    · subst hk0
      simp [lineSliceCountPerm, Memory.countPerm]
    · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
      have hmod : (addr + 1) % 64 = addr % 64 + 1 := by omega
      change lineSliceCountPerm fm.stackBase fm.stackTop pred (btGet 58 fm.lines (addr / 64))
          (addr + 1) (addr % 64 + 1) k (acc + inc) =
        acc + (inc + Memory.countPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr + 1#64) k)
      rw [← hmod, bv_ofNat_succ,
        lineSliceCountPerm_eq fm pred k (addr + 1) (acc + inc) _
          (congrArg (btGet 58 fm.lines) hdiv.symm) (by omega) (by omega)]
      omega

theorem memory_countPerm_unmapped_slice (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (k addr : Nat),
      btGet 58 fm.lines (addr / 64) = none →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (addr + k ≤ fm.stackBase ∨ fm.stackTop ≤ addr) →
      Memory.countPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) k =
        if pred none then k else 0
  | 0, _, _, _, _, _ => by simp [Memory.countPerm]
  | k + 1, addr, hnone, hlo, hwrap, hdisj => by
    dsimp only [Memory.countPerm]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hp : (⟨fm.cellAt⟩ : Memory).perm (BitVec.ofNat 64 addr) = none := by
      rw [← fm.perm_eq (fun _ => rfl)]
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, hnone]
      have hst : (decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hst]
    rw [hp, bv_ofNat_succ]
    by_cases hk0 : k = 0
    · subst hk0
      cases pred none <;> simp [Memory.countPerm]
    · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
      rw [memory_countPerm_unmapped_slice fm pred k (addr + 1) (by rw [hdiv]; exact hnone)
        (by omega) (by omega) (by omega)]
      cases pred none
      · simp
      · simp; omega

def countPermLinesLoop (fm : FastMem) (pred : Option Perm → Bool) (predNone : Bool) :
    Nat → Nat → Nat → Nat → Nat
  | _, _, 0, acc => acc
  | 0, _, _ + 1, acc => acc
  | fuel + 1, addr, rem, acc =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    let lnOpt := btGet 58 fm.lines hi
    let nextAcc :=
      match lnOpt with
      | none =>
        if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
          Nat.add acc (if predNone then step else 0)
        else
          lineSliceCountPerm fm.stackBase fm.stackTop pred none addr lo step acc
      | some ln =>
        lineSliceCountPerm fm.stackBase fm.stackTop pred (some ln) addr lo step acc
    withForcedNat nextAcc fun acc' =>
    withForcedNat (Nat.add addr step) fun addr' =>
    withForcedNat (Nat.sub rem step) fun rem' =>
      countPermLinesLoop fm pred predNone fuel addr' rem' acc'

theorem countPermLinesLoop_eq (fm : FastMem) (pred : Option Perm → Bool) :
    ∀ (fuel addr rem acc : Nat),
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      countPermLinesLoop fm pred (pred none) fuel addr rem acc =
        acc + Memory.countPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) rem
  | _, _, 0, acc, _, _ => by simp [countPermLinesLoop, Memory.countPerm]
  | 0, _, rem + 1, _, hf, _ => absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, addr, rem + 1, acc, hf, hwrap => by
    unfold countPermLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    simp only [withForcedNat_eq]
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hslice_eq :
        (match btGet 58 fm.lines (addr / 64) with
         | none =>
           if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
             Nat.add acc (if pred none then step else 0)
           else
             lineSliceCountPerm fm.stackBase fm.stackTop pred none addr (addr % 64) step acc
         | some ln =>
           lineSliceCountPerm fm.stackBase fm.stackTop pred (some ln) addr (addr % 64) step acc) =
        acc + Memory.countPerm ⟨fm.cellAt⟩ pred (BitVec.ofNat 64 addr) step := by
      cases h58 : btGet 58 fm.lines (addr / 64) with
      | some ln =>
        exact lineSliceCountPerm_eq fm pred step addr acc (some ln) h58.symm hlo_le (by omega)
      | none =>
        dsimp only
        have ha_add : Nat.add addr step = addr + step := rfl
        rw [ha_add, ble_eq_decide, ble_eq_decide]
        by_cases hdisj : (decide (addr + step ≤ fm.stackBase) || decide (fm.stackTop ≤ addr)) = true
        · simp only [hdisj, ↓reduceIte]
          have hdisj' : addr + step ≤ fm.stackBase ∨ fm.stackTop ≤ addr := by
            simpa [Bool.or_eq_true, decide_eq_true_eq] using hdisj
          rw [memory_countPerm_unmapped_slice fm pred step addr h58 hlo_le (by omega) hdisj']
          rfl
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact lineSliceCountPerm_eq fm pred step addr acc none h58.symm hlo_le (by omega)
    rw [hslice_eq]
    have ha_add : Nat.add addr step = addr + step := rfl
    have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
    rw [ha_add, hr_sub]
    rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
    · have hz : rem + 1 - step = 0 := hzero
      have hstep_eq : step = rem + 1 := by omega
      rw [hz, hstep_eq]
      cases fuel <;> simp [countPermLinesLoop]
    · rw [countPermLinesLoop_eq fm pred fuel (addr + step) (rem + 1 - step) _ hnext (by omega)]
      conv_rhs => rw [hrem_split]
      rw [memory_countPerm_add ⟨fm.cellAt⟩ pred step (rem + 1 - step) (BitVec.ofNat 64 addr),
        bv_ofNat_add]
      exact Nat.add_assoc _ _ _

@[inline] def rawOptCellPerm : Option Cell → Option Perm
  | some (some p, _) => some p.rwx
  | _ => none

@[inline] def rawOptCellShouldDel (onlyWritable : Bool) (oc : Option Cell) : Bool :=
  let p := rawOptCellPerm oc
  if onlyWritable then p.w else !p.frozen

def delLineSlice (onlyWritable : Bool) (ln : Line64) (lo : Nat) : Nat → Bool × Line64
  | 0 => (false, ln)
  | k + 1 =>
    if rawOptCellShouldDel onlyWritable (btGet 6 ln lo) then
      match btDel 6 ln lo with
      | .empty => (true, .empty)
      | ln1 => (true, (delLineSlice onlyWritable ln1 (Nat.add lo 1) k).2)
    else
      delLineSlice onlyWritable ln (Nat.add lo 1) k

def unmapLineStep (onlyWritable : Bool) (lines : BinTree Line64) (hi lo step : Nat) :
    BinTree Line64 :=
  match btGet 58 lines hi with
  | none => lines
  | some ln =>
    match delLineSlice onlyWritable ln lo step with
    | (false, _) => lines
    | (true, .empty) => btDel 58 lines hi
    | (true, ln') => btSet58Line lines hi ln'

theorem unmapLoop_add (ow : Bool) :
    ∀ (n1 n2 : Nat) (fm : FastMem) (a : BitVec 64),
      fm.unmapLoop ow a (n1 + n2) =
        (fm.unmapLoop ow a n1).unmapLoop ow (a + BitVec.ofNat 64 n1) n2
  | 0, n2, fm, a => by simp [FastMem.unmapLoop]
  | n1 + 1, n2, fm, a => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [FastMem.unmapLoop]
    rw [unmapLoop_add ow n1 n2 _ (a + 1#64)]
    have hbv : a + 1#64 + BitVec.ofNat 64 n1 = a + BitVec.ofNat 64 (n1 + 1) := by bv_omega
    rw [hbv]

private theorem unmapLoop_empty_line (ow : Bool) :
    ∀ (k addr : Nat) (lines : BinTree Line64) (sb top : Nat),
      btGet 58 lines (addr / 64) = none →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      FastMem.unmapLoop ow ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) k = ⟨lines, sb, top⟩
  | 0, _, lines, sb, top, _, _, _ => rfl
  | k + 1, addr, lines, sb, top, hnone, hlo, hwrap => by
    dsimp only [FastMem.unmapLoop]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hdel_noop : (⟨lines, sb, top⟩ : FastMem).delCellDisjoint (BitVec.ofNat 64 addr) =
        ⟨lines, sb, top⟩ := by
      simp only [FastMem.delCellDisjoint, withForcedBinTree_eq, hto, delRawCell]
      have hd : Nat.div addr 64 = addr / 64 := rfl
      rw [hd, hnone]
    have hfm' : (if (if ow then ((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).w
        else !((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).frozen) then
          (⟨lines, sb, top⟩ : FastMem).delCellDisjoint (BitVec.ofNat 64 addr)
        else ⟨lines, sb, top⟩) = ⟨lines, sb, top⟩ := by
      by_cases hc : (if ow then ((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).w
          else !((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).frozen) = true <;>
        simp [hc, hdel_noop]
    rw [hfm', bv_ofNat_succ]
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
      exact unmapLoop_empty_line ow k (addr + 1) lines sb top
        (by rw [hdiv]; exact hnone) (by omega) (by omega)

private theorem delLineSlice_false_eq (ow : Bool) :
    ∀ (k lo : Nat) (ln ln' : Line64),
      delLineSlice ow ln lo k = (false, ln') → ln' = ln
  | 0, _, ln, ln', h => by injection h with _ h2; exact h2.symm
  | k + 1, lo, ln, ln', h => by
    unfold delLineSlice at h
    split at h
    · split at h <;> simp at h
    · exact delLineSlice_false_eq ow k (Nat.add lo 1) ln ln' h

private theorem unmapLoop_some_line (ow : Bool) :
    ∀ (k addr : Nat) (lines : BinTree Line64) (sb top : Nat) (ln : Line64),
      btGet 58 lines (addr / 64) = some ln →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (∀ x : Nat, addr ≤ x → x < addr + k → ¬ (sb ≤ x ∧ x < top)) →
      FastMem.unmapLoop ow ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) k =
        ⟨match delLineSlice ow ln (addr % 64) k with
         | (false, _) => lines
         | (true, .empty) => btDel 58 lines (addr / 64)
         | (true, ln') => btSet 58 lines (addr / 64) ln', sb, top⟩
  | 0, _, lines, sb, top, ln, _, _, _, _ => by simp [FastMem.unmapLoop, delLineSlice]
  | k + 1, addr, lines, sb, top, ln, h58, hlo, hwrap, hdisj => by
    dsimp only [FastMem.unmapLoop, delLineSlice]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hdisj0 : ¬ (sb ≤ addr ∧ addr < top) := hdisj addr (Nat.le_refl _) (by omega)
    have hperm_eq : (⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr) =
        rawOptCellPerm (btGet 6 ln (addr % 64)) := by
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, h58, rawOptCellPerm]
      cases btGet 6 ln (addr % 64) with
      | none =>
        have hst : (decide (sb ≤ addr) && decide (addr < top)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        simp [hst]
      | some c => rcases c with ⟨_ | p, _⟩ <;> rfl
    have hsd_eq : (if ow then ((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).w
        else !((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).frozen) =
        rawOptCellShouldDel ow (btGet 6 ln (addr % 64)) := by
      rw [hperm_eq]; rfl
    rw [hsd_eq, bv_ofNat_succ]
    have hdisj' : ∀ x : Nat, addr + 1 ≤ x → x < addr + 1 + k → ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x (by omega) (by omega)
    cases hsd : rawOptCellShouldDel ow (btGet 6 ln (addr % 64))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hk0 : k = 0
      · subst hk0; simp [FastMem.unmapLoop, delLineSlice]
      · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
        have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
          change (addr + 1) % 64 = addr % 64 + 1; omega
        rw [unmapLoop_some_line ow k (addr + 1) lines sb top ln
          (by rw [hdiv]; exact h58) (by omega) (by omega) hdisj', hdiv, hmod]
    · simp only [↓reduceIte, FastMem.delCellDisjoint, withForcedBinTree_eq, hto, delRawCell]
      have hd : Nat.div addr 64 = addr / 64 := rfl
      have hm : Nat.mod addr 64 = addr % 64 := rfl
      rw [hd, hm, h58]
      dsimp only
      cases hdel6 : btDel 6 ln (addr % 64) with
      | empty =>
        dsimp only
        by_cases hk0 : k = 0
        · subst hk0; rfl
        · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
          exact unmapLoop_empty_line ow k (addr + 1) (btDel 58 lines (addr / 64)) sb top
            (by rw [hdiv]; exact btGet_btDel_same 58 lines (addr / 64)) (by omega) (by omega)
      | twig j u =>
        dsimp only
        rw [btSet58Line_eq]
        by_cases hk0 : k = 0
        · subst hk0; simp [FastMem.unmapLoop, delLineSlice]
        · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
          have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
            change (addr + 1) % 64 = addr % 64 + 1; omega
          rw [unmapLoop_some_line ow k (addr + 1) (btSet 58 lines (addr / 64) (.twig j u)) sb top
            (.twig j u) (by rw [hdiv]; exact btGet_btSet_same' 58 (addr / 64) lines _)
            (by omega) (by omega) hdisj', hdiv, hmod]
          cases hres : delLineSlice ow (.twig j u) (Nat.add (addr % 64) 1) k with
          | mk ch ln2 =>
            cases ch
            · have heq := delLineSlice_false_eq ow k _ _ _ hres
              subst heq; rfl
            · cases ln2 with
              | empty =>
                dsimp only
                rw [btDel_btSet_of_btGet_eq_some 58 lines (addr / 64) ln (.twig j u) h58]
              | twig j2 u2 =>
                dsimp only
                rw [btSet_btSet_same 58 lines (addr / 64) (.twig j u) (.twig j2 u2)]
              | branch x2 y2 =>
                dsimp only
                rw [btSet_btSet_same 58 lines (addr / 64) (.twig j u) (.branch x2 y2)]
      | branch x y =>
        dsimp only
        rw [btSet58Line_eq]
        by_cases hk0 : k = 0
        · subst hk0; simp [FastMem.unmapLoop, delLineSlice]
        · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
          have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
            change (addr + 1) % 64 = addr % 64 + 1; omega
          rw [unmapLoop_some_line ow k (addr + 1) (btSet 58 lines (addr / 64) (.branch x y)) sb top
            (.branch x y) (by rw [hdiv]; exact btGet_btSet_same' 58 (addr / 64) lines _)
            (by omega) (by omega) hdisj', hdiv, hmod]
          cases hres : delLineSlice ow (.branch x y) (Nat.add (addr % 64) 1) k with
          | mk ch ln2 =>
            cases ch
            · have heq := delLineSlice_false_eq ow k _ _ _ hres
              subst heq; rfl
            · cases ln2 with
              | empty =>
                dsimp only
                rw [btDel_btSet_of_btGet_eq_some 58 lines (addr / 64) ln (.branch x y) h58]
              | twig j2 u2 =>
                dsimp only
                rw [btSet_btSet_same 58 lines (addr / 64) (.branch x y) (.twig j2 u2)]
              | branch x2 y2 =>
                dsimp only
                rw [btSet_btSet_same 58 lines (addr / 64) (.branch x y) (.branch x2 y2)]

theorem unmapLineStep_eq (ow : Bool) (lines : BinTree Line64) (sb top addr step : Nat)
    (hlo : addr % 64 + step ≤ 64) (hwrap : addr + step ≤ 2 ^ 64)
    (hdisj : ∀ x : Nat, addr ≤ x → x < addr + step → ¬ (sb ≤ x ∧ x < top)) :
    (⟨unmapLineStep ow lines (addr / 64) (addr % 64) step, sb, top⟩ : FastMem) =
      FastMem.unmapLoop ow ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) step := by
  unfold unmapLineStep
  cases h58 : btGet 58 lines (addr / 64) with
  | none =>
    exact (unmapLoop_empty_line ow step addr lines sb top h58 hlo hwrap).symm
  | some ln =>
    dsimp only
    rw [unmapLoop_some_line ow step addr lines sb top ln h58 hlo hwrap hdisj]
    cases delLineSlice ow ln (addr % 64) step with
    | mk ch ln' =>
      cases ch
      · rfl
      · cases ln' <;> simp [btSet58Line_eq]

def unmapLinesLoop (onlyWritable : Bool) : Nat → BinTree Line64 → Nat → Nat → BinTree Line64
  | _, lines, _, 0 => lines
  | 0, lines, _, _ + 1 => lines
  | fuel + 1, lines, addr, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    withForcedBinTree (unmapLineStep onlyWritable lines hi lo step) fun lines' =>
    withForcedNat (Nat.add addr step) fun addr' =>
    withForcedNat (Nat.sub rem step) fun rem' =>
      unmapLinesLoop onlyWritable fuel lines' addr' rem'

theorem unmapLinesLoop_eq (ow : Bool) :
    ∀ (fuel : Nat) (lines : BinTree Line64) (sb top addr rem : Nat),
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      (∀ x : Nat, addr ≤ x → x < addr + rem → ¬ (sb ≤ x ∧ x < top)) →
      (⟨unmapLinesLoop ow fuel lines addr rem, sb, top⟩ : FastMem) =
        FastMem.unmapLoop ow ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) rem
  | fuel, lines, sb, top, _, 0, _, _, _ => by cases fuel <;> rfl
  | 0, _, _, _, _, rem + 1, hf, _, _ =>
    absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, lines, sb, top, addr, rem + 1, hf, hwrap, hdisj => by
    unfold unmapLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    simp only [withForcedBinTree_eq, withForcedNat_eq]
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hdisj1 : ∀ x : Nat, addr ≤ x → x < addr + step → ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x hx1 (by omega)
    have hdisj2 : ∀ x : Nat, addr + step ≤ x → x < (addr + step) + (rem + 1 - step) →
        ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x (by omega) (by omega)
    have ha_add : Nat.add addr step = addr + step := rfl
    have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
    rw [ha_add, hr_sub]
    rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
    · have hz : rem + 1 - step = 0 := hzero
      have hstep_eq : step = rem + 1 := by omega
      rw [hz, hstep_eq]
      have h0 : unmapLinesLoop ow fuel
          (unmapLineStep ow lines (addr / 64) (addr % 64) (rem + 1)) (addr + (rem + 1)) 0 =
          unmapLineStep ow lines (addr / 64) (addr % 64) (rem + 1) := by
        cases fuel <;> rfl
      rw [h0]
      exact unmapLineStep_eq ow lines sb top addr (rem + 1) (by omega) hwrap hdisj
    · rw [unmapLinesLoop_eq ow fuel _ sb top (addr + step) (rem + 1 - step) hnext (by omega) hdisj2,
        unmapLineStep_eq ow lines sb top addr step hlo_le (by omega) hdisj1,
        ← bv_ofNat_add, ← unmapLoop_add ow step (rem + 1 - step) ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr),
        ← hrem_split]

theorem prepareUnmapFastMem_disj_nat (fm : FastMem) (base : BitVec 64) (clen : Nat)
    (_hwrap : base.toNat + clen ≤ 2 ^ 64) :
    ∀ x : Nat, base.toNat ≤ x → x < base.toNat + clen →
      ¬ ((FastMem.prepareUnmapFastMem fm base clen).stackBase ≤ x ∧
         x < (FastMem.prepareUnmapFastMem fm base clen).stackTop) := by
  intro x hx1 hx2
  unfold FastMem.prepareUnmapFastMem
  split
  · omega
  · split
    · rename_i _ h2
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
      omega
    · intro hst
      unfold materializeStackFallback at hst
      dsimp only at hst
      split at hst <;> simp at hst

def setPermLineSlice (p : Perm) (ln : Line64) (lo : Nat) : Nat → Bool × Line64
  | 0 => (false, ln)
  | k + 1 =>
    match btGet 6 ln lo with
    | some (some q, b) =>
      if !(some q.rwx : Option Perm).frozen then
        let ln1 := btSet6Cell ln lo (some { p with lazyFree := q.lazyFree, anon := q.anon }) b
        (true, (setPermLineSlice p ln1 (Nat.add lo 1) k).2)
      else
        setPermLineSlice p ln (Nat.add lo 1) k
    | _ =>
      setPermLineSlice p ln (Nat.add lo 1) k

def setPermLineStep (p : Perm) (lines : BinTree Line64) (hi lo step : Nat) : BinTree Line64 :=
  match btGet 58 lines hi with
  | none => lines
  | some ln =>
    match setPermLineSlice p ln lo step with
    | (false, _) => lines
    | (true, ln') => btSet58Line lines hi ln'

theorem setPermLoop_add (p : Perm) :
    ∀ (n1 n2 : Nat) (fm : FastMem) (a : BitVec 64),
      fm.setPermLoop p a (n1 + n2) =
        (fm.setPermLoop p a n1).setPermLoop p (a + BitVec.ofNat 64 n1) n2
  | 0, n2, fm, a => by simp [FastMem.setPermLoop]
  | n1 + 1, n2, fm, a => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [FastMem.setPermLoop]
    rw [setPermLoop_add p n1 n2 _ (a + 1#64)]
    have hbv : a + 1#64 + BitVec.ofNat 64 n1 = a + BitVec.ofNat 64 (n1 + 1) := by bv_omega
    rw [hbv]

private theorem setPermLineSlice_false_eq (p : Perm) :
    ∀ (k lo : Nat) (ln ln' : Line64),
      setPermLineSlice p ln lo k = (false, ln') → ln' = ln
  | 0, _, ln, ln', h => by injection h with _ h2; exact h2.symm
  | k + 1, lo, ln, ln', h => by
    unfold setPermLineSlice at h
    cases h6 : btGet 6 ln lo with
    | none =>
      simp only [h6] at h
      exact setPermLineSlice_false_eq p k (Nat.add lo 1) ln ln' h
    | some c =>
      rcases c with ⟨_ | q, b⟩
      · simp only [h6] at h
        exact setPermLineSlice_false_eq p k (Nat.add lo 1) ln ln' h
      · simp only [h6] at h
        cases hfr : q.frozen
        · simp [hfr] at h
        · simp [hfr] at h
          exact setPermLineSlice_false_eq p k (lo + 1) ln ln' h

private theorem setPermLoop_empty_line (p : Perm) :
    ∀ (k addr : Nat) (lines : BinTree Line64) (sb top : Nat),
      btGet 58 lines (addr / 64) = none →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (∀ x : Nat, addr ≤ x → x < addr + k → ¬ (sb ≤ x ∧ x < top)) →
      FastMem.setPermLoop p ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) k = ⟨lines, sb, top⟩
  | 0, _, lines, sb, top, _, _, _, _ => rfl
  | k + 1, addr, lines, sb, top, hnone, hlo, hwrap, hdisj => by
    dsimp only [FastMem.setPermLoop]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hdisj0 : ¬ (sb ≤ addr ∧ addr < top) := hdisj addr (Nat.le_refl _) (by omega)
    have hpm : ((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).mapped = false := by
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, hnone]
      have hst : (decide (sb ≤ addr) && decide (addr < top)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hst]
    simp only [hpm, Bool.false_and, Bool.false_eq_true, ↓reduceIte, bv_ofNat_succ]
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
      exact setPermLoop_empty_line p k (addr + 1) lines sb top (by rw [hdiv]; exact hnone)
        (by omega) (by omega) (fun x hx1 hx2 => hdisj x (by omega) (by omega))

private theorem setPermLoop_some_line (p : Perm) :
    ∀ (k addr : Nat) (lines : BinTree Line64) (sb top : Nat) (ln : Line64),
      btGet 58 lines (addr / 64) = some ln →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (∀ x : Nat, addr ≤ x → x < addr + k → ¬ (sb ≤ x ∧ x < top)) →
      FastMem.setPermLoop p ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) k =
        ⟨match setPermLineSlice p ln (addr % 64) k with
         | (false, _) => lines
         | (true, ln') => btSet 58 lines (addr / 64) ln', sb, top⟩
  | 0, _, lines, sb, top, ln, _, _, _, _ => by simp [FastMem.setPermLoop, setPermLineSlice]
  | k + 1, addr, lines, sb, top, ln, h58, hlo, hwrap, hdisj => by
    dsimp only [FastMem.setPermLoop, setPermLineSlice]
    have had : addr < 2 ^ 64 := by omega
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hdisj0 : ¬ (sb ≤ addr ∧ addr < top) := hdisj addr (Nat.le_refl _) (by omega)
    have hst : (decide (sb ≤ addr) && decide (addr < top)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have hcell : (⟨lines, sb, top⟩ : FastMem).cellAt (BitVec.ofNat 64 addr) =
        btGet 6 ln (addr % 64) := by
      simp only [FastMem.cellAt, rawCellAt, hto, h58]
      cases btGet 6 ln (addr % 64) <;> simp [hst]
    have hread : (⟨lines, sb, top⟩ : FastMem).read8 (BitVec.ofNat 64 addr) =
        match btGet 6 ln (addr % 64) with | some (_, b) => b | none => 0#8 := by
      simp only [FastMem.read8, rawCellAt, hto, h58]
      cases btGet 6 ln (addr % 64) <;> rfl
    have hdisj' : ∀ x : Nat, addr + 1 ≤ x → x < addr + 1 + k → ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x (by omega) (by omega)
    rw [bv_ofNat_succ]
    cases h6 : btGet 6 ln (addr % 64) with
    | none =>
      have hcond : (((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).mapped &&
          !((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).frozen) = false := by
        simp [FastMem.perm, hcell, h6]
      rw [hcond]
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hk0 : k = 0
      · subst hk0; simp [FastMem.setPermLoop, setPermLineSlice]
      · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
        have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
          change (addr + 1) % 64 = addr % 64 + 1; omega
        rw [setPermLoop_some_line p k (addr + 1) lines sb top ln
          (by rw [hdiv]; exact h58) (by omega) (by omega) hdisj', hdiv, hmod]
    | some c =>
      rcases c with ⟨_ | q, b⟩
      · have hcond : (((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).mapped &&
            !((⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr)).frozen) = false := by
          simp [FastMem.perm, hcell, h6]
        rw [hcond]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hk0 : k = 0
        · subst hk0; simp [FastMem.setPermLoop, setPermLineSlice]
        · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
          have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
            change (addr + 1) % 64 = addr % 64 + 1; omega
          rw [setPermLoop_some_line p k (addr + 1) lines sb top ln
            (by rw [hdiv]; exact h58) (by omega) (by omega) hdisj', hdiv, hmod]
      · dsimp only
        have hperm_q : (⟨lines, sb, top⟩ : FastMem).perm (BitVec.ofNat 64 addr) = some q.rwx := by
          simp [FastMem.perm, hcell, h6]
        have hlf_q : (⟨lines, sb, top⟩ : FastMem).isLazyFree (BitVec.ofNat 64 addr) = q.lazyFree := by
          simp [FastMem.isLazyFree, hcell, h6]
        have han_q : (⟨lines, sb, top⟩ : FastMem).isAnon (BitVec.ofNat 64 addr) = q.anon := by
          simp [FastMem.isAnon, hcell, h6]
        have hrd_b : (⟨lines, sb, top⟩ : FastMem).read8 (BitVec.ofNat 64 addr) = b := by
          simp [hread, h6]
        rw [hperm_q, hlf_q, han_q, hrd_b]
        have hcond_eq : ((some q.rwx : Option Perm).mapped && !(some q.rwx : Option Perm).frozen) =
            !(some q.rwx : Option Perm).frozen := rfl
        rw [hcond_eq]
        cases hmf : !(some q.rwx : Option Perm).frozen
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hk0 : k = 0
          · subst hk0; simp [FastMem.setPermLoop, setPermLineSlice]
          · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
            have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
              change (addr + 1) % 64 = addr % 64 + 1; omega
            rw [setPermLoop_some_line p k (addr + 1) lines sb top ln
              (by rw [hdiv]; exact h58) (by omega) (by omega) hdisj', hdiv, hmod]
        · simp only [↓reduceIte, FastMem.setCell, setRawCell, withForcedCell_eq,
            withForcedBinTree_eq, hto, h58, Option.getD_some, btSet6Cell_eq]
          set cNew : Cell := (some { p with lazyFree := q.lazyFree, anon := q.anon }, b)
          set ln1 := btSet 6 ln (addr % 64) cNew
          by_cases hk0 : k = 0
          · subst hk0; simp [FastMem.setPermLoop, setPermLineSlice]
          · have hdiv : (addr + 1) / 64 = addr / 64 := by omega
            have hmod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
              change (addr + 1) % 64 = addr % 64 + 1; omega
            rw [setPermLoop_some_line p k (addr + 1) (btSet 58 lines (addr / 64) ln1) sb top ln1
              (by rw [hdiv]; exact btGet_btSet_same' 58 (addr / 64) lines ln1)
              (by omega) (by omega) hdisj', hdiv, hmod]
            cases hres : setPermLineSlice p ln1 (Nat.add (addr % 64) 1) k with
            | mk ch ln2 =>
              cases ch
              · have heq := setPermLineSlice_false_eq p k _ _ _ hres
                subst heq; rfl
              · dsimp only
                rw [btSet_btSet_same 58 lines (addr / 64) ln1 ln2]

theorem setPermLineStep_eq (p : Perm) (lines : BinTree Line64) (sb top addr step : Nat)
    (hlo : addr % 64 + step ≤ 64) (hwrap : addr + step ≤ 2 ^ 64)
    (hdisj : ∀ x : Nat, addr ≤ x → x < addr + step → ¬ (sb ≤ x ∧ x < top)) :
    (⟨setPermLineStep p lines (addr / 64) (addr % 64) step, sb, top⟩ : FastMem) =
      FastMem.setPermLoop p ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) step := by
  unfold setPermLineStep
  cases h58 : btGet 58 lines (addr / 64) with
  | none =>
    exact (setPermLoop_empty_line p step addr lines sb top h58 hlo hwrap hdisj).symm
  | some ln =>
    dsimp only
    rw [setPermLoop_some_line p step addr lines sb top ln h58 hlo hwrap hdisj]
    cases setPermLineSlice p ln (addr % 64) step with
    | mk ch ln' =>
      cases ch
      · rfl
      · simp [btSet58Line_eq]

def setPermLinesLoop (p : Perm) : Nat → BinTree Line64 → Nat → Nat → BinTree Line64
  | _, lines, _, 0 => lines
  | 0, lines, _, _ + 1 => lines
  | fuel + 1, lines, addr, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    withForcedBinTree (setPermLineStep p lines hi lo step) fun lines' =>
    withForcedNat (Nat.add addr step) fun addr' =>
    withForcedNat (Nat.sub rem step) fun rem' =>
      setPermLinesLoop p fuel lines' addr' rem'

theorem setPermLinesLoop_eq (p : Perm) :
    ∀ (fuel : Nat) (lines : BinTree Line64) (sb top addr rem : Nat),
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      (∀ x : Nat, addr ≤ x → x < addr + rem → ¬ (sb ≤ x ∧ x < top)) →
      (⟨setPermLinesLoop p fuel lines addr rem, sb, top⟩ : FastMem) =
        FastMem.setPermLoop p ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr) rem
  | fuel, lines, sb, top, _, 0, _, _, _ => by cases fuel <;> rfl
  | 0, _, _, _, _, rem + 1, hf, _, _ =>
    absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, lines, sb, top, addr, rem + 1, hf, hwrap, hdisj => by
    unfold setPermLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    simp only [withForcedBinTree_eq, withForcedNat_eq]
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hdisj1 : ∀ x : Nat, addr ≤ x → x < addr + step → ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x hx1 (by omega)
    have hdisj2 : ∀ x : Nat, addr + step ≤ x → x < (addr + step) + (rem + 1 - step) →
        ¬ (sb ≤ x ∧ x < top) :=
      fun x hx1 hx2 => hdisj x (by omega) (by omega)
    have ha_add : Nat.add addr step = addr + step := rfl
    have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
    rw [ha_add, hr_sub]
    rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
    · have hz : rem + 1 - step = 0 := hzero
      have hstep_eq : step = rem + 1 := by omega
      rw [hz, hstep_eq]
      have h0 : setPermLinesLoop p fuel
          (setPermLineStep p lines (addr / 64) (addr % 64) (rem + 1)) (addr + (rem + 1)) 0 =
          setPermLineStep p lines (addr / 64) (addr % 64) (rem + 1) := by
        cases fuel <;> rfl
      rw [h0]
      exact setPermLineStep_eq p lines sb top addr (rem + 1) (by omega) hwrap hdisj
    · rw [setPermLinesLoop_eq p fuel _ sb top (addr + step) (rem + 1 - step) hnext (by omega) hdisj2,
        setPermLineStep_eq p lines sb top addr step hlo_le (by omega) hdisj1,
        ← bv_ofNat_add, ← setPermLoop_add p step (rem + 1 - step) ⟨lines, sb, top⟩ (BitVec.ofNat 64 addr),
        ← hrem_split]

/-- Balanced full binary tree of depth `d` with shared left and right subtrees (`d + 1` nodes). -/
def mkFullTree {α : Type} (v : α) : Nat → BinTree α
  | 0 => .twig 0 v
  | d + 1 =>
    let sub := mkFullTree v d
    .branch sub sub

/-- Uniform 64-byte `(some Perm.rw, 0#8)` cache line represented as a 7-node DAG. -/
def rwZeroLine64 : Line64 :=
  mkFullTree (some Perm.rw, 0#8) 6

@[inline] def mapZeroNewCell (lnOpt : Option Line64) (lo : Nat) : Cell :=
  match lnOpt with
  | some ln =>
    match btGet 6 ln lo with
    | some (some q, b) => (some q, b)
    | _ => (some Perm.rw, 0#8)
  | none => (some Perm.rw, 0#8)

def mapZeroLineSlice (lnOpt : Option Line64) (curLine : Line64) (lo : Nat) : Nat → Line64
  | 0 => curLine
  | k + 1 =>
    let cell := mapZeroNewCell lnOpt lo
    mapZeroLineSlice lnOpt (btSet6Cell curLine lo cell.1 cell.2) (Nat.add lo 1) k

theorem mapZeroLineSlice_empty_64 :
    mapZeroLineSlice none .empty 0 64 = rwZeroLine64 :=
  rfl

def mapZeroLineStep (lines : BinTree Line64) (hi lo step : Nat) : BinTree Line64 :=
  match btGet 58 lines hi with
  | none =>
    if Nat.beq step 64 then
      btSet58Line lines hi rwZeroLine64
    else
      btSet58Line lines hi (mapZeroLineSlice none .empty lo step)
  | some ln =>
    btSet58Line lines hi (mapZeroLineSlice (some ln) ln lo step)

def mapZeroLinesLoop : Nat → BinTree Line64 → Nat → Nat → BinTree Line64
  | _, lines, _, 0 => lines
  | 0, lines, _, _ + 1 => lines
  | fuel + 1, lines, addr, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    withForcedBinTree (mapZeroLineStep lines hi lo step) fun lines' =>
    withForcedNat (Nat.add addr step) fun addr' =>
    withForcedNat (Nat.sub rem step) fun rem' =>
      mapZeroLinesLoop fuel lines' addr' rem'

private theorem mapZeroCell_eq (fm : FastMem) (addr : Nat) (lnOpt : Option Line64) :
    (match FastMem.cellAtWithLine fm addr lnOpt with
     | some (some q, b) => (some q, b)
     | some (none, _) => (some Perm.rw, 0#8)
     | none => (some Perm.rw, 0#8)) =
    mapZeroNewCell lnOpt (addr % 64) := by
  unfold FastMem.cellAtWithLine mapZeroNewCell
  cases lnOpt with
  | none =>
    dsimp only
    cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
  | some ln =>
    dsimp only
    cases btGet 6 ln (addr % 64) with
    | none =>
      dsimp only
      cases decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop) <;> rfl
    | some c =>
      rcases c with ⟨_ | q, b⟩ <;> rfl

private theorem buildMapCells_mapZero_succ (fm : FastMem) (curHi : Nat)
    (curLine : Option Line64) (addr n : Nat) :
    FastMem.buildMapCells fm true Perm.rw curHi curLine addr (n + 1) =
      let hi := addr / 64
      let lineOpt := if hi == curHi then curLine else btGet 58 fm.lines hi
      let cell := mapZeroNewCell lineOpt (addr % 64)
      cell :: FastMem.buildMapCells fm true Perm.rw hi lineOpt (addr + 1) n := by
  conv_lhs => unfold FastMem.buildMapCells
  dsimp only
  simp only [withForcedNat_eq, ↓reduceIte]
  congr 1
  exact mapZeroCell_eq fm addr _

private theorem flushAndSetCells_cons_same (lines : BinTree Line64) (curHi : Nat)
    (curLine : Line64) {addr : Nat} (had : addr < 2 ^ 64) (hdiv : addr / 64 = curHi)
    (c : Cell) (cs : List Cell) :
    flushAndSetCells lines curHi curLine addr (c :: cs) =
      flushAndSetCells lines curHi (btSet6Cell curLine (addr % 64) c.1 c.2) (addr + 1) cs := by
  rcases c with ⟨p, b⟩
  conv_lhs => unfold flushAndSetCells
  have hblt : Nat.blt addr (2 ^ 64) = true := Nat.blt_eq.mpr had
  simp only [hblt, ↓reduceIte, hdiv, beq_self_eq_true]

private theorem flushAndSetCells_cons_diff (lines : BinTree Line64) (curHi : Nat)
    (curLine : Line64) {addr : Nat} (had : addr < 2 ^ 64) (hne : addr / 64 ≠ curHi)
    (c : Cell) (cs : List Cell) :
    flushAndSetCells lines curHi curLine addr (c :: cs) =
      setCellsAt (btSet58Line lines curHi curLine) addr (c :: cs) := by
  rcases c with ⟨p, b⟩
  unfold flushAndSetCells setCellsAt
  have hblt : Nat.blt addr (2 ^ 64) = true := Nat.blt_eq.mpr had
  have hbeq : (addr / 64 == curHi) = false := Bool.eq_false_iff.mpr (fun h => hne (beq_iff_eq.mp h))
  simp only [hblt, ↓reduceIte, hbeq, Bool.false_eq_true]
  cases btSet58Line lines curHi curLine <;> rfl

private theorem setCellsAt_cons (lines : BinTree Line64) {addr : Nat} (had : addr < 2 ^ 64)
    (c : Cell) (rest : List Cell) :
    setCellsAt lines addr (c :: rest) =
      flushAndSetCells lines (addr / 64)
        (btSet6Cell ((btGet 58 lines (addr / 64)).getD .empty) (addr % 64) c.1 c.2)
        (addr + 1) rest := by
  rcases c with ⟨p, b⟩
  unfold setCellsAt
  have hblt : Nat.blt addr (2 ^ 64) = true := Nat.blt_eq.mpr had
  simp only [hblt, ↓reduceIte]

private theorem buildMapCells_irrel_mem (lines1 lines2 : BinTree Line64) (sb1 top1 sb2 top2 : Nat) :
    ∀ (rem curHi1 curHi2 : Nat) (curLine1 curLine2 : Option Line64) (addr : Nat),
      curLine1 = btGet 58 lines1 curHi1 →
      curLine2 = btGet 58 lines2 curHi2 →
      (∀ h : Nat, addr / 64 ≤ h → btGet 58 lines1 h = btGet 58 lines2 h) →
      FastMem.buildMapCells ⟨lines1, sb1, top1⟩ true Perm.rw curHi1 curLine1 addr rem =
        FastMem.buildMapCells ⟨lines2, sb2, top2⟩ true Perm.rw curHi2 curLine2 addr rem
  | 0, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, curHi1, curHi2, curLine1, curLine2, addr, hc1, hc2, hge => by
    rw [buildMapCells_mapZero_succ, buildMapCells_mapZero_succ]
    dsimp only
    have hl1 : (if addr / 64 == curHi1 then curLine1 else btGet 58 lines1 (addr / 64)) =
        btGet 58 lines1 (addr / 64) := by
      split
      · rename_i heq; rw [hc1, beq_iff_eq.mp heq]
      · rfl
    have hl2 : (if addr / 64 == curHi2 then curLine2 else btGet 58 lines2 (addr / 64)) =
        btGet 58 lines2 (addr / 64) := by
      split
      · rename_i heq; rw [hc2, beq_iff_eq.mp heq]
      · rfl
    rw [hl1, hl2, hge (addr / 64) (Nat.le_refl _)]
    congr 1
    exact buildMapCells_irrel_mem lines1 lines2 sb1 top1 sb2 top2 rem
      (addr / 64) (addr / 64) _ _ (addr + 1) (hge (addr / 64) (Nat.le_refl _)).symm rfl
      (fun h hh => hge h (by omega))

private theorem flushAndSetCells_mapZero_slice (fm : FastMem) :
    ∀ (k : Nat) (lines : BinTree Line64) (hi addr : Nat) (lnOpt : Option Line64)
      (curLine : Line64) (remAfter : Nat),
      addr / 64 = hi →
      lnOpt = btGet 58 fm.lines hi →
      addr % 64 + k ≤ 64 →
      (0 < remAfter → addr % 64 + k = 64) →
      addr + k + remAfter ≤ 2 ^ 64 →
      flushAndSetCells lines hi curLine addr
          (FastMem.buildMapCells fm true Perm.rw hi lnOpt addr (k + remAfter)) =
        if remAfter == 0 then
          btSet58Line lines hi (mapZeroLineSlice lnOpt curLine (addr % 64) k)
        else
          setCellsAt (btSet58Line lines hi (mapZeroLineSlice lnOpt curLine (addr % 64) k))
            (addr + k)
            (FastMem.buildMapCells fm true Perm.rw (hi + 1) (btGet 58 fm.lines (hi + 1))
              (addr + k) remAfter)
  | 0, lines, hi, addr, lnOpt, curLine, remAfter, hdiv, hln, hlo, hfull, hwrap => by
    dsimp only [mapZeroLineSlice, Nat.add_zero]
    cases remAfter with
    | zero =>
      rfl
    | succ r =>
      have h64 : addr % 64 + 0 = 64 := hfull (Nat.succ_pos r)
      omega
  | k + 1, lines, hi, addr, lnOpt, curLine, remAfter, hdiv, hln, hlo, hfull, hwrap => by
    have had : addr < 2 ^ 64 := by omega
    have hsum : (k + 1) + remAfter = (k + remAfter) + 1 := by omega
    rw [hsum, buildMapCells_mapZero_succ]
    dsimp only
    simp only [hdiv, beq_self_eq_true, ↓reduceIte]
    rw [flushAndSetCells_cons_same lines hi curLine had hdiv]
    dsimp only [mapZeroLineSlice]
    set cell := mapZeroNewCell lnOpt (addr % 64)
    set curLine1 := btSet6Cell curLine (addr % 64) cell.1 cell.2
    by_cases hk0 : k = 0
    · subst hk0
      dsimp only [mapZeroLineSlice]
      rw [Nat.zero_add]
      cases remAfter with
      | zero =>
        rfl
      | succ r =>
        have h64 : addr % 64 + 1 = 64 := hfull (Nat.succ_pos r)
        have ha1_div : (addr + 1) / 64 = hi + 1 := by omega
        have ha1_lt : addr + 1 < 2 ^ 64 := by omega
        have hr0 : (r + 1 == 0) = false := rfl
        simp only [hr0, Bool.false_eq_true, ↓reduceIte]
        rw [buildMapCells_mapZero_succ, buildMapCells_mapZero_succ]
        dsimp only
        have hne_hi : (hi + 1 == hi) = false := Bool.eq_false_iff.mpr (by simp)
        simp only [ha1_div, hne_hi, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte]
        exact flushAndSetCells_cons_diff lines hi curLine1 ha1_lt (by omega) _ _
    · have ha1_div : (addr + 1) / 64 = hi := by omega
      have ha1_mod : (addr + 1) % 64 = Nat.add (addr % 64) 1 := by
        change (addr + 1) % 64 = addr % 64 + 1; omega
      have ih := flushAndSetCells_mapZero_slice fm k lines hi (addr + 1) lnOpt curLine1 remAfter
        ha1_div hln (by omega) (fun hr => by have := hfull hr; omega) (by omega)
      have hadd_assoc : addr + 1 + k = addr + (k + 1) := by omega
      rw [ha1_mod, hadd_assoc] at ih
      exact ih

private theorem setCellsAt_mapZero_step (fm : FastMem) (lines : BinTree Line64)
    (addr step remAfter : Nat)
    (hstep_pos : 0 < step)
    (hlo : addr % 64 + step ≤ 64)
    (hfull : 0 < remAfter → addr % 64 + step = 64)
    (hwrap : addr + step + remAfter ≤ 2 ^ 64)
    (hge : ∀ h : Nat, addr / 64 ≤ h → h < 2 ^ 58 → btGet 58 lines h = btGet 58 fm.lines h) :
    setCellsAt lines addr
        (FastMem.buildMapCells fm true Perm.rw (addr / 64) (btGet 58 fm.lines (addr / 64))
          addr (step + remAfter)) =
      let lines' := mapZeroLineStep lines (addr / 64) (addr % 64) step
      if remAfter == 0 then
        lines'
      else
        setCellsAt lines' (addr + step)
          (FastMem.buildMapCells fm true Perm.rw ((addr + step) / 64)
            (btGet 58 fm.lines ((addr + step) / 64)) (addr + step) remAfter) := by
  obtain ⟨k, rfl⟩ : ∃ k, step = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have had : addr < 2 ^ 64 := by omega
  have hsum : (k + 1) + remAfter = (k + remAfter) + 1 := by omega
  have hline_eq : btGet 58 lines (addr / 64) = btGet 58 fm.lines (addr / 64) :=
    hge (addr / 64) (Nat.le_refl _) (div64_lt_2pow58 had)
  have hstep_line :
      btSet58Line lines (addr / 64)
        (mapZeroLineSlice (btGet 58 fm.lines (addr / 64))
          ((btGet 58 lines (addr / 64)).getD .empty) (addr % 64) (k + 1)) =
      mapZeroLineStep lines (addr / 64) (addr % 64) (k + 1) := by
    unfold mapZeroLineStep
    rw [← hline_eq]
    cases btGet 58 lines (addr / 64) with
    | some ln => rfl
    | none =>
      dsimp only [Option.getD_none]
      cases hbeq : Nat.beq (k + 1) 64
      · rfl
      · have h64 : k + 1 = 64 := Nat.beq_eq.mp hbeq
        have hlo0 : addr % 64 = 0 := by omega
        simp only [↓reduceIte, h64, hlo0, mapZeroLineSlice_empty_64]
  have hmain := flushAndSetCells_mapZero_slice fm (k + 1) lines (addr / 64) addr
    (btGet 58 fm.lines (addr / 64)) ((btGet 58 lines (addr / 64)).getD .empty) remAfter
    rfl rfl hlo hfull hwrap
  rw [hsum, buildMapCells_mapZero_succ] at hmain ⊢
  dsimp only at hmain ⊢
  simp only [beq_self_eq_true, ↓reduceIte] at hmain ⊢
  rw [flushAndSetCells_cons_same _ _ _ had rfl] at hmain
  rw [setCellsAt_cons _ had, hmain, hstep_line]
  cases hrem0 : (remAfter == 0)
  · have hrpos : 0 < remAfter := by
      cases remAfter with
      | zero => simp at hrem0
      | succ r => exact Nat.succ_pos r
    have h64 := hfull hrpos
    have hdiv_next : (addr + (k + 1)) / 64 = addr / 64 + 1 := by omega
    rw [hdiv_next]
  · rfl

theorem mapZeroLinesLoop_eq (fm : FastMem) :
    ∀ (fuel : Nat) (lines : BinTree Line64) (addr rem : Nat),
      0 < rem →
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      (∀ h : Nat, addr / 64 ≤ h → h < 2 ^ 58 → btGet 58 lines h = btGet 58 fm.lines h) →
      mapZeroLinesLoop fuel lines addr rem =
        setCellsAt lines addr
          (FastMem.buildMapCells fm true Perm.rw (addr / 64) (btGet 58 fm.lines (addr / 64))
            addr rem)
  | 0, _, _, rem, hpos, hf, _, _ =>
    absurd (Nat.le_trans (lineSpanFuel_pos hpos) hf) (by omega)
  | fuel + 1, lines, addr, rem, hpos, hf, hwrap, hge => by
    unfold mapZeroLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    cases rem with
    | zero => exact absurd hpos (Nat.lt_irrefl 0)
    | succ r =>
      dsimp only
      simp only [withForcedBinTree_eq, withForcedNat_eq]
      rw [hd, hm, hs]
      set step := min (r + 1) (64 - addr % 64)
      have hstep_pos : 0 < step := by omega
      have hlo_le : addr % 64 + step ≤ 64 := by omega
      have hrem_split : r + 1 = step + (r + 1 - step) := by omega
      have hfull : 0 < r + 1 - step → addr % 64 + step = 64 := by intro _; omega
      have ha_add : Nat.add addr step = addr + step := rfl
      have hr_sub : Nat.sub (r + 1) step = r + 1 - step := rfl
      rw [ha_add, hr_sub]
      have hstep_eq := setCellsAt_mapZero_step fm lines addr step (r + 1 - step)
        hstep_pos hlo_le hfull (by omega) hge
      rw [← hrem_split] at hstep_eq
      rw [hstep_eq]
      dsimp only
      rcases lineSpanFuel_step (Nat.succ_pos r) hf with hzero | hnext
      · rw [hzero]
        simp only [beq_self_eq_true, ↓reduceIte]
        cases fuel <;> rfl
      · by_cases hz : r + 1 - step = 0
        · rw [hz]
          simp only [beq_self_eq_true, ↓reduceIte]
          cases fuel <;> rfl
        · have hrpos : 0 < r + 1 - step := by omega
          have hzf : (r + 1 - step == 0) = false := beq_false_of_ne hz
          rw [hzf]
          simp only [Bool.false_eq_true, ↓reduceIte]
          have h64 := hfull hrpos
          have hge' : ∀ h : Nat, (addr + step) / 64 ≤ h → h < 2 ^ 58 →
              btGet 58 (mapZeroLineStep lines (addr / 64) (addr % 64) step) h =
                btGet 58 fm.lines h := by
            intro h hh hlt58
            have hne_hi : addr / 64 ≠ h := by omega
            have hhi_lt : addr / 64 < 2 ^ 58 := div64_lt_2pow58 (by omega)
            unfold mapZeroLineStep
            cases h58 : btGet 58 lines (addr / 64) with
            | some ln =>
              dsimp only
              rw [btSet58Line_eq, btGet_btSet_ne 58 (addr / 64) h lines _ hhi_lt hlt58 hne_hi]
              exact hge h (by omega) hlt58
            | none =>
              dsimp only
              cases Nat.beq step 64 <;>
                (simp only [↓reduceIte, Bool.false_eq_true, btSet58Line_eq];
                 rw [btGet_btSet_ne 58 (addr / 64) h lines _ hhi_lt hlt58 hne_hi];
                 exact hge h (by omega) hlt58)
          exact mapZeroLinesLoop_eq fm fuel _ (addr + step) (r + 1 - step) hrpos hnext
            (by omega) hge'

theorem findMappedByteFast_add (fm : FastMem) (base : BitVec 64) :
    ∀ (n1 n2 curOff : Nat),
      findMappedByteFast fm base curOff (n1 + n2) =
        match findMappedByteFast fm base curOff n1 with
        | some off => some off
        | none => findMappedByteFast fm base (curOff + n1) n2
  | 0, n2, curOff => by simp [findMappedByteFast]
  | n1 + 1, n2, curOff => by
    have h1 : (n1 + 1) + n2 = (n1 + n2) + 1 := by omega
    rw [h1]
    dsimp only [findMappedByteFast]
    split
    · rfl
    · rw [findMappedByteFast_add fm base n1 n2 (curOff + 1)]
      have hadd : curOff + 1 + n1 = curOff + (n1 + 1) := by omega
      rw [hadd]

def lineSliceFindMapped (sb top : Nat) (lnOpt : Option Line64) (addr lo curOff : Nat) :
    Nat → Option Nat
  | 0 => none
  | k + 1 =>
    if (optCellPerm sb top addr lnOpt lo).mapped then
      some curOff
    else
      lineSliceFindMapped sb top lnOpt (Nat.add addr 1) (Nat.add lo 1) (Nat.add curOff 1) k

theorem lineSliceFindMapped_eq (fm : FastMem) (base : BitVec 64) :
    ∀ (k curOff : Nat) (lnOpt : Option Line64),
      let addr := base.toNat + curOff
      lnOpt = btGet 58 fm.lines (addr / 64) →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      lineSliceFindMapped fm.stackBase fm.stackTop lnOpt addr (addr % 64) curOff k =
        findMappedByteFast fm base curOff k
  | 0, _, _, _, _, _ => rfl
  | k + 1, curOff, lnOpt, hln, hlo, hwrap => by
    dsimp only [lineSliceFindMapped, findMappedByteFast]
    set addr := base.toNat + curOff
    have had : addr < 2 ^ 64 := by omega
    have hbv_eq : base + BitVec.ofNat 64 curOff = BitVec.ofNat 64 addr := by
      have hb : BitVec.ofNat 64 base.toNat = base := by simp
      rw [← hb, bv_ofNat_add]
    rw [hln, optCellPerm_eq fm addr had, hbv_eq]
    cases (fm.perm (BitVec.ofNat 64 addr)).mapped
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hk0 : k = 0
      · subst hk0; rfl
      · have hdiv : (base.toNat + (curOff + 1)) / 64 = addr / 64 := by omega
        have hmod : (base.toNat + (curOff + 1)) % 64 = addr % 64 + 1 := by omega
        have ha1 : Nat.add addr 1 = base.toNat + (curOff + 1) := by
          change addr + 1 = base.toNat + (curOff + 1); omega
        have hlo1 : Nat.add (addr % 64) 1 = (base.toNat + (curOff + 1)) % 64 := by
          change addr % 64 + 1 = _; omega
        have hc1 : Nat.add curOff 1 = curOff + 1 := rfl
        rw [ha1, hlo1, hc1]
        exact lineSliceFindMapped_eq fm base k (curOff + 1) _
          (congrArg (btGet 58 fm.lines) hdiv.symm) (by omega) (by omega)
    · rfl

theorem findMappedByteFast_unmapped_slice (fm : FastMem) (base : BitVec 64) :
    ∀ (k curOff : Nat),
      let addr := base.toNat + curOff
      btGet 58 fm.lines (addr / 64) = none →
      addr % 64 + k ≤ 64 →
      addr + k ≤ 2 ^ 64 →
      (addr + k ≤ fm.stackBase ∨ fm.stackTop ≤ addr) →
      findMappedByteFast fm base curOff k = none
  | 0, _, _, _, _, _ => rfl
  | k + 1, curOff, hnone, hlo, hwrap, hdisj => by
    dsimp only [findMappedByteFast]
    set addr := base.toNat + curOff
    have had : addr < 2 ^ 64 := by omega
    have hbv_eq : base + BitVec.ofNat 64 curOff = BitVec.ofNat 64 addr := by
      have hb : BitVec.ofNat 64 base.toNat = base := by simp
      rw [← hb, bv_ofNat_add]
    have hto : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt had
    have hpm : (fm.perm (BitVec.ofNat 64 addr)).mapped = false := by
      simp only [FastMem.perm, FastMem.cellAt, rawCellAt, hto, hnone]
      have hst : (decide (fm.stackBase ≤ addr) && decide (addr < fm.stackTop)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp [hst]
    rw [hbv_eq, hpm]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hk0 : k = 0
    · subst hk0; rfl
    · have hdiv : (base.toNat + (curOff + 1)) / 64 = addr / 64 := by omega
      exact findMappedByteFast_unmapped_slice fm base k (curOff + 1)
        (by rw [hdiv]; exact hnone) (by omega) (by omega) (by omega)

def findMappedByteLinesLoop (fm : FastMem) : Nat → Nat → Nat → Nat → Option Nat
  | _, _, _, 0 => none
  | 0, _, _, _ + 1 => none
  | fuel + 1, addr, curOff, rem =>
    let hi := Nat.div addr 64
    let lo := Nat.mod addr 64
    let step := min rem (Nat.sub 64 lo)
    let lnOpt := btGet 58 fm.lines hi
    let sliceHit :=
      match lnOpt with
      | none =>
        if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
          none
        else
          lineSliceFindMapped fm.stackBase fm.stackTop none addr lo curOff step
      | some ln =>
        lineSliceFindMapped fm.stackBase fm.stackTop (some ln) addr lo curOff step
    match sliceHit with
    | some off => some off
    | none =>
      withForcedNat (Nat.add addr step) fun addr' =>
      withForcedNat (Nat.add curOff step) fun curOff' =>
      withForcedNat (Nat.sub rem step) fun rem' =>
        findMappedByteLinesLoop fm fuel addr' curOff' rem'

theorem findMappedByteLinesLoop_eq (fm : FastMem) (base : BitVec 64) :
    ∀ (fuel curOff rem : Nat),
      let addr := base.toNat + curOff
      lineSpanFuel addr rem ≤ fuel →
      addr + rem ≤ 2 ^ 64 →
      findMappedByteLinesLoop fm fuel addr curOff rem =
        findMappedByteFast fm base curOff rem
  | fuel, _, 0, _, _ => by cases fuel <;> rfl
  | 0, curOff, rem + 1, hf, _ =>
    absurd (Nat.le_trans (lineSpanFuel_pos (Nat.succ_pos rem)) hf) (by omega)
  | fuel + 1, curOff, rem + 1, hf, hwrap => by
    set addr := base.toNat + curOff
    unfold findMappedByteLinesLoop
    have hd : Nat.div addr 64 = addr / 64 := rfl
    have hm : Nat.mod addr 64 = addr % 64 := rfl
    have hs : Nat.sub 64 (addr % 64) = 64 - addr % 64 := rfl
    dsimp only
    rw [hd, hm, hs]
    set step := min (rem + 1) (64 - addr % 64)
    have hlo_le : addr % 64 + step ≤ 64 := by omega
    have hrem_split : rem + 1 = step + (rem + 1 - step) := by omega
    have hslice_eq :
        (match btGet 58 fm.lines (addr / 64) with
         | none =>
           if Nat.ble (Nat.add addr step) fm.stackBase || Nat.ble fm.stackTop addr then
             none
           else
             lineSliceFindMapped fm.stackBase fm.stackTop none addr (addr % 64) curOff step
         | some ln =>
           lineSliceFindMapped fm.stackBase fm.stackTop (some ln) addr (addr % 64) curOff step) =
        findMappedByteFast fm base curOff step := by
      cases h58 : btGet 58 fm.lines (addr / 64) with
      | some ln =>
        exact lineSliceFindMapped_eq fm base step curOff (some ln) h58.symm hlo_le (by omega)
      | none =>
        dsimp only
        have ha_add : Nat.add addr step = addr + step := rfl
        rw [ha_add, ble_eq_decide, ble_eq_decide]
        by_cases hdisj : (decide (addr + step ≤ fm.stackBase) || decide (fm.stackTop ≤ addr)) = true
        · simp only [hdisj, ↓reduceIte]
          have hdisj' : addr + step ≤ fm.stackBase ∨ fm.stackTop ≤ addr := by
            simpa [Bool.or_eq_true, decide_eq_true_eq] using hdisj
          exact (findMappedByteFast_unmapped_slice fm base step curOff h58 hlo_le
            (by omega) hdisj').symm
        · simp only [hdisj, Bool.false_eq_true, ↓reduceIte]
          exact lineSliceFindMapped_eq fm base step curOff none h58.symm hlo_le (by omega)
    rw [hslice_eq, hrem_split, findMappedByteFast_add fm base step (rem + 1 - step) curOff]
    cases findMappedByteFast fm base curOff step with
    | some off => rfl
    | none =>
      dsimp only
      simp only [withForcedNat_eq]
      have ha_add : Nat.add addr step = base.toNat + (curOff + step) := by
        change addr + step = base.toNat + (curOff + step); omega
      have hc_add : Nat.add curOff step = curOff + step := rfl
      have hr_sub : Nat.sub (rem + 1) step = rem + 1 - step := rfl
      rw [ha_add, hc_add, hr_sub]
      rcases lineSpanFuel_step (Nat.succ_pos rem) hf with hzero | hnext
      · rw [hzero]
        cases fuel <;> rfl
      · have hnext' : lineSpanFuel (base.toNat + (curOff + step)) (rem + 1 - step) ≤ fuel := by
          have heq_a : base.toNat + (curOff + step) = addr + step := by omega
          rwa [heq_a]
        exact findMappedByteLinesLoop_eq fm base fuel (curOff + step) (rem + 1 - step)
          hnext' (by omega)

def findMappedByteFastB (fm : FastMem) (base : BitVec 64) (curOff rem : Nat) : Option Nat :=
  if base.toNat + curOff + rem ≤ 2 ^ 64 then
    let addr := base.toNat + curOff
    findMappedByteLinesLoop fm (lineSpanFuel addr rem) addr curOff rem
  else
    findMappedByteFast fm base curOff rem

theorem findMappedByteFast_eq_batched (fm : FastMem) (base : BitVec 64) (curOff rem : Nat) :
    findMappedByteFast fm base curOff rem = findMappedByteFastB fm base curOff rem := by
  unfold findMappedByteFastB
  split
  · rename_i hwrap
    exact (findMappedByteLinesLoop_eq fm base _ curOff rem (Nat.le_refl _) hwrap).symm
  · rfl

end Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMem.FastMem

set_option autoImplicit false

open Arm64 Arm64.Memory
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched

/-- 64-byte line-batched counterpart of `FastMem.allPerm`. -/
def allPermB (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) : Bool :=
  if n == 0 then true
  else if addr.toNat + n ≤ 2 ^ 64 then
    allPermLinesLoop fm pred (pred none) (lineSpanFuel addr.toNat n) addr.toNat n
  else
    fm.allPerm pred addr n

theorem allPerm_eq_batched (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) :
    fm.allPerm pred addr n = fm.allPermB pred addr n := by
  unfold allPermB
  by_cases hn : (n == 0) = true
  · have hn0 : n = 0 := beq_iff_eq.mp hn
    subst hn0; simp [allPerm]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hwrap
      rw [fm.allPerm_eq (m := ⟨fm.cellAt⟩) (fun _ => rfl),
        allPermLinesLoop_eq fm pred _ addr.toNat n (Nat.le_refl _) hwrap, BitVec.ofNat_toNat]
      simp
    · rfl

def canMapB (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool :=
  fm.allPermB (fun p => !p.mapped) addr n

theorem canMap_eq_batched (fm : FastMem) (addr : BitVec 64) (n : Nat) :
    fm.canMap addr n = fm.canMapB addr n :=
  fm.allPerm_eq_batched (fun p => !p.mapped) addr n

def allAnonB (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool :=
  if n == 0 then true
  else if addr.toNat + n ≤ 2 ^ 64 then
    allAnonLinesLoop fm (lineSpanFuel addr.toNat n) addr.toNat n
  else
    fm.allAnon addr n

theorem allAnon_eq_batched (fm : FastMem) (addr : BitVec 64) (n : Nat) :
    fm.allAnon addr n = fm.allAnonB addr n := by
  unfold allAnonB
  by_cases hn : (n == 0) = true
  · have hn0 : n = 0 := beq_iff_eq.mp hn
    subst hn0; rfl
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hwrap
      rw [fm.allAnon_eq (m := ⟨fm.cellAt⟩) (fun _ => rfl),
        allAnonLinesLoop_eq fm _ addr.toNat n (Nat.le_refl _) hwrap, BitVec.ofNat_toNat]
      simp
    · rfl

def countPermB (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) : Nat :=
  if n == 0 then 0
  else if addr.toNat + n ≤ 2 ^ 64 then
    countPermLinesLoop fm pred (pred none) (lineSpanFuel addr.toNat n) addr.toNat n 0
  else
    fm.countPerm pred addr n

theorem countPerm_eq_batched (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) :
    fm.countPerm pred addr n = fm.countPermB pred addr n := by
  unfold countPermB
  by_cases hn : (n == 0) = true
  · have hn0 : n = 0 := beq_iff_eq.mp hn
    subst hn0; rfl
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hwrap
      rw [fm.countPerm_eq (m := ⟨fm.cellAt⟩) (fun _ => rfl),
        countPermLinesLoop_eq fm pred _ addr.toNat n 0 (Nat.le_refl _) hwrap,
        Nat.zero_add, BitVec.ofNat_toNat]
      simp
    · rfl

def countRwB (fm : FastMem) (addr : BitVec 64) (n : Nat) : Nat :=
  fm.countPermB (· == some Perm.rw) addr n

theorem countRw_eq_batched (fm : FastMem) (addr : BitVec 64) (n : Nat) :
    fm.countRw addr n = fm.countRwB addr n :=
  fm.countPerm_eq_batched (· == some Perm.rw) addr n

def unmapWritableB (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  if base.toNat + clen ≤ 2 ^ 64 then
    let fm0 := prepareUnmapFastMem fm base clen
    match fm0 with
    | ⟨lines, sb, top⟩ =>
      withForcedBinTree (unmapLinesLoop true (lineSpanFuel base.toNat clen) lines base.toNat clen)
        fun lines' => ⟨lines', sb, top⟩
  else
    fm.unmapWritable base len

theorem unmapWritable_eq_batched (fm : FastMem) (base : BitVec 64) (len : Nat) :
    fm.unmapWritable base len = fm.unmapWritableB base len := by
  unfold unmapWritableB
  dsimp only
  set clen := min len (2 ^ 64)
  split
  · rename_i hwrap
    change unmapLoop true (prepareUnmapFastMem fm base clen) base clen = _
    have hdisj := prepareUnmapFastMem_disj_nat fm base clen hwrap
    generalize hfm0 : prepareUnmapFastMem fm base clen = fm0 at hdisj ⊢
    rcases fm0 with ⟨lines, sb, top⟩
    simp only [withForcedBinTree_eq]
    have hloop := (unmapLinesLoop_eq true (lineSpanFuel base.toNat clen) lines sb top base.toNat clen
      (Nat.le_refl _) hwrap hdisj).symm
    have hbv : BitVec.ofNat 64 base.toNat = base := by simp
    rw [hbv] at hloop
    exact hloop
  · rfl

def unmapNonFrozenB (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  if base.toNat + clen ≤ 2 ^ 64 then
    let fm0 := prepareUnmapFastMem fm base clen
    match fm0 with
    | ⟨lines, sb, top⟩ =>
      withForcedBinTree (unmapLinesLoop false (lineSpanFuel base.toNat clen) lines base.toNat clen)
        fun lines' => ⟨lines', sb, top⟩
  else
    fm.unmapNonFrozen base len

theorem unmapNonFrozen_eq_batched (fm : FastMem) (base : BitVec 64) (len : Nat) :
    fm.unmapNonFrozen base len = fm.unmapNonFrozenB base len := by
  unfold unmapNonFrozenB
  dsimp only
  set clen := min len (2 ^ 64)
  split
  · rename_i hwrap
    change unmapLoop false (prepareUnmapFastMem fm base clen) base clen = _
    have hdisj := prepareUnmapFastMem_disj_nat fm base clen hwrap
    generalize hfm0 : prepareUnmapFastMem fm base clen = fm0 at hdisj ⊢
    rcases fm0 with ⟨lines, sb, top⟩
    simp only [withForcedBinTree_eq]
    have hloop := (unmapLinesLoop_eq false (lineSpanFuel base.toNat clen) lines sb top base.toNat clen
      (Nat.le_refl _) hwrap hdisj).symm
    have hbv : BitVec.ofNat 64 base.toNat = base := by simp
    rw [hbv] at hloop
    exact hloop
  · rfl

/-- 64-byte line-batched counterpart of `FastMem.mapZero` that updates lines in place without
allocating an intermediate cell list. -/
def mapZeroB (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  if clen == 0 then fm
  else if base.toNat + clen ≤ 2 ^ 64 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      withForcedBinTree (mapZeroLinesLoop (lineSpanFuel base.toNat clen) lines base.toNat clen)
        fun lines' => ⟨lines', sb, top⟩
  else
    fm.mapRangeSlow true Perm.rw base clen

theorem mapZero_eq_batched (fm : FastMem) (base : BitVec 64) (len : Nat) :
    fm.mapZero base len = fm.mapZeroB base len := by
  unfold mapZero mapZeroB
  set clen := min len (2 ^ 64)
  by_cases hz : (clen == 0) = true
  · simp [hz]
  · simp only [hz, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hwrap
      rcases fm with ⟨lines, sb, top⟩
      simp only [withForcedBinTree_eq]
      have hpos : 0 < clen := by
        cases hcl : clen with
        | zero => simp [hcl] at hz
        | succ k => exact Nat.succ_pos k
      rw [mapZeroLinesLoop_eq ⟨lines, sb, top⟩ _ lines base.toNat clen hpos
        (Nat.le_refl _) hwrap (fun _ _ _ => rfl)]
    · rfl

def setPermNonFrozenB (fm : FastMem) (base : BitVec 64) (len : Nat) (p : Perm) : FastMem :=
  let clen := min len (2 ^ 64)
  if base.toNat + clen ≤ 2 ^ 64 &&
      (fm.stackTop ≤ fm.stackBase || base.toNat + clen ≤ fm.stackBase || fm.stackTop ≤ base.toNat) then
    match fm with
    | ⟨lines, sb, top⟩ =>
      withForcedBinTree (setPermLinesLoop p (lineSpanFuel base.toNat clen) lines base.toNat clen)
        fun lines' => ⟨lines', sb, top⟩
  else
    fm.setPermNonFrozen base len p

theorem setPermNonFrozen_eq_batched (fm : FastMem) (base : BitVec 64) (len : Nat) (p : Perm) :
    fm.setPermNonFrozen base len p = fm.setPermNonFrozenB base len p := by
  unfold setPermNonFrozenB
  dsimp only
  set clen := min len (2 ^ 64)
  split
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
    rcases hcond with ⟨hwrap, hdisj_or⟩
    rcases fm with ⟨lines, sb, top⟩
    dsimp only at hdisj_or
    change setPermLoop p ⟨lines, sb, top⟩ base clen = _
    simp only [withForcedBinTree_eq]
    have hdisj : ∀ x : Nat, base.toNat ≤ x → x < base.toNat + clen → ¬ (sb ≤ x ∧ x < top) := by
      intro x hx1 hx2; omega
    have hloop := (setPermLinesLoop_eq p (lineSpanFuel base.toNat clen) lines sb top base.toNat clen
      (Nat.le_refl _) hwrap hdisj).symm
    have hbv : BitVec.ofNat 64 base.toNat = base := by simp
    rw [hbv] at hloop
    exact hloop
  · rfl

end Symbolic.BugInjection.Proofs.CliExec.RadixMem.FastMem

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched

set_option autoImplicit false

open Arm64 Arm64.Memory
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

def findUnmappedAreaLoopFastB (fm : FastMem) (size : Nat) : Nat → Nat → Option (BitVec 64)
  | 0, _ => none
  | fuel + 1, addr =>
    if !decide (addr + size ≤ USER_VA_LIMIT) then
      none
    else
      let base := BitVec.ofNat 64 addr
      match findMappedByteFastB fm base 0 size with
      | none => some base
      | some off =>
        let nextPage := ((addr + off) / PAGE_SIZE + 1) * PAGE_SIZE
        findUnmappedAreaLoopFastB fm size fuel nextPage

theorem findUnmappedAreaLoopFast_eq_batched (fm : FastMem) (size : Nat) :
    ∀ (fuel addr : Nat),
      findUnmappedAreaLoopFast fm size fuel addr = findUnmappedAreaLoopFastB fm size fuel addr
  | 0, _ => rfl
  | fuel + 1, addr => by
    unfold findUnmappedAreaLoopFast findUnmappedAreaLoopFastB
    split
    · rfl
    · dsimp only
      rw [← findMappedByteFast_eq_batched]
      cases findMappedByteFast fm (BitVec.ofNat 64 addr) 0 size with
      | none => rfl
      | some off => exact findUnmappedAreaLoopFast_eq_batched fm size fuel _

def findUnmappedAreaFastB (fm : FastMem) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else
    findUnmappedAreaLoopFastB fm size ((USER_VA_LIMIT - MMAP_MIN_ADDR) / PAGE_SIZE + 1) MMAP_MIN_ADDR

theorem findUnmappedAreaFast_eq_batched (fm : FastMem) (size : Nat) :
    findUnmappedAreaFast fm size = findUnmappedAreaFastB fm size := by
  unfold findUnmappedAreaFast findUnmappedAreaFastB
  rw [findUnmappedAreaLoopFast_eq_batched]

def sanitizeMmapAddrFastB (fm : FastMem) (cand : BitVec 64) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else if decide (MMAP_MIN_ADDR ≤ cand.toNat) && cand.toNat % PAGE_SIZE == 0 &&
      decide (cand.toNat + size ≤ USER_VA_LIMIT) && fm.canMapB cand size then
    some cand
  else
    findUnmappedAreaFastB fm size

theorem sanitizeMmapAddrFast_eq_batched (fm : FastMem) (cand : BitVec 64) (size : Nat) :
    sanitizeMmapAddrFast fm cand size = sanitizeMmapAddrFastB fm cand size := by
  unfold sanitizeMmapAddrFast sanitizeMmapAddrFastB
  rw [fm.canMap_eq_batched, findUnmappedAreaFast_eq_batched]

end Symbolic.BugInjection.Proofs.CliExec.RadixMemPlacedBatched

