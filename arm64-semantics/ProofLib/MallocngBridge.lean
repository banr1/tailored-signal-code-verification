/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.MallocngIface
public import ProofLib.SyscallModels
public import ProofLib.StdStartup.NonVmSteps
import Arm64.Trusted.ISA.Memory
import Arm64.Trusted.ISA.State
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import Arm64.Trusted.Syscalls.Common
import Arm64.Trusted.Syscalls.Alloc
import Arm64.Trusted.Syscalls.Mm.Mmap
import Arm64.Trusted.Syscalls.Mm.Mremap
import Arm64.Trusted.Syscalls.Mm.Mprotect
import Arm64.Trusted.Syscalls.Mm.Madvise
import Arm64.Trusted.Syscalls

/-!
# Greedy Virtual-Address Gap Discharge and Allocator Syscall Bridge

Proves greedy page-aligned virtual-address gap existence (`hasGap_of_coversAbove`,
`hasGap_of_mappedIntervals`) inside `[MMAP_MIN_ADDR, 2^48)` for any finite cover of mapped
intervals, along with `physPlusRw` conservation under `allocMallocng` and cross-program
`MallocngCoreIface` call helpers (`sepWP_call_other_prog`, `call_malloc_placed`,
`call_free_some_placed`).
-/

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Interval Projection and Cover Monotonicity -/

/-- Project a `(base, len)` virtual-address interval into `Nat × Nat` inside `[0, 2^48)`. -/
def toNatInterval (iv : BitVec 64 × Nat) : Nat × Nat :=
  (if iv.1.toNat < 2 ^ 48 then iv.1.toNat else 0, iv.2)

theorem mem_toNatInterval {iv : BitVec 64 × Nat} {a : BitVec 64}
    (ha48 : a.toNat < 2 ^ 48) (hivLen : iv.2 ≤ 2 ^ 48)
    (hin : (a - iv.1).toNat < iv.2) :
    (toNatInterval iv).1 ≤ a.toNat ∧ a.toNat < (toNatInterval iv).1 + (toNatInterval iv).2 := by
  unfold toNatInterval
  by_cases hlt : iv.1.toNat < 2 ^ 48
  · simp only [hlt, ↓reduceIte]
    bv_omega
  · simp only [hlt, ↓reduceIte, Nat.zero_le, Nat.zero_add, true_and]
    bv_omega

/-- Every mapped byte in `m` inside `[cur, 2^48)` belongs to at least one interval in `nIvs`. -/
def CoversAbove (cur : Nat) (nIvs : List (Nat × Nat)) (m : Memory) : Prop :=
  ∀ a : BitVec 64, cur ≤ a.toNat → a.toNat < 2 ^ 48 → (m.perm a).mapped = true →
    ∃ iv ∈ nIvs, iv.1 ≤ a.toNat ∧ a.toNat < iv.1 + iv.2

theorem filter_strict_drop {α : Type} (p : α → Bool) {l : List α} {x : α}
    (hx : x ∈ l) (hpx : p x = false) :
    (l.filter p).length < l.length := by
  induction l with
  | nil => nomatch hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hys
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le p ys)
    · simp only [List.filter_cons, List.length_cons]
      have hlt := ih hys
      by_cases hp : p y
      · simp only [hp, ↓reduceIte, List.length_cons]; omega
      · simp only [Bool.not_eq_true] at hp
        simp only [hp, Bool.false_eq_true, ↓reduceIte]; omega

theorem filter_snd_sum_le (p : Nat × Nat → Bool) :
    ∀ (ys : List (Nat × Nat)), ((ys.filter p).map Prod.snd).sum ≤ (ys.map Prod.snd).sum
  | [] => Nat.le_refl _
  | z :: zs => by
    have ihz := filter_snd_sum_le p zs
    by_cases hp : p z
    · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.sum_cons]; omega
    · simp only [Bool.not_eq_true] at hp
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

theorem filter_snd_sum_drop (p : Nat × Nat → Bool) {l : List (Nat × Nat)} {x : Nat × Nat}
    (hx : x ∈ l) (hpx : p x = false) :
    ((l.filter p).map Prod.snd).sum + x.2 ≤ (l.map Prod.snd).sum := by
  induction l with
  | nil => nomatch hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hys
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
      have hsub := filter_snd_sum_le p ys
      omega
    · have hih := ih hys
      by_cases hp : p y
      · simp only [List.filter_cons, hp, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · simp only [Bool.not_eq_true] at hp
        simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
        omega

/-! ## Greedy Page-Aligned Virtual-Address Gap Existence -/

/-- Greedy interval-complement bound: if every mapped byte of `m` in `[cur, 2^48)` is covered by
    `nIvs` (`nIvs.length ≤ k`) and
    `cur + (nIvs.map Prod.snd).sum + nIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48`,
    then `m` has an unmapped page-aligned gap `slot` of size `sz` in `[MMAP_MIN_ADDR, 2^48)`. -/
theorem hasGap_of_coversAbove :
    ∀ (k cur sz : Nat) (nIvs : List (Nat × Nat)) (m : Memory),
      nIvs.length ≤ k →
      MMAP_MIN_ADDR ≤ cur →
      cur % PAGE_SIZE = 0 →
      PAGE_SIZE ≤ sz →
      sz % PAGE_SIZE = 0 →
      CoversAbove cur nIvs m →
      cur + (nIvs.map Prod.snd).sum + nIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48 →
      ∃ slot : BitVec 64,
        MMAP_MIN_ADDR ≤ slot.toNat ∧
        slot.toNat % PAGE_SIZE = 0 ∧
        slot.toNat + sz ≤ 2 ^ 48 ∧
        m.canMap slot sz = true
  | k, cur, sz, nIvs, m, hk, hmin, hcurAl, hszPos, hszAl, hcov, hfit => by
    have hPage : PAGE_SIZE = 4096 := rfl
    let slot : BitVec 64 := BitVec.ofNat 64 cur
    have hslotNat : slot.toNat = cur := by unfold slot; bv_omega
    by_cases hcan : m.canMap slot sz = true
    · exact ⟨slot, by omega, by rwa [hslotNat], by omega, hcan⟩
    · have hNotAll : ¬ (∀ i < sz, (!(m.perm (slot + BitVec.ofNat 64 i)).mapped) = true) := by
        intro hAll
        exact hcan ((Memory.allPerm_iff m (fun p => !p.mapped) slot sz).mpr hAll)
      obtain ⟨i, hiNot⟩ := Classical.not_forall.mp hNotAll
      have hiLt : i < sz := Classical.byContradiction fun h => hiNot fun hi => False.elim (h hi)
      have hPerm : (m.perm (slot + BitVec.ofNat 64 i)).mapped = true := by
        cases hp : (m.perm (slot + BitVec.ofNat 64 i)).mapped
        · exact False.elim (hiNot fun _ => by simp [hp])
        · rfl
      let a := slot + BitVec.ofNat 64 i
      have haNat : a.toNat = cur + i := by
        change (slot + BitVec.ofNat 64 i).toNat = cur + i
        bv_omega
      obtain ⟨iv, hivMem, hivLo, hivHi⟩ :=
        hcov a (by omega) (by omega) hPerm
      cases k with
      | zero =>
        have : nIvs = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this; nomatch hivMem
      | succ k' =>
        let cur' := Arm64.pageAlignUp (iv.1 + iv.2)
        have hcur'_ge : iv.1 + iv.2 ≤ cur' := by
          unfold cur' Arm64.pageAlignUp PAGE_SIZE; omega
        have hcur'_le : cur' ≤ cur + iv.2 + (sz + PAGE_SIZE) := by
          unfold cur' Arm64.pageAlignUp PAGE_SIZE
          omega
        have hcur'_al : cur' % PAGE_SIZE = 0 := by
          unfold cur' Arm64.pageAlignUp PAGE_SIZE; omega
        let keep : Nat × Nat → Bool := fun iv2 => decide (cur' < iv2.1 + iv2.2)
        let nIvs' := nIvs.filter keep
        have hivDrop : keep iv = false := by
          simp only [keep, decide_eq_false_iff_not]; omega
        have hlenLt : nIvs'.length < nIvs.length := filter_strict_drop keep hivMem hivDrop
        have hsumLe : (nIvs'.map Prod.snd).sum + iv.2 ≤ (nIvs.map Prod.snd).sum :=
          filter_snd_sum_drop keep hivMem hivDrop
        have hcov' : CoversAbove cur' nIvs' m := by
          intro b hbLo hbHi hbMap
          obtain ⟨iv2, hiv2Mem, hiv2Lo, hiv2Hi⟩ := hcov b (by omega) hbHi hbMap
          refine ⟨iv2, List.mem_filter.mpr ⟨hiv2Mem, ?_⟩, hiv2Lo, hiv2Hi⟩
          simp only [keep, decide_eq_true_eq]; omega
        have hmulStep : (nIvs'.length + 1) * (sz + PAGE_SIZE) ≤ nIvs.length * (sz + PAGE_SIZE) :=
          Nat.mul_le_mul_right (sz + PAGE_SIZE) hlenLt
        have hmulExpand : (nIvs'.length + 1) * (sz + PAGE_SIZE) =
            nIvs'.length * (sz + PAGE_SIZE) + (sz + PAGE_SIZE) := Nat.succ_mul _ _
        exact hasGap_of_coversAbove k' cur' sz nIvs' m (by omega) (by omega) hcur'_al
          hszPos hszAl hcov' (by omega)

theorem snd_le_sum_of_mem {iv : BitVec 64 × Nat} {ivs : List (BitVec 64 × Nat)}
    (h : iv ∈ ivs) : iv.2 ≤ (ivs.map Prod.snd).sum := by
  induction ivs with
  | nil => nomatch h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hxs
    · simp
    · have := ih hxs; simp; omega

/-- If every mapped byte of `m` lies in some `(base, len) ∈ totIvs` (`(a - iv.1).toNat < iv.2`)
    and `MMAP_MIN_ADDR + (totIvs.map Prod.snd).sum + totIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48`,
    then `m` admits a page-aligned unmapped gap of size `sz` in `[MMAP_MIN_ADDR, 2^48)`. -/
theorem hasGap_of_mappedIntervals {totIvs : List (BitVec 64 × Nat)} {m : Memory} {sz : Nat}
    (hMapped : ∀ a : BitVec 64, (m.perm a).mapped = true →
      ∃ iv ∈ totIvs, (a - iv.1).toNat < iv.2)
    (hSzPos : PAGE_SIZE ≤ sz)
    (hSzAl : sz % PAGE_SIZE = 0)
    (hFit : MMAP_MIN_ADDR + (totIvs.map Prod.snd).sum + totIvs.length * (sz + PAGE_SIZE) + sz ≤ 2 ^ 48) :
    ∃ slot : BitVec 64,
      MMAP_MIN_ADDR ≤ slot.toNat ∧
      slot.toNat % PAGE_SIZE = 0 ∧
      slot.toNat + sz ≤ 2 ^ 48 ∧
      m.canMap slot sz = true := by
  let nIvs := totIvs.map toNatInterval
  have hnLen : nIvs.length = totIvs.length := List.length_map _
  have hnSum : (nIvs.map Prod.snd).sum = (totIvs.map Prod.snd).sum := by
    have : nIvs.map Prod.snd = totIvs.map Prod.snd := by
      simp [nIvs, List.map_map, toNatInterval, Function.comp_def]
    rw [this]
  have hcov : CoversAbove MMAP_MIN_ADDR nIvs m := by
    intro a haLo haHi haMap
    obtain ⟨iv, hivMem, hin⟩ := hMapped a haMap
    have hivLen : iv.2 ≤ 2 ^ 48 := by
      have := snd_le_sum_of_mem hivMem; omega
    exact ⟨toNatInterval iv, List.mem_map_of_mem hivMem, mem_toNatInterval haHi hivLen hin⟩
  exact hasGap_of_coversAbove nIvs.length MMAP_MIN_ADDR sz nIvs m (Nat.le_refl _)
    (Nat.le_refl _) (by decide) hSzPos hSzAl hcov (by rw [hnLen, hnSum]; exact hFit)

theorem subroutine_ok_of_steps_outcome {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : ∀ (x : α) (R : SepProp) (s0 : State),
      s0.pc = entry → s0.status = .Running → (s0.mem ⊨ spec.pre x s0 ∗ R) →
      s0.spAligned = true → prog.CodeLoaded s0.mem →
      ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf) :
    subroutine_ok prog entry spec :=
  subroutine_ok_iff.mpr fun x R s0 hpc hrun hpre hsp =>
    reaches_outcome_iff.mpr (h x R s0 hpc hrun hpre hsp)

theorem subroutine_ok_elim_steps_outcome {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec) (x : α) (R : SepProp) (s0 : State)
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ spec.pre x s0 ∗ R) (hsp : s0.spAligned = true)
    (hL : prog.CodeLoaded s0.mem) :
    ∃ sf, Steps prog s0 sf ∧ SubroutineOutcome spec x R s0 sf :=
  reaches_outcome_iff.mp (subroutine_ok_iff.mp h x R s0 hpc hrun hpre hsp) hL

/-! ## `Syscall.alloc` Dispatch and `physPlusRw` Conservation -/

open ProofLib.StdStartup

private def countPred (f : BitVec 64 → Bool) (addr : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => (if f addr then 1 else 0) + countPred f (addr + 1#64) n

private theorem countRw_eq_countPred (m : Memory) :
    ∀ (addr : BitVec 64) (n : Nat),
      m.countRw addr n = countPred (fun a => m.perm a == some Perm.rw) addr n
  | _, 0 => rfl
  | addr, n + 1 => by
    change (if m.perm addr == some Perm.rw then 1 else 0) + m.countRw (addr + 1#64) n =
      (if m.perm addr == some Perm.rw then 1 else 0) +
        countPred (fun a => m.perm a == some Perm.rw) (addr + 1#64) n
    rw [countRw_eq_countPred m (addr + 1#64) n]

private theorem countPred_congr {f g : BitVec 64 → Bool} :
    ∀ (addr : BitVec 64) {n : Nat},
      (∀ i < n, f (addr + BitVec.ofNat 64 i) = g (addr + BitVec.ofNat 64 i)) →
      countPred f addr n = countPred g addr n
  | _, 0, _ => rfl
  | addr, n + 1, h => by
    have h0 : f addr = g addr := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : countPred f (addr + 1#64) n = countPred g (addr + 1#64) n := by
      apply countPred_congr (addr + 1#64)
      intro i hi
      have hi1 := h (i + 1) (Nat.succ_lt_succ hi)
      have hadj : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by bv_omega
      rwa [hadj] at hi1
    simp only [countPred, h0, hrest]

private theorem countPred_zero_of_false {f : BitVec 64 → Bool} (hf : ∀ a, f a = false) :
    ∀ (addr : BitVec 64) (n : Nat), countPred f addr n = 0
  | _, 0 => rfl
  | addr, n + 1 => by simp [countPred, hf addr, countPred_zero_of_false hf (addr + 1#64) n]

private theorem countPred_clear1_le (f : BitVec 64 → Bool) (target addr : BitVec 64) :
    ∀ {n : Nat}, n ≤ 2 ^ 64 →
      countPred f addr n ≤ countPred (fun a => if a = target then false else f a) addr n + 1
  | 0, _ => Nat.zero_le _
  | n + 1, hn => by
    simp only [countPred]
    by_cases hhit : addr = target
    · simp only [hhit, ↓reduceIte, Bool.false_eq_true]
      have hrest : countPred f (target + 1#64) n =
          countPred (fun a => if a = target then false else f a) (target + 1#64) n := by
        apply countPred_congr (target + 1#64)
        intro i hi
        have hne : target + 1#64 + BitVec.ofNat 64 i ≠ target := by bv_omega
        simp only [hne, ↓reduceIte]
      rw [hrest]
      by_cases hft : f target = true <;> (simp only [hft, ↓reduceIte, Bool.false_eq_true]; omega)
    · simp only [hhit, ↓reduceIte]
      have ih := @countPred_clear1_le f target (addr + 1#64) n (by omega)
      omega

private def clearRange (f : BitVec 64 → Bool) (base : BitVec 64) : Nat → BitVec 64 → Bool
  | 0 => f
  | k + 1 => fun a => if a = base + BitVec.ofNat 64 k then false else clearRange f base k a

private theorem clearRange_of_false {f : BitVec 64 → Bool} {base a : BitVec 64} (hf : f a = false) :
    ∀ (k : Nat), clearRange f base k a = false
  | 0 => hf
  | k + 1 => by simp [clearRange, clearRange_of_false hf k]

private theorem clearRange_false_of_lt (f : BitVec 64 → Bool) (base : BitVec 64) :
    ∀ (k : Nat) (a : BitVec 64), (a - base).toNat < k → clearRange f base k a = false
  | 0, _, h => nomatch h
  | k + 1, a, h => by
    simp only [clearRange]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
    · rw [clearRange_false_of_lt f base k a hlt, ite_self]
    · have ha : a = base + BitVec.ofNat 64 k := by bv_omega
      simp [ha]

private theorem countPred_le_clearRange_add (f : BitVec 64 → Bool) (base : BitVec 64)
    {N : Nat} (hN : N ≤ 2 ^ 64) :
    ∀ (k : Nat), countPred f 0#64 N ≤ countPred (clearRange f base k) 0#64 N + k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have ih := countPred_le_clearRange_add f base hN k
    have h1 := countPred_clear1_le (clearRange f base k) (base + BitVec.ofNat 64 k) 0#64 hN
    change countPred (clearRange f base k) 0#64 N ≤ countPred (clearRange f base (k + 1)) 0#64 N + 1 at h1
    omega

private def clearIntervals : (BitVec 64 → Bool) → List (BitVec 64 × Nat) → BitVec 64 → Bool
  | f, [] => f
  | f, iv :: ivs => clearIntervals (clearRange f iv.1 iv.2) ivs

private theorem clearIntervals_of_false {a : BitVec 64} :
    ∀ (ivs : List (BitVec 64 × Nat)) {f : BitVec 64 → Bool},
      f a = false → clearIntervals f ivs a = false
  | [], _, hf => hf
  | iv :: ivs, _, hf => clearIntervals_of_false ivs (clearRange_of_false hf iv.2)

private theorem clearIntervals_false_of_in {a : BitVec 64} :
    ∀ (ivs : List (BitVec 64 × Nat)) (f : BitVec 64 → Bool),
      (∃ iv ∈ ivs, (a - iv.1).toNat < iv.2) → clearIntervals f ivs a = false
  | [], _, h => by rcases h with ⟨_, hmem, _⟩; nomatch hmem
  | iv :: ivs, f, h => by
    rcases h with ⟨iv', hmem, hin⟩
    rcases List.mem_cons.mp hmem with hhead | hmem'
    · subst hhead
      exact clearIntervals_of_false ivs (clearRange_false_of_lt f iv'.1 iv'.2 a hin)
    · exact clearIntervals_false_of_in ivs (clearRange f iv.1 iv.2) ⟨iv', hmem', hin⟩

private theorem countPred_le_clearIntervals_add {N : Nat} (hN : N ≤ 2 ^ 64) :
    ∀ (ivs : List (BitVec 64 × Nat)) (f : BitVec 64 → Bool),
      countPred f 0#64 N ≤ countPred (clearIntervals f ivs) 0#64 N + (ivs.map Prod.snd).sum
  | [], _ => Nat.le_refl _
  | iv :: ivs, f => by
    have h1 := countPred_le_clearRange_add f iv.1 hN iv.2
    have h2 := countPred_le_clearIntervals_add hN ivs (clearRange f iv.1 iv.2)
    change countPred f 0#64 N ≤
      countPred (clearIntervals (clearRange f iv.1 iv.2) ivs) 0#64 N + (iv.2 + (ivs.map Prod.snd).sum)
    omega

private theorem countRw_le_intervals_sum {totIvs : List (BitVec 64 × Nat)} {m : Memory}
    {N : Nat} (hN : N ≤ 2 ^ 64)
    (hMapped : ∀ a : BitVec 64, (m.perm a).mapped = true →
      ∃ iv ∈ totIvs, (a - iv.1).toNat < iv.2) :
    m.countRw 0#64 N ≤ (totIvs.map Prod.snd).sum := by
  let f : BitVec 64 → Bool := fun a => m.perm a == some Perm.rw
  rw [countRw_eq_countPred]
  change countPred f 0#64 N ≤ (totIvs.map Prod.snd).sum
  have hle := countPred_le_clearIntervals_add hN totIvs f
  have hzero : countPred (clearIntervals f totIvs) 0#64 N = 0 := by
    apply countPred_zero_of_false
    intro a
    cases hfa : f a
    · exact clearIntervals_of_false totIvs hfa
    · have hmap : (m.perm a).mapped = true := by
        have hrw : m.perm a = some Perm.rw := eq_of_beq hfa
        rw [hrw]; rfl
      exact clearIntervals_false_of_in totIvs f (hMapped a hmap)
  omega

private theorem countPred_add (f : BitVec 64 → Bool) :
    ∀ (addr : BitVec 64) (m k : Nat),
      countPred f addr (m + k) = countPred f addr m + countPred f (addr + BitVec.ofNat 64 m) k
  | addr, 0, k => by simp [countPred]
  | addr, m + 1, k => by
    rw [Nat.succ_add, countPred, countPred, countPred_add f (addr + 1#64) m k]
    have hadj : addr + 1#64 + BitVec.ofNat 64 m = addr + BitVec.ofNat 64 (m + 1) := by bv_omega
    rw [hadj]
    omega

private theorem countPred_eq_zero_of_false_on {f : BitVec 64 → Bool} :
    ∀ (addr : BitVec 64) {n : Nat},
      (∀ i < n, f (addr + BitVec.ofNat 64 i) = false) →
      countPred f addr n = 0
  | _, 0, _ => rfl
  | addr, n + 1, h => by
    have h0 : f addr = false := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : countPred f (addr + 1#64) n = 0 := by
      apply countPred_eq_zero_of_false_on (addr + 1#64)
      intro i hi
      have hi1 := h (i + 1) (Nat.succ_lt_succ hi)
      have hadj : addr + BitVec.ofNat 64 (i + 1) = addr + 1#64 + BitVec.ofNat 64 i := by bv_omega
      rwa [hadj] at hi1
    simp [countPred, h0, hrest]

private theorem countPred_eq_len_of_true_on {f : BitVec 64 → Bool} :
    ∀ (addr : BitVec 64) {n : Nat},
      (∀ i < n, f (addr + BitVec.ofNat 64 i) = true) →
      countPred f addr n = n
  | _, 0, _ => rfl
  | addr, n + 1, h => by
    have h0 : f addr = true := by simpa using h 0 (Nat.zero_lt_succ n)
    have hrest : countPred f (addr + 1#64) n = n := by
      apply countPred_eq_len_of_true_on (addr + 1#64)
      intro i hi
      have hi1 := h (i + 1) (Nat.succ_lt_succ hi)
      have hadj : addr + 1#64 + BitVec.ofNat 64 i = addr + BitVec.ofNat 64 (i + 1) := by bv_omega
      rw [hadj]
      exact hi1
    simp [countPred, h0, hrest]
    omega

private theorem countPred_le_len (f : BitVec 64 → Bool) :
    ∀ (addr : BitVec 64) (n : Nat), countPred f addr n ≤ n
  | _, 0 => Nat.le_refl 0
  | addr, n + 1 => by
    have ih := countPred_le_len f (addr + 1#64) n
    simp only [countPred]
    by_cases h : f addr = true <;> (simp [h]; omega)

private theorem countRw_le_len (m : Memory) (addr : BitVec 64) (n : Nat) :
    m.countRw addr n ≤ n := by
  rw [countRw_eq_countPred]
  exact countPred_le_len _ addr n

private theorem countRw_congr {m1 m2 : Memory} (h : ∀ a, m1.perm a = m2.perm a)
    (addr : BitVec 64) (n : Nat) : m1.countRw addr n = m2.countRw addr n := by
  rw [countRw_eq_countPred, countRw_eq_countPred]
  exact countPred_congr addr (fun i _ => by simp [h])

private theorem countRw_split_region {m1 m2 : Memory} (base : BitVec 64) (len : Nat)
    {N : Nat} (hN : base.toNat + len ≤ N) (hN64 : N ≤ 2 ^ 64)
    (hout : ∀ a : BitVec 64, ¬ (a - base).toNat < len → m1.perm a = m2.perm a) :
    m1.countRw 0#64 N + m2.countRw base len = m2.countRw 0#64 N + m1.countRw base len := by
  let f1 : BitVec 64 → Bool := fun a => m1.perm a == some Perm.rw
  let f2 : BitVec 64 → Bool := fun a => m2.perm a == some Perm.rw
  rw [countRw_eq_countPred m1 0#64 N, countRw_eq_countPred m2 base len,
      countRw_eq_countPred m2 0#64 N, countRw_eq_countPred m1 base len]
  change countPred f1 0#64 N + countPred f2 base len =
    countPred f2 0#64 N + countPred f1 base len
  let pre := base.toNat
  let suf := N - (base.toNat + len)
  have hN_eq : N = pre + (len + suf) := by omega
  have hbase_eq : (0#64 : BitVec 64) + BitVec.ofNat 64 pre = base := by
    change (0#64 : BitVec 64) + BitVec.ofNat 64 base.toNat = base
    bv_omega
  have hsplit1 : countPred f1 0#64 N =
      countPred f1 0#64 pre + countPred f1 base len +
        countPred f1 (base + BitVec.ofNat 64 len) suf := by
    conv => lhs; rw [hN_eq]
    rw [countPred_add f1 0#64 pre (len + suf), hbase_eq, countPred_add f1 base len suf]
    omega
  have hsplit2 : countPred f2 0#64 N =
      countPred f2 0#64 pre + countPred f2 base len +
        countPred f2 (base + BitVec.ofNat 64 len) suf := by
    conv => lhs; rw [hN_eq]
    rw [countPred_add f2 0#64 pre (len + suf), hbase_eq, countPred_add f2 base len suf]
    omega
  have hpre : countPred f1 0#64 pre = countPred f2 0#64 pre := by
    apply countPred_congr 0#64
    intro i hi
    have hnot : ¬ (0#64 + BitVec.ofNat 64 i - base).toNat < len := by
      change i < base.toNat at hi
      bv_omega
    dsimp only [f1, f2]
    rw [hout _ hnot]
  have hsuf : countPred f1 (base + BitVec.ofNat 64 len) suf =
      countPred f2 (base + BitVec.ofNat 64 len) suf := by
    apply countPred_congr (base + BitVec.ofNat 64 len)
    intro i hi
    have hnot : ¬ (base + BitVec.ofNat 64 len + BitVec.ofNat 64 i - base).toNat < len := by
      change i < N - (base.toNat + len) at hi
      bv_omega
    dsimp only [f1, f2]
    rw [hout _ hnot]
  omega

@[irreducible] def rwBytes (m : Memory) : Nat :=
  m.countRw 0#64 (2 ^ 64)

theorem rwBytes_congr {m1 m2 : Memory} (h : ∀ a, m1.perm a = m2.perm a) :
    rwBytes m1 = rwBytes m2 := by
  unfold rwBytes
  exact countRw_congr h 0#64 (2 ^ 64)

theorem rwBytes_le_intervals_sum {totIvs : List (BitVec 64 × Nat)} {m : Memory}
    (hMapped : ∀ a : BitVec 64, (m.perm a).mapped = true →
      ∃ iv ∈ totIvs, (a - iv.1).toNat < iv.2) :
    rwBytes m ≤ (totIvs.map Prod.snd).sum := by
  unfold rwBytes
  exact countRw_le_intervals_sum (Nat.le_refl _) hMapped

private theorem rwBytes_split_region {m1 m2 : Memory} (base : BitVec 64) (len : Nat)
    (hbound : base.toNat + len ≤ 2 ^ 64)
    (hout : ∀ a : BitVec 64, ¬ (a - base).toNat < len → m1.perm a = m2.perm a) :
    rwBytes m1 + m2.countRw base len = rwBytes m2 + m1.countRw base len := by
  unfold rwBytes
  exact countRw_split_region base len hbound (Nat.le_refl _) hout

private theorem countRw_eq_zero_of_not_rw {m : Memory} {addr : BitVec 64} {n : Nat}
    (h : ∀ i < n, m.perm (addr + BitVec.ofNat 64 i) ≠ some Perm.rw) :
    m.countRw addr n = 0 := by
  rw [countRw_eq_countPred]
  exact countPred_eq_zero_of_false_on addr fun i hi => beq_eq_false_iff_ne.mpr (h i hi)

private theorem countRw_eq_len_of_rw {m : Memory} {addr : BitVec 64} {n : Nat}
    (h : ∀ i < n, m.perm (addr + BitVec.ofNat 64 i) = some Perm.rw) :
    m.countRw addr n = n := by
  rw [countRw_eq_countPred]
  exact countPred_eq_len_of_true_on addr fun i hi => beq_iff_eq.mpr (h i hi)

private theorem rwBytes_unmapWritable (m : Memory) (base : BitVec 64) (len : Nat)
    (hb : base.toNat + len ≤ 2 ^ 64) :
    rwBytes m = rwBytes (m.unmapWritable base len) + m.countRw base len := by
  have h0 : (m.unmapWritable base len).countRw base len = 0 := by
    apply countRw_eq_zero_of_not_rw
    intro i hi
    rw [Memory.perm_unmapWritable]
    have hin : (base + BitVec.ofNat 64 i - base).toNat < len := by bv_omega
    simp only [hin, decide_true, Bool.true_and]
    intro hcontra
    by_cases hw : (m.perm (base + BitVec.ofNat 64 i)).w = true
    · simp only [hw, ↓reduceIte] at hcontra; nomatch hcontra
    · simp only [Bool.eq_false_iff.mpr hw, Bool.false_eq_true, ↓reduceIte] at hcontra
      rw [hcontra] at hw; revert hw; decide
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m.unmapWritable base len) base len hb
    fun a hout => by
      rw [Memory.perm_unmapWritable]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

private theorem rwBytes_unmapNonFrozen (m : Memory) (base : BitVec 64) (len : Nat)
    (hb : base.toNat + len ≤ 2 ^ 64) :
    rwBytes m = rwBytes (m.unmapNonFrozen base len) + m.countRw base len := by
  have h0 : (m.unmapNonFrozen base len).countRw base len = 0 := by
    apply countRw_eq_zero_of_not_rw
    intro i hi
    rw [Memory.perm_unmapNonFrozen]
    have hin : (base + BitVec.ofNat 64 i - base).toNat < len := by bv_omega
    simp only [hin, decide_true, Bool.true_and]
    intro hcontra
    by_cases hfr : (m.perm (base + BitVec.ofNat 64 i)).frozen = true
    · simp only [hfr, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcontra
      rw [hcontra] at hfr; revert hfr; decide
    · simp only [Bool.eq_false_iff.mpr hfr, Bool.not_false, ↓reduceIte] at hcontra
      nomatch hcontra
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m.unmapNonFrozen base len) base len hb
    fun a hout => by
      rw [Memory.perm_unmapNonFrozen]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

private theorem countRw_eq_zero_of_canMap {m : Memory} {base : BitVec 64} {len : Nat}
    (hcan : m.canMap base len = true) :
    m.countRw base len = 0 := by
  apply countRw_eq_zero_of_not_rw
  intro i hi
  have hm := (Memory.allPerm_iff m (fun p => !p.mapped) base len).mp hcan i hi
  intro hrw
  rw [hrw] at hm; revert hm; decide

private theorem rwBytes_mapZero_of_canMap {m : Memory} {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 64) (hcan : m.canMap base len = true) :
    rwBytes (m.mapZero base len) = rwBytes m + len := by
  have h0 : m.countRw base len = 0 := countRw_eq_zero_of_canMap hcan
  have hlen : (m.mapZero base len).countRw base len = len := by
    apply countRw_eq_len_of_rw
    intro i hi
    have hm := (Memory.allPerm_iff m (fun p => !p.mapped) base len).mp hcan i hi
    have hin : (base + BitVec.ofNat 64 i - base).toNat < len := by bv_omega
    rw [Memory.perm_mapZero]
    simp only [hin, decide_true, Bool.true_and, hm, ↓reduceIte]
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m.mapZero base len) base len hb
    fun a hout => by
      rw [Memory.perm_mapZero]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

private theorem countRw_setPermNonFrozen_protNone (m : Memory) (base : BitVec 64) (len : Nat)
    (_hb : base.toNat + len ≤ 2 ^ 64) :
    (m.setPermNonFrozen base len Perm.protNone).countRw base len = 0 := by
  apply countRw_eq_zero_of_not_rw
  intro i hi
  rw [Memory.perm_setPermNonFrozen]
  have hin : (base + BitVec.ofNat 64 i - base).toNat < len := by bv_omega
  simp only [hin, decide_true, Bool.true_and]
  intro hcontra
  by_cases hcond : ((m.perm (base + BitVec.ofNat 64 i)).mapped &&
      !(m.perm (base + BitVec.ofNat 64 i)).frozen) = true
  · simp only [hcond, ↓reduceIte] at hcontra
    injection hcontra with hcontra; nomatch hcontra
  · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte] at hcontra
    rw [hcontra] at hcond; revert hcond; decide

private theorem rwBytes_setPermNonFrozen_protNone (m : Memory) (base : BitVec 64) (len : Nat)
    (hb : base.toNat + len ≤ 2 ^ 64) :
    rwBytes m = rwBytes (m.setPermNonFrozen base len Perm.protNone) + m.countRw base len := by
  have h0 := countRw_setPermNonFrozen_protNone m base len hb
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m.setPermNonFrozen base len Perm.protNone) base len hb
    fun a hout => by
      rw [Memory.perm_setPermNonFrozen]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

private theorem rwBytes_mmapFixed_protNone (m : Memory) (base : BitVec 64) (len : Nat)
    (hb : base.toNat + len ≤ 2 ^ 64) :
    rwBytes m =
      rwBytes (((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone) +
        m.countRw base len := by
  let m' := ((m.unmapNonFrozen base len).mapZero base len).setPermNonFrozen base len Perm.protNone
  have h0 : m'.countRw base len = 0 :=
    countRw_setPermNonFrozen_protNone ((m.unmapNonFrozen base len).mapZero base len) base len hb
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m') base len hb
    fun a hout => by
      dsimp only [m']
      rw [Memory.perm_setPermNonFrozen, Memory.perm_mapZero, Memory.perm_unmapNonFrozen]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  dsimp only [m'] at h0 hsplit
  omega

private theorem rwBytes_mapZero_protNone_of_canMap {m : Memory} {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 64) (hcan : m.canMap base len = true) :
    rwBytes ((m.mapZero base len).setPermNonFrozen base len Perm.protNone) = rwBytes m := by
  let m' := (m.mapZero base len).setPermNonFrozen base len Perm.protNone
  have h0 : m'.countRw base len = 0 := countRw_setPermNonFrozen_protNone (m.mapZero base len) base len hb
  have h0_m : m.countRw base len = 0 := countRw_eq_zero_of_canMap hcan
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m') base len hb
    fun a hout => by
      dsimp only [m']
      rw [Memory.perm_setPermNonFrozen, Memory.perm_mapZero]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  dsimp only [m'] at h0 hsplit
  omega

private theorem rwBytes_setPermNonFrozen_rw {m : Memory} {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 64)
    (hnf : m.allPerm (fun p => !p.frozen) base len = true)
    (hmap : m.allPerm (·.mapped) base len = true) :
    rwBytes m + len =
      rwBytes (m.setPermNonFrozen base len Perm.rw) + m.countRw base len := by
  have hlen : (m.setPermNonFrozen base len Perm.rw).countRw base len = len := by
    apply countRw_eq_len_of_rw
    intro i hi
    have h1 := (Memory.allPerm_iff m (fun p => !p.frozen) base len).mp hnf i hi
    have h2 := (Memory.allPerm_iff m (·.mapped) base len).mp hmap i hi
    have hin : (base + BitVec.ofNat 64 i - base).toNat < len := by bv_omega
    rw [Memory.perm_setPermNonFrozen]
    simp only [hin, decide_true, h1, h2, Bool.and_self, ↓reduceIte]; rfl
  have hsplit := rwBytes_split_region (m1 := m) (m2 := m.setPermNonFrozen base len Perm.rw) base len hb
    fun a hout => by
      rw [Memory.perm_setPermNonFrozen]
      simp only [hout, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  omega

private theorem rwBytes_remapRw {m : Memory} {oldBase : BitVec 64} {oldSize : Nat}
    {newBase : BitVec 64} {newSize : Nat}
    (holdBound : oldBase.toNat + oldSize ≤ 2 ^ 64)
    (hnewBound : newBase.toNat + newSize ≤ 2 ^ 64)
    (hrw : m.allPerm (· == some Perm.rw) oldBase oldSize = true)
    (hcan : (m.unmapNonFrozen oldBase oldSize).canMap newBase newSize = true) :
    rwBytes m + newSize =
      rwBytes (m.remapRw oldBase oldSize newBase newSize) + oldSize := by
  let m1 := m.unmapNonFrozen oldBase oldSize
  have holdRw : m.countRw oldBase oldSize = oldSize := by
    apply countRw_eq_len_of_rw
    intro i hi
    exact eq_of_beq ((Memory.allPerm_iff m (· == some Perm.rw) oldBase oldSize).mp hrw i hi)
  have hm1 : rwBytes m = rwBytes m1 + oldSize := by
    rw [rwBytes_unmapNonFrozen m oldBase oldSize holdBound, holdRw]
  have hm2 : rwBytes (m1.mapZero newBase newSize) = rwBytes m1 + newSize :=
    rwBytes_mapZero_of_canMap hnewBound hcan
  have hcongr : rwBytes (m.remapRw oldBase oldSize newBase newSize) =
      rwBytes (m1.mapZero newBase newSize) := by
    apply rwBytes_congr
    intro a
    rw [Memory.perm_remapRw_raw, Memory.perm_mapZero]
    by_cases hn : (a - newBase).toNat < newSize
    · have ha : newBase + BitVec.ofNat 64 (a - newBase).toNat = a := by bv_omega
      have hum := (Memory.allPerm_iff m1 (fun p => !p.mapped) newBase newSize).mp hcan
        (a - newBase).toNat hn
      rw [ha] at hum
      have hnf : (m.perm a).frozen = false := by
        cases hfr : (m.perm a).frozen
        · rfl
        · have hm1a : m1.perm a = m.perm a := by
            dsimp only [m1]; rw [Memory.perm_unmapNonFrozen]; simp [hfr]
          rw [hm1a] at hum
          cases hpa : m.perm a with
          | none => rw [hpa] at hfr; nomatch hfr
          | some p => rw [hpa] at hum; nomatch hum
      simp only [hn, decide_true, Bool.true_and, hum, hnf, Bool.false_eq_true, ↓reduceIte]
    · simp only [hn, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      dsimp only [m1]
      rw [Memory.perm_unmapNonFrozen]
      by_cases hfr : (m.perm a).frozen = true
      · simp [hfr]
      · simp [hfr]
  omega

abbrev physPlusRw (s : State) : Nat := s.physMemAvail + rwBytes s.mem

private theorem physPlusRw_adv (s : State) : physPlusRw s.advancePC = physPlusRw s := by cases s; rfl
private theorem physPlusRw_w64 (s : State) (r : Reg) (v : BitVec 64) :
    physPlusRw (s.writeReg64 r v) = physPlusRw s := by cases s; cases r <;> rfl
private theorem physPlusRw_st (s : State) (st : ExecStatus) :
    physPlusRw (s.setStatus st) = physPlusRw s := by cases s; rfl
private theorem physPlusRw_or (s : State) :
    physPlusRw s.nextOracle = physPlusRw s := by cases s; rfl

private theorem physPlusRw_execBrk (s : State) : physPlusRw (execBrk s) = physPlusRw s := by
  dsimp only [execBrk]
  split
  · simp [physPlusRw_adv, physPlusRw_w64]
  · split
    · split
      · simp [physPlusRw_adv, physPlusRw_w64]
      · simp only [physPlusRw_adv, physPlusRw_w64]
        let oldPage := Arm64.pageAlignUp s.brk.toNat
        let newPage := Arm64.pageAlignUp (s.readReg64 Reg.x0).toNat
        change (s.physMemAvail + s.mem.countRw (BitVec.ofNat 64 newPage) (oldPage - newPage)) +
          rwBytes (s.mem.unmapWritable (BitVec.ofNat 64 newPage) (oldPage - newPage)) =
          s.physMemAvail + rwBytes s.mem
        have hold64 : oldPage ≤ 2 ^ 64 := by
          unfold oldPage Arm64.pageAlignUp PAGE_SIZE
          have := s.brk.isLt; omega
        by_cases heq : newPage = oldPage
        · have hsub : oldPage - newPage = 0 := by omega
          rw [hsub]
          have h0 : s.mem.countRw (BitVec.ofNat 64 newPage) 0 = 0 := rfl
          have hm0 : rwBytes (s.mem.unmapWritable (BitVec.ofNat 64 newPage) 0) = rwBytes s.mem :=
            rwBytes_congr fun a => by rw [Memory.perm_unmapWritable]; simp
          omega
        · have hlt : newPage < 2 ^ 64 := by omega
          have hb : (BitVec.ofNat 64 newPage).toNat + (oldPage - newPage) ≤ 2 ^ 64 := by
            have : (BitVec.ofNat 64 newPage).toNat = newPage := Nat.mod_eq_of_lt hlt
            omega
          have hrw := rwBytes_unmapWritable s.mem (BitVec.ofNat 64 newPage) (oldPage - newPage) hb
          omega
    · split
      · simp [physPlusRw_adv, physPlusRw_w64]
      · next hcan_guard =>
        split
        · simp [physPlusRw_st]
        · next hphys =>
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq,
            USER_VA_LIMIT, BRK_GUARD_GAP, PAGE_SIZE] at hcan_guard hphys
          let oldPage := Arm64.pageAlignUp s.brk.toNat
          let newPage := Arm64.pageAlignUp (s.readReg64 Reg.x0).toNat
          let growBytes := newPage - oldPage
          have hold64 : oldPage ≤ 2 ^ 64 := by
            unfold oldPage Arm64.pageAlignUp PAGE_SIZE
            have := s.brk.isLt; omega
          have hnew48 : newPage + 256 * 4096 ≤ 2 ^ 48 := of_decide_eq_true hcan_guard.1
          have hb : (BitVec.ofNat 64 oldPage).toNat + growBytes ≤ 2 ^ 64 := by
            have holdLt : oldPage < 2 ^ 64 := by omega
            have : (BitVec.ofNat 64 oldPage).toNat = oldPage := Nat.mod_eq_of_lt holdLt
            omega
          have hcan : s.mem.canMap (BitVec.ofNat 64 oldPage) growBytes = true := by
            rw [Memory.canMap, Memory.allPerm_iff]
            intro i hi
            exact (Memory.allPerm_iff s.mem (fun p => !p.mapped) (BitVec.ofNat 64 oldPage)
              (growBytes + 256 * 4096)).mp hcan_guard.2 i (by omega)
          have hrw := rwBytes_mapZero_of_canMap hb hcan
          simp only [physPlusRw_adv, physPlusRw_w64]
          change (s.physMemAvail - growBytes) +
            rwBytes (s.mem.mapZero (BitVec.ofNat 64 oldPage) growBytes) =
            s.physMemAvail + rwBytes s.mem
          omega

private theorem physPlusRw_execMunmap (s : State) : physPlusRw (execMunmap s) = physPlusRw s := by
  dsimp only [execMunmap]
  split
  · simp [physPlusRw_adv, physPlusRw_w64]
  · next hvalid =>
    split
    · simp [physPlusRw_st]
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hvalid
      have hb : (s.readReg64 Reg.x0).toNat + Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat ≤ 2 ^ 64 := by
        have := hvalid.2; omega
      have hrw := rwBytes_unmapNonFrozen s.mem (s.readReg64 Reg.x0)
        (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) hb
      simp only [physPlusRw_adv, physPlusRw_w64]
      change (s.physMemAvail + s.mem.countRw (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)) +
        rwBytes (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)) =
        s.physMemAvail + rwBytes s.mem
      omega

private theorem physPlusRw_execMremap (s : State) : physPlusRw (execMremap s) = physPlusRw s := by
  dsimp only [execMremap]
  split
  · simp [physPlusRw_st]
  · split
    · simp [physPlusRw_adv, physPlusRw_w64]
    · split
      · simp [physPlusRw_st]
      · split
        · simp [physPlusRw_adv, physPlusRw_w64]
        · next holdLim =>
          split
          · simp [physPlusRw_st]
          · split
            · simp [physPlusRw_adv, physPlusRw_w64]
            · split
              · simp [physPlusRw_st]
              · next hrw =>
                split
                · simp [physPlusRw_st]
                · next _ =>
                  split
                  · simp [physPlusRw_adv, physPlusRw_w64, physPlusRw_or]
                  · split
                    · simp [physPlusRw_adv, physPlusRw_w64, physPlusRw_or]
                    · next newBase hsan =>
                      split
                      · simp [physPlusRw_st]
                      · next hphys =>
                        simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq, USER_VA_LIMIT]
                          at holdLim hrw hphys
                        obtain ⟨_, _, hnbFit, hcan⟩ := sanitizeMmapAddr_spec hsan
                        simp only [USER_VA_LIMIT] at hnbFit
                        have holdBound : (s.readReg64 Reg.x0).toNat +
                            Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat ≤ 2 ^ 64 := by
                          have := of_decide_eq_true holdLim; omega
                        have hrw_eq := rwBytes_remapRw holdBound (by omega) hrw hcan
                        simp only [physPlusRw_adv, physPlusRw_w64, physPlusRw_or]
                        change (s.physMemAvail + Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat -
                            Arm64.pageAlignUp (s.readReg64 Reg.x2).toNat) +
                          rwBytes (s.mem.remapRw (s.readReg64 Reg.x0)
                            (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) newBase
                            (Arm64.pageAlignUp (s.readReg64 Reg.x2).toNat)) =
                          s.physMemAvail + rwBytes s.mem
                        omega

private theorem physPlusRw_execMmap (s : State) : physPlusRw (execMmap s) = physPlusRw s := by
  dsimp only [execMmap]
  split
  · simp [physPlusRw_st]
  · split
    · simp [physPlusRw_adv, physPlusRw_w64]
    · split
      · split
        · simp [physPlusRw_st]
        · next haddr =>
          split
          · simp [physPlusRw_st]
          · next hfrz =>
            simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at haddr hfrz
            have hb : (s.readReg64 Reg.x0).toNat + Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat ≤ 2 ^ 64 := by
              have := haddr.2; omega
            split
            · have hrw := rwBytes_mmapFixed_protNone s.mem (s.readReg64 Reg.x0)
                (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) hb
              simp only [physPlusRw_adv, physPlusRw_w64]
              change (s.physMemAvail + s.mem.countRw (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)) +
                rwBytes (((s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)).mapZero
                  (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)).setPermNonFrozen
                  (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) Perm.protNone) =
                s.physMemAvail + rwBytes s.mem
              omega
            · split
              · simp [physPlusRw_st]
              · next hphys =>
                simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at hphys
                have hcan : (s.mem.unmapNonFrozen (s.readReg64 Reg.x0)
                    (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)).canMap
                    (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) = true := by
                  unfold Memory.canMap
                  rw [Memory.allPerm_iff] at hfrz ⊢
                  intro i hi
                  have hin : (s.readReg64 Reg.x0 + BitVec.ofNat 64 i - s.readReg64 Reg.x0).toNat <
                      Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat := by
                    bv_omega
                  rw [Memory.perm_unmapNonFrozen]
                  simp only [hin, decide_true, Bool.true_and]
                  have hfr := hfrz i hi
                  rw [hfr]
                  rfl
                have hunm := rwBytes_unmapNonFrozen s.mem (s.readReg64 Reg.x0)
                  (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) hb
                have hmz := rwBytes_mapZero_of_canMap hb hcan
                simp only [physPlusRw_adv, physPlusRw_w64]
                change (s.physMemAvail + s.mem.countRw (s.readReg64 Reg.x0)
                    (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) -
                    Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) +
                  rwBytes ((s.mem.unmapNonFrozen (s.readReg64 Reg.x0)
                    (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)).mapZero
                    (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)) =
                  s.physMemAvail + rwBytes s.mem
                omega
      · split
        · next base hsan =>
          obtain ⟨_, _, hfit, hcan⟩ := sanitizeMmapAddr_spec hsan
          simp only [USER_VA_LIMIT] at hfit
          have hb : base.toNat + Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat ≤ 2 ^ 64 := by omega
          split
          · have hrw := rwBytes_mapZero_protNone_of_canMap hb hcan
            simp only [physPlusRw_adv, physPlusRw_w64, physPlusRw_or]
            change s.physMemAvail + rwBytes ((s.mem.mapZero base (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)).setPermNonFrozen
              base (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) Perm.protNone) =
              s.physMemAvail + rwBytes s.mem
            omega
          · split
            · simp [physPlusRw_st]
            · next hphys =>
              simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at hphys
              have hrw := rwBytes_mapZero_of_canMap hb hcan
              simp only [physPlusRw_adv, physPlusRw_w64, physPlusRw_or]
              change (s.physMemAvail - Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) +
                rwBytes (s.mem.mapZero base (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)) =
                s.physMemAvail + rwBytes s.mem
              omega
        · simp [physPlusRw_st]

private theorem physPlusRw_execMprotect (s : State) (hprot : s.readReg64 Reg.x2 = MMAP_PROT_RW) :
    physPlusRw (execMprotect s) = physPlusRw s := by
  dsimp only [execMprotect]
  split
  · simp [physPlusRw_st]
  · split
    · simp [physPlusRw_adv, physPlusRw_w64]
    · split
      · simp [physPlusRw_st]
      · next hfit =>
        simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at hfit
        have hb : (s.readReg64 Reg.x0).toNat + Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat ≤ 2 ^ 64 := by omega
        split
        · simp [physPlusRw_adv, physPlusRw_w64]
        · split
          · simp [physPlusRw_st]
          · next hnf =>
            split
            · split <;> simp [physPlusRw_adv, physPlusRw_w64, physPlusRw_st]
            · next hmap =>
              simp only [Bool.not_eq_true, Bool.not_eq_false'] at hnf hmap
              split
              · next hnone =>
                exact absurd (eq_of_beq hnone) (by rw [hprot]; decide)
              · split
                · simp [physPlusRw_st]
                · next hphys =>
                  simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq] at hphys
                  have hrw := rwBytes_setPermNonFrozen_rw hb hnf hmap
                  have hle := countRw_le_len s.mem (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat)
                  simp only [physPlusRw_adv, physPlusRw_w64]
                  change (s.physMemAvail - (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat -
                      s.mem.countRw (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat))) +
                    rwBytes (s.mem.setPermNonFrozen (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) Perm.rw) =
                    s.physMemAvail + rwBytes s.mem
                  omega

private theorem physPlusRw_execMadvise (s : State) : physPlusRw (execMadvise s) = physPlusRw s := by
  dsimp (config := { zetaHave := true }) only [execMadvise]
  have hzero : physPlusRw (s.setMem (s.mem.zeroNonFrozen (s.readReg64 Reg.x0)
      (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat))) = physPlusRw s := by
    change s.physMemAvail + rwBytes (s.mem.zeroNonFrozen _ _) = s.physMemAvail + rwBytes s.mem
    rw [rwBytes_congr (Memory.perm_zeroNonFrozen_apply s.mem _ _)]
  have hmadv : physPlusRw (s.setMem (s.mem.madvFreeNonFrozen (s.readReg64 Reg.x0)
      (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat))) = physPlusRw s := by
    change s.physMemAvail + rwBytes (s.mem.madvFreeNonFrozen _ _) = s.physMemAvail + rwBytes s.mem
    rw [rwBytes_congr (Memory.perm_madvFreeNonFrozen_apply s.mem _ _)]
  (repeat' split) <;> simp only [physPlusRw_adv, physPlusRw_w64, physPlusRw_st, hzero, hmadv]

/-- Allocator syscall dispatcher for `mallocng`, identical to `Syscall.alloc` except that
    `SYS_MPROTECT` with `x2 ≠ MMAP_PROT_RW` traps (`mallocng` only promotes pages to `PROT_READ |
    PROT_WRITE`, so `physPlusRw` is strictly conserved). -/
def allocMallocng (s : State) : State :=
  if s.readReg64 Reg.x8 == SYS_MPROTECT && s.readReg64 Reg.x2 != MMAP_PROT_RW then
    s.setStatus (.Exception "unmodeled mprotect")
  else
    Syscall.alloc s

theorem evalSvc_allocMallocng (s : State) : evalSvc allocMallocng s = allocMallocng s := by
  unfold allocMallocng
  by_cases h : (s.readReg64 Reg.x8 == SYS_MPROTECT && s.readReg64 Reg.x2 != MMAP_PROT_RW) = true
  · unfold evalSvc; simp only [h, ↓reduceIte]
    cases s; simp [State.setStatus]
  · simp only [Bool.not_eq_true] at h
    have hev := evalSvc_alloc s
    unfold evalSvc at hev ⊢
    simp only [h, Bool.false_eq_true, ↓reduceIte, hev]

theorem physPlusRw_alloc (s : State) : physPlusRw (allocMallocng s) = physPlusRw s := by
  unfold allocMallocng
  split
  · exact physPlusRw_st s _
  · next hnot =>
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hnot
    unfold Syscall.alloc Syscall.dispatch
    split
    · rename_i nr fn hfind
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred : (nr == s.readReg64 Reg.x8) = true :=
        List.find?_some (p := fun x : BitVec 64 × (State → State) => x.1 == s.readReg64 Reg.x8) hfind
      have hx8 : s.readReg64 .x8 = nr := (beq_iff_eq.mp hpred).symm
      simp only [Syscall.allocTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> injection h with hnr hfn <;> subst hnr hfn
      · exact physPlusRw_execBrk s
      · exact physPlusRw_execMunmap s
      · exact physPlusRw_execMremap s
      · exact physPlusRw_execMmap s
      · rcases hnot with hne | hprot
        · exact absurd hx8 hne
        · exact physPlusRw_execMprotect s hprot
      · exact physPlusRw_execMadvise s
    · exact physPlusRw_st s _

theorem step_withSvc_alloc_of_noHooks {prog baseProg : Program} {s1 s2 : State}
    (h_no : ∀ pc, prog.externAt? pc = none) (h_svc : prog.svc = allocMallocng)
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h : Step prog s1 s2) : Step (baseProg.withSvc allocMallocng) s1 s2 := by
  have hf_eq : ∀ pc, prog.fetchMem s1.mem pc = (baseProg.withSvc allocMallocng).fetchMem s1.mem pc := fun pc => by
    unfold Program.fetchMem
    rw [h_no pc, Program.withSvc_externAt?, h_base_no pc]
  have hev : ∀ inst, prog.evalInst inst s1 = (baseProg.withSvc allocMallocng).evalInst inst s1 := fun inst => by
    simp only [Program.evalInst, h_svc, Program.withSvc_svc]
  cases h with
  | @exec inst hr hf =>
    rw [hf_eq s1.pc] at hf
    rw [hev inst]
    exact Step.exec hr hf
  | halt_unmapped hr hf _ =>
    rw [hf_eq s1.pc] at hf
    exact Step.halt_unmapped hr hf (by rw [Program.withSvc_externAt?]; exact h_base_no s1.pc)
  | extern _ he _ _ => rw [h_no s1.pc] at he; nomatch he
  | extern_fault _ he _ => rw [h_no s1.pc] at he; nomatch he

theorem steps_withSvc_alloc_of_noHooks {prog baseProg : Program} {s0 sf : State}
    (h_no : ∀ pc, prog.externAt? pc = none) (h_svc : prog.svc = allocMallocng)
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h : Steps prog s0 sf) : Steps (baseProg.withSvc allocMallocng) s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | step h1 _ ih => exact Steps.step (step_withSvc_alloc_of_noHooks h_no h_svc h_base_no h1) ih

theorem physPlusRw_step_withSvc_alloc {baseProg : Program} {s1 s2 : State}
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h : Step (baseProg.withSvc allocMallocng) s1 s2) : physPlusRw s2 = physPlusRw s1 := by
  cases h with
  | @exec inst _ _ =>
    by_cases hsvc0 : inst.isSvc0 = true
    · have hinst : inst = .system false 0#16 := by
        cases inst <;> simp [Instr.isSvc0] at hsvc0
        rcases hsvc0 with ⟨rfl, rfl⟩; rfl
      subst hinst
      rw [Program.evalInst_svc0, Program.withSvc_svc, evalSvc_allocMallocng]
      exact physPlusRw_alloc s1
    · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
      rw [evalInst_eq_execInst_of_not_isSvc0 _ hnsvc0]
      have hvm := execInst_vmFields_of_not_isSvc0 hnsvc0 s1
      unfold physPlusRw
      rw [hvm.physMemAvail_eq, rwBytes_congr hvm.perm_eq]
  | halt_unmapped _ _ _ => exact physPlusRw_st s1 _
  | extern _ he _ _ => rw [Program.withSvc_externAt?, h_base_no] at he; nomatch he
  | extern_fault _ he _ => rw [Program.withSvc_externAt?, h_base_no] at he

theorem physPlusRw_steps_withSvc_alloc {baseProg : Program} {s0 sf : State}
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h : Steps (baseProg.withSvc allocMallocng) s0 sf) : physPlusRw sf = physPlusRw s0 := by
  induction h with
  | refl _ => rfl
  | step h1 _ ih => exact ih.trans (physPlusRw_step_withSvc_alloc h_base_no h1)

theorem alloc_eq_standard_of_running {s : State}
    (hr : (allocMallocng s).status = .Running) :
    allocMallocng s = Syscall.standard s := by
  unfold allocMallocng at hr ⊢
  by_cases hcond : (s.readReg64 Reg.x8 == SYS_MPROTECT && s.readReg64 Reg.x2 != MMAP_PROT_RW) = true
  · simp only [hcond, ↓reduceIte, State.setStatus] at hr
    nomatch hr
  · simp only [Bool.not_eq_true] at hcond
    simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    have hstd : Syscall.standard = execSyscall := rfl
    rw [hstd]
    unfold Syscall.alloc Syscall.dispatch at hr
    cases hfind : Syscall.allocTable.find? (·.1 == s.readReg64 Reg.x8) with
    | none =>
      simp only [hfind, State.setStatus] at hr
      nomatch hr
    | some p =>
      rcases p with ⟨nr, fn⟩
      have hmem := List.mem_of_find?_eq_some hfind
      have hpred : (nr == s.readReg64 Reg.x8) = true :=
        List.find?_some (p := fun x : BitVec 64 × (State → State) => x.1 == s.readReg64 Reg.x8) hfind
      have hx8 : s.readReg64 .x8 = nr := (beq_iff_eq.mp hpred).symm
      simp only [Syscall.allocTable, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h | h | h <;> injection h with hnr _ <;> subst hnr
      · rw [alloc_brk s hx8, execSyscall_brk s hx8]
      · rw [alloc_munmap s hx8, execSyscall_munmap s hx8]
      · rw [alloc_mremap s hx8, execSyscall_mremap s hx8]
      · rw [alloc_mmap s hx8, execSyscall_mmap s hx8]
      · rw [alloc_mprotect s hx8, execSyscall_mprotect s hx8]
      · rw [alloc_madvise s hx8]
        unfold execSyscall Syscall.standard Syscall.dispatch Syscall.standardTable
          Syscall.stdioTable Syscall.fileIoOnlyTable Syscall.pollTable Syscall.allocTable
        simp [hx8, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE]

private theorem steps_start_running_bridge {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

theorem steps_of_withSvc_alloc {baseProg : Program} {s0 sf : State}
    (h_base_no : ∀ pc, baseProg.externAt? pc = none)
    (h_base_svc : baseProg.svc = Syscall.standard)
    (h : Steps (baseProg.withSvc allocMallocng) s0 sf) (hrun_f : sf.status = .Running) :
    Steps baseProg s0 sf := by
  induction h with
  | refl s => exact Steps.refl s
  | @step s1 s2 s3 h1 hrest ih =>
    have hr2 : s2.status = .Running := steps_start_running_bridge hrest hrun_f
    have hsteps_rest : Steps baseProg s2 s3 := ih hrun_f
    have hf_eq : (baseProg.withSvc allocMallocng).fetchMem s1.mem s1.pc =
        baseProg.fetchMem s1.mem s1.pc := by
      unfold Program.fetchMem; rw [Program.withSvc_externAt?]
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hr_svc : (allocMallocng s1).status = .Running := by
          rwa [Program.evalInst_svc0, Program.withSvc_svc, evalSvc_allocMallocng] at hr2
        have hev_eq : (baseProg.withSvc allocMallocng).evalInst (.system false 0#16) s1 =
            baseProg.evalInst (.system false 0#16) s1 := by
          rw [Program.evalInst_svc0, Program.withSvc_svc, evalSvc_allocMallocng,
              Program.evalInst_svc0, h_base_svc, evalSvc_standard,
              alloc_eq_standard_of_running hr_svc]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev_eq : (baseProg.withSvc allocMallocng).evalInst inst s1 =
            baseProg.evalInst inst s1 := by
          rw [evalInst_eq_execInst_of_not_isSvc0 hnsvc0, evalInst_eq_execInst_of_not_isSvc0 hnsvc0]
        rw [hev_eq] at hsteps_rest
        exact Steps.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern _ he _ _ => rw [Program.withSvc_externAt?, h_base_no] at he; nomatch he
    | extern_fault _ he _ => rw [Program.withSvc_externAt?, h_base_no] at he; nomatch he

/-! ## Cross-Program `MallocngCoreIface` Call and Transport Helpers -/

/-- Framed call from a placed block program `P_caller` (with no extern/override hooks and matching
    `svc`) into a subroutine proved over another hook-free `Program` `Q` (such as an allocator
    `MallocngCoreIface Q addrs lim`), given `Q.CodeLoaded s.mem`. -/
theorem sepWP_call_other_prog {α : Type} {P_caller Q : Program}
    {entry target_pc ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok Q entry spec)
    (hext_P : ∀ pc, P_caller.externAt? pc = none)
    (hext_Q : ∀ pc, Q.externAt? pc = none)
    (hsvc : P_caller.svc = Q.svc)
    {x : α} {s : State} {Pre F : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcl : Q.CodeLoaded s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (h_no_panic : ∀ R' sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s sf ∗ R'))
    (h_no_exit : ∀ R' code sf, sf.status = .Exited code → ¬(sf.mem ⊨ spec.onExit x code s sf ∗ R'))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWP P_caller target_pc sf (spec.post x s sf ∗ F) post oom)
    (h_oom : ∀ R' sf, sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ oom sf ∗ R') := by
      wp_close_oom_default) :
    SepWP P_caller target_pc s Pre post oom :=
  SepWP.call_subroutine_frame_other (P := P_caller) (Q := Q) hcall
    (fun pc => (hext_Q pc).trans (hext_P pc).symm) hsvc.symm hcl hpc hrun hsp hlr hpre
    h_no_panic h_no_exit (fun sf hpc' hrun' hsp' hcs' _ => hnext sf hpc' hrun' hsp' hcs') h_oom

/-- Transport `M.Heap γ lc blk` across any transition preserving `ProofLib.StdStartup.VmFieldsPreserved`. -/
theorem MallocngCoreIface.transport_vm {P : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface P addrs lim) {γ : GhostName} {lc blk : Nat} {s1 s2 : State}
    (hvm : ProofLib.StdStartup.VmFieldsPreserved s1 s2) :
    M.Heap γ lc blk s1 ⊢ M.Heap γ lc blk s2 := by
  rcases hvm with ⟨hb, hbs, hp, hm⟩
  exact M.heap_transport hb hbs hp hm

/-- Call `M.malloc_ok γ` on `Q` directly from any hook-free caller program `P_caller` with matching
    `svc`, given `Q.CodeLoaded s.mem`. -/
theorem call_malloc_placed {P_caller Q : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface Q addrs lim) (γ : GhostName)
    {target_pc ret_pc : BitVec 64}
    (hext_P : ∀ pc, P_caller.externAt? pc = none)
    (hext_Q : ∀ pc, Q.externAt? pc = none)
    (hsvc : P_caller.svc = Q.svc)
    {lc blk req : Nat} {e0 : BitVec 32} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hcl : Q.CodeLoaded s.mem)
    (hpc : s.pc = addrs.mallocAddr)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hreq : req = (s.readReg64 (.gpr 0#5)).toNat)
    (hreq_le : req ≤ lim.maxReq)
    (hcost : lc + mallocngBlockCost req ≤ lim.maxPeakCost)
    (hblk : blk + 1 ≤ lim.maxPeakBlocks)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp MallocngStackBytes) ∗
        (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      let ret := sf.readReg64 (.gpr 0#5)
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      ret ≠ 0#64 → 16 ∣ ret.toNat → ret.toNat + req < 2 ^ 64 →
      SepWP P_caller target_pc sf
        ((M.Heap γ (lc + mallocngBlockCost req) (blk + 1) sf ∗
          M.Block γ ret req ∗ memRegion ret req ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp MallocngStackBytes) ∗ F) post) :
    SepWP P_caller target_pc s Pre post := by
  refine sepWP_call_other_prog (M.malloc_ok γ) hext_P hext_Q hsvc
    (x := (lc, blk, req, e0)) (F := F) hcl hpc hrun hsp hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
  · intro R hm
    have hm1 := hpre R hm
    have hassoc :
        (M.Heap γ lc blk s ∗ (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp MallocngStackBytes) ∗ (F ∗ R) =
        (M.Heap γ lc blk s ∗ ((muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp MallocngStackBytes)) ∗ (F ∗ R) := by
      simp [sepConj_assoc]
    rw [hassoc] at hm1
    dsimp only
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm1 ⊢
    exact ⟨⟨hreq, hreq_le, hcost, hblk⟩, hm1⟩
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    rintro ⟨hmsp, hnz, hal16, hnw⟩
    have htp : muslErrnoAddr s = muslErrnoAddr sf := by
      unfold muslErrnoAddr; rw [hmsp.2.2.2.1]
    rw [htp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    refine SepWP.weaken_pre ?_ (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp hnz hal16 hnw)
    sep_entail

/-- Call `M.free_ok γ` on non-null pointer `p ≠ 0#64` (`optReq = some req`) directly from any
    hook-free caller program `P_caller` with matching `svc`, given `Q.CodeLoaded s.mem`. -/
theorem call_free_some_placed {P_caller Q : Program} {addrs : MallocngAddrs} {lim : MallocngLimits}
    (M : MallocngCoreIface Q addrs lim) (γ : GhostName)
    {target_pc ret_pc : BitVec 64}
    (hext_P : ∀ pc, P_caller.externAt? pc = none)
    (hext_Q : ∀ pc, Q.externAt? pc = none)
    (hsvc : P_caller.svc = Q.svc)
    {lc blk req : Nat} {p : BitVec 64} {e0 : BitVec 32} {s : State} {Pre F : SepProp}
    {post : State → SepProp → Prop}
    (hcl : Q.CodeLoaded s.mem)
    (hpc : s.pc = addrs.freeAddr)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hp_reg : s.readReg64 (.gpr 0#5) = p)
    (hp_nz : p ≠ 0#64)
    (hpre : ∀ R : SepProp, (s.mem ⊨ Pre ∗ R) →
      (s.mem ⊨ (M.Heap γ lc blk s ∗ M.Block γ p req ∗ memRegion p req ∗
        (muslErrnoAddr s ↦₃₂ e0) ∗ stackAt s.sp MallocngStackBytes) ∗ (F ∗ R)))
    (hnext : ∀ (sf : State) (e1 : BitVec 32),
      sf.pc = ret_pc → sf.status = .Running → sf.sp = s.sp → CalleeSavedPreserved s sf →
      MallocngStatePreserved s sf →
      SepWP P_caller target_pc sf
        ((M.Heap γ (lc - mallocngBlockCost req) (blk - 1) sf ∗
          (muslErrnoAddr sf ↦₃₂ e1) ∗ stackAt s.sp MallocngStackBytes) ∗ F) post) :
    SepWP P_caller target_pc s Pre post := by
  refine sepWP_call_other_prog (M.free_ok γ) hext_P hext_Q hsvc
    (x := (lc, blk, some req, e0)) (F := F) hcl hpc hrun hsp hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h) ?_
  · intro R hm
    have hm1 := hpre R hm
    dsimp only; rw [hp_reg]
    refine Satisfies.mono ?_ hm1
    rw [pure_sepConj_of_true hp_nz]
    sep_entail
  · intro sf hpc_f hrun_f hsp_f hcs_f
    dsimp only
    rw [sepConj_assoc]
    apply SepWP.pure_elim
    intro hmsp
    have htp : muslErrnoAddr s = muslErrnoAddr sf := by
      unfold muslErrnoAddr; rw [hmsp.2.2.2.1]
    rw [htp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWP.exists_elim fun e1 => ?_
    refine SepWP.weaken_pre ?_ (hnext sf e1 hpc_f hrun_f hsp_f hcs_f hmsp)
    sep_entail

end ProofLib
