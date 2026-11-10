/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Process.FastParse
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine

/-!
# Relocatable Virtual Memory and Initial `FastMem` Operations

Provides computable `FastMem` counterparts and `Arm64.Memory` agreement theorems for Linux virtual
memory and path syscalls (`brk`, `munmap`, `mmap`, `mprotect`, `mremap`, `openat`), backed by
`BinTree` key deletion (`btDel`) and on-demand materialization of the lazy stack fallback. Also
defines relocatable ELF initial memory construction (`initFastMemAndSpPlaced`) with parameterized
CPU-probe token updates (`patchTokenFastMemPlaced`).
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

set_option autoImplicit false

open Arm64 Arm64.Memory
open Arm64.Process (ElfImage ProcessInputs buildInitialStack)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem

/-- `btDel d tr k` deletes key `k` at depth `d` in `tr` and collapses empty branches. -/
def btDel {α : Type} : Nat → BinTree α → Nat → BinTree α
  | _, .empty, _ => .empty
  | _, .twig kj v, k => if Nat.beq k kj then .empty else .twig kj v
  | 0, .branch _ _, _ => .empty
  | d + 1, .branch lo hi, k =>
    if Nat.beq (Nat.mod k 2) 0 then
      let lo' := btDel d lo (Nat.div k 2)
      match lo', hi with
      | .empty, .empty => .empty
      | _, _ => mkBranchL lo' hi
    else
      let hi' := btDel d hi (Nat.div k 2)
      match lo, hi' with
      | .empty, .empty => .empty
      | _, _ => mkBranchR lo hi'

theorem btGet_btDel_same {α : Type} :
    ∀ (d : Nat) (tr : BinTree α) (k : Nat), btGet d (btDel d tr k) k = none
  | d, .empty, _ => by cases d <;> rfl
  | d, .twig kj v, k => by
    unfold btDel
    by_cases h : Nat.beq k kj = true
    · simp [h]
    · simp [h]
  | 0, .branch _ _, _ => rfl
  | d + 1, .branch lo hi, k => by
    dsimp only [btDel]
    by_cases hm : Nat.beq (Nat.mod k 2) 0 = true
    · simp only [hm, ↓reduceIte]
      generalize hlo : btDel d lo (Nat.div k 2) = lo'
      have ih := btGet_btDel_same d lo (Nat.div k 2)
      rw [hlo] at ih
      cases lo' <;> cases hi <;> simp [btGet, hm, ih]
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      generalize hhi : btDel d hi (Nat.div k 2) = hi'
      have ih := btGet_btDel_same d hi (Nat.div k 2)
      rw [hhi] at ih
      cases lo <;> cases hi' <;> simp [btGet, hm, ih]

theorem btGet_btDel_ne {α : Type} :
    ∀ (d : Nat) (tr : BinTree α) (k j : Nat),
      k < 2 ^ d → j < 2 ^ d → j ≠ k → btGet d (btDel d tr k) j = btGet d tr j
  | d, .empty, _, _, _, _, _ => by cases d <;> rfl
  | d, .twig kj v, k, j, _, _, hne => by
    unfold btDel
    by_cases hk : Nat.beq k kj = true
    · have hkj : k = kj := Nat.beq_eq.mp hk
      subst hkj
      have hjk : Nat.beq j k = false := Bool.eq_false_iff.mpr fun h => hne (Nat.beq_eq.mp h)
      simp [hjk]
    · simp [hk]
  | 0, .branch _ _, k, j, hk, hj, hne => by omega
  | d + 1, .branch lo hi, k, j, hk, hj, hne => by
    have hk2 : Nat.div k 2 < 2 ^ d := by
      change k / 2 < 2 ^ d
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
    have hj2 : Nat.div j 2 < 2 ^ d := by
      change j / 2 < 2 ^ d
      have : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      omega
    dsimp only [btDel]
    by_cases hmk : Nat.beq (Nat.mod k 2) 0 = true
    · simp only [hmk, ↓reduceIte]
      generalize hlo : btDel d lo (Nat.div k 2) = lo'
      have hbr : btGet (d + 1)
          (match lo', hi with
           | .empty, .empty => .empty
           | _, _ => mkBranchL lo' hi) j =
          btGet (d + 1) (.branch lo' hi) j := by
        cases lo' <;> cases hi <;> simp [btGet]
      refine hbr.trans ?_
      rw [← hlo]
      dsimp only [btGet]
      by_cases hmj : Nat.beq (Nat.mod j 2) 0 = true
      · simp only [hmj, ↓reduceIte]
        have hne2 : Nat.div j 2 ≠ Nat.div k 2 := by
          change j / 2 ≠ k / 2
          have hm1 : k % 2 = 0 := Nat.beq_eq.mp hmk
          have hm2 : j % 2 = 0 := Nat.beq_eq.mp hmj
          omega
        exact btGet_btDel_ne d lo (Nat.div k 2) (Nat.div j 2) hk2 hj2 hne2
      · simp only [hmj, Bool.false_eq_true, ↓reduceIte]
    · simp only [hmk, Bool.false_eq_true, ↓reduceIte]
      generalize hhi : btDel d hi (Nat.div k 2) = hi'
      have hbr : btGet (d + 1)
          (match lo, hi' with
           | .empty, .empty => .empty
           | _, _ => mkBranchR lo hi') j =
          btGet (d + 1) (.branch lo hi') j := by
        cases lo <;> cases hi' <;> simp [btGet]
      refine hbr.trans ?_
      rw [← hhi]
      dsimp only [btGet]
      by_cases hmj : Nat.beq (Nat.mod j 2) 0 = true
      · simp only [hmj, ↓reduceIte]
      · simp only [hmj, Bool.false_eq_true, ↓reduceIte]
        have hne2 : Nat.div j 2 ≠ Nat.div k 2 := by
          change j / 2 ≠ k / 2
          have hm1 : k % 2 ≠ 0 := fun h => hmk (Nat.beq_eq.mpr h)
          have hm2 : j % 2 ≠ 0 := fun h => hmj (Nat.beq_eq.mpr h)
          omega
        exact btGet_btDel_ne d hi (Nat.div k 2) (Nat.div j 2) hk2 hj2 hne2

/-- Delete the byte cell at `addr < 2 ^ 64` from `lines`, and prune the outer line entry if empty. -/
def delRawCell (lines : BinTree Line64) (addr : Nat) : BinTree Line64 :=
  let hi := Nat.div addr 64
  let lo := Nat.mod addr 64
  match btGet 58 lines hi with
  | none => lines
  | some ln =>
    match btDel 6 ln lo with
    | .empty => btDel 58 lines hi
    | ln' => btSet58Line lines hi ln'

theorem rawCellAt_delRawCell_same (lines : BinTree Line64) {addr : Nat} (_h : addr < 2 ^ 64) :
    rawCellAt (delRawCell lines addr) addr = none := by
  dsimp only [delRawCell, rawCellAt]
  have hd : Nat.div addr 64 = addr / 64 := rfl
  have hm : Nat.mod addr 64 = addr % 64 := rfl
  rw [hd, hm]
  cases h58 : btGet 58 lines (addr / 64) with
  | none => simp [h58]
  | some ln =>
    dsimp only
    generalize hdel : btDel 6 ln (addr % 64) = ln'
    have h6 := btGet_btDel_same 6 ln (addr % 64)
    rw [hdel] at h6
    cases ln' with
    | empty => dsimp only; simp [btGet_btDel_same]
    | twig j u => dsimp only; simp [btSet58Line_eq, btGet_btSet_same', h6]
    | branch x y => dsimp only; simp [btSet58Line_eq, btGet_btSet_same', h6]

theorem rawCellAt_delRawCell_ne (lines : BinTree Line64) {addr a : Nat}
    (haddr : addr < 2 ^ 64) (ha : a < 2 ^ 64) (hne : a ≠ addr) :
    rawCellAt (delRawCell lines addr) a = rawCellAt lines a := by
  dsimp only [delRawCell, rawCellAt]
  have hd : Nat.div addr 64 = addr / 64 := rfl
  have hm : Nat.mod addr 64 = addr % 64 := rfl
  rw [hd, hm]
  cases h58 : btGet 58 lines (addr / 64) with
  | none => rfl
  | some ln =>
    dsimp only
    have hhi_addr : addr / 64 < 2 ^ 58 := div64_lt_2pow58 haddr
    have hhi_a : a / 64 < 2 ^ 58 := div64_lt_2pow58 ha
    by_cases hhieq : a / 64 = addr / 64
    · have hlo_ne : a % 64 ≠ addr % 64 := by omega
      have h6ne := btGet_btDel_ne 6 ln (addr % 64) (a % 64)
        (mod64_lt_2pow6 addr) (mod64_lt_2pow6 a) hlo_ne
      rw [hhieq, h58]
      cases hdel : btDel 6 ln (addr % 64) with
      | empty =>
        dsimp only
        rw [hdel] at h6ne
        simp [btGet_btDel_same, ← h6ne]
      | twig j u =>
        dsimp only
        rw [hdel] at h6ne
        simp [btSet58Line_eq, btGet_btSet_same', h6ne]
      | branch x y =>
        dsimp only
        rw [hdel] at h6ne
        simp [btSet58Line_eq, btGet_btSet_same', h6ne]
    · cases hdel : btDel 6 ln (addr % 64) with
      | empty =>
        dsimp only
        rw [btGet_btDel_ne 58 lines (addr / 64) (a / 64) hhi_addr hhi_a hhieq]
      | twig j u =>
        dsimp only
        rw [btSet58Line_eq, btGet_btSet_ne 58 (addr / 64) (a / 64) lines _ hhi_addr hhi_a
          (Ne.symm hhieq)]
      | branch x y =>
        dsimp only
        rw [btSet58Line_eq, btGet_btSet_ne 58 (addr / 64) (a / 64) lines _ hhi_addr hhi_a
          (Ne.symm hhieq)]

/-- Materialize untouched stack-fallback bytes in `[sb, sb + cnt)` (`sb + cnt ≤ 2 ^ 64`). -/
def materializeStackLoop (lines : BinTree Line64) (sb : Nat) : Nat → BinTree Line64
  | 0 => lines
  | k + 1 =>
    let addr := sb + k
    match rawCellAt lines addr with
    | some _ => materializeStackLoop lines sb k
    | none =>
      withForcedBinTree (setRawCell lines addr (some Perm.rw, 0#8)) fun lines' =>
        materializeStackLoop lines' sb k

theorem rawCellAt_materializeStackLoop (lines : BinTree Line64) (sb cnt : Nat)
    (htop : sb + cnt ≤ 2 ^ 64) (a : Nat) (ha : a < 2 ^ 64) :
    rawCellAt (materializeStackLoop lines sb cnt) a =
      match rawCellAt lines a with
      | some c => some c
      | none => if sb ≤ a && a < sb + cnt then some (some Perm.rw, 0#8) else none := by
  induction cnt generalizing lines with
  | zero =>
    dsimp only [materializeStackLoop]
    cases rawCellAt lines a with
    | some _ => rfl
    | none => simp
  | succ k ih =>
    dsimp only [materializeStackLoop]
    have htop' : sb + k ≤ 2 ^ 64 := by omega
    have haddr_lt : sb + k < 2 ^ 64 := by omega
    cases hcur : rawCellAt lines (sb + k) with
    | some c0 =>
      rw [ih lines htop']
      by_cases heq : a = sb + k
      · subst heq; simp [hcur]
      · cases rawCellAt lines a with
        | some c => rfl
        | none =>
          have hiff : (sb ≤ a ∧ a < sb + k) ↔ (sb ≤ a ∧ a < sb + (k + 1)) := by omega
          by_cases hr : sb ≤ a ∧ a < sb + k
          · have hr2 := hiff.mp hr
            simp [hr, hr2]
          · have hr2 : ¬ (sb ≤ a ∧ a < sb + (k + 1)) := fun h => hr (hiff.mpr h)
            simp [hr, hr2]
    | none =>
      simp only [withForcedBinTree_eq]
      rw [ih (setRawCell lines (sb + k) (some Perm.rw, 0#8)) htop']
      by_cases heq : a = sb + k
      · subst heq
        rw [rawCellAt_setRawCell_same]
        have hr : sb ≤ sb + k ∧ sb + k < sb + (k + 1) := by omega
        simp [hcur, hr]
      · rw [rawCellAt_setRawCell_ne lines _ haddr_lt ha heq]
        cases rawCellAt lines a with
        | some c => rfl
        | none =>
          have hiff : (sb ≤ a ∧ a < sb + k) ↔ (sb ≤ a ∧ a < sb + (k + 1)) := by omega
          by_cases hr : sb ≤ a ∧ a < sb + k
          · have hr2 := hiff.mp hr
            simp [hr, hr2]
          · have hr2 : ¬ (sb ≤ a ∧ a < sb + (k + 1)) := fun h => hr (hiff.mpr h)
            simp [hr, hr2]

/-- Materialize `fm`'s lazy zero-stack fallback so `stackBase = 0 ∧ stackTop = 0`. -/
def materializeStackFallback (fm : FastMem) : FastMem :=
  let top' := min fm.stackTop (2 ^ 64)
  if top' ≤ fm.stackBase then
    { lines := fm.lines, stackBase := 0, stackTop := 0 }
  else
    { lines := materializeStackLoop fm.lines fm.stackBase (top' - fm.stackBase)
      stackBase := 0
      stackTop := 0 }

theorem materializeStackFallback_cellAt (fm : FastMem) (a : BitVec 64) :
    (materializeStackFallback fm).cellAt a = fm.cellAt a := by
  unfold materializeStackFallback
  set top' := min fm.stackTop (2 ^ 64)
  have ha := a.isLt
  have hlt_iff : a.toNat < top' ↔ a.toNat < fm.stackTop := by omega
  by_cases hle : top' ≤ fm.stackBase
  · simp only [hle, ↓reduceIte, FastMem.cellAt]
    cases rawCellAt fm.lines a.toNat with
    | some c => rfl
    | none =>
      have hnot : ¬ (fm.stackBase ≤ a.toNat ∧ a.toNat < fm.stackTop) := by omega
      simp [hnot]
  · simp only [hle, ↓reduceIte, FastMem.cellAt]
    have hsub : fm.stackBase + (top' - fm.stackBase) = top' := by omega
    have htop_le : fm.stackBase + (top' - fm.stackBase) ≤ 2 ^ 64 := by omega
    rw [rawCellAt_materializeStackLoop fm.lines fm.stackBase (top' - fm.stackBase) htop_le
      a.toNat ha, hsub]
    cases rawCellAt fm.lines a.toNat with
    | some c => rfl
    | none =>
      by_cases hr : fm.stackBase ≤ a.toNat ∧ a.toNat < top'
      · have hr' : fm.stackBase ≤ a.toNat ∧ a.toNat < fm.stackTop := ⟨hr.1, hlt_iff.mp hr.2⟩
        simp [hr, hr']
      · have hr' : ¬ (fm.stackBase ≤ a.toNat ∧ a.toNat < fm.stackTop) :=
          fun h => hr ⟨h.1, hlt_iff.mpr h.2⟩
        simp [hr, hr']

end Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMem.FastMem

set_option autoImplicit false

open Arm64 Arm64.Memory
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

/-- Check that `[addr, addr + n)` is mapped anonymous (`Memory.allAnon`). -/
def allAnon (fm : FastMem) (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 => fm.isAnon addr && fm.allAnon (addr + 1#64) n

theorem allAnon_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    ∀ (n : Nat) (addr : BitVec 64), fm.allAnon addr n = m.allAnon addr n
  | 0, _ => rfl
  | n + 1, addr => by
    simp only [allAnon, Memory.allAnon, fm.isAnon_eq h addr, allAnon_eq h n (addr + 1#64)]

/-- Count bytes in `[addr, addr + n)` whose `perm` satisfies `pred` (`Memory.countPerm`). -/
def countPerm (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => (if pred (fm.perm addr) then 1 else 0) + fm.countPerm pred (addr + 1#64) n

theorem countPerm_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (pred : Option Perm → Bool) :
    ∀ (n : Nat) (addr : BitVec 64), fm.countPerm pred addr n = m.countPerm pred addr n
  | 0, _ => rfl
  | n + 1, addr => by
    simp only [countPerm, Memory.countPerm, fm.perm_eq h addr, countPerm_eq h pred n (addr + 1#64)]

def countRw (fm : FastMem) (addr : BitVec 64) (n : Nat) : Nat :=
  fm.countPerm (· == some Perm.rw) addr n

theorem countRw_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.countRw addr n = m.countRw addr n :=
  fm.countPerm_eq h (· == some Perm.rw) n addr

/-- Delete cell `a` from `fm.lines` when `a` lies outside `[stackBase, stackTop)`. -/
def delCellDisjoint (fm : FastMem) (a : BitVec 64) : FastMem :=
  match fm with
  | ⟨lines, sb, top⟩ =>
    withForcedBinTree (delRawCell lines a.toNat) fun lines' => ⟨lines', sb, top⟩

def unmapLoop (onlyWritable : Bool) (fm : FastMem) (addr : BitVec 64) : Nat → FastMem
  | 0 => fm
  | rem + 1 =>
    let shouldDel :=
      if onlyWritable then (fm.perm addr).w else !(fm.perm addr).frozen
    let fm' := if shouldDel then fm.delCellDisjoint addr else fm
    unmapLoop onlyWritable fm' (addr + 1#64) rem

private theorem unmapLoop_cellAt (onlyWritable : Bool) :
    ∀ (rem : Nat) (fm : FastMem) (base a : BitVec 64),
      rem ≤ 2 ^ 64 →
      (∀ x : BitVec 64, (x - base).toNat < rem → ¬ (fm.stackBase ≤ x.toNat ∧ x.toNat < fm.stackTop)) →
      (unmapLoop onlyWritable fm base rem).cellAt a =
        if (a - base).toNat < rem &&
            (if onlyWritable then (fm.perm a).w else !(fm.perm a).frozen) then
          none
        else
          fm.cellAt a
  | 0, fm, base, a, _, _ => by simp [unmapLoop]
  | rem + 1, fm, base, a, hrem, hdisj => by
    dsimp only [unmapLoop]
    set shouldDel := if onlyWritable then (fm.perm base).w else !(fm.perm base).frozen
    set fm' := if shouldDel then fm.delCellDisjoint base else fm
    have hdisj_base : ¬ (fm.stackBase ≤ base.toNat ∧ base.toNat < fm.stackTop) :=
      hdisj base (by simp)
    have hfm'_same : shouldDel = true → fm'.cellAt base = none := by
      intro hsd
      rcases fm with ⟨lines, sb, top⟩
      dsimp only [fm', delCellDisjoint]
      simp only [hsd, ↓reduceIte, withForcedBinTree_eq]
      dsimp only [cellAt]
      rw [rawCellAt_delRawCell_same lines base.isLt]
      simp [hdisj_base]
    have hfm'_other : ∀ x : BitVec 64, x ≠ base → fm'.cellAt x = fm.cellAt x := by
      intro x hne
      by_cases hsd : shouldDel = true
      · rcases fm with ⟨lines, sb, top⟩
        dsimp only [fm', delCellDisjoint]
        simp only [hsd, ↓reduceIte, withForcedBinTree_eq]
        dsimp only [cellAt]
        have hne_nat : x.toNat ≠ base.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
        rw [rawCellAt_delRawCell_ne lines base.isLt x.isLt hne_nat]
      · simp [fm', hsd]
    have hdisj' : ∀ x : BitVec 64, (x - (base + 1#64)).toNat < rem →
        ¬ (fm'.stackBase ≤ x.toNat ∧ x.toNat < fm'.stackTop) := by
      intro x hx
      have hsb_eq : fm'.stackBase = fm.stackBase ∧ fm'.stackTop = fm.stackTop := by
        rcases fm with ⟨lines, sb, top⟩
        by_cases hsd : shouldDel = true <;> simp [fm', hsd, delCellDisjoint, withForcedBinTree_eq]
      rw [hsb_eq.1, hsb_eq.2]
      apply hdisj x
      by_cases hxb : x = base
      · subst hxb; simp
      · have hstep := toNat_sub_succ_base hxb
        omega
    rw [unmapLoop_cellAt onlyWritable rem fm' (base + 1#64) a (by omega) hdisj']
    by_cases hab : a = base
    · subst hab
      have hnot_rem : ¬ ((a - (a + 1#64)).toNat < rem) := by
        have hsub : a - (a + 1#64) = BitVec.ofNat 64 (2 ^ 64 - 1) := by bv_omega
        rw [hsub]; simp; omega
      have hz : (a - a).toNat < rem + 1 := by simp
      have hlhs : (decide ((a - (a + 1#64)).toNat < rem) &&
          (if onlyWritable then (fm'.perm a).w else !(fm'.perm a).frozen)) = false := by
        simp only [decide_eq_false hnot_rem, Bool.false_and]
      rw [hlhs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change fm'.cellAt a = if decide ((a - a).toNat < rem + 1) && shouldDel then none else fm.cellAt a
      rw [decide_eq_true hz, Bool.true_and]
      by_cases hsd : shouldDel = true
      · simp only [hsd, ↓reduceIte, hfm'_same hsd]
      · simp [fm', hsd]
    · have hc_eq := hfm'_other a hab
      have hp_eq : fm'.perm a = fm.perm a := by simp only [perm, hc_eq]
      rw [hc_eq, hp_eq]
      have hstep := toNat_sub_succ_base hab
      have hiff : ((a - (base + 1#64)).toNat < rem) ↔ ((a - base).toNat < rem + 1) := by omega
      by_cases hlt : (a - (base + 1#64)).toNat < rem
      · simp only [hlt, hiff.mp hlt, decide_true, Bool.true_and]
      · have hlt2 : ¬ ((a - base).toNat < rem + 1) := fun h => hlt (hiff.mpr h)
        simp only [hlt, hlt2, decide_false, Bool.false_and]

/-- Materialize the lazy stack fallback if `[base, base + clen)` can overlap `[stackBase, stackTop)`. -/
def prepareUnmapFastMem (fm : FastMem) (base : BitVec 64) (clen : Nat) : FastMem :=
  if fm.stackTop ≤ fm.stackBase then
    fm
  else if base.toNat + clen ≤ 2 ^ 64 &&
      (base.toNat + clen ≤ fm.stackBase || fm.stackTop ≤ base.toNat) then
    fm
  else
    materializeStackFallback fm

private theorem prepareUnmapFastMem_spec (fm : FastMem) (base : BitVec 64) (clen : Nat) :
    (∀ a : BitVec 64, (prepareUnmapFastMem fm base clen).cellAt a = fm.cellAt a) ∧
    (∀ x : BitVec 64, (x - base).toNat < clen →
      ¬ ((prepareUnmapFastMem fm base clen).stackBase ≤ x.toNat ∧
         x.toNat < (prepareUnmapFastMem fm base clen).stackTop)) := by
  unfold prepareUnmapFastMem
  split
  · exact ⟨fun _ => rfl, fun _ _ h => by omega⟩
  · split
    · rename_i _ h2
      refine ⟨fun _ => rfl, fun x hx hst => ?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
      have hrng := (sub_lt_iff_range h2.1).mp hx
      omega
    · refine ⟨materializeStackFallback_cellAt fm, fun x _ hst => ?_⟩
      unfold materializeStackFallback at hst
      dsimp only at hst
      split at hst <;> simp at hst

/-- Unmap writable bytes in `[base, base + len)` (`Memory.unmapWritable`). -/
def unmapWritable (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  let fm0 := prepareUnmapFastMem fm base clen
  unmapLoop true fm0 base clen

theorem unmapWritable_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (len : Nat) :
    (fm.unmapWritable base len).Agrees (m.unmapWritable base len) := by
  intro a
  dsimp only [unmapWritable, Memory.unmapWritable]
  set clen := min len (2 ^ 64)
  obtain ⟨hcell0, hdisj0⟩ := prepareUnmapFastMem_spec fm base clen
  rw [unmapLoop_cellAt true clen _ base a (Nat.min_le_right _ _) hdisj0]
  have hp0 : (prepareUnmapFastMem fm base clen).perm a = m.perm a := by
    rw [ ← fm.perm_eq h a]; simp only [perm, hcell0 a]
  rw [hp0, hcell0 a, h a]
  have hclen_iff : (a - base).toNat < clen ↔ (a - base).toNat < len := by
    have := (a - base).isLt; omega
  by_cases hl : (a - base).toNat < clen
  · simp only [hl, hclen_iff.mp hl, decide_true, Bool.true_and, ↓reduceIte]
  · have hl2 : ¬ ((a - base).toNat < len) := fun h' => hl (hclen_iff.mpr h')
    simp only [hl, hl2, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Unmap non-frozen bytes in `[base, base + len)` (`Memory.unmapNonFrozen`). -/
def unmapNonFrozen (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  let fm0 := prepareUnmapFastMem fm base clen
  unmapLoop false fm0 base clen

theorem unmapNonFrozen_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (len : Nat) :
    (fm.unmapNonFrozen base len).Agrees (m.unmapNonFrozen base len) := by
  intro a
  dsimp only [unmapNonFrozen, Memory.unmapNonFrozen]
  set clen := min len (2 ^ 64)
  obtain ⟨hcell0, hdisj0⟩ := prepareUnmapFastMem_spec fm base clen
  rw [unmapLoop_cellAt false clen _ base a (Nat.min_le_right _ _) hdisj0]
  have hp0 : (prepareUnmapFastMem fm base clen).perm a = m.perm a := by
    rw [← fm.perm_eq h a]; simp only [perm, hcell0 a]
  rw [hp0, hcell0 a, h a]
  have hclen_iff : (a - base).toNat < clen ↔ (a - base).toNat < len := by
    have := (a - base).isLt; omega
  by_cases hl : (a - base).toNat < clen
  · simp only [hl, hclen_iff.mp hl, decide_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
  · have hl2 : ¬ ((a - base).toNat < len) := fun h' => hl (hclen_iff.mpr h')
    simp only [hl, hl2, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

def setPermLoop (p : Perm) (fm : FastMem) (addr : BitVec 64) : Nat → FastMem
  | 0 => fm
  | rem + 1 =>
    let fm' :=
      if (fm.perm addr).mapped && !(fm.perm addr).frozen then
        fm.setCell addr (some { p with lazyFree := fm.isLazyFree addr, anon := fm.isAnon addr },
          fm.read8 addr)
      else
        fm
    setPermLoop p fm' (addr + 1#64) rem

private theorem setPermLoop_cellAt (p : Perm) :
    ∀ (rem : Nat) (fm : FastMem) (base a : BitVec 64),
      rem ≤ 2 ^ 64 →
      (setPermLoop p fm base rem).cellAt a =
        if (a - base).toNat < rem && (fm.perm a).mapped && !(fm.perm a).frozen then
          some (some { p with lazyFree := fm.isLazyFree a, anon := fm.isAnon a }, fm.read8 a)
        else
          fm.cellAt a
  | 0, fm, base, a, _ => by simp [setPermLoop]
  | rem + 1, fm, base, a, hrem => by
    dsimp only [setPermLoop]
    set cond := ((fm.perm base).mapped && !(fm.perm base).frozen)
    set newC : Cell := (some { p with lazyFree := fm.isLazyFree base, anon := fm.isAnon base },
      fm.read8 base)
    set fm' := if cond then fm.setCell base newC else fm
    have hfm'_other : ∀ x : BitVec 64, x ≠ base → fm'.cellAt x = fm.cellAt x := by
      intro x hne
      by_cases hc : cond = true
      · simp only [fm', hc, ↓reduceIte, cellAt_setCell_ne fm newC hne]
      · simp [fm', hc]
    rw [setPermLoop_cellAt p rem fm' (base + 1#64) a (by omega)]
    by_cases hab : a = base
    · subst hab
      have hnot_rem : ¬ ((a - (a + 1#64)).toNat < rem) := by
        have hsub : a - (a + 1#64) = BitVec.ofNat 64 (2 ^ 64 - 1) := by bv_omega
        rw [hsub]; simp; omega
      have hz : (a - a).toNat < rem + 1 := by simp
      have hlhs : (decide ((a - (a + 1#64)).toNat < rem) && (fm'.perm a).mapped && !(fm'.perm a).frozen) = false := by
        simp only [decide_eq_false hnot_rem, Bool.false_and]
      rw [hlhs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      change fm'.cellAt a = if decide ((a - a).toNat < rem + 1) && (fm.perm a).mapped && !(fm.perm a).frozen then some newC else fm.cellAt a
      rw [decide_eq_true hz, Bool.true_and]
      change fm'.cellAt a = if cond then some newC else fm.cellAt a
      by_cases hc : cond = true
      · simp only [hc, ↓reduceIte, fm', cellAt_setCell_same]
      · simp [hc, fm']
    · have hc_eq := hfm'_other a hab
      have hp_eq : fm'.perm a = fm.perm a := by simp only [perm, hc_eq]
      have hlf_eq : fm'.isLazyFree a = fm.isLazyFree a := by simp only [isLazyFree, hc_eq]
      have han_eq : fm'.isAnon a = fm.isAnon a := by simp only [isAnon, hc_eq]
      have hr_eq : fm'.read8 a = fm.read8 a := by
        rw [read8_eq_of_cellAt, read8_eq_of_cellAt, hc_eq]
      rw [hc_eq, hp_eq, hlf_eq, han_eq, hr_eq]
      have hstep := toNat_sub_succ_base hab
      have hiff : ((a - (base + 1#64)).toNat < rem) ↔ ((a - base).toNat < rem + 1) := by omega
      by_cases hlt : (a - (base + 1#64)).toNat < rem
      · simp only [hlt, hiff.mp hlt, decide_true, Bool.true_and]
      · have hlt2 : ¬ ((a - base).toNat < rem + 1) := fun h => hlt (hiff.mpr h)
        simp only [hlt, hlt2, decide_false, Bool.false_and]

/-- Set permission of non-frozen mapped bytes in `[base, base + len)` to `p` (`Memory.setPermNonFrozen`). -/
def setPermNonFrozen (fm : FastMem) (base : BitVec 64) (len : Nat) (p : Perm) : FastMem :=
  let clen := min len (2 ^ 64)
  setPermLoop p fm base clen

theorem setPermNonFrozen_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (len : Nat) (p : Perm) :
    (fm.setPermNonFrozen base len p).Agrees (m.setPermNonFrozen base len p) := by
  intro a
  dsimp only [setPermNonFrozen, Memory.setPermNonFrozen]
  set clen := min len (2 ^ 64)
  rw [setPermLoop_cellAt p clen fm base a (Nat.min_le_right _ _),
    fm.perm_eq h a, fm.isLazyFree_eq h a, fm.isAnon_eq h a, fm.read8_eq h a, h a]
  have hclen_iff : (a - base).toNat < clen ↔ (a - base).toNat < len := by
    have := (a - base).isLt; omega
  by_cases hl : (a - base).toNat < clen
  · simp only [hl, hclen_iff.mp hl, decide_true, Bool.true_and]
  · have hl2 : ¬ ((a - base).toNat < len) := fun h' => hl (hclen_iff.mpr h')
    simp only [hl, hl2, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Copy and zero-fill loop for `remapRw` from the pre-unmap snapshot `fmSrc` into `fmCur`. -/
def remapWriteLoop (fmSrc : FastMem) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (fmCur : FastMem) (curOff : Nat) : Nat → FastMem
  | 0 => fmCur
  | rem + 1 =>
    let dst := newBase + BitVec.ofNat 64 curOff
    let fmNext :=
      if (fmSrc.perm dst).frozen then
        fmCur
      else
        let src := oldBase + BitVec.ofNat 64 curOff
        let b := if curOff < oldSize then fmSrc.read8 src else 0#8
        let q :=
          if curOff < oldSize then
            { Perm.rw with lazyFree := fmSrc.isLazyFree src, anon := fmSrc.isAnon src }
          else
            Perm.rw
        fmCur.setCell dst (some q, b)
    remapWriteLoop fmSrc oldBase oldSize newBase fmNext (curOff + 1) rem

private theorem remapWriteLoop_cellAt (fmSrc : FastMem) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) :
    ∀ (rem curOff : Nat) (fmCur : FastMem) (a : BitVec 64),
      curOff + rem ≤ 2 ^ 64 →
      (remapWriteLoop fmSrc oldBase oldSize newBase fmCur curOff rem).cellAt a =
        let off := (a - newBase).toNat
        if curOff ≤ off && off < curOff + rem && !(fmSrc.perm a).frozen then
          let src := oldBase + BitVec.ofNat 64 off
          let b := if off < oldSize then fmSrc.read8 src else 0#8
          let q :=
            if off < oldSize then
              { Perm.rw with lazyFree := fmSrc.isLazyFree src, anon := fmSrc.isAnon src }
            else
              Perm.rw
          some (some q, b)
        else
          fmCur.cellAt a
  | 0, curOff, fmCur, a, _ => by
    dsimp only [remapWriteLoop]
    have hfalse : (decide (curOff ≤ (a - newBase).toNat) &&
        decide ((a - newBase).toNat < curOff + 0)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    rw [hfalse]
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | rem + 1, curOff, fmCur, a, hbound => by
    dsimp only [remapWriteLoop]
    set dst := newBase + BitVec.ofNat 64 curOff
    set src0 := oldBase + BitVec.ofNat 64 curOff
    set b0 : BitVec 8 := if curOff < oldSize then fmSrc.read8 src0 else 0#8
    set q0 : Perm :=
      if curOff < oldSize then
        { Perm.rw with lazyFree := fmSrc.isLazyFree src0, anon := fmSrc.isAnon src0 }
      else Perm.rw
    set fmNext := if (fmSrc.perm dst).frozen then fmCur else fmCur.setCell dst (some q0, b0)
    rw [remapWriteLoop_cellAt fmSrc oldBase oldSize newBase rem (curOff + 1) fmNext a (by omega)]
    have hdst_off : (dst - newBase).toNat = curOff := by
      have hsub : dst - newBase = BitVec.ofNat 64 curOff := by dsimp only [dst]; bv_omega
      rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases hadst : a = dst
    · subst hadst
      dsimp only
      rw [hdst_off]
      have h1 : decide (curOff + 1 ≤ curOff) = false := decide_eq_false (by omega)
      have h2 : decide (curOff ≤ curOff) = true := decide_eq_true (Nat.le_refl _)
      have h3 : decide (curOff < curOff + (rem + 1)) = true := decide_eq_true (by omega)
      simp only [h1, h2, h3, Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      by_cases hfrz : (fmSrc.perm dst).frozen = true
      · simp [hfrz, fmNext]
      · simp [hfrz, fmNext, cellAt_setCell_same, src0, b0, q0]
    · have hne_off : (a - newBase).toNat ≠ curOff := by
        intro heq
        apply hadst
        have h1 : a = newBase + (a - newBase) := by bv_omega
        have h2 : a - newBase = BitVec.ofNat 64 curOff := by
          apply BitVec.eq_of_toNat_eq
          rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [h2] at h1
        exact h1
      have hnext_eq : fmNext.cellAt a = fmCur.cellAt a := by
        by_cases hfrz : (fmSrc.perm dst).frozen = true
        · simp [fmNext, hfrz]
        · simp [fmNext, hfrz, cellAt_setCell_ne fmCur _ hadst]
      rw [hnext_eq]
      dsimp only
      have hiff : (curOff + 1 ≤ (a - newBase).toNat ∧ (a - newBase).toNat < curOff + 1 + rem) ↔
          (curOff ≤ (a - newBase).toNat ∧ (a - newBase).toNat < curOff + (rem + 1)) := by omega
      by_cases hr : curOff + 1 ≤ (a - newBase).toNat ∧ (a - newBase).toNat < curOff + 1 + rem
      · have hr2 := hiff.mp hr
        simp only [decide_eq_true hr.1, decide_eq_true hr.2, decide_eq_true hr2.1,
          decide_eq_true hr2.2, Bool.true_and]
      · have hb1 : (decide (curOff + 1 ≤ (a - newBase).toNat) &&
            decide ((a - newBase).toNat < curOff + 1 + rem)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        have hb2 : (decide (curOff ≤ (a - newBase).toNat) &&
            decide ((a - newBase).toNat < curOff + (rem + 1))) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        rw [hb1, hb2]

/-- Relocate/resize `[oldBase, oldBase + oldSize)` to `[newBase, newBase + newSize)` (`Memory.remapRw`). -/
def remapRw (fm : FastMem) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) : FastMem :=
  let fmUnmapped := fm.unmapNonFrozen oldBase oldSize
  let cNewSize := min newSize (2 ^ 64)
  let copyLen := min cNewSize oldSize
  let fmCopied := remapWriteLoop fm oldBase oldSize newBase fmUnmapped 0 copyLen
  if copyLen < cNewSize then
    let zeroBase := newBase + BitVec.ofNat 64 copyLen
    let zeroLen := cNewSize - copyLen
    if !(fm.allPerm (fun p => !p.frozen) zeroBase zeroLen) ||
        !(fmCopied.canMap zeroBase zeroLen) then
      remapWriteLoop fm oldBase oldSize newBase fmCopied copyLen zeroLen
    else
      fmCopied.mapZero zeroBase zeroLen
  else
    fmCopied

theorem remapRw_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (oldBase : BitVec 64) (oldSize : Nat) (newBase : BitVec 64) (newSize : Nat) :
    (fm.remapRw oldBase oldSize newBase newSize).Agrees
      (m.remapRw oldBase oldSize newBase newSize) := by
  intro a
  dsimp only [remapRw]
  set fmUnmapped := fm.unmapNonFrozen oldBase oldSize
  set cNewSize := min newSize (2 ^ 64)
  set copyLen := min cNewSize oldSize
  have hunm := fm.unmapNonFrozen_agrees h oldBase oldSize
  have hfull_eq :
      (let fmCopied := remapWriteLoop fm oldBase oldSize newBase fmUnmapped 0 copyLen
       if copyLen < cNewSize then
         let zeroBase := newBase + BitVec.ofNat 64 copyLen
         let zeroLen := cNewSize - copyLen
         if !(fm.allPerm (fun p => !p.frozen) zeroBase zeroLen) ||
             !(fmCopied.canMap zeroBase zeroLen) then
           remapWriteLoop fm oldBase oldSize newBase fmCopied copyLen zeroLen
         else
           fmCopied.mapZero zeroBase zeroLen
       else
         fmCopied).cellAt a =
      (remapWriteLoop fm oldBase oldSize newBase fmUnmapped 0 cNewSize).cellAt a := by
    dsimp only
    set fmCopied := remapWriteLoop fm oldBase oldSize newBase fmUnmapped 0 copyLen
    have hsplit : ∀ (fm1 : FastMem) (k1 k2 : Nat),
        remapWriteLoop fm oldBase oldSize newBase (remapWriteLoop fm oldBase oldSize newBase fm1 0 k1) k1 k2 =
          remapWriteLoop fm oldBase oldSize newBase fm1 0 (k1 + k2) := by
      intro fm1 k1 k2
      have hgen : ∀ (s1 : Nat) (f0 : FastMem),
          remapWriteLoop fm oldBase oldSize newBase
            (remapWriteLoop fm oldBase oldSize newBase f0 s1 k1) (s1 + k1) k2 =
          remapWriteLoop fm oldBase oldSize newBase f0 s1 (k1 + k2) := by
        induction k1 with
        | zero => intro s1 f0; dsimp only [remapWriteLoop]; simp only [Nat.add_zero, Nat.zero_add]
        | succ n ih =>
          intro s1 f0
          simp only [remapWriteLoop, Nat.succ_add]
          have hadd : s1 + (n + 1) = (s1 + 1) + n := by omega
          rw [hadd]
          exact ih (s1 + 1) _
      simpa using hgen 0 fm1
    by_cases hlt : copyLen < cNewSize
    · simp only [hlt, ↓reduceIte]
      have hsum : copyLen + (cNewSize - copyLen) = cNewSize := by omega
      by_cases hcond : (!(fm.allPerm (fun p => !p.frozen) (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen)) ||
          !(fmCopied.canMap (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen))) = true
      · simp only [hcond, ↓reduceIte]
        rw [hsplit fmUnmapped copyLen (cNewSize - copyLen), hsum]
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        have hfast : fm.allPerm (fun p => !p.frozen) (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen) = true ∧
            fmCopied.canMap (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen) = true := by
          revert hcond
          cases fm.allPerm (fun p => !p.frozen) (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen) <;>
            cases fmCopied.canMap (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen) <;> simp
        let mCopied : Memory := ⟨fmCopied.cellAt⟩
        have hagC : fmCopied.Agrees mCopied := fun _ => rfl
        have hmZero := fmCopied.mapZero_agrees hagC (newBase + BitVec.ofNat 64 copyLen) (cNewSize - copyLen) a
        rw [hmZero, ← hsum, ← hsplit fmUnmapped copyLen (cNewSize - copyLen)]
        rw [remapWriteLoop_cellAt fm oldBase oldSize newBase (cNewSize - copyLen) copyLen fmCopied a
          (by have : cNewSize ≤ 2 ^ 64 := Nat.min_le_right _ _; omega)]
        dsimp only [Memory.mapZero]
        set zeroBase := newBase + BitVec.ofNat 64 copyLen
        set zeroLen := cNewSize - copyLen
        have hoff_iff : ((a - zeroBase).toNat < zeroLen) ↔
            (copyLen ≤ (a - newBase).toNat ∧ (a - newBase).toNat < copyLen + zeroLen) := by
          have hc_lt : copyLen < 2 ^ 64 := by
            have : cNewSize ≤ 2 ^ 64 := Nat.min_le_right _ _; omega
          have hzb : a - zeroBase = (a - newBase) - BitVec.ofNat 64 copyLen := by
            simp only [zeroBase]; bv_omega
          rw [hzb, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc_lt]
          have han := (a - newBase).isLt
          have hcz : copyLen + zeroLen ≤ 2 ^ 64 := by
            have : cNewSize ≤ 2 ^ 64 := Nat.min_le_right _ _; omega
          omega
        by_cases hzr : (a - zeroBase).toNat < zeroLen
        · have hrng := hoff_iff.mp hzr
          have hmSrc : fm.Agrees ⟨fm.cellAt⟩ := fun _ => rfl
          have hall1 := fm.allPerm_eq hmSrc (fun p => !p.frozen) zeroBase zeroLen
          rw [hfast.1] at hall1
          have hstep_allPerm : ∀ (m0 : Memory) (pred : Option Perm → Bool) (b : BitVec 64) (n k : Nat),
              k < n → m0.allPerm pred b n = true → pred (m0.perm (b + BitVec.ofNat 64 k)) = true := by
            intro m0 pred b n
            induction n generalizing b with
            | zero => intro k hk; omega
            | succ n' ih =>
              intro k hk hall
              simp only [Memory.allPerm, Bool.and_eq_true] at hall
              cases k with
              | zero => simpa using hall.1
              | succ j =>
                have hj := ih (b + 1#64) j (by omega) hall.2
                have hb_add : b + 1#64 + BitVec.ofNat 64 j = b + BitVec.ofNat 64 (j + 1) := by bv_omega
                rwa [hb_add] at hj
          have ha_eq : zeroBase + BitVec.ofNat 64 (a - zeroBase).toNat = a := by
            rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
          have hnfrz : (!(fm.perm a).frozen) = true := by
            have h1 := hstep_allPerm ⟨fm.cellAt⟩ (fun p => !p.frozen) zeroBase zeroLen
              (a - zeroBase).toNat hzr hall1.symm
            rwa [ha_eq, ← fm.perm_eq hmSrc a] at h1
          have hunmapC : (!(mCopied.perm a).mapped) = true := by
            have hcan := fmCopied.canMap_eq hagC zeroBase zeroLen
            rw [hfast.2] at hcan
            have h1 := hstep_allPerm mCopied (fun p => !p.mapped) zeroBase zeroLen
              (a - zeroBase).toNat hzr hcan.symm
            rwa [ha_eq] at h1
          have hge_old : ¬ ((a - newBase).toNat < oldSize) := by
            have : copyLen = oldSize := by
              dsimp only [copyLen] at hlt ⊢; omega
            omega
          simp only [mCopied, Nat.add_sub_cancel_left, decide_eq_true hzr, hunmapC, decide_eq_true hrng.1, decide_eq_true hrng.2,
            hnfrz, Bool.true_and, ↓reduceIte, hge_old]
        · have hrng_b : (decide (copyLen ≤ (a - newBase).toNat) &&
              decide ((a - newBase).toNat < copyLen + zeroLen)) = false := by
            have hrng : ¬ (copyLen ≤ (a - newBase).toNat ∧ (a - newBase).toNat < copyLen + zeroLen) :=
              fun h => hzr (hoff_iff.mpr h)
            simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
          rw [hrng_b]
          simp only [mCopied, Nat.add_sub_cancel_left, decide_eq_false hzr, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have heq_len : copyLen = cNewSize := by
        have : copyLen ≤ cNewSize := Nat.min_le_left _ _; omega
      simp only [hlt, ↓reduceIte]
      simp only [fmCopied, heq_len]
  rw [hfull_eq, remapWriteLoop_cellAt fm oldBase oldSize newBase cNewSize 0 fmUnmapped a
    (by dsimp only [cNewSize]; have := Nat.min_le_right newSize (2 ^ 64); omega)]
  dsimp only [Memory.remapRw]
  rw [fm.perm_eq h a, hunm a]
  have hc_iff : (a - newBase).toNat < cNewSize ↔ (a - newBase).toNat < newSize := by
    have := (a - newBase).isLt; omega
  by_cases hfrz : (m.perm a).frozen = true
  · simp [hfrz, Memory.unmapNonFrozen]
  · simp only [Bool.not_eq_true] at hfrz
    simp only [hfrz, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.and_true, Nat.zero_le,
      decide_true, Bool.true_and, Nat.zero_add]
    by_cases hnew : (a - newBase).toNat < cNewSize
    · simp only [hnew, hc_iff.mp hnew, decide_true, ↓reduceIte]
      set src := oldBase + BitVec.ofNat 64 (a - newBase).toNat
      rw [fm.read8_eq h src, fm.isLazyFree_eq h src, fm.isAnon_eq h src]
    · have hnew2 : ¬ ((a - newBase).toNat < newSize) := fun h' => hnew (hc_iff.mpr h')
      simp only [hnew, hnew2, decide_false, Bool.false_eq_true, ↓reduceIte, Memory.unmapNonFrozen,
        hfrz, Bool.not_false, Bool.and_true]
      simp

end Symbolic.BugInjection.Proofs.CliExec.RadixMem.FastMem

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced

set_option autoImplicit false

open Arm64 Arm64.Memory
open Arm64.Process (ElfImage ProcessInputs buildInitialStack)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine

def findMappedByteFast (fm : FastMem) (base : BitVec 64) (curOff : Nat) : Nat → Option Nat
  | 0 => none
  | rem + 1 =>
    if (fm.perm (base + BitVec.ofNat 64 curOff)).mapped then some curOff
    else findMappedByteFast fm base (curOff + 1) rem

theorem findMappedByteFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    ∀ (rem : Nat) (base : BitVec 64) (curOff : Nat),
      findMappedByteFast fm base curOff rem = findMappedByte m base curOff rem
  | 0, _, _ => rfl
  | rem + 1, base, curOff => by
    simp only [findMappedByteFast, findMappedByte, fm.perm_eq h,
      findMappedByteFast_eq h rem base (curOff + 1)]

def findUnmappedAreaLoopFast (fm : FastMem) (size : Nat) : Nat → Nat → Option (BitVec 64)
  | 0, _ => none
  | fuel + 1, addr =>
    if !decide (addr + size ≤ USER_VA_LIMIT) then
      none
    else
      let base := BitVec.ofNat 64 addr
      match findMappedByteFast fm base 0 size with
      | none => some base
      | some off =>
        let nextPage := ((addr + off) / PAGE_SIZE + 1) * PAGE_SIZE
        findUnmappedAreaLoopFast fm size fuel nextPage

theorem findUnmappedAreaLoopFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (size : Nat) :
    ∀ (fuel addr : Nat),
      findUnmappedAreaLoopFast fm size fuel addr = findUnmappedAreaLoop m size fuel addr
  | 0, _ => rfl
  | fuel + 1, addr => by
    simp only [findUnmappedAreaLoopFast, findUnmappedAreaLoop, findMappedByteFast_eq h]
    split
    · rfl
    · cases findMappedByte m (BitVec.ofNat 64 addr) 0 size with
      | none => rfl
      | some off => exact findUnmappedAreaLoopFast_eq h size fuel _

def findUnmappedAreaFast (fm : FastMem) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else
    findUnmappedAreaLoopFast fm size ((USER_VA_LIMIT - MMAP_MIN_ADDR) / PAGE_SIZE + 1) MMAP_MIN_ADDR

theorem findUnmappedAreaFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (size : Nat) :
    findUnmappedAreaFast fm size = findUnmappedArea m size := by
  simp only [findUnmappedAreaFast, findUnmappedArea, findUnmappedAreaLoopFast_eq h]

def sanitizeMmapAddrFast (fm : FastMem) (cand : BitVec 64) (size : Nat) : Option (BitVec 64) :=
  if size == 0 || size % PAGE_SIZE != 0 then
    none
  else if decide (MMAP_MIN_ADDR ≤ cand.toNat) && cand.toNat % PAGE_SIZE == 0 &&
      decide (cand.toNat + size ≤ USER_VA_LIMIT) && fm.canMap cand size then
    some cand
  else
    findUnmappedAreaFast fm size

theorem sanitizeMmapAddrFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (cand : BitVec 64) (size : Nat) :
    sanitizeMmapAddrFast fm cand size = sanitizeMmapAddr m cand size := by
  simp only [sanitizeMmapAddrFast, sanitizeMmapAddr, fm.canMap_eq h, findUnmappedAreaFast_eq h]

def readCStringAuxFast (fm : FastMem) (ptr : BitVec 64) : Nat → List Char → FsResolve String
  | 0, _ => .errno ENAMETOOLONG
  | fuel + 1, acc =>
    if !(fm.perm ptr).r then .errno 14#64
    else if !fm.canRead ptr 1 then .trap "openat path in lazy-free memory"
    else
      let b := fm.read8 ptr
      if b == 0#8 then .ok (String.ofList acc.reverse)
      else readCStringAuxFast fm (ptr + 1#64) fuel (Char.ofNat b.toNat :: acc)

theorem readCStringAuxFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    ∀ (fuel : Nat) (ptr : BitVec 64) (acc : List Char),
      readCStringAuxFast fm ptr fuel acc = readCStringAux m ptr fuel acc
  | 0, _, _ => rfl
  | fuel + 1, ptr, acc => by
    simp only [readCStringAuxFast, readCStringAux, fm.perm_eq h ptr, fm.canRead_eq h ptr 1,
      fm.read8_eq h ptr, readCStringAuxFast_eq h fuel (ptr + 1#64)]

def readCStringFast (fm : FastMem) (ptr : BitVec 64) : FsResolve String :=
  readCStringAuxFast fm ptr PATH_MAX []

theorem readCStringFast_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (ptr : BitVec 64) :
    readCStringFast fm ptr = readCString m ptr :=
  readCStringAuxFast_eq h PATH_MAX ptr []

/-- Zero the 1-byte `STORAGE.0` flag at `tokStorageAddr` and the 4-byte `TOKEN.state` word at
`tokOnceAddr + 8`, as in `CliBinaryPq.Placed.cliTokenPatchPlaced`. -/
def patchTokenFastMemPlaced (tokStorageAddr tokOnceAddr : BitVec 64) (fm0 : FastMem) : FastMem :=
  (fm0.writeBytes tokStorageAddr [0#8]).writeBytes (tokOnceAddr + 8#64) [0#8, 0#8, 0#8, 0#8]

def patchTokenLinesPlaced (tokStorageAddr tokOnceAddr : BitVec 64) (lines : BinTree Line64) :
    BinTree Line64 :=
  (patchTokenFastMemPlaced tokStorageAddr tokOnceAddr
    { lines := lines, stackBase := 0, stackTop := 0 }).lines

/-- Initial `(sp, FastMem)` for `elf` and `pinputs` with `patchTokenFastMemPlaced` applied, or `none` on address wrap. -/
def initFastMemAndSpPlaced (tokStorageAddr tokOnceAddr : BitVec 64)
    (elf : ElfImage) (pinputs : ProcessInputs) : Option (BitVec 64 × FastMem) :=
  match buildInitialStack elf pinputs with
  | .error _ => none
  | .ok (sp, stackRegion) =>
    let regions := elf.segments ++ [stackRegion]
    let top := pinputs.init.stackTop.toNat
    let sz := pinputs.init.stackSize
    if sz ≤ top && top ≤ 2 ^ 64 &&
        regions.all (fun r => decide (r.start.toNat + r.bytes.length ≤ 2 ^ 64)) then
      let fm0 : FastMem := { lines := loadRegionsLines regions, stackBase := top - sz, stackTop := top }
      let fm1 := patchTokenFastMemPlaced tokStorageAddr tokOnceAddr fm0
      some (sp, fm1)
    else
      none

theorem initFastMemAndSpPlaced_agrees {tokStorageAddr tokOnceAddr : BitVec 64}
    {elf : ElfImage} {pinputs : ProcessInputs} {sp : BitVec 64} {fm : FastMem}
    (hinit : initFastMemAndSpPlaced tokStorageAddr tokOnceAddr elf pinputs = some (sp, fm)) :
    (elf.rawState pinputs).sp = sp ∧
      fm.Agrees (((elf.rawState pinputs).mem.writeBytes tokStorageAddr [0#8]).writeBytes
        (tokOnceAddr + 8#64) [0#8, 0#8, 0#8, 0#8]) := by
  unfold initFastMemAndSpPlaced at hinit
  generalize hstk : buildInitialStack elf pinputs = stkRes at hinit
  cases stkRes with
  | error _ => nomatch hinit
  | ok pair =>
    rcases pair with ⟨sp0, stackRegion⟩; dsimp only at hinit
    split at hinit
    · rename_i hcond; injection hinit with hinit; rcases Prod.mk.inj hinit with ⟨rfl, rfl⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      rcases hcond with ⟨⟨hsz_le, htop_le⟩, hreg_wrap⟩
      have hsp : (elf.rawState pinputs).sp = sp0 := by simp [ElfImage.rawState, hstk]
      have hmem : (elf.rawState pinputs).mem =
          Memory.mapZero ⟨Snapshot.loadCellAt (elf.segments ++ [stackRegion])⟩
            (BitVec.ofNat 64 (pinputs.init.stackTop.toNat - pinputs.init.stackSize))
            pinputs.init.stackSize := by
        simp [ElfImage.rawState, hstk]
      refine ⟨hsp, ?_⟩
      rw [hmem]
      unfold patchTokenFastMemPlaced
      apply FastMem.writeBytes_agrees; apply FastMem.writeBytes_agrees
      intro a; dsimp only [FastMem.cellAt]
      exact baseRegions_mapZero_cells_eq (elf.segments ++ [stackRegion])
        pinputs.init.stackTop.toNat pinputs.init.stackSize hsz_le htop_le
        hreg_wrap a
    · nomatch hinit

end Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
