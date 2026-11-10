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
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine

/-!
# Sparse 64-Bit Radix-Tree Memory

Defines `FastMem`, a closure-free representation of the 64-bit address space as a depth-58
`BinTree` of 64-byte (`Line64`) cache lines with a lazy zero-mapped `Perm.rw` stack fallback on
`[stackBase, stackTop)`. Provides single-byte, little-endian multi-byte, bulk read/write, range
mapping (`mapFresh`, `mapZero`), and range permission operations proved extensionally equal to
`Arm64.Memory`, and re-exports the core primitives from `RadixMemAux` and `RadixMemLine`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.RadixMem

open Arm64

export Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (
  withForcedNat withForcedNat_eq
  withForcedBool withForcedBool_eq
  withForcedBV withForcedBV_eq
  withForcedPerm withForcedPerm_eq
  withForcedPermOpt withForcedPermOpt_eq
  withForcedPState withForcedPState_eq canonPState canonPState_eq
  Cell withForcedCell withForcedCell_eq
  withForcedExecStatus withForcedExecStatus_eq
  withForcedListSpine withForcedListSpine_eq
  withForcedIvList withForcedIvList_eq
  BinTree withForcedBinTree withForcedBinTree_eq btGet btSet btGet_empty btGet_twig
  btGet_btSet_same' btGet_btSet_same btGet_btSet_ne btGet_btSet_btSet_same_key
  FastRegs withForcedFastRegs withForcedFastRegs_eq
  Line64 btSet6Cell btSet6Cell_eq btSet58Line btSet58Line_eq
  lineByteCanRead lineByteCanWrite lineCanReadAux lineCanWriteAux lineCellWritePerm writeLineByte
  rawCellAt setRawCell div64_lt_2pow58 mod64_lt_2pow6
  rawCellAt_setRawCell_same rawCellAt_setRawCell_ne
  foldSetRawCell flushAndSetCells setCellsAt
  LinesEq linesEq_setRawCell linesEq_foldSetRawCell
  linesEq_flushAndSetCells linesEq_setCellsAt
  rawCellAt_foldSetRawCell_noWrap sub_lt_iff_range
  toNat_sub_succ_base memory_writeBytes_cells_noWrap
  regionToCells regionToCells_length regionToCells_getElem
  loadRegionFast linesEq_loadRegionFast
)

/-- Sparse 64-bit memory: a depth-58 `BinTree` of 64-byte cache lines with an untouched
zero-mapped `Perm.rw` fallback on `[stackBase, stackTop)`. -/
structure FastMem where
  lines     : BinTree Line64 := .empty
  stackBase : Nat := 0
  stackTop  : Nat := 0
  deriving DecidableEq, Repr, Inhabited

@[inline] def withForcedFastMem {α : Type} (fm : FastMem) (k : FastMem → α) : α :=
  match fm with
  | ⟨lines, sb, top⟩ => k ⟨lines, sb, top⟩

@[simp] theorem withForcedFastMem_eq {α : Type} (fm : FastMem) (k : FastMem → α) :
    withForcedFastMem fm k = k fm := by cases fm; rfl

namespace FastMem

private theorem cachedLine_eq (lines : BinTree Line64) (hi curHi : Nat) (curLine : Option Line64)
    (hcur : curLine = btGet 58 lines curHi) :
    (if hi == curHi then curLine else btGet 58 lines hi) = btGet 58 lines hi := by
  split
  · rename_i heq; rw [hcur, beq_iff_eq.mp heq]
  · rfl

/-- Byte cell at `a`, with `(some Perm.rw, 0#8)` fallback on `[stackBase, stackTop)`. -/
def cellAt (fm : FastMem) (a : BitVec 64) : Option Cell :=
  let addr := a.toNat
  match rawCellAt fm.lines addr with
  | some c => some c
  | none => if fm.stackBase ≤ addr && addr < fm.stackTop then some (some Perm.rw, 0#8) else none

/-- Extensional agreement with `Arm64.Memory`. -/
def Agrees (fm : FastMem) (m : Memory) : Prop := ∀ a : BitVec 64, fm.cellAt a = m.cells a

def setCell (fm : FastMem) (a : BitVec 64) (c : Cell) : FastMem :=
  match fm with
  | ⟨lines, sb, top⟩ => withForcedBinTree (setRawCell lines a.toNat c) fun lines' => ⟨lines', sb, top⟩

theorem cellAt_setCell_same (fm : FastMem) (a : BitVec 64) (c : Cell) :
    (fm.setCell a c).cellAt a = some c := by
  rcases fm with ⟨lines, sb, top⟩
  simp only [setCell, withForcedBinTree_eq, cellAt, rawCellAt_setRawCell_same]

theorem cellAt_setCell_ne (fm : FastMem) {a a' : BitVec 64} (c : Cell) (hne : a' ≠ a) :
    (fm.setCell a c).cellAt a' = fm.cellAt a' := by
  rcases fm with ⟨lines, sb, top⟩
  have hne' : a'.toNat ≠ a.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  dsimp only [setCell]; rw [withForcedBinTree_eq]; dsimp only [cellAt]
  rw [rawCellAt_setRawCell_ne lines c a.isLt a'.isLt hne']

def rawPerm (fm : FastMem) (addr : BitVec 64) : Option Perm :=
  match fm.cellAt addr with
  | some (p, _) => p
  | none => none

/-- Normalized 3-bit protection (`p.rwx`) at `addr` without `lazyFree` or `anon`. -/
def perm (fm : FastMem) (addr : BitVec 64) : Option Perm :=
  match fm.cellAt addr with
  | some (some (p : Perm), _) => some p.rwx
  | _ => none

def isLazyFree (fm : FastMem) (addr : BitVec 64) : Bool :=
  match fm.cellAt addr with
  | some (some (p : Perm), _) => p.lazyFree
  | _ => false

def isAnon (fm : FastMem) (addr : BitVec 64) : Bool :=
  match fm.cellAt addr with
  | some (some (p : Perm), _) => p.anon
  | _ => false

def permNoLazy (fm : FastMem) (addr : BitVec 64) : Option Perm :=
  match fm.cellAt addr with
  | some (some (p : Perm), _) => some { r := p.r, w := p.w, x := p.x, lazyFree := p.lazyFree }
  | _ => none

/-- Read one byte at `addr` (`0#8` if unmapped or in the untouched zero stack). -/
def read8 (fm : FastMem) (addr : BitVec 64) : BitVec 8 :=
  match rawCellAt fm.lines addr.toNat with
  | some (_, b) => b
  | none => 0#8

theorem read8_eq_of_cellAt (fm : FastMem) (a : BitVec 64) :
    fm.read8 a = match fm.cellAt a with | some (_, b) => b | none => 0#8 := by
  dsimp only [read8, cellAt]
  cases rawCellAt fm.lines a.toNat with
  | some cb => rfl
  | none =>
    by_cases hs : (decide (fm.stackBase ≤ a.toNat) && decide (a.toNat < fm.stackTop)) = true
    · simp only [hs, ↓reduceIte]
    · simp only [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, ↓reduceIte]

theorem rawPerm_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.rawPerm a = m.rawPerm a := by
  rw [rawPerm, Memory.rawPerm, h a]
  rcases m.cells a with _ | ⟨_, _⟩ <;> rfl

theorem perm_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.perm a = m.perm a := by
  rw [perm, Memory.perm, h a]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

theorem isLazyFree_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.isLazyFree a = m.isLazyFree a := by
  rw [isLazyFree, Memory.isLazyFree, h a]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

theorem isAnon_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.isAnon a = m.isAnon a := by
  rw [isAnon, Memory.isAnon, h a]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

theorem permNoLazy_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.permNoLazy a = m.permNoLazy a := by
  rw [permNoLazy, Memory.permNoLazy, h a]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

theorem read8_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read8 a = m.read8 a := by
  rw [read8_eq_of_cellAt, Memory.read8, h a]
  rcases m.cells a with _ | ⟨_, _⟩ <;> rfl

@[inline] def mkFastMem (lines : BinTree Line64) (sb top : Nat) : FastMem :=
  match lines with
  | .empty => ⟨.empty, sb, top⟩
  | .twig j u => ⟨.twig j u, sb, top⟩
  | .branch x y => ⟨.branch x y, sb, top⟩

@[simp] theorem mkFastMem_eq (lines : BinTree Line64) (sb top : Nat) :
    mkFastMem lines sb top = ⟨lines, sb, top⟩ := by cases lines <;> rfl

private theorem ble_eq_decide (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.ble_eq]

private theorem blt_eq_decide (a b : Nat) : Nat.blt a b = decide (a < b) := by
  apply Bool.eq_iff_iff.mpr; simp [Nat.blt_eq]

private theorem lineCellWritePerm_eq (fm : FastMem) (addr : BitVec 64) :
    lineCellWritePerm fm.stackBase fm.stackTop addr.toNat
      ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat % 64) =
      match fm.rawPerm addr with | some p => some { p with lazyFree := false } | none => none := by
  simp only [lineCellWritePerm, rawPerm, cellAt, rawCellAt, ble_eq_decide, blt_eq_decide]
  cases h58 : btGet 58 fm.lines (addr.toNat / 64) with
  | none =>
    simp only [Option.getD_none, btGet_empty]
    cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
  | some ln =>
    simp only [Option.getD_some]
    cases h6 : btGet 6 ln (addr.toNat % 64) with
    | none => cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
    | some c => rcases c with ⟨_ | ⟨r, w, x, _ | _, an⟩, b⟩ <;> rfl

/-- Write `val` at `addr` and clear `lazyFree` on mapped bytes. -/
def write8 (fm : FastMem) (addr : BitVec 64) (val : BitVec 8) : FastMem :=
  match fm with
  | ⟨lines, sb, top⟩ =>
    let a := addr.toNat
    let hi := Nat.div a 64
    let ln0 := (btGet 58 lines hi).getD .empty
    mkFastMem (btSet58Line lines hi (writeLineByte sb top a ln0 (Nat.mod a 64) val)) sb top

def write8? (fm : FastMem) (addr : BitVec 64) (val : BitVec 8) : Option FastMem :=
  some (fm.write8 addr val)

theorem write8_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (addr : BitVec 64) (val : BitVec 8) :
    (fm.write8 addr val).Agrees (m.write8 addr val) := by
  have heq_sc : fm.write8 addr val =
      fm.setCell addr (match fm.rawPerm addr with | some p => some { p with lazyFree := false } | none => none, val) := by
    rcases fm with ⟨lines, sb, top⟩
    have hd : Nat.div addr.toNat 64 = addr.toNat / 64 := rfl
    have hm : Nat.mod addr.toNat 64 = addr.toNat % 64 := rfl
    simp only [write8, mkFastMem_eq, btSet58Line_eq, writeLineByte, btSet6Cell_eq, hd, hm,
      lineCellWritePerm_eq ⟨lines, sb, top⟩ addr, setCell, setRawCell, withForcedCell_eq, withForcedBinTree_eq]
  intro a
  rw [heq_sc, Memory.write8, rawPerm_eq h addr]
  by_cases heq : a = addr
  · subst heq; simp only [↓reduceIte, cellAt_setCell_same]; rcases m.rawPerm a with _ | _ <;> rfl
  · simp only [heq, ↓reduceIte]; rw [cellAt_setCell_ne _ _ heq, h a]

private theorem writeLineByte_step_agrees {lines : BinTree Line64} {sb top : Nat} {m : Memory}
    {addr : BitVec 64} {k : Nat} (hk : addr.toNat % 64 + k < 64) (ln : Line64) (b : BitVec 8)
    (h : (⟨btSet 58 lines (addr.toNat / 64) ln, sb, top⟩ : FastMem).Agrees m) :
    (⟨btSet 58 lines (addr.toNat / 64)
      (writeLineByte sb top (addr.toNat + k) ln (addr.toNat % 64 + k) b), sb, top⟩ : FastMem).Agrees
      (m.write8 (addr + BitVec.ofNat 64 k) b) := by
  have ha := addr.isLt
  set ak := addr + BitVec.ofNat 64 k
  have htoNat : ak.toNat = addr.toNat + k := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hdiv : Nat.div (addr.toNat + k) 64 = addr.toNat / 64 := by change (addr.toNat + k) / 64 = _; omega
  have hrem : Nat.mod (addr.toNat + k) 64 = addr.toNat % 64 + k := by change (addr.toNat + k) % 64 = _; omega
  have hw := write8_agrees h ak b
  simp only [write8, mkFastMem_eq, btSet58Line_eq, htoNat, hdiv, hrem, btGet_btSet_same',
    Option.getD_some] at hw
  intro x
  rw [← hw x]
  dsimp only [cellAt, rawCellAt]
  rw [btGet_btSet_btSet_same_key 58 (addr.toNat / 64) (x.toNat / 64) lines ln _
    (div64_lt_2pow58 ha) (div64_lt_2pow58 x.isLt)]

@[inline] def withForcedLineOpt {α : Type} (ln : Option Line64) (k : Option Line64 → α) : α :=
  match ln with | none => k none | some t => withForcedBinTree t fun t' => k (some t')

@[simp] theorem withForcedLineOpt_eq {α : Type} (ln : Option Line64) (k : Option Line64 → α) :
    withForcedLineOpt ln k = k ln := by cases ln <;> simp [withForcedLineOpt]

def readBytesCached (fm : FastMem) (curHi : Nat) (curLine : Option Line64)
    (base : BitVec 64) : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 =>
    let addr := base.toNat
    let hi := addr / 64
    let lo := addr % 64
    withForcedLineOpt (if hi == curHi then curLine else btGet 58 fm.lines hi) fun lineOpt =>
      let b := match lineOpt with
        | some line => match btGet 6 line lo with | some (_, byte) => byte | none => 0#8
        | none => 0#8
      withForcedBV (base + 1#64) fun base' => b :: readBytesCached fm hi lineOpt base' n

def readBytes (fm : FastMem) (base : BitVec 64) (count : Nat) : List (BitVec 8) :=
  match count with
  | 0 => []
  | _ + 1 =>
    let hi := base.toNat / 64
    withForcedLineOpt (btGet 58 fm.lines hi) fun ln => readBytesCached fm hi ln base count

private theorem readBytesCached_eq (fm : FastMem) {m : Memory} (h : fm.Agrees m) :
    ∀ (n : Nat) (base : BitVec 64) (curHi : Nat) (curLine : Option Line64),
      curLine = btGet 58 fm.lines curHi →
      readBytesCached fm curHi curLine base n = m.readBytes base n
  | 0, _, _, _, _ => rfl
  | n + 1, base, curHi, curLine, hcur => by
    simp only [readBytesCached, withForcedLineOpt_eq, withForcedBV_eq, Memory.readBytes]
    rw [cachedLine_eq fm.lines (base.toNat / 64) curHi curLine hcur]
    have hb : (match btGet 58 fm.lines (base.toNat / 64) with
        | some line => match btGet 6 line (base.toNat % 64) with | some (_, byte) => byte | none => 0#8
        | none => 0#8) = m.read8 base := by
      rw [← read8_eq h base]
      simp only [read8, rawCellAt]
      cases btGet 58 fm.lines (base.toNat / 64) <;> rfl
    rw [hb, readBytesCached_eq fm h n (base + 1#64) (base.toNat / 64) _ rfl]

theorem readBytes_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (base : BitVec 64) (n : Nat) :
    fm.readBytes base n = m.readBytes base n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [readBytes, withForcedLineOpt_eq]
    exact readBytesCached_eq fm h (n + 1) base (base.toNat / 64) _ rfl

def cellAtWithLine (fm : FastMem) (addr : Nat) (lineOpt : Option Line64) : Option Cell :=
  match lineOpt with
  | some line =>
    match btGet 6 line (addr % 64) with
    | some c => some c
    | none =>
      if fm.stackBase ≤ addr && addr < fm.stackTop then some (some Perm.rw, 0#8) else none
  | none =>
    if fm.stackBase ≤ addr && addr < fm.stackTop then some (some Perm.rw, 0#8) else none

theorem cellAtWithLine_eq (fm : FastMem) (a : BitVec 64) :
    cellAtWithLine fm a.toNat (btGet 58 fm.lines (a.toNat / 64)) = fm.cellAt a := by
  simp only [cellAtWithLine, cellAt, rawCellAt]
  cases btGet 58 fm.lines (a.toNat / 64) <;> rfl

/-- Build updated cells for `writeBytes` in one cached-line pass when `addr + bs.length ≤ 2 ^ 64`. -/
def buildWriteCells (fm : FastMem) (curHi : Nat) (curLine : Option Line64)
    (addr : Nat) : List (BitVec 8) → List Cell
  | [] => []
  | b :: bs =>
    let hi := addr / 64
    withForcedLineOpt (if hi == curHi then curLine else btGet 58 fm.lines hi) fun lineOpt =>
      let p' := match cellAtWithLine fm addr lineOpt with
        | some (some (p : Perm), _) => some { p with lazyFree := false }
        | _ => none
      withForcedNat (addr + 1) fun addr' => (p', b) :: buildWriteCells fm hi lineOpt addr' bs

private theorem buildWriteCells_length (fm : FastMem) :
    ∀ (bs : List (BitVec 8)) (curHi : Nat) (curLine : Option Line64) (addr : Nat),
      (buildWriteCells fm curHi curLine addr bs).length = bs.length
  | [], _, _, _ => rfl
  | _ :: bs, curHi, curLine, addr => by
    simp only [buildWriteCells, withForcedLineOpt_eq, withForcedNat_eq, List.length_cons,
      buildWriteCells_length fm bs]

private theorem buildWriteCells_getElem (fm : FastMem) :
    ∀ (bs : List (BitVec 8)) (curHi : Nat) (curLine : Option Line64) (addr : Nat),
      curLine = btGet 58 fm.lines curHi →
      addr + bs.length ≤ 2 ^ 64 →
      ∀ (i : Nat) (hi : i < bs.length),
        (buildWriteCells fm curHi curLine addr bs)[i]'(by rw [buildWriteCells_length]; exact hi) =
          (match fm.rawPerm (BitVec.ofNat 64 (addr + i)) with
           | some p => some { p with lazyFree := false }
           | none => none, bs[i]'hi)
  | [], _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | b :: bs, curHi, curLine, addr, hcur, hwrap, i, hi => by
    simp only [List.length_cons] at hwrap hi
    cases i with
    | zero =>
      simp only [buildWriteCells, withForcedLineOpt_eq, withForcedNat_eq, List.getElem_cons_zero, Nat.add_zero]
      rw [cachedLine_eq fm.lines (addr / 64) curHi curLine hcur]
      have hadr : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt (by omega)
      have hc := cellAtWithLine_eq fm (BitVec.ofNat 64 addr)
      rw [hadr] at hc
      rw [hc, rawPerm]
      rcases fm.cellAt (BitVec.ofNat 64 addr) with _ | ⟨_ | p, _⟩ <;> rfl
    | succ j =>
      have hj : j < bs.length := by omega
      have hline := cachedLine_eq fm.lines (addr / 64) curHi curLine hcur
      have hrec := buildWriteCells_getElem fm bs (addr / 64)
        (if addr / 64 == curHi then curLine else btGet 58 fm.lines (addr / 64))
        (addr + 1) hline (by omega) j hj
      have hadd : addr + 1 + j = addr + (j + 1) := by omega
      simp only [buildWriteCells, withForcedLineOpt_eq, withForcedNat_eq, List.getElem_cons_succ]
      simpa only [hadd] using hrec

/-- Byte-by-byte fallback for wrap-around writes (`base.toNat + bs.length > 2 ^ 64`). -/
def writeBytesSlow (fm : FastMem) (base : BitVec 64) : List (BitVec 8) → FastMem
  | [] => fm
  | b :: rest => (fm.write8 base b).writeBytesSlow (base + 1#64) rest

theorem writeBytesSlow_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (bs : List (BitVec 8)) :
    (fm.writeBytesSlow base bs).Agrees (m.writeBytes base bs) := by
  induction bs generalizing fm m base with
  | nil => exact h
  | cons b rest ih => exact ih (write8_agrees h base b) (base + 1#64)

/-- Write `bs` at `base`, batched by 64-byte cache line when `base.toNat + bs.length ≤ 2 ^ 64`. -/
def writeBytes (fm : FastMem) (base : BitVec 64) (bs : List (BitVec 8)) : FastMem :=
  match bs with
  | [] => fm
  | _ :: _ =>
    if base.toNat + bs.length ≤ 2 ^ 64 then
      match fm with
      | ⟨lines, sb, top⟩ =>
        let hi := base.toNat / 64
        withForcedLineOpt (btGet 58 lines hi) fun ln =>
          let cs := buildWriteCells ⟨lines, sb, top⟩ hi ln base.toNat bs
          withForcedBinTree (setCellsAt lines base.toNat cs) fun lines' =>
            ⟨lines', sb, top⟩
    else
      fm.writeBytesSlow base bs

theorem writeBytes_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (bs : List (BitVec 8)) :
    (fm.writeBytes base bs).Agrees (m.writeBytes base bs) := by
  cases bs with
  | nil => exact h
  | cons b rest =>
    simp only [writeBytes]; split
    · rename_i hwrap; rcases fm with ⟨lines, sb, top⟩
      simp only [withForcedLineOpt_eq, withForcedBinTree_eq]; intro a
      rw [memory_writeBytes_cells_noWrap m base (b :: rest) hwrap a]
      set cs := buildWriteCells ⟨lines, sb, top⟩ (base.toNat / 64) (btGet 58 lines (base.toNat / 64)) base.toNat (b :: rest)
      have hlen : cs.length = (b :: rest).length := buildWriteCells_length _ _ _ _ _
      have hraw : rawCellAt (setCellsAt lines base.toNat cs) a.toNat =
          if h : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length then some (cs[a.toNat - base.toNat]'(by omega))
          else rawCellAt lines a.toNat :=
        (linesEq_setCellsAt lines base.toNat cs a.toNat a.isLt).trans
          (rawCellAt_foldSetRawCell_noWrap lines base.toNat cs (by rw [hlen]; exact hwrap) a.toNat a.isLt)
      dsimp only [cellAt]; rw [hraw]
      by_cases hrng : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + (b :: rest).length
      · have hrng1 : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length := by rw [hlen]; exact hrng
        rw [dite_eq_left_of_eq_true (eq_true hrng1), dite_eq_left_of_eq_true (eq_true hrng)]; dsimp only; congr 1
        have hget := buildWriteCells_getElem ⟨lines, sb, top⟩ (b :: rest) (base.toNat / 64)
          (btGet 58 lines (base.toNat / 64)) base.toNat rfl hwrap (a.toNat - base.toNat) (by omega)
        rw [hget]
        have ha_eq : BitVec.ofNat 64 (base.toNat + (a.toNat - base.toNat)) = a := by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        rw [ha_eq, rawPerm_eq h a]; rcases m.rawPerm a with _ | _ <;> rfl
      · have hrng1 : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length) := by rw [hlen]; exact hrng
        rw [dite_eq_right_of_eq_false (eq_false hrng1), dite_eq_right_of_eq_false (eq_false hrng)]; exact h a
    · exact writeBytesSlow_agrees h base (b :: rest)

@[inline] def lineByte (lineOpt : Option Line64) (lo : Nat) : BitVec 8 :=
  match lineOpt with
  | some line => match btGet 6 line lo with | some (_, b) => b | none => 0#8
  | none => 0#8

private theorem lineByte_eq_read8 (fm : FastMem) (addr : BitVec 64) (k : Nat)
    (hmod : addr.toNat % 64 + k < 64) :
    lineByte (btGet 58 fm.lines (addr.toNat / 64)) (addr.toNat % 64 + k) =
      fm.read8 (addr + BitVec.ofNat 64 k) := by
  have ha := addr.isLt
  have htoNat : (addr + BitVec.ofNat 64 k).toNat = addr.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hdiv : (addr.toNat + k) / 64 = addr.toNat / 64 := by omega
  have hrem : (addr.toNat + k) % 64 = addr.toNat % 64 + k := by omega
  simp only [read8, rawCellAt, htoNat, hdiv, hrem, lineByte]
  rcases btGet 58 fm.lines (addr.toNat / 64) with _ | line
  · rfl
  · rcases btGet 6 line (addr.toNat % 64 + k) with _ | ⟨_, _⟩ <;> rfl

def read16 (fm : FastMem) (addr : BitVec 64) : BitVec 16 :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 62 then
    let ln := btGet 58 fm.lines (Nat.div a 64)
    lineByte ln (lo + 1) ++ lineByte ln (lo + 0)
  else (fm.read8 (addr + 1#64)) ++ (fm.read8 (addr + 0#64))

def write16 (fm : FastMem) (addr : BitVec 64) (val : BitVec 16) : FastMem :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 62 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      let hi := Nat.div a 64; let ln0 := (btGet 58 lines hi).getD .empty
      let ln1 := writeLineByte sb top a       ln0 lo       (val.extractLsb' 0 8)
      let ln2 := writeLineByte sb top (a + 1) ln1 (lo + 1) (val.extractLsb' 8 8)
      mkFastMem (btSet58Line lines hi ln2) sb top
  else (fm.write8 addr (val.extractLsb' 0 8)).write8 (addr + 1#64) (val.extractLsb' 8 8)

def read32 (fm : FastMem) (addr : BitVec 64) : BitVec 32 :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 60 then
    let ln := btGet 58 fm.lines (Nat.div a 64)
    lineByte ln (lo + 3) ++ lineByte ln (lo + 2) ++ lineByte ln (lo + 1) ++ lineByte ln (lo + 0)
  else
    (fm.read8 (addr + 3#64)) ++ (fm.read8 (addr + 2#64)) ++
    (fm.read8 (addr + 1#64)) ++ (fm.read8 (addr + 0#64))

def write32 (fm : FastMem) (addr : BitVec 64) (val : BitVec 32) : FastMem :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 60 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      let hi := Nat.div a 64; let ln0 := (btGet 58 lines hi).getD .empty
      let ln1 := writeLineByte sb top a       ln0 lo       (val.extractLsb' 0  8)
      let ln2 := writeLineByte sb top (a + 1) ln1 (lo + 1) (val.extractLsb' 8  8)
      let ln3 := writeLineByte sb top (a + 2) ln2 (lo + 2) (val.extractLsb' 16 8)
      let ln4 := writeLineByte sb top (a + 3) ln3 (lo + 3) (val.extractLsb' 24 8)
      mkFastMem (btSet58Line lines hi ln4) sb top
  else
    (((fm.write8 addr (val.extractLsb' 0 8)).write8 (addr + 1#64) (val.extractLsb' 8 8)).write8
      (addr + 2#64) (val.extractLsb' 16 8)).write8 (addr + 3#64) (val.extractLsb' 24 8)

def read64 (fm : FastMem) (addr : BitVec 64) : BitVec 64 :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 56 then
    let ln := btGet 58 fm.lines (Nat.div a 64)
    lineByte ln (lo + 7) ++ lineByte ln (lo + 6) ++ lineByte ln (lo + 5) ++ lineByte ln (lo + 4) ++
    lineByte ln (lo + 3) ++ lineByte ln (lo + 2) ++ lineByte ln (lo + 1) ++ lineByte ln (lo + 0)
  else
    (fm.read8 (addr + 7#64)) ++ (fm.read8 (addr + 6#64)) ++
    (fm.read8 (addr + 5#64)) ++ (fm.read8 (addr + 4#64)) ++
    (fm.read8 (addr + 3#64)) ++ (fm.read8 (addr + 2#64)) ++
    (fm.read8 (addr + 1#64)) ++ (fm.read8 (addr + 0#64))

def write64 (fm : FastMem) (addr : BitVec 64) (val : BitVec 64) : FastMem :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble lo 56 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      let hi := Nat.div a 64; let ln0 := (btGet 58 lines hi).getD .empty
      let ln1 := writeLineByte sb top a       ln0 lo       (val.extractLsb' 0  8)
      let ln2 := writeLineByte sb top (a + 1) ln1 (lo + 1) (val.extractLsb' 8  8)
      let ln3 := writeLineByte sb top (a + 2) ln2 (lo + 2) (val.extractLsb' 16 8)
      let ln4 := writeLineByte sb top (a + 3) ln3 (lo + 3) (val.extractLsb' 24 8)
      let ln5 := writeLineByte sb top (a + 4) ln4 (lo + 4) (val.extractLsb' 32 8)
      let ln6 := writeLineByte sb top (a + 5) ln5 (lo + 5) (val.extractLsb' 40 8)
      let ln7 := writeLineByte sb top (a + 6) ln6 (lo + 6) (val.extractLsb' 48 8)
      let ln8 := writeLineByte sb top (a + 7) ln7 (lo + 7) (val.extractLsb' 56 8)
      mkFastMem (btSet58Line lines hi ln8) sb top
  else
    (((((((fm.write8 addr (val.extractLsb' 0 8)).write8 (addr + 1#64) (val.extractLsb' 8 8)).write8
      (addr + 2#64) (val.extractLsb' 16 8)).write8 (addr + 3#64) (val.extractLsb' 24 8)).write8
      (addr + 4#64) (val.extractLsb' 32 8)).write8 (addr + 5#64) (val.extractLsb' 40 8)).write8
      (addr + 6#64) (val.extractLsb' 48 8)).write8 (addr + 7#64) (val.extractLsb' 56 8)

def readSized (fm : FastMem) (sz : MemWidth) (signed : Bool) (addr : BitVec 64) : BitVec 64 :=
  match sz with
  | .B8  => let b := fm.read8 addr;  if signed then b.signExtend 64 else b.zeroExtend 64
  | .H16 => let w := fm.read16 addr; if signed then w.signExtend 64 else w.zeroExtend 64
  | .W32 => let w := fm.read32 addr; if signed then w.signExtend 64 else w.zeroExtend 64
  | .X64 => fm.read64 addr

def writeSized (fm : FastMem) (sz : MemWidth) (addr : BitVec 64) (val : BitVec 64) : FastMem :=
  match sz with
  | .B8  => fm.write8 addr (val.truncate 8)
  | .H16 => fm.write16 addr (val.truncate 16)
  | .W32 => fm.write32 addr (val.truncate 32)
  | .X64 => fm.write64 addr val

def read128 (fm : FastMem) (addr : BitVec 64) : BitVec 128 :=
  (fm.read64 (addr + 8#64)) ++ (fm.read64 addr)

def write128 (fm : FastMem) (addr : BitVec 64) (val : BitVec 128) : FastMem :=
  (fm.write64 addr (val.extractLsb' 0 64)).write64 (addr + 8#64) (val.extractLsb' 64 64)

def readSimdSized (fm : FastMem) (sz : SimdMemSize) (addr : BitVec 64) : BitVec 128 :=
  match sz with
  | .B8   => (fm.read8 addr).zeroExtend 128
  | .H16  => (fm.read16 addr).zeroExtend 128
  | .S32  => (fm.read32 addr).zeroExtend 128
  | .D64  => (fm.read64 addr).zeroExtend 128
  | .Q128 => fm.read128 addr

def writeSimdSized (fm : FastMem) (sz : SimdMemSize) (addr : BitVec 64) (val : BitVec 128) : FastMem :=
  match sz with
  | .B8   => fm.write8 addr (val.truncate 8)
  | .H16  => fm.write16 addr (val.truncate 16)
  | .S32  => fm.write32 addr (val.truncate 32)
  | .D64  => fm.write64 addr (val.truncate 64)
  | .Q128 => fm.write128 addr val

theorem read16_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read16 a = m.read16 a := by
  unfold read16
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 62
  · simp only [Bool.false_eq_true, ↓reduceIte, Memory.read16, read8_eq h]
  · have hlo := Nat.ble_eq.mp hb
    simp only [↓reduceIte, lineByte_eq_read8 fm a 1 (by omega), lineByte_eq_read8 fm a 0 (by omega), Memory.read16, read8_eq h]

theorem write16_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) (v : BitVec 16) :
    (fm.write16 a v).Agrees (m.write16 a v) := by
  unfold write16 Memory.write16
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 62
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
    exact write8_agrees (write8_agrees h _ _) _ _
  · have hlo := Nat.ble_eq.mp hb
    rcases fm with ⟨lines, sb, top⟩; simp only [↓reduceIte, mkFastMem_eq, btSet58Line_eq]
    have h0 : (⟨btSet 58 lines (a.toNat / 64) (writeLineByte sb top a.toNat ((btGet 58 lines (a.toNat / 64)).getD .empty) (a.toNat % 64) (v.extractLsb' 0 8)), sb, top⟩ : FastMem).Agrees (m.write8 (a + 0#64) (v.extractLsb' 0 8)) := by
      simpa only [BitVec.add_zero, write8, mkFastMem_eq, btSet58Line_eq, hd, hm] using write8_agrees h (a + 0#64) (v.extractLsb' 0 8)
    exact writeLineByte_step_agrees (k := 1) (by omega) _ _ h0

theorem read32_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read32 a = m.read32 a := by
  unfold read32
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 60
  · simp only [Bool.false_eq_true, ↓reduceIte, Memory.read32, read8_eq h]
  · have hlo := Nat.ble_eq.mp hb
    simp only [↓reduceIte, lineByte_eq_read8 fm a 3 (by omega), lineByte_eq_read8 fm a 2 (by omega),
      lineByte_eq_read8 fm a 1 (by omega), lineByte_eq_read8 fm a 0 (by omega), Memory.read32, read8_eq h]

theorem write32_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) (v : BitVec 32) :
    (fm.write32 a v).Agrees (m.write32 a v) := by
  unfold write32 Memory.write32
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 60
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
    exact write8_agrees (write8_agrees (write8_agrees (write8_agrees h _ _) _ _) _ _) _ _
  · have hlo := Nat.ble_eq.mp hb
    rcases fm with ⟨lines, sb, top⟩; simp only [↓reduceIte, mkFastMem_eq, btSet58Line_eq]
    have h0 : (⟨btSet 58 lines (a.toNat / 64) (writeLineByte sb top a.toNat ((btGet 58 lines (a.toNat / 64)).getD .empty) (a.toNat % 64) (v.extractLsb' 0 8)), sb, top⟩ : FastMem).Agrees (m.write8 (a + 0#64) (v.extractLsb' 0 8)) := by
      simpa only [BitVec.add_zero, write8, mkFastMem_eq, btSet58Line_eq, hd, hm] using write8_agrees h (a + 0#64) (v.extractLsb' 0 8)
    exact writeLineByte_step_agrees (k := 3) (by omega) _ _
      (writeLineByte_step_agrees (k := 2) (by omega) _ _
      (writeLineByte_step_agrees (k := 1) (by omega) _ _ h0))

theorem read64_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read64 a = m.read64 a := by
  unfold read64
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 56
  · simp only [Bool.false_eq_true, ↓reduceIte, Memory.read64, read8_eq h]
  · have hlo := Nat.ble_eq.mp hb
    simp only [↓reduceIte, lineByte_eq_read8 fm a 7 (by omega), lineByte_eq_read8 fm a 6 (by omega),
      lineByte_eq_read8 fm a 5 (by omega), lineByte_eq_read8 fm a 4 (by omega),
      lineByte_eq_read8 fm a 3 (by omega), lineByte_eq_read8 fm a 2 (by omega),
      lineByte_eq_read8 fm a 1 (by omega), lineByte_eq_read8 fm a 0 (by omega), Memory.read64, read8_eq h]

theorem write64_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) (v : BitVec 64) :
    (fm.write64 a v).Agrees (m.write64 a v) := by
  unfold write64 Memory.write64
  have hd : Nat.div a.toNat 64 = a.toNat / 64 := rfl; have hm : Nat.mod a.toNat 64 = a.toNat % 64 := rfl
  dsimp only; rw [hd, hm]
  cases hb : Nat.ble (a.toNat % 64) 56
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
    exact write8_agrees (write8_agrees (write8_agrees (write8_agrees (write8_agrees (write8_agrees (write8_agrees (write8_agrees h _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _
  · have hlo := Nat.ble_eq.mp hb
    rcases fm with ⟨lines, sb, top⟩; simp only [↓reduceIte, mkFastMem_eq, btSet58Line_eq]
    have h0 : (⟨btSet 58 lines (a.toNat / 64) (writeLineByte sb top a.toNat ((btGet 58 lines (a.toNat / 64)).getD .empty) (a.toNat % 64) (v.extractLsb' 0 8)), sb, top⟩ : FastMem).Agrees (m.write8 (a + 0#64) (v.extractLsb' 0 8)) := by
      simpa only [BitVec.add_zero, write8, mkFastMem_eq, btSet58Line_eq, hd, hm] using write8_agrees h (a + 0#64) (v.extractLsb' 0 8)
    exact writeLineByte_step_agrees (k := 7) (by omega) _ _
      (writeLineByte_step_agrees (k := 6) (by omega) _ _
      (writeLineByte_step_agrees (k := 5) (by omega) _ _
      (writeLineByte_step_agrees (k := 4) (by omega) _ _
      (writeLineByte_step_agrees (k := 3) (by omega) _ _
      (writeLineByte_step_agrees (k := 2) (by omega) _ _
      (writeLineByte_step_agrees (k := 1) (by omega) _ _ h0))))))

theorem readSized_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (sz : MemWidth) (signed : Bool) (a : BitVec 64) :
    fm.readSized sz signed a = m.readSized sz signed a := by
  cases sz <;> simp only [readSized, Memory.readSized, read8_eq h, read16_eq h, read32_eq h, read64_eq h]

theorem writeSized_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (sz : MemWidth) (a : BitVec 64) (v : BitVec 64) :
    (fm.writeSized sz a v).Agrees (m.writeSized sz a v) := by
  cases sz with
  | B8 => exact write8_agrees h _ _ | H16 => exact write16_agrees h _ _
  | W32 => exact write32_agrees h _ _ | X64 => exact write64_agrees h _ _

theorem read128_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read128 a = m.read128 a := by simp only [read128, Memory.read128, read64_eq h]

theorem write128_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) (v : BitVec 128) :
    (fm.write128 a v).Agrees (m.write128 a v) := by
  unfold write128 Memory.write128; exact write64_agrees (write64_agrees h _ _) _ _

theorem readSimdSized_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (sz : SimdMemSize) (a : BitVec 64) :
    fm.readSimdSized sz a = m.readSimdSized sz a := by
  cases sz <;> simp only [readSimdSized, Memory.readSimdSized, read8_eq h, read16_eq h, read32_eq h, read64_eq h, read128_eq h]

theorem writeSimdSized_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (sz : SimdMemSize) (a : BitVec 64) (v : BitVec 128) :
    (fm.writeSimdSized sz a v).Agrees (m.writeSimdSized sz a v) := by
  cases sz with
  | B8 => exact write8_agrees h _ _ | H16 => exact write16_agrees h _ _ | S32 => exact write32_agrees h _ _
  | D64 => exact write64_agrees h _ _ | Q128 => exact write128_agrees h _ _

/-- Build updated cells for `mapFresh` / `mapZero` in one cached-line pass. -/
def buildMapCells (fm : FastMem) (zeroFill : Bool) (p : Perm)
    (curHi : Nat) (curLine : Option Line64) (addr : Nat) : Nat → List Cell
  | 0 => []
  | n + 1 =>
    let hi := addr / 64
    let lineOpt := if hi == curHi then curLine else btGet 58 fm.lines hi
    let cell := match cellAtWithLine fm addr lineOpt with
      | some (some q, b) => (some q, b)
      | some (none, b) => (some p, if zeroFill then 0#8 else b)
      | none => (some p, 0#8)
    withForcedNat (addr + 1) fun addr' => cell :: buildMapCells fm zeroFill p hi lineOpt addr' n

private theorem buildMapCells_length (fm : FastMem) (zeroFill : Bool) (p : Perm) :
    ∀ (n curHi : Nat) (curLine : Option Line64) (addr : Nat),
      (buildMapCells fm zeroFill p curHi curLine addr n).length = n
  | 0, _, _, _ => rfl
  | n + 1, curHi, curLine, addr => by
    simp only [buildMapCells, withForcedNat_eq, List.length_cons, buildMapCells_length fm zeroFill p n]

private theorem buildMapCells_getElem (fm : FastMem) (zeroFill : Bool) (p : Perm) :
    ∀ (n curHi : Nat) (curLine : Option Line64) (addr : Nat),
      curLine = btGet 58 fm.lines curHi →
      addr + n ≤ 2 ^ 64 →
      ∀ (i : Nat) (hi : i < n),
        some ((buildMapCells fm zeroFill p curHi curLine addr n)[i]'(by rw [buildMapCells_length]; exact hi)) =
          let a := BitVec.ofNat 64 (addr + i)
          if !(fm.perm a).mapped then
            some (some p, if zeroFill then 0#8 else fm.read8 a)
          else
            fm.cellAt a
  | 0, _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, curHi, curLine, addr, hcur, hwrap, i, hi => by
    cases i with
    | zero =>
      simp only [buildMapCells, withForcedNat_eq, List.getElem_cons_zero, Nat.add_zero]
      rw [cachedLine_eq fm.lines (addr / 64) curHi curLine hcur]
      have hadr : (BitVec.ofNat 64 addr).toNat = addr := Nat.mod_eq_of_lt (by omega)
      have hc := cellAtWithLine_eq fm (BitVec.ofNat 64 addr)
      rw [hadr] at hc
      rw [hc, read8_eq_of_cellAt, perm]
      rcases fm.cellAt (BitVec.ofNat 64 addr) with _ | ⟨_ | q, b⟩
      · cases zeroFill <;> rfl
      · rfl
      · rfl
    | succ j =>
      have hj : j < n := by omega
      have hline := cachedLine_eq fm.lines (addr / 64) curHi curLine hcur
      have hrec := buildMapCells_getElem fm zeroFill p n (addr / 64)
        (if addr / 64 == curHi then curLine else btGet 58 fm.lines (addr / 64))
        (addr + 1) hline (by omega) j hj
      have hadd : addr + 1 + j = addr + (j + 1) := by omega
      simp only [buildMapCells, withForcedNat_eq, List.getElem_cons_succ]
      simpa only [hadd] using hrec

/-- Byte-by-byte fallback for `mapFresh` and `mapZero` when `base.toNat + len > 2 ^ 64`. -/
def mapRangeSlow (fm : FastMem) (zeroFill : Bool) (p : Perm)
    (base : BitVec 64) : Nat → FastMem
  | 0 => fm
  | n + 1 =>
    let fm' := if !(fm.perm base).mapped then
      fm.setCell base (some p, if zeroFill then 0#8 else fm.read8 base)
    else fm
    mapRangeSlow fm' zeroFill p (base + 1#64) n

private theorem mapRangeSlow_cellAt (fm : FastMem) (zeroFill : Bool) (p : Perm)
    (base : BitVec 64) (len : Nat) (hmax : len ≤ 2 ^ 64) (a : BitVec 64) :
    (mapRangeSlow fm zeroFill p base len).cellAt a =
      if (a - base).toNat < len && !(fm.perm a).mapped then
        some (some p, if zeroFill then 0#8 else fm.read8 a)
      else
        fm.cellAt a := by
  induction len generalizing fm base with
  | zero => simp [mapRangeSlow]
  | succ n ih =>
    simp only [mapRangeSlow]
    set fm' := if !(fm.perm base).mapped then
      fm.setCell base (some p, if zeroFill then 0#8 else fm.read8 base) else fm
    have hperm_other : ∀ x : BitVec 64, x ≠ base → fm'.cellAt x = fm.cellAt x := by
      intro x hx; dsimp only [fm']; split
      · exact cellAt_setCell_ne fm _ hx
      · rfl
    rw [ih fm' (base + 1#64) (by omega)]
    by_cases heq : a = base
    · subst heq
      have hnot_rest : ¬ ((a - (a + 1#64)).toNat < n) := by
        have hsub : (a - (a + 1#64)).toNat = 2 ^ 64 - 1 := by
          have ha := a.isLt; simp only [BitVec.toNat_sub, BitVec.toNat_add]
          have h1 : (1#64).toNat = 1 := rfl; rw [h1]
          by_cases htop : a.toNat + 1 = 2 ^ 64
          · rw [htop, Nat.mod_self, Nat.sub_zero, Nat.add_mod_left, Nat.mod_eq_of_lt ha]; omega
          · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
        omega
      have hzero : (a - a).toNat < n + 1 := by simp
      simp only [hnot_rest, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        hzero, decide_true, Bool.true_and, fm']
      by_cases hm : (!(fm.perm a).mapped) = true
      · simp only [hm, ↓reduceIte, cellAt_setCell_same]
      · simp only [Bool.not_eq_true] at hm; simp only [hm, Bool.false_eq_true, ↓reduceIte]
    · have hsub_step := toNat_sub_succ_base heq
      have hc_eq := hperm_other a heq
      have hp_eq : fm'.perm a = fm.perm a := by simp only [perm, hc_eq]
      have hr_eq : fm'.read8 a = fm.read8 a := by
        rw [read8_eq_of_cellAt, read8_eq_of_cellAt, hc_eq]
      rw [hc_eq, hp_eq, hr_eq]
      have hlt_iff : ((a - (base + 1#64)).toNat < n) ↔ ((a - base).toNat < n + 1) := by omega
      by_cases hlt : (a - (base + 1#64)).toNat < n
      · simp only [hlt, hlt_iff.mp hlt, decide_true, Bool.true_and]
      · have hlt2 : ¬ ((a - base).toNat < n + 1) := fun h2 => hlt (hlt_iff.mpr h2)
        simp only [hlt, hlt2, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Map unmapped bytes in `[base, base + len)` with permission `p` (`Memory.mapFresh`). -/
def mapFresh (fm : FastMem) (base : BitVec 64) (len : Nat) (p : Perm) : FastMem :=
  let clen := min len (2 ^ 64)
  if clen == 0 then fm
  else if base.toNat + clen ≤ 2 ^ 64 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      let hi := base.toNat / 64
      let cs := buildMapCells ⟨lines, sb, top⟩ false p hi (btGet 58 lines hi) base.toNat clen
      withForcedBinTree (setCellsAt lines base.toNat cs) fun lines' => ⟨lines', sb, top⟩
  else
    mapRangeSlow fm false p base clen

/-- Map unmapped bytes in `[base, base + len)` read-write and zero-filled (`Memory.mapZero`). -/
def mapZero (fm : FastMem) (base : BitVec 64) (len : Nat) : FastMem :=
  let clen := min len (2 ^ 64)
  if clen == 0 then fm
  else if base.toNat + clen ≤ 2 ^ 64 then
    match fm with
    | ⟨lines, sb, top⟩ =>
      let hi := base.toNat / 64
      let cs := buildMapCells ⟨lines, sb, top⟩ true Perm.rw hi (btGet 58 lines hi) base.toNat clen
      withForcedBinTree (setCellsAt lines base.toNat cs) fun lines' => ⟨lines', sb, top⟩
  else
    mapRangeSlow fm true Perm.rw base clen

private theorem mapRange_agrees_aux {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (zeroFill : Bool) (p : Perm) (base : BitVec 64) (len : Nat) (a : BitVec 64) :
    (let clen := min len (2 ^ 64)
     if clen == 0 then fm
     else if base.toNat + clen ≤ 2 ^ 64 then
       match fm with
       | ⟨lines, sb, top⟩ =>
         let hi := base.toNat / 64
         let cs := buildMapCells ⟨lines, sb, top⟩ zeroFill p hi (btGet 58 lines hi) base.toNat clen
         withForcedBinTree (setCellsAt lines base.toNat cs) fun lines' => ⟨lines', sb, top⟩
     else
       mapRangeSlow fm zeroFill p base clen).cellAt a =
      if (a - base).toNat < len && !(m.perm a).mapped then
        some (some p, if zeroFill then 0#8 else m.read8 a)
      else
        m.cells a := by
  simp only [withForcedBinTree_eq]
  have hclen_iff : ((a - base).toNat < min len (2 ^ 64)) ↔ ((a - base).toNat < len) := by
    have := (a - base).isLt
    omega
  by_cases hz : (min len (2 ^ 64) == 0) = true
  · simp only [hz, ↓reduceIte]
    have hz0 : min len (2 ^ 64) = 0 := beq_iff_eq.mp hz
    have hnot : ¬ ((a - base).toNat < len) := by omega
    simp only [hnot, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, h a]
  · simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hwrap
      set cs := buildMapCells fm zeroFill p (base.toNat / 64) (btGet 58 fm.lines (base.toNat / 64))
        base.toNat (min len (2 ^ 64))
      have hlen : cs.length = min len (2 ^ 64) :=
        buildMapCells_length fm zeroFill p (min len (2 ^ 64)) _ _ _
      have hraw : rawCellAt (setCellsAt fm.lines base.toNat cs) a.toNat =
          if h : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length then
            some (cs[a.toNat - base.toNat]'(by omega))
          else
            rawCellAt fm.lines a.toNat :=
        (linesEq_setCellsAt fm.lines base.toNat cs a.toNat a.isLt).trans
          (rawCellAt_foldSetRawCell_noWrap fm.lines base.toNat cs (by rw [hlen]; exact hwrap) a.toNat a.isLt)
      dsimp only [cellAt]
      rw [hraw]
      have hrng_iff := sub_lt_iff_range hwrap (a := a)
      by_cases hrng : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + min len (2 ^ 64)
      · have hrng1 : base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length := by
          rw [hlen]; exact hrng
        rw [dite_eq_left_of_eq_true (eq_true hrng1)]
        dsimp only
        have hlt_len : (a - base).toNat < len := hclen_iff.mp (hrng_iff.mpr hrng)
        simp only [hlt_len, decide_true, Bool.true_and]
        have hget := buildMapCells_getElem fm zeroFill p (min len (2 ^ 64))
          (base.toNat / 64) (btGet 58 fm.lines (base.toNat / 64)) base.toNat rfl hwrap
          (a.toNat - base.toNat) (by omega)
        have ha_eq : BitVec.ofNat 64 (base.toNat + (a.toNat - base.toNat)) = a := by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          omega
        dsimp only at hget
        rw [ha_eq] at hget
        rw [hget, perm_eq h a, read8_eq h a, h a]
      · have hrng1 : ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + cs.length) := by
          rw [hlen]; exact hrng
        rw [dite_eq_right_of_eq_false (eq_false hrng1)]
        have hnot_len : ¬ ((a - base).toNat < len) :=
          fun hl => hrng (hrng_iff.mp (hclen_iff.mpr hl))
        simp only [hnot_len, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact h a
    · rw [mapRangeSlow_cellAt fm zeroFill p base (min len (2 ^ 64)) (Nat.min_le_right _ _) a,
        perm_eq h a, read8_eq h a, h a]
      by_cases hl : (a - base).toNat < len
      · simp only [hl, hclen_iff.mpr hl, decide_true, Bool.true_and]
      · have hl' : ¬ ((a - base).toNat < min len (2 ^ 64)) := fun h1 => hl (hclen_iff.mp h1)
        simp only [hl, hl', decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem mapFresh_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (len : Nat) (p : Perm) :
    (fm.mapFresh base len p).Agrees (m.mapFresh base len p) := by
  intro a
  simpa only [mapFresh, Memory.mapFresh, Bool.false_eq_true, ↓reduceIte] using
    mapRange_agrees_aux h false p base len a

theorem mapZero_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (base : BitVec 64) (len : Nat) :
    (fm.mapZero base len).Agrees (m.mapZero base len) := by
  intro a
  simpa only [mapZero, Memory.mapZero, ↓reduceIte] using
    mapRange_agrees_aux h true Perm.rw base len a

/-- Map unmapped bytes in `[addr, addr + size)` with `Perm.rw` and write `bs` at `addr`. -/
def allocBytes (fm : FastMem) (addr : BitVec 64) (size : Nat) (bs : List (BitVec 8)) : FastMem :=
  (fm.mapFresh addr size Perm.rw).writeBytes addr bs

def allocBytes? (fm : FastMem) (addr : BitVec 64) (size : Nat) (bs : List (BitVec 8)) : Option FastMem :=
  some (fm.allocBytes addr size bs)

theorem allocBytes_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (addr : BitVec 64) (size : Nat) (bs : List (BitVec 8)) :
    (fm.allocBytes addr size bs).Agrees ((m.mapFresh addr size Perm.rw).writeBytes addr bs) :=
  writeBytes_agrees (mapFresh_agrees h _ size Perm.rw) _ bs

def allPermCached (fm : FastMem) (pred : Option Perm → Bool)
    (curHi : Nat) (curLine : Option Line64) (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 =>
    let a := addr.toNat
    let hi := a / 64
    withForcedLineOpt (if hi == curHi then curLine else btGet 58 fm.lines hi) fun lineOpt =>
      let p := match cellAtWithLine fm a lineOpt with
        | some (some (q : Perm), _) => some q.rwx
        | _ => none
      withForcedBV (addr + 1#64) fun addr' => pred p && allPermCached fm pred hi lineOpt addr' n

def allPerm (fm : FastMem) (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ + 1 =>
    let hi := addr.toNat / 64
    withForcedLineOpt (btGet 58 fm.lines hi) fun ln => allPermCached fm pred hi ln addr n

private theorem allPermCached_eq (fm : FastMem) {m : Memory} (h : fm.Agrees m)
    (pred : Option Perm → Bool) :
    ∀ (n : Nat) (addr : BitVec 64) (curHi : Nat) (curLine : Option Line64),
      curLine = btGet 58 fm.lines curHi →
      allPermCached fm pred curHi curLine addr n = m.allPerm pred addr n
  | 0, _, _, _, _ => rfl
  | n + 1, addr, curHi, curLine, hcur => by
    simp only [allPermCached, withForcedLineOpt_eq, withForcedBV_eq, Memory.allPerm]
    rw [cachedLine_eq fm.lines (addr.toNat / 64) curHi curLine hcur, cellAtWithLine_eq fm addr,
      allPermCached_eq fm h pred n (addr + 1#64) (addr.toNat / 64) _ rfl,
      ← perm_eq h addr, perm]

theorem allPerm_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (pred : Option Perm → Bool) (addr : BitVec 64) (n : Nat) :
    fm.allPerm pred addr n = m.allPerm pred addr n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [allPerm, withForcedLineOpt_eq]
    exact allPermCached_eq fm h pred (n + 1) addr (addr.toNat / 64) _ rfl

def allNoLazyFreeCached (fm : FastMem) (curHi : Nat) (curLine : Option Line64)
    (addr : BitVec 64) : Nat → Bool
  | 0 => true
  | n + 1 =>
    let a := addr.toNat
    let hi := a / 64
    withForcedLineOpt (if hi == curHi then curLine else btGet 58 fm.lines hi) fun lineOpt =>
      let lf := match cellAtWithLine fm a lineOpt with
        | some (some (q : Perm), _) => q.lazyFree
        | _ => false
      withForcedBV (addr + 1#64) fun addr' => !lf && allNoLazyFreeCached fm hi lineOpt addr' n

def allNoLazyFree (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool :=
  match n with
  | 0 => true
  | _ + 1 =>
    let hi := addr.toNat / 64
    withForcedLineOpt (btGet 58 fm.lines hi) fun ln => allNoLazyFreeCached fm hi ln addr n

private theorem allNoLazyFreeCached_eq (fm : FastMem) {m : Memory} (h : fm.Agrees m) :
    ∀ (n : Nat) (addr : BitVec 64) (curHi : Nat) (curLine : Option Line64),
      curLine = btGet 58 fm.lines curHi →
      allNoLazyFreeCached fm curHi curLine addr n = m.allNoLazyFree addr n
  | 0, _, _, _, _ => rfl
  | n + 1, addr, curHi, curLine, hcur => by
    simp only [allNoLazyFreeCached, withForcedLineOpt_eq, withForcedBV_eq, Memory.allNoLazyFree]
    rw [cachedLine_eq fm.lines (addr.toNat / 64) curHi curLine hcur, cellAtWithLine_eq fm addr,
      allNoLazyFreeCached_eq fm h n (addr + 1#64) (addr.toNat / 64) _ rfl,
      ← isLazyFree_eq h addr, isLazyFree]

theorem allNoLazyFree_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.allNoLazyFree addr n = m.allNoLazyFree addr n := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [allNoLazyFree, withForcedLineOpt_eq]
    exact allNoLazyFreeCached_eq fm h (n + 1) addr (addr.toNat / 64) _ rfl

private theorem lineByteCanRead_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) :
    lineByteCanRead fm.stackBase fm.stackTop addr.toNat
      ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat % 64) =
      ((m.perm addr).r && !m.isLazyFree addr) := by
  rw [← perm_eq h addr, ← isLazyFree_eq h addr]
  simp only [lineByteCanRead, perm, isLazyFree, cellAt, rawCellAt, ble_eq_decide, blt_eq_decide]
  cases h58 : btGet 58 fm.lines (addr.toNat / 64) with
  | none =>
    simp only [Option.getD_none, btGet_empty]
    cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
  | some ln =>
    simp only [Option.getD_some]
    cases h6 : btGet 6 ln (addr.toNat % 64) with
    | none => cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
    | some c => rcases c with ⟨_ | p, b⟩ <;> rfl

private theorem lineByteCanWrite_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) :
    lineByteCanWrite fm.stackBase fm.stackTop addr.toNat
      ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat % 64) =
      ((m.perm addr).w && !(m.perm addr).x) := by
  rw [← perm_eq h addr]
  simp only [lineByteCanWrite, perm, cellAt, rawCellAt, ble_eq_decide, blt_eq_decide]
  cases h58 : btGet 58 fm.lines (addr.toNat / 64) with
  | none =>
    simp only [Option.getD_none, btGet_empty]
    cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
  | some ln =>
    simp only [Option.getD_some]
    cases h6 : btGet 6 ln (addr.toNat % 64) with
    | none => cases decide (fm.stackBase ≤ addr.toNat) && decide (addr.toNat < fm.stackTop) <;> rfl
    | some c => rcases c with ⟨_ | p, b⟩ <;> rfl

private theorem lineCanReadAux_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    ∀ (n : Nat) (addr : BitVec 64) (_hlo : addr.toNat % 64 + n ≤ 64),
      lineCanReadAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty)
        addr.toNat (addr.toNat % 64) n = m.canRead addr n
  | 0, _, _ => rfl
  | 1, addr, _ => by
    simp only [lineCanReadAux, lineByteCanRead_eq h addr, Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, Bool.and_true]
  | n + 2, addr, hlo => by
    have ha := addr.isLt; have hlt2 : addr.toNat + 1 < 2 ^ 64 := by omega
    have htoNat : (addr + 1#64).toNat = addr.toNat + 1 := by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt2
    have hdiv : (addr + 1#64).toNat / 64 = addr.toNat / 64 := by rw [htoNat]; omega
    have hrem : (addr + 1#64).toNat % 64 = addr.toNat % 64 + 1 := by rw [htoNat]; omega
    have ih := lineCanReadAux_eq h (n + 1) (addr + 1#64) (by rw [hrem]; omega); rw [hdiv, hrem, htoNat] at ih
    change (lineByteCanRead fm.stackBase fm.stackTop addr.toNat ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat % 64) &&
      lineCanReadAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat + 1) (addr.toNat % 64 + 1) (n + 1)) =
      (((m.perm addr).r && m.allPerm (·.r) (addr + 1#64) (n + 1)) && (!m.isLazyFree addr && m.allNoLazyFree (addr + 1#64) (n + 1)))
    rw [lineByteCanRead_eq h addr, ih]; dsimp only [Memory.canRead]
    cases (m.perm addr).r <;> cases (!m.isLazyFree addr) <;> simp

private theorem lineCanWriteAux_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) :
    ∀ (n : Nat) (addr : BitVec 64) (_hlo : addr.toNat % 64 + n ≤ 64),
      lineCanWriteAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty)
        addr.toNat (addr.toNat % 64) n = m.canWrite addr n
  | 0, _, _ => rfl
  | 1, addr, _ => by
    simp only [lineCanWriteAux, lineByteCanWrite_eq h addr, Memory.canWrite, Memory.allPerm, Bool.and_true]
  | n + 2, addr, hlo => by
    have ha := addr.isLt; have hlt2 : addr.toNat + 1 < 2 ^ 64 := by omega
    have htoNat : (addr + 1#64).toNat = addr.toNat + 1 := by rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt2
    have hdiv : (addr + 1#64).toNat / 64 = addr.toNat / 64 := by rw [htoNat]; omega
    have hrem : (addr + 1#64).toNat % 64 = addr.toNat % 64 + 1 := by rw [htoNat]; omega
    have ih := lineCanWriteAux_eq h (n + 1) (addr + 1#64) (by rw [hrem]; omega); rw [hdiv, hrem, htoNat] at ih
    change (lineByteCanWrite fm.stackBase fm.stackTop addr.toNat ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat % 64) &&
      lineCanWriteAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (addr.toNat / 64)).getD .empty) (addr.toNat + 1) (addr.toNat % 64 + 1) (n + 1)) =
      (((m.perm addr).w && !(m.perm addr).x) && m.canWrite (addr + 1#64) (n + 1))
    rw [lineByteCanWrite_eq h addr, ih]

def canRead (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble (Nat.add lo n) 64 then
    lineCanReadAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (Nat.div a 64)).getD .empty) a lo n
  else fm.allPerm (·.r) addr n && fm.allNoLazyFree addr n

def canWrite (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool :=
  let a := addr.toNat; let lo := Nat.mod a 64
  if Nat.ble (Nat.add lo n) 64 then
    lineCanWriteAux fm.stackBase fm.stackTop ((btGet 58 fm.lines (Nat.div a 64)).getD .empty) a lo n
  else fm.allPerm (fun p => p.w && !p.x) addr n

def canExec (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool := fm.allPerm (·.x) addr n
def canMap (fm : FastMem) (addr : BitVec 64) (n : Nat) : Bool := fm.allPerm (fun p => !p.mapped) addr n

theorem canRead_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.canRead addr n = m.canRead addr n := by
  unfold canRead
  have hd : Nat.div addr.toNat 64 = addr.toNat / 64 := rfl
  have hm : Nat.mod addr.toNat 64 = addr.toNat % 64 := rfl
  have ha : Nat.add (addr.toNat % 64) n = addr.toNat % 64 + n := rfl
  dsimp only; rw [hd, hm, ha]
  cases hb : Nat.ble (addr.toNat % 64 + n) 64
  · simp only [Bool.false_eq_true, ↓reduceIte, Memory.canRead, allPerm_eq h, allNoLazyFree_eq h]
  · simp only [↓reduceIte, lineCanReadAux_eq h n addr (Nat.ble_eq.mp hb)]

theorem canWrite_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.canWrite addr n = m.canWrite addr n := by
  unfold canWrite
  have hd : Nat.div addr.toNat 64 = addr.toNat / 64 := rfl
  have hm : Nat.mod addr.toNat 64 = addr.toNat % 64 := rfl
  have ha : Nat.add (addr.toNat % 64) n = addr.toNat % 64 + n := rfl
  dsimp only; rw [hd, hm, ha]
  cases hb : Nat.ble (addr.toNat % 64 + n) 64
  · simp only [Bool.false_eq_true, ↓reduceIte, Memory.canWrite, allPerm_eq h]
  · simp only [↓reduceIte, lineCanWriteAux_eq h n addr (Nat.ble_eq.mp hb)]

theorem canExec_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.canExec addr n = m.canExec addr n := by simp only [canExec, Memory.canExec, allPerm_eq h]

theorem canMap_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (addr : BitVec 64) (n : Nat) :
    fm.canMap addr n = m.canMap addr n := by simp only [canMap, Memory.canMap, allPerm_eq h]

end FastMem

theorem fastMem_read8_eq {fm : FastMem} {m : Memory} (h : fm.Agrees m) (a : BitVec 64) :
    fm.read8 a = m.read8 a := fm.read8_eq h a

theorem fastMem_write8_agrees {fm : FastMem} {m : Memory} (h : fm.Agrees m)
    (a : BitVec 64) (v : BitVec 8) (fm' : FastMem) (hw : fm.write8? a v = some fm') :
    fm'.Agrees (m.write8 a v) := by injection hw with hw; subst hw; exact fm.write8_agrees h a v

export Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (
  loadRegionsLines rawCellAt_loadRegionsLines baseRegions_mapZero_cells_eq
)

end Symbolic.BugInjection.Proofs.CliExec.RadixMem
