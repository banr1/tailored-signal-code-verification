/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops
import ProofLib.SepLogic.WPp

/-!
# Shared Stack-Frame, Locals, and State Helpers for `main`

Separation-logic and state-invariant helpers for `main`'s `0x4e0`-byte stack frame: carving and
collapsing sub-regions in the `0x480`-byte `locals` area, `mainSaved` callee-saved register slots,
`stackAt` splitting and disjointness bounds, and `InMain` alignment/step preservation.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## 1. `localsFrom` / `locals` / `cell` Helpers -/

/-- Upper offset bounding the leading gap of `localsFrom fsp off cs`. -/
def localsBound : List (Nat × Nat × SepProp) → Nat
  | [] => 0x480
  | (o, _, _) :: _ => o

/-- End offset after laying out `cs` starting from `off`. -/
def localsEnd (off : Nat) : List (Nat × Nat × SepProp) → Nat
  | [] => off
  | (o, n, _) :: cs => localsEnd (o + n) cs

/-- Spatial context surrounding a focused entry `(o, n, _)` inside `localsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂)`. -/
def localsCtx (fsp : BitVec 64) :
    Nat → List (Nat × Nat × SepProp) → Nat → Nat → List (Nat × Nat × SepProp) → SepProp
  | off, [], o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗ localsFrom fsp (o + n) cs₂
  | off, (o₁, n₁, P₁) :: cs₁, o, n, cs₂ =>
    memRegion (fsp + BitVec.ofNat 64 off) (o₁ - off) ∗ P₁ ∗
      localsCtx fsp (o₁ + n₁) cs₁ o n cs₂

/-- Well-formedness of an ordered list of local pieces starting from `off`. -/
def LocalsWF : Nat → List (Nat × Nat × SepProp) → Prop
  | off, [] => off ≤ 0x480
  | off, (o, n, _) :: cs => off ≤ o ∧ LocalsWF (o + n) cs

theorem LocalsWF.le_top {off : Nat} {cs : List (Nat × Nat × SepProp)} (h : LocalsWF off cs) :
    off ≤ 0x480 := by
  induction cs generalizing off with
  | nil => exact h
  | cons c cs ih =>
    rcases c with ⟨o, n, _⟩
    have h1 : off ≤ o := h.1
    have h2 : o + n ≤ 0x480 := ih h.2
    omega

theorem locals_nil (fsp : BitVec 64) :
    locals fsp [] = memRegion fsp 0x480 := by
  simp only [locals, localsFrom, BitVec.add_zero, Nat.sub_zero]

theorem localsFrom_focus (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    localsFrom fsp off (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ localsCtx fsp off cs₁ o n cs₂ := by
  induction cs₁ generalizing off with
  | nil =>
    simp only [List.nil_append, localsFrom, localsCtx]
    ac_rfl
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, localsFrom, localsCtx, ih (o₁ + n₁)]
    ac_rfl

/-- Pull the owned piece `P` at `(o, n)` to the front of `locals`, or put a new piece back via `.symm`. -/
theorem locals_focus (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) (P : SepProp)
    (cs₂ : List (Nat × Nat × SepProp)) :
    locals fsp (cs₁ ++ (o, n, P) :: cs₂) =
      P ∗ localsCtx fsp 0 cs₁ o n cs₂ :=
  localsFrom_focus fsp 0 cs₁ o n P cs₂

/-- Replace an owned piece `P` with `Q` at `(o, n)` when `P ⊢ Q`. -/
theorem locals_mono_piece (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat) {P Q : SepProp}
    (cs₂ : List (Nat × Nat × SepProp)) (hPQ : P ⊢ Q) :
    locals fsp (cs₁ ++ (o, n, P) :: cs₂) ⊢
      locals fsp (cs₁ ++ (o, n, Q) :: cs₂) := by
  rw [locals_focus fsp cs₁ o n P cs₂, locals_focus fsp cs₁ o n Q cs₂]
  exact sepConj_mono_left hPQ

/-- Carve `(o, n, memRegion (fsp + BitVec.ofNat 64 o) n)` out of the leading gap of `localsFrom`. -/
theorem localsFrom_carve_region (fsp : BitVec 64) (off o n : Nat)
    (cs : List (Nat × Nat × SepProp))
    (hlo : off ≤ o := by decide)
    (hhi : o + n ≤ localsBound cs := by decide)
    (hbnd : localsBound cs ≤ 0x480 := by decide) :
    localsFrom fsp off cs =
      localsFrom fsp off ((o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs) := by
  have hsplit1 :
      memRegion (fsp + BitVec.ofNat 64 off) (localsBound cs - off) =
        memRegion (fsp + BitVec.ofNat 64 off) (o - off) ∗
          memRegion (fsp + BitVec.ofNat 64 o) (localsBound cs - o) := by
    refine ProofLib.memRegion_split' (n := o - off) (k := localsBound cs - o)
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  have hsplit2 :
      memRegion (fsp + BitVec.ofNat 64 o) (localsBound cs - o) =
        memRegion (fsp + BitVec.ofNat 64 o) n ∗
          memRegion (fsp + BitVec.ofNat 64 (o + n)) (localsBound cs - (o + n)) := by
    refine ProofLib.memRegion_split' (n := n) (k := localsBound cs - (o + n))
      (by omega) ?_ (by omega)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  cases cs with
  | nil =>
    simp only [localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [localsFrom, hsplit1, hsplit2]
  | cons c cs' =>
    rcases c with ⟨o', n', P'⟩
    simp only [localsBound] at hhi hbnd hsplit1 hsplit2
    simp only [localsFrom, hsplit1, hsplit2]
    ac_rfl

private theorem localsFrom_carve_after (fsp : BitVec 64) (off : Nat)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd off cs₁ ≤ o)
    (hhi : o + n ≤ localsBound cs₂)
    (hbnd : localsBound cs₂ ≤ 0x480) :
    localsFrom fsp off (cs₁ ++ cs₂) =
      localsFrom fsp off (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) := by
  induction cs₁ generalizing off with
  | nil =>
    exact localsFrom_carve_region fsp off o n cs₂ hlo hhi hbnd
  | cons c cs₁ ih =>
    rcases c with ⟨o₁, n₁, P₁⟩
    simp only [List.cons_append, localsFrom]
    rw [ih (o₁ + n₁) hlo]

/-- Carve `(o, n, memRegion (fsp + BitVec.ofNat 64 o) n)` at any gap inside `locals fsp (cs₁ ++ cs₂)`. -/
theorem locals_carve_region (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o n : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd 0 cs₁ ≤ o := by simp [localsEnd])
    (hhi : o + n ≤ localsBound cs₂ := by simp [localsBound])
    (hbnd : localsBound cs₂ ≤ 0x480 := by simp [localsBound]) :
    locals fsp (cs₁ ++ cs₂) =
      locals fsp (cs₁ ++ (o, n, memRegion (fsp + BitVec.ofNat 64 o) n) :: cs₂) :=
  localsFrom_carve_after fsp 0 cs₁ o n cs₂ hlo hhi hbnd

/-- Carve an 8-byte `cell fsp o v` with existential `v` out of any gap of `locals`. -/
theorem locals_carve_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd 0 cs₁ ≤ o := by simp [localsEnd])
    (hhi : o + 8 ≤ localsBound cs₂ := by simp [localsBound])
    (hbnd : localsBound cs₂ ≤ 0x480 := by simp [localsBound]) :
    locals fsp (cs₁ ++ cs₂) =
      ∃∗ v : BitVec 64, locals fsp (cs₁ ++ cell fsp o v :: cs₂) := by
  rw [locals_carve_region fsp cs₁ o 8 cs₂ hlo hhi hbnd,
    locals_focus fsp cs₁ o 8 _ cs₂, ProofLib.memRegion_eight, sepExists_sepConj_left]
  congr 1; funext v
  exact (locals_focus fsp cs₁ o 8 _ cs₂).symm

/-- Entailment from a 64-bit cell to its 8-byte `memRegion`. -/
theorem pointsTo64_entails_memRegion (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ memRegion a 8 := by
  rw [ProofLib.memRegion_eight]
  exact Entails.sepExists_right v (Entails.refl _)

/-- Forget one concrete `cell fsp o v` back into the surrounding uninitialized gap of `locals`. -/
theorem locals_forget_cell (fsp : BitVec 64)
    (cs₁ : List (Nat × Nat × SepProp)) (o : Nat) (v : BitVec 64)
    (cs₂ : List (Nat × Nat × SepProp))
    (hlo : localsEnd 0 cs₁ ≤ o := by simp [localsEnd])
    (hhi : o + 8 ≤ localsBound cs₂ := by simp [localsBound])
    (hbnd : localsBound cs₂ ≤ 0x480 := by simp [localsBound]) :
    locals fsp (cs₁ ++ cell fsp o v :: cs₂) ⊢ locals fsp (cs₁ ++ cs₂) := by
  rw [locals_carve_cell fsp cs₁ o cs₂ hlo hhi hbnd]
  exact Entails.sepExists_right v (Entails.refl _)

/-- Forget all owned pieces in a well-formed `localsFrom` list once each piece entails its `memRegion`. -/
theorem localsFrom_to_memRegion (fsp : BitVec 64) (off : Nat)
    (cs : List (Nat × Nat × SepProp))
    (hwf : LocalsWF off cs)
    (hent : ∀ o n P, (o, n, P) ∈ cs → P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n) :
    localsFrom fsp off cs ⊢ memRegion (fsp + BitVec.ofNat 64 off) (0x480 - off) := by
  induction cs generalizing off with
  | nil => exact Entails.refl _
  | cons c cs ih =>
    rcases c with ⟨o, n, P⟩
    rcases hwf with ⟨hlo, hwf'⟩
    have hP := hent o n P (.head _)
    have htail := ih (o + n) hwf' (fun o' n' P' hm => hent o' n' P' (.tail _ hm))
    simp only [localsFrom]
    refine Entails.trans (sepConj_mono (Entails.refl _) (sepConj_mono hP htail)) ?_
    exact Entails.of_eq (localsFrom_carve_region fsp off o n [] hlo hwf'.le_top (by decide)).symm

/-- Collapse a well-formed `locals fsp cs` into `memRegion fsp 0x480`. -/
theorem locals_to_memRegion (fsp : BitVec 64)
    (cs : List (Nat × Nat × SepProp))
    (hwf : LocalsWF 0 cs := by simp [LocalsWF])
    (hent : ∀ o n P, (o, n, P) ∈ cs → P ⊢ memRegion (fsp + BitVec.ofNat 64 o) n) :
    locals fsp cs ⊢ memRegion fsp 0x480 := by
  have h := localsFrom_to_memRegion fsp 0 cs hwf hent
  simpa only [locals, BitVec.add_zero, Nat.sub_zero] using h

theorem callCells_to_memRegion (fsp : BitVec 64) (w : CallW) :
    locals fsp (callCells fsp w) ⊢ memRegion fsp 0x480 := by
  refine locals_to_memRegion fsp (callCells fsp w) (by simp [LocalsWF]) ?_
  intro o n P hm
  simp only [callCells, cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact pointsTo64_entails_memRegion _ _

theorem m4Cells_to_memRegion (fsp : BitVec 64) (w : CallW) (inPtr : BitVec 64) (coinsLen : Nat) :
    locals fsp (m4Cells fsp w inPtr coinsLen) ⊢ memRegion fsp 0x480 := by
  refine locals_to_memRegion fsp (m4Cells fsp w inPtr coinsLen) (by simp [LocalsWF]) ?_
  intro o n P hm
  simp only [m4Cells, cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact pointsTo64_entails_memRegion _ _

theorem m6Cells_to_memRegion (fsp outCap outPtr outLen inCap inPtr : BitVec 64) :
    locals fsp (m6Cells fsp outCap outPtr outLen inCap inPtr) ⊢ memRegion fsp 0x480 := by
  refine locals_to_memRegion fsp (m6Cells fsp outCap outPtr outLen inCap inPtr) (by simp [LocalsWF]) ?_
  intro o n P hm
  simp only [m6Cells, cell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact pointsTo64_entails_memRegion _ _

/-! ## 2. `mainSaved` Helpers -/

/-- Canonical `s0.sp - N#64` form of `mainSaved s0`, matching `bv_sub_add_lit` normalization. -/
theorem mainSaved_eq_sub (s0 : State) :
    mainSaved s0 =
      ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗
      ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
      ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
      ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
      ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
      ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
      ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
      ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
      ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
      ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
      ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
  dsimp only [mainSaved]
  rw [BitVec.add_zero (s0.sp - 0x60#64),
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x08,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x10,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x18,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x20,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x28,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x30,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x38,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x40,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x48,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x50,
      ProofLib.bv_sub_add_lit s0.sp 0x60 0x58]

/-- Forget register values in `mainSaved s0` back to `cells (s0.sp - 0x60#64) 12`. -/
theorem mainSaved_entails_cells (s0 : State) :
    mainSaved s0 ⊢ cells (s0.sp - 0x60#64) 12 := by
  rw [mainSaved_eq_sub]
  cells_unfold
  exact
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ <|
    Entails.sepExists_right _ (Entails.refl _)

/-- Forget `mainSaved s0` back to `memRegion (s0.sp - 0x60#64) 0x60`. -/
theorem mainSaved_entails_memRegion (s0 : State) :
    mainSaved s0 ⊢ memRegion (s0.sp - 0x60#64) 0x60 := by
  rw [show (0x60 : Nat) = 8 * 12 by rfl, ProofLib.memRegion_cells (s0.sp - 0x60#64) 12 (by decide)]
  exact mainSaved_entails_cells s0

/-- Assemble `CalleeSavedPreserved s0 sf` from callee-saved GPR equalities and `calleeSavedVRegs`. -/
theorem calleeSavedPreserved_of_regs {s0 sf : State}
    (hx19 : sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5))
    (hx20 : sf.readReg64 (.gpr 20#5) = s0.readReg64 (.gpr 20#5))
    (hx21 : sf.readReg64 (.gpr 21#5) = s0.readReg64 (.gpr 21#5))
    (hx22 : sf.readReg64 (.gpr 22#5) = s0.readReg64 (.gpr 22#5))
    (hx23 : sf.readReg64 (.gpr 23#5) = s0.readReg64 (.gpr 23#5))
    (hx24 : sf.readReg64 (.gpr 24#5) = s0.readReg64 (.gpr 24#5))
    (hx25 : sf.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5))
    (hx26 : sf.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5))
    (hx27 : sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5))
    (hx28 : sf.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5))
    (hfp : sf.readReg64 .fp = s0.readReg64 .fp)
    (hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0) :
    CalleeSavedPreserved s0 sf := by
  simp only [calleeSavedVRegs] at hvregs
  simp only [CalleeSavedPreserved, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hfp, hvregs, and_self]

/-! ## 3. `stackAt` Split, Memory Disjointness Bounds, and Frame Merge -/

/-- Split off the bottom `d` bytes of `stackAt sp (n + d)`. -/
theorem stackAt_split_bottom_open (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = memRegion (sp - BitVec.ofNat 64 (n + d)) d ∗ stackAt sp n :=
  ProofLib.stackAt_split_bottom sp n d h

/-- Split `stackAt sp m` (`n ≤ m ≤ 2 ^ 64`) into `memRegion (sp - m) (m - n) ∗ stackAt sp n`. -/
theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

/-- Split `stackAt sp stk` at `main`'s entry into the 12 callee-save slots, `locals ... []`,
and the sub-callee stack `stackAt (sp - 0x4e0) (stk - 0x4e0)`. -/
theorem stackAt_mainFrame_split (sp : BitVec 64) {stk : Nat}
    (hstk : mainFrameSize ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      cells (sp - 0x60#64) 12 ∗
      locals (sp - BitVec.ofNat 64 mainFrameSize) [] ∗
      stackAt (sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) := by
  rw [stackAt_split_ge sp hstk hstk64]
  have hframe :
      stackAt sp mainFrameSize =
        locals (sp - BitVec.ofNat 64 mainFrameSize) [] ∗ cells (sp - 0x60#64) 12 := by
    simp only [stackAt, locals_nil, mainFrameSize]
    rw [ProofLib.memRegion_split' (b := sp - 0x4e0#64) (b' := sp - 0x60#64)
          (N := 0x4e0) (n := 0x480) (k := 0x60) (by decide)
          (ProofLib.bv_sub_add_lit sp 0x4e0 0x480).symm (by decide),
        show (0x60 : Nat) = 8 * 12 by rfl,
        ProofLib.memRegion_cells (sp - 0x60#64) 12 (by decide)]
  have hsub_sp :
      sp - BitVec.ofNat 64 stk =
        sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 (stk - mainFrameSize) := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    congr 2; omega
  rw [hframe, hsub_sp]
  dsimp only [stackAt]
  ac_rfl

/-- Any concrete memory containing `mainSaved s0` and `stackAt (s0.sp - mainFrameSize) sub`
satisfies `sub + mainFrameSize ≤ 2 ^ 64` (by disjointness with cell `s0.sp - 0x08#64`). -/
theorem subStack_add_mainFrameSize_le_of_mainSaved {m : Memory} {s0 : State}
    {sub : Nat} {R : SepProp}
    (hm : m ⊨ mainSaved s0 ∗ stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) sub ∗ R) :
    sub + mainFrameSize ≤ 2 ^ 64 := by
  by_cases hsub0 : sub = 0
  · simp [hsub0, mainFrameSize]
  · have hlast : mainSaved s0 ⊢ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ anyHeap := by
      rw [mainSaved_eq_sub]
      let rest11 : SepProp :=
        ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗
        ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
        ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
        ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
        ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
        ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
        ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
        ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
        ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
        ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5))
      have hassoc11 :
          ((s0.sp - 0x60#64) ↦₆₄ s0.readReg64 .fp) ∗
          ((s0.sp - 0x58#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((s0.sp - 0x50#64) ↦₆₄ s0.readReg64 (.gpr 28#5)) ∗
          ((s0.sp - 0x48#64) ↦₆₄ s0.readReg64 (.gpr 27#5)) ∗
          ((s0.sp - 0x40#64) ↦₆₄ s0.readReg64 (.gpr 26#5)) ∗
          ((s0.sp - 0x38#64) ↦₆₄ s0.readReg64 (.gpr 25#5)) ∗
          ((s0.sp - 0x30#64) ↦₆₄ s0.readReg64 (.gpr 24#5)) ∗
          ((s0.sp - 0x28#64) ↦₆₄ s0.readReg64 (.gpr 23#5)) ∗
          ((s0.sp - 0x20#64) ↦₆₄ s0.readReg64 (.gpr 22#5)) ∗
          ((s0.sp - 0x18#64) ↦₆₄ s0.readReg64 (.gpr 21#5)) ∗
          ((s0.sp - 0x10#64) ↦₆₄ s0.readReg64 (.gpr 20#5)) ∗
          ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) =
          rest11 ∗ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) := by
        simp only [rest11, sepConj_assoc]
      rw [hassoc11, sepConj_comm]
      exact sepConj_mono_right (ProofLib.entails_anyHeap _)
    have hm1 := Satisfies.mono (sepConj_mono_left hlast) hm
    have hm2 :
        m ⊨ ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
          (stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) sub ∗ (anyHeap ∗ R)) := by
      have heq :
          (((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗ anyHeap) ∗
            stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) sub ∗ R =
          ((s0.sp - 0x08#64) ↦₆₄ s0.readReg64 (.gpr 19#5)) ∗
            (stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) sub ∗ (anyHeap ∗ R)) := by
        ac_rfl
      rwa [heq] at hm1
    have hd := disjointRegions_of_coversRegion (by decide) (Nat.pos_of_ne_zero hsub0)
      (IsBlock.pointsTo64 (s0.sp - 0x08#64) (s0.readReg64 (.gpr 19#5))).covers
      (IsBlock.memRegion ((s0.sp - BitVec.ofNat 64 mainFrameSize) - BitVec.ofNat 64 sub) sub).covers
      hm2
    have h1 := hd.1
    have h2 := hd.2
    have hring : ∀ (x y z : BitVec 64), (x + y) - (x - z) = z + y := by
      intro x y z
      calc
        (x + y) - (x - z) = (x + -x) + (z + y) := by
          simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg]
          ac_rfl
        _ = 0#64 + (z + y) := by rw [BitVec.add_neg_eq_sub, BitVec.sub_self]
        _ = z + y := BitVec.zero_add _
    have heq2 :
        (s0.sp - 0x08#64) - (s0.sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 sub) =
          BitVec.ofNat 64 (sub + 0x4d8) := by
      simp only [mainFrameSize]
      rw [← ProofLib.bv_sub_add_lit s0.sp 0x4e0 0x4d8, hring, ← BitVec.ofNat_add]
    have heq1 :
        (s0.sp - BitVec.ofNat 64 mainFrameSize - BitVec.ofNat 64 sub) - (s0.sp - 0x08#64) =
          - BitVec.ofNat 64 (sub + 0x4d8) := by
      have hneg_sub : ∀ (a b : BitVec 64), a - b = -(b - a) := by
        intro a b
        simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_comm]
      rw [hneg_sub, heq2]
    rw [heq2, BitVec.toNat_ofNat] at h2
    rw [heq1, BitVec.toNat_neg, BitVec.toNat_ofNat] at h1
    have hsub_lt : sub + 0x4d8 < 2 ^ 64 := by
      by_contra hge
      have hlt64 : sub < 2 ^ 64 := by
        have := Nat.mod_lt (sub + 0x4d8) (show 0 < 2 ^ 64 by decide)
        omega
      omega
    have hmod : (sub + 0x4d8) % 2 ^ 64 = sub + 0x4d8 := Nat.mod_eq_of_lt hsub_lt
    rw [hmod] at h1 h2
    have hpos : 0 < sub + 0x4d8 := by omega
    have hneg_mod : (2 ^ 64 - (sub + 0x4d8)) % 2 ^ 64 = 2 ^ 64 - (sub + 0x4d8) :=
      Nat.mod_eq_of_lt (by omega)
    rw [hneg_mod] at h1
    simp only [mainFrameSize]
    omega

/-- Unconditional `stk ≤ 2 ^ 64` bound extracted whenever `mainSaved s0` coexists with
`stackAt (s0.sp - mainFrameSize) (stk - mainFrameSize)`. -/
theorem stk_le_two_pow_64_of_mainSaved {m : Memory} {s0 : State} {stk : Nat} {R : SepProp}
    (hstk : mainFrameSize ≤ stk)
    (hm : m ⊨ mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ R) :
    stk ≤ 2 ^ 64 := by
  have h := subStack_add_mainFrameSize_le_of_mainSaved hm
  omega

/-- Introduce `stk ≤ 2 ^ 64` inside any `SepWPp` goal whose precondition frames `mainSaved s0` and
`stackAt (s0.sp - mainFrameSize) (stk - mainFrameSize)` (no external `hstk64` hypothesis needed). -/
theorem sepWPp_with_stk_le_two_pow_64 {prog : Program} {ret : BitVec 64} {s0 s : State}
    {stk : Nat} {P F : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hstk : mainFrameSize ≤ stk)
    (hfoc : P ⊢ mainSaved s0 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ F)
    (hk : stk ≤ 2 ^ 64 → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  have hm' :
      s.mem ⊨ mainSaved s0 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗ (F ∗ R) := by
    simpa only [sepConj_assoc] using Satisfies.mono (sepConj_mono_left hfoc) hm
  exact hk (stk_le_two_pow_64_of_mainSaved hstk hm') R hm hL

/-- Reassemble `stackAt s0.sp stk` from `mainSaved s0`, the `0x480` locals region, and
`stackAt (s0.sp - mainFrameSize) (stk - mainFrameSize)`. -/
theorem mainFrame_merge {s0 : State} {stk : Nat}
    (hstk : mainFrameSize ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
      stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ⊢
      stackAt s0.sp stk := by
  rw [stackAt_mainFrame_split s0.sp hstk hstk64, locals_nil]
  exact sepConj_mono_left (mainSaved_entails_cells s0)

/-- Entailment from `retMem A s0 stk` to `main`'s postcondition memory shape (`stk ≤ 2 ^ 64` comes
from `sepWPp_with_stk_le_two_pow_64` at runtime). -/
theorem retMem_entails_post (A : RustAlloc) (s0 : State) {stk : Nat}
    (hstk : mainFrameSize ≤ stk) (hstk64 : stk ≤ 2 ^ 64) :
    retMem A s0 stk ⊢ stackAt s0.sp stk ∗ A.pool ∗ anyHeap := by
  unfold retMem
  have hassoc :
      mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize) ∗
        A.pool ∗ anyHeap =
      (mainSaved s0 ∗ memRegion (s0.sp - BitVec.ofNat 64 mainFrameSize) 0x480 ∗
        stackAt (s0.sp - BitVec.ofNat 64 mainFrameSize) (stk - mainFrameSize)) ∗
        (A.pool ∗ anyHeap) := by
    simp only [sepConj_assoc]
  rw [hassoc]
  exact sepConj_mono_left (mainFrame_merge hstk hstk64)

/-! ## 4. `InMain` Alignment and Step Helpers -/

/-- When `s0.spAligned = true`, every state `s` in `InMain` has `s.spAligned = true`. -/
theorem InMain.spAligned_of_s0 {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat}
    (hs : InMain img ext s0 s k) (hsp0 : s0.spAligned = true) :
    s.spAligned = true := by
  simp only [State.spAligned, hs.sp, mainFrameSize]
  exact ProofLib.spAligned_sub s0.sp 0x4e0#64 hsp0

/-- Equivalence: `s.spAligned = true` in `InMain` iff `s0.spAligned = true`. -/
theorem InMain.spAligned_iff {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (hs : InMain img ext s0 s k) :
    s.spAligned = true ↔ s0.spAligned = true := by
  refine ⟨fun h => ?_, hs.spAligned_of_s0⟩
  have heq : s0.sp = s.sp - (-0x4e0#64) := by
    calc
      s0.sp = s0.sp + (-0x4e0#64 + 0x4e0#64) := (BitVec.add_zero s0.sp).symm
      _ = (s0.sp + -0x4e0#64) + 0x4e0#64 := (BitVec.add_assoc _ _ _).symm
      _ = s.sp - (-0x4e0#64) := by
        rw [hs.sp, mainFrameSize]
        simp only [BitVec.sub_eq_add_neg, BitVec.neg_neg]
  simp only [State.spAligned] at h ⊢
  rw [heq]
  exact ProofLib.spAligned_sub s.sp (-0x4e0#64) h

/-- Every state `s` in `InMain` has `s.spAligned = true` (from `hs.spAligned : s0.spAligned = true`). -/
theorem InMain.spAligned_state {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s : State} {k : Nat} (hs : InMain img ext s0 s k) :
    s.spAligned = true :=
  hs.spAligned_of_s0 hs.spAligned

/-- Assemble `InMain` after a straight-line step sequence or call returning with `ImgCallInv`. -/
theorem InMain.mk_step {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMain img ext s0 s k)
    (hpc : s'.pc = mPc img ext k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hfp : s'.readReg64 .fp = s.readReg64 .fp)
    (hinv : ImgCallInv img s')
    (hvregs : calleeSavedVRegs s' = calleeSavedVRegs s) :
    InMain img ext s0 s' k' where
  pc := hpc
  run := hrun
  sp := hsp.trans hs.sp
  fp := hfp.trans hs.fp
  inv := hinv
  vregs := hvregs.trans hs.vregs
  spAligned := hs.spAligned

/-- Assemble `InMain` across a `subroutine_ok` callee return (`CalleeSavedPreserved s s'`). -/
theorem InMain.of_call {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s s' : State} {k k' : Nat}
    (hs : InMain img ext s0 s k)
    (hpc : s'.pc = mPc img ext k')
    (hrun : s'.status = .Running)
    (hsp : s'.sp = s.sp)
    (hcs : CalleeSavedPreserved s s')
    (hkf : s.mem.KeepsFrozen s'.mem)
    (hsym : s'.symtab = s.symtab) :
    InMain img ext s0 s' k' where
  pc := hpc
  run := hrun
  sp := hsp.trans hs.sp
  fp := hcs.2.2.2.2.2.2.2.2.2.2.1.trans hs.fp
  inv := ⟨Obj.Image.FrozenLoaded.of_keepsFrozen hs.inv.1 hkf, hsym.trans hs.inv.2⟩
  vregs := hcs.2.2.2.2.2.2.2.2.2.2.2.trans hs.vregs
  spAligned := hs.spAligned

end CryptoVerification.SignalSession.Cli.MainHops
