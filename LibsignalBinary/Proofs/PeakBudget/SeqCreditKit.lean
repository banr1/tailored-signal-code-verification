/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Heap.Fine.ClientBounds

/-!
# Sequential Fine-Credit Combinators and `sc = 63` Deallocation Cancellation

Combinator library for per-phase CLI live-heap peak bounds, parametric in
`(M : AllocCostModel) [HasFineReallocCredit M]` and preserving binary call order without event
reordering:
1. Sequential and iterative envelopes (`IterSeqEnv`, `ConcatEnv`, `IterConcatEnv`) extending
   `Heap.SeqEnv`, `FreeOnlyEvs`, and `FitsEnv`.
2. State-threaded symbolic credit specification `PhaseCreditSpec M Env Δcum Δlive Δpeak maxReq`
   and closure combinators (`.nil`, `.mono`, `.of_imp`, `.or`, `.seq`, `.concat`, `.iter`,
   `.iter_const`, `.iter_zero_live`).
3. Deallocation-only envelopes (`.freeOnly` under `FreeNonInc M`, `.freeOnly_align16`).
4. Exact-order `sc = 63` large alloc/free cancellation (`DeallocCreditSpec`,
   `concat_dealloc_cancel`, `largeAllocFree_cancel`, `largeAllocBodyFree_cancel`).
5. Whole-trace `evalLog` and `footprint_le` corollaries at `st0 = M.init`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SeqCreditKit

open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits
  FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small stepEvents_rustAlloc_large
  stepEvents_rustDealloc_small stepEvents_rustDealloc_large
  stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
  stepEvents_rustRealloc_large_large stepEvents_rustRealloc_large_small
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepReq eventStepAlign
)

/-! ## 1. Sequential and Iterative Envelopes in Call Order -/

/-- Iterative left-to-right sequential envelope over `List α` using `Heap.SeqEnv`: preserves call
order and includes prefix early-exits so `FitsEnv` projects step-by-step. -/
def IterSeqEnv {α : Type} (Step : α → List AllocEvent → Prop) :
    List α → List AllocEvent → Prop
  | [], evs => evs = []
  | x :: xs, evs => SeqEnv (Step x) (IterSeqEnv Step xs) evs

/-- Strict left-to-right concatenation envelope (`evs = evs₁ ++ evs₂`) where both phases run to
completion in exact execution order (without `SeqEnv`'s early-exit `Or.inl` disjunct). Used when
a trailing deallocation phase unconditionally runs and cancels a preceding large allocation. -/
def ConcatEnv (E₁ E₂ : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  ∃ evs₁ evs₂, evs = evs₁ ++ evs₂ ∧ E₁ evs₁ ∧ E₂ evs₂

/-- Strict left-to-right concatenation over `List α` where every element's phase completes. -/
def IterConcatEnv {α : Type} (Step : α → List AllocEvent → Prop) :
    List α → List AllocEvent → Prop
  | [], evs => evs = []
  | x :: xs, evs => ConcatEnv (Step x) (IterConcatEnv Step xs) evs

/-- Deallocation-only event list with standard Rust `al ≤ 16` alignments. -/
def FreeOnlyAlign16Evs (evs : List AllocEvent) : Prop :=
  ∀ ev ∈ evs, ∃ al, al ≤ 16 ∧ ∃ sz, ev = .free al sz

theorem SeqEnv.mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    SeqEnv E₁' E₂' evs := by
  rcases h with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  · exact Or.inl (h1 evs hE1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

/-- Left-reassociation of `SeqEnv` in exact execution order (`E₁; (E₂; E₃)` implies `(E₁; E₂); E₃`). -/
theorem SeqEnv.assoc_left {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv E₁ (SeqEnv E₂ E₃) evs) :
    SeqEnv (SeqEnv E₁ E₂) E₃ evs := by
  rcases h with h1 | ⟨evs₁, evs₂₃, rfl, h1, h23⟩
  · exact Or.inl (Or.inl h1)
  · rcases h23 with h2 | ⟨evs₂, evs₃, rfl, h2, h3⟩
    · exact Or.inl (Or.inr ⟨evs₁, evs₂₃, rfl, h1, h2⟩)
    · exact Or.inr ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
        Or.inr ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩

theorem ConcatEnv.append {E₁ E₂ : List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent}
    (h1 : E₁ evs₁) (h2 : E₂ evs₂) :
    ConcatEnv E₁ E₂ (evs₁ ++ evs₂) :=
  ⟨evs₁, evs₂, rfl, h1, h2⟩

theorem ConcatEnv.toSeqEnv {E₁ E₂ : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : ConcatEnv E₁ E₂ evs) :
    SeqEnv E₁ E₂ evs :=
  Or.inr h

theorem ConcatEnv.mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h1 : ∀ evs, E₁ evs → E₁' evs) (h2 : ∀ evs, E₂ evs → E₂' evs)
    {evs : List AllocEvent} (h : ConcatEnv E₁ E₂ evs) :
    ConcatEnv E₁' E₂' evs := by
  obtain ⟨evs₁, evs₂, rfl, hE1, hE2⟩ := h
  exact ⟨evs₁, evs₂, rfl, h1 evs₁ hE1, h2 evs₂ hE2⟩

theorem ConcatEnv.nil_left_iff {E : List AllocEvent → Prop} {evs : List AllocEvent} :
    ConcatEnv (· = []) E evs ↔ E evs := by
  constructor
  · rintro ⟨evs₁, evs₂, rfl, rfl, hE⟩
    simpa using hE
  · intro hE
    exact ⟨[], evs, rfl, rfl, hE⟩

theorem ConcatEnv.nil_right_iff {E : List AllocEvent → Prop} {evs : List AllocEvent} :
    ConcatEnv E (· = []) evs ↔ E evs := by
  constructor
  · rintro ⟨evs₁, evs₂, rfl, hE, rfl⟩
    simpa using hE
  · intro hE
    exact ⟨evs, [], (List.append_nil evs).symm, hE, rfl⟩

theorem ConcatEnv.assoc_iff {E₁ E₂ E₃ : List AllocEvent → Prop} {evs : List AllocEvent} :
    ConcatEnv (ConcatEnv E₁ E₂) E₃ evs ↔ ConcatEnv E₁ (ConcatEnv E₂ E₃) evs := by
  constructor
  · rintro ⟨evs₁₂, evs₃, rfl, ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩
    exact ⟨evs₁, evs₂ ++ evs₃, List.append_assoc evs₁ evs₂ evs₃, h1, ⟨evs₂, evs₃, rfl, h2, h3⟩⟩
  · rintro ⟨evs₁, evs₂₃, rfl, h1, ⟨evs₂, evs₃, rfl, h2, h3⟩⟩
    exact ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
      ⟨evs₁, evs₂, rfl, h1, h2⟩, h3⟩

theorem IterSeqEnv.nil {α : Type} (Step : α → List AllocEvent → Prop) :
    IterSeqEnv Step [] [] :=
  rfl

theorem IterSeqEnv.nil_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {evs : List AllocEvent} :
    IterSeqEnv Step [] evs ↔ evs = [] :=
  Iff.rfl

theorem IterSeqEnv.cons_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {xs : List α} {evs : List AllocEvent} :
    IterSeqEnv Step (x :: xs) evs ↔ SeqEnv (Step x) (IterSeqEnv Step xs) evs :=
  Iff.rfl

theorem IterSeqEnv.cons_inl {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {xs : List α} {evs : List AllocEvent} (hx : Step x evs) :
    IterSeqEnv Step (x :: xs) evs :=
  Or.inl hx

theorem IterSeqEnv.cons_append {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {xs : List α} {evs₁ evs₂ : List AllocEvent}
    (hx : Step x evs₁) (hxs : IterSeqEnv Step xs evs₂) :
    IterSeqEnv Step (x :: xs) (evs₁ ++ evs₂) :=
  SeqEnv.append hx hxs

theorem IterSeqEnv.singleton {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent} (hx : Step x evs) :
    IterSeqEnv Step [x] evs :=
  Or.inl hx

theorem IterSeqEnv.singleton_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent} :
    IterSeqEnv Step [x] evs ↔ Step x evs := by
  constructor
  · rintro (hx | ⟨evs₁, evs₂, rfl, hx, rfl⟩)
    · exact hx
    · simpa using hx
  · exact Or.inl

theorem IterSeqEnv.mono {α : Type} {Step₁ Step₂ : α → List AllocEvent → Prop}
    {xs : List α} (hstep : ∀ x ∈ xs, ∀ evs, Step₁ x evs → Step₂ x evs) :
    ∀ {evs : List AllocEvent}, IterSeqEnv Step₁ xs evs → IterSeqEnv Step₂ xs evs := by
  induction xs with
  | nil =>
    intro evs h
    exact h
  | cons x xs ih =>
    intro evs h
    exact SeqEnv.mono
      (hstep x List.mem_cons_self)
      (fun evs' h' => ih (fun y hy => hstep y (List.mem_cons_of_mem x hy)) h')
      h

/-- Decomposes `IterSeqEnv Step (xs ++ ys)` into `SeqEnv (IterSeqEnv Step xs) (IterSeqEnv Step ys)`
in exact execution order for arbitrary `xs, ys : List α`. -/
theorem IterSeqEnv.to_seqEnv_append {α : Type} {Step : α → List AllocEvent → Prop}
    (xs ys : List α) :
    ∀ {evs : List AllocEvent},
      IterSeqEnv Step (xs ++ ys) evs →
      SeqEnv (IterSeqEnv Step xs) (IterSeqEnv Step ys) evs := by
  induction xs with
  | nil =>
    intro evs h
    exact Or.inr ⟨[], evs, rfl, rfl, h⟩
  | cons x xs ih =>
    intro evs h
    rcases h with hx | ⟨evs₁, evs_rest, rfl, hx, hrest⟩
    · exact Or.inl (Or.inl hx)
    · rcases ih hrest with hxs | ⟨evs₂, evs₃, rfl, hxs, hys⟩
      · exact Or.inl (Or.inr ⟨evs₁, evs_rest, rfl, hx, hxs⟩)
      · exact Or.inr ⟨evs₁ ++ evs₂, evs₃, (List.append_assoc evs₁ evs₂ evs₃).symm,
          Or.inr ⟨evs₁, evs₂, rfl, hx, hxs⟩, hys⟩

/-- Non-empty prefix lift for `IterSeqEnv`: any early-exiting or completed trace of a non-empty
prefix `xs` is a valid trace of `xs ++ ys`. -/
theorem IterSeqEnv.prefix_of_ne_nil {α : Type} {Step : α → List AllocEvent → Prop}
    {xs : List α} (ys : List α) (hne : xs ≠ []) :
    ∀ {evs : List AllocEvent}, IterSeqEnv Step xs evs → IterSeqEnv Step (xs ++ ys) evs := by
  induction xs with
  | nil => exact False.elim (hne rfl)
  | cons x xs ih =>
    intro evs h
    rcases h with hx | ⟨evs₁, evs₂, rfl, hx, hxs⟩
    · exact Or.inl hx
    · cases xs with
      | nil =>
        cases hxs
        rw [List.append_nil]
        exact Or.inl hx
      | cons x' xs' =>
        exact Or.inr ⟨evs₁, evs₂, rfl, hx, ih (List.cons_ne_nil x' xs') hxs⟩

theorem IterConcatEnv.nil {α : Type} (Step : α → List AllocEvent → Prop) :
    IterConcatEnv Step [] [] :=
  rfl

theorem IterConcatEnv.nil_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {evs : List AllocEvent} :
    IterConcatEnv Step [] evs ↔ evs = [] :=
  Iff.rfl

theorem IterConcatEnv.cons_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {xs : List α} {evs : List AllocEvent} :
    IterConcatEnv Step (x :: xs) evs ↔ ConcatEnv (Step x) (IterConcatEnv Step xs) evs :=
  Iff.rfl

theorem IterConcatEnv.cons_append {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {xs : List α} {evs₁ evs₂ : List AllocEvent}
    (hx : Step x evs₁) (hxs : IterConcatEnv Step xs evs₂) :
    IterConcatEnv Step (x :: xs) (evs₁ ++ evs₂) :=
  ⟨evs₁, evs₂, rfl, hx, hxs⟩

theorem IterConcatEnv.singleton {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent} (hx : Step x evs) :
    IterConcatEnv Step [x] evs :=
  ⟨evs, [], (List.append_nil evs).symm, hx, rfl⟩

theorem IterConcatEnv.singleton_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {x : α} {evs : List AllocEvent} :
    IterConcatEnv Step [x] evs ↔ Step x evs :=
  ConcatEnv.nil_right_iff

theorem IterConcatEnv.mono {α : Type} {Step₁ Step₂ : α → List AllocEvent → Prop}
    {xs : List α} (hstep : ∀ x ∈ xs, ∀ evs, Step₁ x evs → Step₂ x evs) :
    ∀ {evs : List AllocEvent}, IterConcatEnv Step₁ xs evs → IterConcatEnv Step₂ xs evs := by
  induction xs with
  | nil =>
    intro evs h
    exact h
  | cons x xs ih =>
    intro evs h
    exact ConcatEnv.mono
      (hstep x List.mem_cons_self)
      (fun evs' h' => ih (fun y hy => hstep y (List.mem_cons_of_mem x hy)) h')
      h

theorem IterConcatEnv.toIterSeqEnv {α : Type} {Step : α → List AllocEvent → Prop}
    {xs : List α} :
    ∀ {evs : List AllocEvent}, IterConcatEnv Step xs evs → IterSeqEnv Step xs evs := by
  induction xs with
  | nil =>
    intro evs h
    exact h
  | cons _ xs ih =>
    rintro evs ⟨evs₁, evs₂, rfl, hx, hxs⟩
    exact Or.inr ⟨evs₁, evs₂, rfl, hx, ih hxs⟩

theorem IterConcatEnv.append {α : Type} {Step : α → List AllocEvent → Prop}
    {xs ys : List α} {evs₁ evs₂ : List AllocEvent}
    (hxs : IterConcatEnv Step xs evs₁) (hys : IterConcatEnv Step ys evs₂) :
    IterConcatEnv Step (xs ++ ys) (evs₁ ++ evs₂) := by
  induction xs generalizing evs₁ with
  | nil =>
    cases hxs
    simpa using hys
  | cons _ xs ih =>
    obtain ⟨e₁, e_rest, rfl, hx, hrest⟩ := hxs
    rw [List.append_assoc]
    exact ⟨e₁, e_rest ++ evs₂, rfl, hx, ih hrest⟩

theorem IterConcatEnv.append_iff {α : Type} {Step : α → List AllocEvent → Prop}
    {xs ys : List α} {evs : List AllocEvent} :
    IterConcatEnv Step (xs ++ ys) evs ↔
      ConcatEnv (IterConcatEnv Step xs) (IterConcatEnv Step ys) evs := by
  induction xs generalizing evs with
  | nil =>
    simpa [IterConcatEnv] using ConcatEnv.nil_left_iff.symm
  | cons x xs ih =>
    constructor
    · rintro ⟨e₁, e_rest, rfl, hx, hrest⟩
      obtain ⟨e₂, e₃, rfl, hxs, hys⟩ := ih.mp hrest
      exact ⟨e₁ ++ e₂, e₃, (List.append_assoc e₁ e₂ e₃).symm,
        ⟨e₁, e₂, rfl, hx, hxs⟩, hys⟩
    · rintro ⟨_, e₃, rfl, ⟨e₁, e₂, rfl, hx, hxs⟩, hys⟩
      exact ⟨e₁, e₂ ++ e₃, List.append_assoc e₁ e₂ e₃,
        hx, ih.mpr ⟨e₂, e₃, rfl, hxs, hys⟩⟩

/-- Constructs `IterSeqEnv Step (xs ++ ys) (evs₁ ++ evs₂)` from a completed prefix `xs`
followed in exact order by a `ys` trace. -/
theorem IterSeqEnv.of_concat_append {α : Type} {Step : α → List AllocEvent → Prop}
    {xs ys : List α} {evs₁ evs₂ : List AllocEvent}
    (hxs : IterConcatEnv Step xs evs₁) (hys : IterSeqEnv Step ys evs₂) :
    IterSeqEnv Step (xs ++ ys) (evs₁ ++ evs₂) := by
  induction xs generalizing evs₁ with
  | nil =>
    cases hxs
    simpa using hys
  | cons _ xs ih =>
    obtain ⟨e₁, e_rest, rfl, hx, hrest⟩ := hxs
    rw [List.append_assoc]
    exact Or.inr ⟨e₁, e_rest ++ evs₂, rfl, hx, ih hrest⟩

/-- Project `FitsEnv` to the head element of `IterSeqEnv Step (x :: xs)`. -/
theorem FitsEnv.iterSeq_head {α : Type} {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Step : α → List AllocEvent → Prop} {x : α} {xs : List α}
    (h : FitsEnv M lim st (IterSeqEnv Step (x :: xs))) :
    FitsEnv M lim st (Step x) :=
  FitsEnv.seq_left h

/-- Advance `FitsEnv` past a completed head element `Step x evs₁` into `IterSeqEnv Step xs`. -/
theorem FitsEnv.iterSeq_tail {α : Type} {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {Step : α → List AllocEvent → Prop} {x : α} {xs : List α} {evs₁ : List AllocEvent}
    (h : FitsEnv M lim st (IterSeqEnv Step (x :: xs))) (hx : Step x evs₁) :
    FitsEnv M lim (M.stepEvents evs₁ st) (IterSeqEnv Step xs) :=
  FitsEnv.seq_right h hx

theorem FreeOnlyAlign16Evs.nil : FreeOnlyAlign16Evs [] := by
  intro _ h; nomatch h

theorem FreeOnlyAlign16Evs.singleton {al : Nat} (hal : al ≤ 16) (sz : Nat) :
    FreeOnlyAlign16Evs [.free al sz] := by
  intro ev hev
  rw [List.mem_singleton] at hev
  exact ⟨al, hal, sz, hev⟩

theorem FreeOnlyAlign16Evs.rustDealloc {al : Nat} (hal : al ≤ 16) (sz : Nat) :
    FreeOnlyAlign16Evs (rustDeallocEvents sz al) :=
  FreeOnlyAlign16Evs.singleton hal sz

theorem FreeOnlyAlign16Evs.append {evs₁ evs₂ : List AllocEvent}
    (h1 : FreeOnlyAlign16Evs evs₁) (h2 : FreeOnlyAlign16Evs evs₂) :
    FreeOnlyAlign16Evs (evs₁ ++ evs₂) := by
  intro ev hev
  rcases List.mem_append.mp hev with he1 | he2
  · exact h1 ev he1
  · exact h2 ev he2

theorem FreeOnlyAlign16Evs.toFreeOnlyEvs {evs : List AllocEvent}
    (h : FreeOnlyAlign16Evs evs) : FreeOnlyEvs evs := by
  intro ev hev
  obtain ⟨al, _, sz, heq⟩ := h ev hev
  exact ⟨al, sz, heq⟩

namespace Simp

@[scoped simp] theorem iterSeqEnv_nil {α : Type} (Step : α → List AllocEvent → Prop)
    (evs : List AllocEvent) :
    IterSeqEnv Step [] evs ↔ evs = [] := Iff.rfl

@[scoped simp] theorem iterSeqEnv_cons {α : Type} (Step : α → List AllocEvent → Prop)
    (x : α) (xs : List α) (evs : List AllocEvent) :
    IterSeqEnv Step (x :: xs) evs ↔ SeqEnv (Step x) (IterSeqEnv Step xs) evs := Iff.rfl

@[scoped simp] theorem iterConcatEnv_nil {α : Type} (Step : α → List AllocEvent → Prop)
    (evs : List AllocEvent) :
    IterConcatEnv Step [] evs ↔ evs = [] := Iff.rfl

@[scoped simp] theorem iterConcatEnv_cons {α : Type} (Step : α → List AllocEvent → Prop)
    (x : α) (xs : List α) (evs : List AllocEvent) :
    IterConcatEnv Step (x :: xs) evs ↔ ConcatEnv (Step x) (IterConcatEnv Step xs) evs := Iff.rfl

end Simp

/-! ## 2. `FreeNonInc` & `PhaseCreditSpec` Symbolic Peak/Credit Combinators -/

/-- Plain `Prop` hypothesis asserting that arbitrary-alignment `.free al sz` events never raise
`cumSmall`, `liveLarge`, or `peakLarge` (discharged on `fineCostModel` by
`SeqCreditKitLemmas.fineCostModel_freeNonInc` without needing `al ≤ 16` on `Heap.FreeOnlyEvs`). -/
def FreeNonInc (M : AllocCostModel) [HasFineReallocCredit M] : Prop :=
  ∀ (al sz : Nat) (st : M.σ),
    let st' := M.step (.free al sz) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st

/-- Bundled cost-model hypotheses for per-phase peak bounds: `FreeNonInc M`, affine small/large
allocation and metadata bounds (`hSmallAff`, `hLargeAff`, `hMeta`), and `0`-size-inclusive `al ≤ 16`
small-step transitions (`step_*_any`). Discharged on `fineCostModel` by
`SeqCreditKitLemmas.fineCostModel_modelHyps`. -/
structure ModelHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  /-- Arbitrary-alignment `.free al sz` events never raise `cumSmall`, `liveLarge`, or `peakLarge`. -/
  freeNonInc : FreeNonInc M
  /-- Small-class `.alloc` and `al ≤ 16` `.realloc` charges satisfy `≤ 2 * r + 9539`. -/
  hSmallAff : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
    HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 ∧
    HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539
  /-- Direct-`mmap` (`sc = 63`) byte weight satisfies `largeCost M r ≤ r + 8195`. -/
  hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
    HasFineReallocCredit.largeCost M r ≤ r + 8195
  /-- Out-of-line `meta_area` charge on `sc = 63` allocations satisfies `largeMetaCost M ≤ 122`. -/
  hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122
  /-- Small `.alloc req` including `req = 0` (`req ≤ smallMaxReq M`). -/
  step_alloc_small_any : ∀ {req : Nat} (st : M.σ),
    req ≤ HasFineReallocCredit.smallMaxReq M →
    let st' := M.step (.alloc req) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallAllocCost M req ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  /-- Small `.aligned al req` including `req = 0` (`al ≤ 16`, `req ≤ smallMaxReq M`). -/
  step_aligned_small_any : ∀ {al req : Nat} (st : M.σ),
    al ≤ 16 → req ≤ HasFineReallocCredit.smallMaxReq M →
    let st' := M.step (.aligned al req) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallAllocCost M req ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  /-- Quadrant S→S `.realloc al old new` including `old = 0` or `new = 0` (`al ≤ 16`). -/
  step_realloc_small_small_any : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → old ≤ HasFineReallocCredit.smallMaxReq M →
    new ≤ HasFineReallocCredit.smallMaxReq M →
    let st' := M.step (.realloc al old new) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallReallocCost M new ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  /-- Quadrant S→L `.realloc al old new` including `old = 0` (`al ≤ 16`). -/
  step_realloc_small_large_any : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → old ≤ HasFineReallocCredit.smallMaxReq M →
    HasFineReallocCredit.smallMaxReq M < new →
    let st' := M.step (.realloc al old new) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.largeMetaCost M ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new)
  /-- Quadrant L→S `.realloc al old new` including `new = 0` (`al ≤ 16`). -/
  step_realloc_large_small_any : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → HasFineReallocCredit.smallMaxReq M < old →
    new ≤ HasFineReallocCredit.smallMaxReq M →
    let st' := M.step (.realloc al old new) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallReallocCost M new ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - HasFineReallocCredit.largeCost M old ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st

theorem ModelHyps.smallAlloc_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {r : Nat} (hr : r ≤ HasFineReallocCredit.smallMaxReq M) :
    HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539 :=
  (hM.hSmallAff r hr).1

theorem ModelHyps.smallRealloc_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {r : Nat} (hr : r ≤ HasFineReallocCredit.smallMaxReq M) :
    HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539 :=
  (hM.hSmallAff r hr).2

theorem ModelHyps.largeCost_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {r : Nat} (hr : HasFineReallocCredit.smallMaxReq M < r) :
    HasFineReallocCredit.largeCost M r ≤ r + 8195 :=
  hM.hLargeAff r hr

theorem ModelHyps.meta_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    HasFineReallocCredit.largeMetaCost M ≤ 122 :=
  hM.hMeta

/-- Uniform single-event affine step bound under `ModelHyps M` for any non-`.free` event with
`eventStepReq ev ≤ maxReq` and `eventStepAlign ev ≤ 16` (including `0`-size `.alloc 0`,
`.aligned al 0`, `.realloc al 0 new`, and `.realloc al old 0`, as in `SpqrBoundedEvs`). -/
theorem ModelHyps.step_nonFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxReq + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + (maxReq + 8195) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + (maxReq + 8195)) := by
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    omega
  | alloc req =>
    simp only [eventStepReq] at hreq
    by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
      have hsa := hM.smallAlloc_le hle
      omega
    · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
      obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_alloc_large st hgt
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      omega
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
      have hsa := hM.smallAlloc_le hle
      omega
    · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
      obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_aligned_large st hal hgt
      have hm := hM.meta_le
      have hla := hM.largeCost_le hgt
      omega
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · by_cases hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
        have hsr := hM.smallRealloc_le hnew_le
        omega
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < new := by omega
        obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_large_any st hal hold_le hnew_gt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hnew_gt
        omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      by_cases hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
        have hsr := hM.smallRealloc_le hnew_le
        omega
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < new := by omega
        obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_realloc_large_large st hal hold_gt hnew_gt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hnew_gt
        omega

/-- State-threaded per-phase symbolic bound from `st0 : M.σ`, tracking cumulative small-class and
metadata bytes (`Δcum`), net post-phase `sc = 63` live-byte increase (`Δlive`), intra-phase
transient `sc = 63` peak above `liveLarge st0` (`Δpeak`), and per-event request/alignment caps
(`maxReq`, `≤ 16`). -/
structure PhaseCreditSpec (M : AllocCostModel) [HasFineReallocCredit M]
    (Env : List AllocEvent → Prop) (Δcum Δlive Δpeak maxReq : Nat) : Prop where
  req_align : ∀ evs, Env evs → ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16
  credit_le : ∀ (st0 : M.σ) {evs : List AllocEvent}, Env evs →
    HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤ HasFineReallocCredit.cumSmall st0 + Δcum ∧
    HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤ HasFineReallocCredit.liveLarge st0 + Δlive ∧
    HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
      max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0 + Δpeak)

/-- Vacuous / unreachable-arm `PhaseCreditSpec`. -/
theorem PhaseCreditSpec.empty (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M (fun _ => False) 0 0 0 0 where
  req_align _ h := False.elim h
  credit_le _ _ h := False.elim h

/-- Empty-trace (`evs = []`) zero-cost `PhaseCreditSpec`. -/
theorem PhaseCreditSpec.nil (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M (· = []) 0 0 0 0 where
  req_align := by
    rintro _ rfl ev hev
    nomatch hev
  credit_le := by
    rintro st0 _ rfl
    simp only [AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩

/-- Zero-cost `PhaseCreditSpec` for any envelope implying `evs = []`. -/
theorem PhaseCreditSpec.of_eq_nil {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} (h : ∀ evs, Env evs → evs = []) :
    PhaseCreditSpec M Env 0 0 0 0 where
  req_align evs hE := (PhaseCreditSpec.nil M).req_align evs (h evs hE)
  credit_le st0 {evs} hE := (PhaseCreditSpec.nil M).credit_le st0 (h evs hE)

/-- Monotonicity in the numeric bounds `(Δcum, Δlive, Δpeak, maxReq)`. -/
theorem PhaseCreditSpec.mono {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hc : c₁ ≤ c₂) (hl : l₁ ≤ l₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂)
    (h : PhaseCreditSpec M Env c₁ l₁ p₁ r₁) :
    PhaseCreditSpec M Env c₂ l₂ p₂ r₂ where
  req_align evs hE ev hev := by
    obtain ⟨hreq, hal⟩ := h.req_align evs hE ev hev
    exact ⟨Nat.le_trans hreq hr, hal⟩
  credit_le st0 {_} hE := by
    obtain ⟨hcum, hlive, hpeak⟩ := h.credit_le st0 hE
    omega

/-- Narrow the envelope (`E₁ → E₂`) while keeping the same numeric bounds. -/
theorem PhaseCreditSpec.of_imp {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c l p r : Nat}
    (hsub : ∀ evs, E₁ evs → E₂ evs)
    (h : PhaseCreditSpec M E₂ c l p r) :
    PhaseCreditSpec M E₁ c l p r where
  req_align evs hE := h.req_align evs (hsub evs hE)
  credit_le st0 {evs} hE := h.credit_le st0 (hsub evs hE)

/-- Combined envelope narrowing and constant weakening. -/
theorem PhaseCreditSpec.congr_mono {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hsub : ∀ evs, E₁ evs → E₂ evs)
    (hc : c₁ ≤ c₂) (hl : l₁ ≤ l₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂)
    (h : PhaseCreditSpec M E₂ c₁ l₁ p₁ r₁) :
    PhaseCreditSpec M E₁ c₂ l₂ p₂ r₂ :=
  (h.of_imp hsub).mono hc hl hp hr

/-- Branching combinator (`E₁ evs ∨ E₂ evs`), taking componentwise maxima. -/
theorem PhaseCreditSpec.or {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (fun evs => E₁ evs ∨ E₂ evs)
      (max c₁ c₂) (max l₁ l₂) (max p₁ p₂) (max r₁ r₂) where
  req_align evs hE ev hev := by
    rcases hE with hE1 | hE2
    · obtain ⟨hreq, hal⟩ := h₁.req_align evs hE1 ev hev
      exact ⟨Nat.le_trans hreq (Nat.le_max_left r₁ r₂), hal⟩
    · obtain ⟨hreq, hal⟩ := h₂.req_align evs hE2 ev hev
      exact ⟨Nat.le_trans hreq (Nat.le_max_right r₁ r₂), hal⟩
  credit_le st0 {_} hE := by
    rcases hE with hE1 | hE2
    · obtain ⟨hcum, hlive, hpeak⟩ := h₁.credit_le st0 hE1
      omega
    · obtain ⟨hcum, hlive, hpeak⟩ := h₂.credit_le st0 hE2
      omega

/-- Branching combinator with inline implication `Env evs → E₁ evs ∨ E₂ evs`. -/
theorem PhaseCreditSpec.or_of_imp {M : AllocCostModel} [HasFineReallocCredit M]
    {Env E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (himp : ∀ evs, Env evs → E₁ evs ∨ E₂ evs)
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M Env (max c₁ c₂) (max l₁ l₂) (max p₁ p₂) (max r₁ r₂) :=
  (h₁.or h₂).of_imp himp

/-- Sequential composition of `PhaseCreditSpec` across `Heap.SeqEnv E₁ E₂`: adds `Δcum` and
`Δlive`, takes `max p₁ (l₁ + p₂)` for `Δpeak`, and `max r₁ r₂` for `maxReq`. -/
theorem PhaseCreditSpec.seq {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) where
  req_align evs hE ev hev := by
    rcases hE with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
    · obtain ⟨hreq, hal⟩ := h₁.req_align evs hE1 ev hev
      exact ⟨Nat.le_trans hreq (Nat.le_max_left r₁ r₂), hal⟩
    · rcases List.mem_append.mp hev with he1 | he2
      · obtain ⟨hreq, hal⟩ := h₁.req_align evs₁ hE1 ev he1
        exact ⟨Nat.le_trans hreq (Nat.le_max_left r₁ r₂), hal⟩
      · obtain ⟨hreq, hal⟩ := h₂.req_align evs₂ hE2 ev he2
        exact ⟨Nat.le_trans hreq (Nat.le_max_right r₁ r₂), hal⟩
  credit_le st0 {_} hE := by
    rcases hE with hE1 | ⟨evs₁, evs₂, rfl, hE1, hE2⟩
    · obtain ⟨hcum, hlive, hpeak⟩ := h₁.credit_le st0 hE1
      omega
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hcum₁, hlive₁, hpeak₁⟩ := h₁.credit_le st0 hE1
      obtain ⟨hcum₂, hlive₂, hpeak₂⟩ := h₂.credit_le (M.stepEvents evs₁ st0) hE2
      omega

/-- Sequential composition across strict concatenation `ConcatEnv E₁ E₂`. -/
theorem PhaseCreditSpec.concat {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (ConcatEnv E₁ E₂) (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) :=
  (h₁.seq h₂).of_imp fun _ => ConcatEnv.toSeqEnv

/-- Exact right-folded transient peak recurrence across a list of sequential phases. -/
def iterPeak {α : Type} (l p : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => max (p x) (l x + iterPeak l p xs)

/-- Closed-form upper bound `iterPeak l p xs ≤ (xs.map l).sum + (xs.map p).foldr max 0`. -/
theorem iterPeak_le_sum_add_max {α : Type} (l p : α → Nat) (xs : List α) :
    iterPeak l p xs ≤ (xs.map l).sum + (xs.map p).foldr max 0 := by
  induction xs with
  | nil => simp [iterPeak]
  | cons x xs ih =>
    simp only [iterPeak, List.map_cons, List.sum_cons, List.foldr_cons]
    omega

/-- Iterative `PhaseCreditSpec` over `IterSeqEnv Step xs` with per-element bounds `(c, l, p, r)`. -/
theorem PhaseCreditSpec.iter {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} (c l p r : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) (c x) (l x) (p x) (r x)) :
    PhaseCreditSpec M (IterSeqEnv Step xs)
      (xs.map c).sum (xs.map l).sum (iterPeak l p xs) ((xs.map r).foldr max 0) := by
  induction xs with
  | nil =>
    simpa [IterSeqEnv, iterPeak] using PhaseCreditSpec.nil M
  | cons x xs ih =>
    have hx := hstep x List.mem_cons_self
    have hxs := ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
    simpa [IterSeqEnv, iterPeak] using hx.seq hxs

/-- Iterative `PhaseCreditSpec` over `IterConcatEnv Step xs` with per-element bounds. -/
theorem PhaseCreditSpec.iterConcat {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} (c l p r : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) (c x) (l x) (p x) (r x)) :
    PhaseCreditSpec M (IterConcatEnv Step xs)
      (xs.map c).sum (xs.map l).sum (iterPeak l p xs) ((xs.map r).foldr max 0) :=
  (PhaseCreditSpec.iter c l p r xs hstep).of_imp fun _ => IterConcatEnv.toIterSeqEnv

/-- Uniform per-step `PhaseCreditSpec` over `IterSeqEnv Step xs`: `xs.length` steps of `(c, l, p, r)`. -/
theorem PhaseCreditSpec.iter_const {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} {c l p r : Nat} (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) c l p r) :
    PhaseCreditSpec M (IterSeqEnv Step xs)
      (xs.length * c) (xs.length * l) (xs.length * l + p) r := by
  induction xs with
  | nil =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | cons x xs ih =>
    have hx := hstep x List.mem_cons_self
    have hxs := ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
    have hseq := hx.seq hxs
    refine hseq.mono ?_ ?_ ?_ ?_
    · rw [List.length_cons, Nat.succ_mul]; omega
    · rw [List.length_cons, Nat.succ_mul]; omega
    · rw [List.length_cons, Nat.succ_mul]; omega
    · omega

/-- Zero-net-live loop combinator (`Δlive = 0` per iteration, e.g. loop bodies that drop their
own large temporaries): `Δpeak` stays `O(1)` (`p`), independent of `xs.length`. -/
theorem PhaseCreditSpec.iter_zero_live {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} {c p r : Nat} (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseCreditSpec M (Step x) c 0 p r) :
    PhaseCreditSpec M (IterSeqEnv Step xs) (xs.length * c) 0 p r := by
  have h := PhaseCreditSpec.iter_const xs hstep
  simpa using h

/-! ## 3. Deallocation-Only Envelopes (`.freeOnly` & `.freeOnly_align16`) -/

/-- Under `FreeNonInc M`, any `Heap.FreeOnlyEvs` list never increases `cumSmall`, `liveLarge`,
or `peakLarge`. -/
theorem stepEvents_freeOnly_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : FreeNonInc M) :
    ∀ {evs : List AllocEvent}, FreeOnlyEvs evs → ∀ (st : M.σ),
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], _, _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: evs, hf, st => by
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    have hf' : FreeOnlyEvs evs := fun e he => hf e (List.mem_cons_of_mem _ he)
    obtain ⟨hc₁, hl₁, hp₁⟩ := hF al sz st
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnly_le hF hf' (M.step (.free al sz) st)
    exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-- Under `FreeNonInc M`, `Heap.FreeOnlyEvs` never raises `cumSmall`, `liveLarge`, or `peakLarge`
(`Δcum = 0, Δlive = 0, Δpeak = 0, maxReq = 0`). -/
theorem PhaseCreditSpec.freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : FreeNonInc M) :
    PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 where
  req_align evs hf ev hev := by
    obtain ⟨al, sz, rfl⟩ := hf ev hev
    exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩
  credit_le st0 {_} hf := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_freeOnly_le hF hf st0
    omega

/-- Lift `PhaseCreditSpec.freeOnly` to any envelope implying `Heap.FreeOnlyEvs`. -/
theorem PhaseCreditSpec.of_freeOnlyEvs {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} (hF : FreeNonInc M)
    (hsub : ∀ evs, Env evs → FreeOnlyEvs evs) :
    PhaseCreditSpec M Env 0 0 0 0 :=
  (PhaseCreditSpec.freeOnly hF).of_imp hsub

/-- `PhaseCreditSpec.freeOnly` directly from `(hM : ModelHyps M)`. -/
theorem PhaseCreditSpec.freeOnly_of_hyps {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M FreeOnlyEvs 0 0 0 0 :=
  PhaseCreditSpec.freeOnly hM.freeNonInc

/-- Lift `PhaseCreditSpec.freeOnly_of_hyps` to any envelope implying `Heap.FreeOnlyEvs`. -/
theorem PhaseCreditSpec.of_freeOnlyEvs_hyps {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} (hM : ModelHyps M)
    (hsub : ∀ evs, Env evs → FreeOnlyEvs evs) :
    PhaseCreditSpec M Env 0 0 0 0 :=
  PhaseCreditSpec.of_freeOnlyEvs hM.freeNonInc hsub

/-- Hypothesis-free `al ≤ 16` `.free` non-increase using only `[HasFineReallocCredit M]`. -/
theorem stepEvents_freeOnlyAlign16_le (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ {evs : List AllocEvent}, FreeOnlyAlign16Evs evs → ∀ (st : M.σ),
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], _, _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: evs, hf, st => by
    obtain ⟨al, hal, sz, rfl⟩ := hf ev List.mem_cons_self
    have hf' : FreeOnlyAlign16Evs evs := fun e he => hf e (List.mem_cons_of_mem _ he)
    have hstep :
        let st' := M.step (.free al sz) st
        HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
        HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
        HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
      by_cases hle : sz ≤ HasFineReallocCredit.smallMaxReq M
      · exact HasFineReallocCredit.step_free_small st hal hle
      · have hgt : HasFineReallocCredit.smallMaxReq M < sz := by omega
        obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_free_large st hal hgt
        exact ⟨hc, Nat.le_trans hl (Nat.sub_le _ _), hp⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnlyAlign16_le M hf' (M.step (.free al sz) st)
    exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-- Hypothesis-free `FreeOnlyAlign16Evs` `PhaseCreditSpec` (requires only `[HasFineReallocCredit M]`). -/
theorem PhaseCreditSpec.freeOnly_align16 (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M FreeOnlyAlign16Evs 0 0 0 0 where
  req_align evs hf ev hev := by
    obtain ⟨al, _, sz, rfl⟩ := hf ev hev
    exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩
  credit_le st0 {_} hf := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_freeOnlyAlign16_le M hf st0
    omega

/-! ## 4. Single-Call Rust Allocator Specs and `sc = 63` Large Alloc/Free Cancellation -/

private theorem req_align_rustAlloc {req al : Nat} (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

private theorem req_align_rustDealloc (req al : Nat) :
    ∀ ev ∈ rustDeallocEvents req al, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩

private theorem req_align_rustRealloc {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ new ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl new, hal⟩

/-- Small `rustAllocEvents req al` (`al ≤ 16`, `0 < req ≤ smallMaxReq M`). -/
theorem PhaseCreditSpec.rustAlloc_small (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hpos : 0 < req)
    (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (HasFineReallocCredit.smallAllocCost M req) 0 0 req where
  req_align := by
    rintro _ rfl
    exact req_align_rustAlloc hal
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_rustAlloc_small M st0 hal hpos hle
    omega

/-- Large `rustAllocEvents req al` (`al ≤ 16`, `smallMaxReq M < req`). -/
theorem PhaseCreditSpec.rustAlloc_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (HasFineReallocCredit.largeMetaCost M)
      (HasFineReallocCredit.largeCost M req)
      (HasFineReallocCredit.largeCost M req)
      req where
  req_align := by
    rintro _ rfl
    exact req_align_rustAlloc hal
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_rustAlloc_large M st0 hal hgt

/-- Standard `al ≤ 16` `rustDeallocEvents req al` (`Δcum = 0, Δlive = 0, Δpeak = 0, maxReq = 0`). -/
theorem PhaseCreditSpec.rustDealloc_align16 (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = rustDeallocEvents req al) 0 0 0 0 :=
  (PhaseCreditSpec.freeOnly_align16 M).of_imp fun _ h => by
    subst h
    exact FreeOnlyAlign16Evs.rustDealloc hal req

/-- Arbitrary-alignment `rustDeallocEvents req al` under `FreeNonInc M`. -/
theorem PhaseCreditSpec.rustDealloc {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : FreeNonInc M) (req al : Nat) :
    PhaseCreditSpec M (· = rustDeallocEvents req al) 0 0 0 0 :=
  (PhaseCreditSpec.freeOnly hF).of_imp fun _ h => by
    subst h
    exact FreeOnlyEvs.singleton al req

/-- Quadrant S→S `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem PhaseCreditSpec.rustRealloc_small_small (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hold_le : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_pos : 0 < new) (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (HasFineReallocCredit.smallReallocCost M new) 0 0 new where
  req_align := by
    rintro _ rfl
    exact req_align_rustRealloc hal hal_new
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ :=
      stepEvents_rustRealloc_small_small M st0 hal hal_new hold_pos hold_le hnew_pos hnew_le
    omega

/-- Quadrant S→L `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem PhaseCreditSpec.rustRealloc_small_large (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hold_le : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_gt : HasFineReallocCredit.smallMaxReq M < new) :
    PhaseCreditSpec M (· = rustReallocEvents old new al)
      (HasFineReallocCredit.largeMetaCost M)
      (HasFineReallocCredit.largeCost M new)
      (HasFineReallocCredit.largeCost M new)
      new where
  req_align := by
    rintro _ rfl
    exact req_align_rustRealloc hal hal_new
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_rustRealloc_small_large M st0 hal hal_new hold_pos hold_le hnew_gt

/-- Chained Quadrant L→L `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`,
`smallMaxReq M < old`, `smallMaxReq M < new`) cancelling `largeCost M old` from `Δlive`
after a preceding phase `E₁` while recording the exact transient overlap
`l_keep + largeCost M old + largeCost M new` in `Δpeak`. -/
theorem PhaseCreditSpec.concat_rustRealloc_large_large {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ : List AllocEvent → Prop} {c₁ l_keep p₁ r₁ old new al : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ (l_keep + HasFineReallocCredit.largeCost M old) p₁ r₁)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_gt : HasFineReallocCredit.smallMaxReq M < old)
    (hnew_gt : HasFineReallocCredit.smallMaxReq M < new) :
    PhaseCreditSpec M (ConcatEnv E₁ (· = rustReallocEvents old new al))
      (c₁ + HasFineReallocCredit.largeMetaCost M)
      (l_keep + HasFineReallocCredit.largeCost M new)
      (max p₁ (l_keep + HasFineReallocCredit.largeCost M old +
        HasFineReallocCredit.largeCost M new))
      (max r₁ new) where
  req_align := by
    rintro _ ⟨evs₁, _, rfl, hE1, rfl⟩ ev hev
    rcases List.mem_append.mp hev with he1 | he2
    · obtain ⟨hreq, ha⟩ := h₁.req_align evs₁ hE1 ev he1
      exact ⟨Nat.le_trans hreq (Nat.le_max_left r₁ new), ha⟩
    · obtain ⟨hreq, ha⟩ := req_align_rustRealloc hal hal_new ev he2
      exact ⟨Nat.le_trans hreq (Nat.le_max_right r₁ new), ha⟩
  credit_le := by
    rintro st0 _ ⟨evs₁, _, rfl, hE1, rfl⟩
    rw [M.stepEvents_append]
    obtain ⟨hc₁, hl₁, hp₁⟩ := h₁.credit_le st0 hE1
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_rustRealloc_large_large M (M.stepEvents evs₁ st0) hal hal_new hold_gt hnew_gt
    omega

/-- Chained Quadrant L→S `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`,
`smallMaxReq M < old`, `0 < new ≤ smallMaxReq M`) cancelling `largeCost M old` from `Δlive`. -/
theorem PhaseCreditSpec.concat_rustRealloc_large_small {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ : List AllocEvent → Prop} {c₁ l_keep p₁ r₁ old new al : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ (l_keep + HasFineReallocCredit.largeCost M old) p₁ r₁)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_gt : HasFineReallocCredit.smallMaxReq M < old)
    (hnew_pos : 0 < new) (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (ConcatEnv E₁ (· = rustReallocEvents old new al))
      (c₁ + HasFineReallocCredit.smallReallocCost M new)
      l_keep p₁ (max r₁ new) where
  req_align := by
    rintro _ ⟨evs₁, _, rfl, hE1, rfl⟩ ev hev
    rcases List.mem_append.mp hev with he1 | he2
    · obtain ⟨hreq, ha⟩ := h₁.req_align evs₁ hE1 ev he1
      exact ⟨Nat.le_trans hreq (Nat.le_max_left r₁ new), ha⟩
    · obtain ⟨hreq, ha⟩ := req_align_rustRealloc hal hal_new ev he2
      exact ⟨Nat.le_trans hreq (Nat.le_max_right r₁ new), ha⟩
  credit_le := by
    rintro st0 _ ⟨evs₁, _, rfl, hE1, rfl⟩
    rw [M.stepEvents_append]
    obtain ⟨hc₁, hl₁, hp₁⟩ := h₁.credit_le st0 hE1
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_rustRealloc_large_small M (M.stepEvents evs₁ st0)
        hal hal_new hold_gt hnew_pos hnew_le
    omega

/-- Exact-order deallocation-credit specification: `Env` emits only `0`-request, `≤ 16`-step-align
events, never increases `cumSmall` or `peakLarge`, and subtracts at least `credit` bytes from
`liveLarge` via `Nat` subtraction, allowing small and `sc = 63` large frees to interleave in drop
order without reordering. -/
structure DeallocCreditSpec (M : AllocCostModel) [HasFineReallocCredit M]
    (Env : List AllocEvent → Prop) (credit : Nat) : Prop where
  req_align : ∀ evs, Env evs → ∀ ev ∈ evs, eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16
  credit_sub : ∀ (st0 : M.σ) {evs : List AllocEvent}, Env evs →
    HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤ HasFineReallocCredit.cumSmall st0 ∧
    HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
      HasFineReallocCredit.liveLarge st0 - credit ∧
    HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤ HasFineReallocCredit.peakLarge st0

theorem DeallocCreditSpec.nil (M : AllocCostModel) [HasFineReallocCredit M] :
    DeallocCreditSpec M (· = []) 0 where
  req_align := by
    rintro _ rfl ev hev
    nomatch hev
  credit_sub := by
    rintro st0 _ rfl
    simp only [AllocCostModel.stepEvents_nil, Nat.sub_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem DeallocCreditSpec.mono {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {c₁ c₂ : Nat} (hc : c₂ ≤ c₁)
    (h : DeallocCreditSpec M Env c₁) :
    DeallocCreditSpec M Env c₂ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hcum, hlive, hpeak⟩ := h.credit_sub st0 hE
    omega

theorem DeallocCreditSpec.of_imp {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c : Nat}
    (hsub : ∀ evs, E₁ evs → E₂ evs) (h : DeallocCreditSpec M E₂ c) :
    DeallocCreditSpec M E₁ c where
  req_align evs hE := h.req_align evs (hsub evs hE)
  credit_sub st0 {evs} hE := h.credit_sub st0 (hsub evs hE)

theorem DeallocCreditSpec.or {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ c₂ : Nat}
    (h₁ : DeallocCreditSpec M E₁ c₁) (h₂ : DeallocCreditSpec M E₂ c₂) :
    DeallocCreditSpec M (fun evs => E₁ evs ∨ E₂ evs) (min c₁ c₂) where
  req_align evs hE ev hev := hE.elim (fun h1 => h₁.req_align evs h1 ev hev)
    (fun h2 => h₂.req_align evs h2 ev hev)
  credit_sub st0 {_} hE := by
    rcases hE with h1 | h2
    · obtain ⟨hcum, hlive, hpeak⟩ := h₁.credit_sub st0 h1
      omega
    · obtain ⟨hcum, hlive, hpeak⟩ := h₂.credit_sub st0 h2
      omega

/-- Sequential composition of `DeallocCreditSpec` in exact drop order (`credit = c₁ + c₂`). -/
theorem DeallocCreditSpec.concat {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ c₂ : Nat}
    (h₁ : DeallocCreditSpec M E₁ c₁) (h₂ : DeallocCreditSpec M E₂ c₂) :
    DeallocCreditSpec M (ConcatEnv E₁ E₂) (c₁ + c₂) where
  req_align := by
    rintro _ ⟨evs₁, evs₂, rfl, hE1, hE2⟩ ev hev
    rcases List.mem_append.mp hev with he1 | he2
    · exact h₁.req_align evs₁ hE1 ev he1
    · exact h₂.req_align evs₂ hE2 ev he2
  credit_sub := by
    rintro st0 _ ⟨evs₁, evs₂, rfl, hE1, hE2⟩
    rw [M.stepEvents_append]
    obtain ⟨hc₁, hl₁, hp₁⟩ := h₁.credit_sub st0 hE1
    obtain ⟨hc₂, hl₂, hp₂⟩ := h₂.credit_sub (M.stepEvents evs₁ st0) hE2
    omega

/-- Iterative `DeallocCreditSpec` over `IterConcatEnv Step xs` summing credits in exact order. -/
theorem DeallocCreditSpec.iterConcat {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop} (c : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, DeallocCreditSpec M (Step x) (c x)) :
    DeallocCreditSpec M (IterConcatEnv Step xs) (xs.map c).sum := by
  induction xs with
  | nil =>
    simpa [IterConcatEnv] using DeallocCreditSpec.nil M
  | cons x xs ih =>
    have hx := hstep x List.mem_cons_self
    have hxs := ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
    simpa [IterConcatEnv] using hx.concat hxs

/-- Small `rustDeallocEvents req al` (`al ≤ 16`, `req ≤ smallMaxReq M`): `0` large credit. -/
theorem DeallocCreditSpec.free_small (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    DeallocCreditSpec M (· = rustDeallocEvents req al) 0 where
  req_align := by
    rintro _ rfl
    exact req_align_rustDealloc req al
  credit_sub := by
    rintro st0 _ rfl
    simpa using stepEvents_rustDealloc_small M st0 hal hle

/-- Large `sc = 63` `rustDeallocEvents req al` (`al ≤ 16`, `smallMaxReq M < req`): credits back
`HasFineReallocCredit.largeCost M req` from `liveLarge`. -/
theorem DeallocCreditSpec.free_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    DeallocCreditSpec M (· = rustDeallocEvents req al)
      (HasFineReallocCredit.largeCost M req) where
  req_align := by
    rintro _ rfl
    exact req_align_rustDealloc req al
  credit_sub := by
    rintro st0 _ rfl
    exact stepEvents_rustDealloc_large M st0 hal hgt

/-- `Heap.FreeOnlyEvs` as a `0`-credit `DeallocCreditSpec` (for interleaving small/opaque drops
between `sc = 63` large deallocations without losing accumulated credit). -/
theorem DeallocCreditSpec.freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hF : FreeNonInc M) :
    DeallocCreditSpec M FreeOnlyEvs 0 where
  req_align evs hf ev hev := by
    obtain ⟨al, sz, rfl⟩ := hf ev hev
    exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩
  credit_sub st0 {_} hf := by
    simpa using stepEvents_freeOnly_le hF hf st0

/-- `FreeOnlyAlign16Evs` as a hypothesis-free `0`-credit `DeallocCreditSpec`. -/
theorem DeallocCreditSpec.freeOnly_align16 (M : AllocCostModel) [HasFineReallocCredit M] :
    DeallocCreditSpec M FreeOnlyAlign16Evs 0 where
  req_align evs hf ev hev := by
    obtain ⟨al, _, sz, rfl⟩ := hf ev hev
    exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩
  credit_sub st0 {_} hf := by
    simpa using stepEvents_freeOnlyAlign16_le M hf st0

/-- Every `DeallocCreditSpec` is a `0`-cost `PhaseCreditSpec`. -/
theorem DeallocCreditSpec.toPhaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {c : Nat} (h : DeallocCreditSpec M Env c) :
    PhaseCreditSpec M Env 0 0 0 0 where
  req_align := h.req_align
  credit_le st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    omega

/-- When `E_work` ends with `Δlive_keep + credit` live large bytes and is followed in call order
(`ConcatEnv E_work E_free`) by a deallocation phase `E_free` crediting back `credit`, the net
post-phase live large delta drops to `Δlive_keep` while `Δpeak` preserves the intra-phase peak. -/
theorem PhaseCreditSpec.concat_dealloc_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    {E_work E_free : List AllocEvent → Prop} {Δcum Δlive_keep credit Δpeak maxReq : Nat}
    (hwork : PhaseCreditSpec M E_work Δcum (Δlive_keep + credit) Δpeak maxReq)
    (hfree : DeallocCreditSpec M E_free credit) :
    PhaseCreditSpec M (ConcatEnv E_work E_free) Δcum Δlive_keep Δpeak maxReq where
  req_align := by
    rintro _ ⟨evs₁, evs₂, rfl, hw, hf⟩ ev hev
    rcases List.mem_append.mp hev with he1 | he2
    · exact hwork.req_align evs₁ hw ev he1
    · obtain ⟨hreq0, hal⟩ := hfree.req_align evs₂ hf ev he2
      exact ⟨Nat.le_trans hreq0 (Nat.zero_le maxReq), hal⟩
  credit_le := by
    rintro st0 _ ⟨evs₁, evs₂, rfl, hw, hf⟩
    rw [M.stepEvents_append]
    obtain ⟨hc₁, hl₁, hp₁⟩ := hwork.credit_le st0 hw
    obtain ⟨hc₂, hl₂, hp₂⟩ := hfree.credit_sub (M.stepEvents evs₁ st0) hf
    omega

/-- Allocating `req > smallMaxReq M` (`al ≤ 16`) and freeing it in call order yields `Δlive = 0`,
`Δcum = largeMetaCost M`, and transient peak `Δpeak = largeCost M req`. -/
theorem PhaseCreditSpec.largeAllocFree_cancel (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents req al) (· = rustDeallocEvents req al))
      (HasFineReallocCredit.largeMetaCost M) 0 (HasFineReallocCredit.largeCost M req) req := by
  have halloc :
      PhaseCreditSpec M (· = rustAllocEvents req al)
        (HasFineReallocCredit.largeMetaCost M)
        (0 + HasFineReallocCredit.largeCost M req)
        (HasFineReallocCredit.largeCost M req) req := by
    simpa using PhaseCreditSpec.rustAlloc_large M hal hgt
  exact halloc.concat_dealloc_cancel (DeallocCreditSpec.free_large M hal hgt)

/-- Allocating a temporary buffer `req > smallMaxReq M` (`al ≤ 16`), running `E_body` while `req`
is live, and freeing `req` in call order (left-associated) cancels `largeCost M req` from `Δlive`
(`Δlive = l_b`) while charging `largeCost M req + p_b` to `Δpeak`. -/
theorem PhaseCreditSpec.largeAllocBodyFree_cancel {M : AllocCostModel} [HasFineReallocCredit M]
    {req al : Nat} {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = rustAllocEvents req al) E_body) (· = rustDeallocEvents req al))
      (HasFineReallocCredit.largeMetaCost M + c_b)
      l_b
      (HasFineReallocCredit.largeCost M req + p_b)
      (max req r_b) := by
  have h12 := (PhaseCreditSpec.rustAlloc_large M hal hgt).concat hbody
  have h12' :
      PhaseCreditSpec M (ConcatEnv (· = rustAllocEvents req al) E_body)
        (HasFineReallocCredit.largeMetaCost M + c_b)
        (l_b + HasFineReallocCredit.largeCost M req)
        (HasFineReallocCredit.largeCost M req + p_b)
        (max req r_b) :=
    h12.mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)
  exact h12'.concat_dealloc_cancel (DeallocCreditSpec.free_large M hal hgt)

/-- Right-associated variant of `PhaseCreditSpec.largeAllocBodyFree_cancel`:
`ConcatEnv (· = rustAllocEvents req al) (ConcatEnv E_body (· = rustDeallocEvents req al))`. -/
theorem PhaseCreditSpec.largeAllocBodyFree_cancel_right
    {M : AllocCostModel} [HasFineReallocCredit M]
    {req al : Nat} {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents req al) (ConcatEnv E_body (· = rustDeallocEvents req al)))
      (HasFineReallocCredit.largeMetaCost M + c_b)
      l_b
      (HasFineReallocCredit.largeCost M req + p_b)
      (max req r_b) :=
  (PhaseCreditSpec.largeAllocBodyFree_cancel hal hgt hbody).of_imp fun _ =>
    ConcatEnv.assoc_iff.mpr

/-- `DeallocCreditSpec.freeOnly` directly from `(hM : ModelHyps M)`. -/
theorem DeallocCreditSpec.freeOnly_of_hyps {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    DeallocCreditSpec M FreeOnlyEvs 0 :=
  DeallocCreditSpec.freeOnly hM.freeNonInc

/-- `0`-size-inclusive small `rustAllocEvents req al` (`al ≤ 16`, `req ≤ smallMaxReq M`) under
`ModelHyps M` (no `0 < req` side condition). -/
theorem PhaseCreditSpec.rustAlloc_small_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16)
    (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (HasFineReallocCredit.smallAllocCost M req) 0 0 req where
  req_align := by
    rintro _ rfl
    exact req_align_rustAlloc hal
  credit_le := by
    rintro st0 _ rfl
    have hstep :
        let st' := M.stepEvents (rustAllocEvents req al) st0
        HasFineReallocCredit.cumSmall st' ≤
          HasFineReallocCredit.cumSmall st0 + HasFineReallocCredit.smallAllocCost M req ∧
        HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 ∧
        HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st0 := by
      unfold rustAllocEvents
      split
      · exact hM.step_alloc_small_any st0 hle
      · exact hM.step_aligned_small_any st0 (by omega) hle
    obtain ⟨hc, hl, hp⟩ := hstep
    omega

/-- Regime-uniform affine bound for `rustAllocEvents req al` (`al ≤ 16`, arbitrary `req : Nat`
including `req = 0`) under `ModelHyps M`, valid without case-splitting on `req = 0`,
`req ≤ smallMaxReq M`, or `smallMaxReq M < req`. -/
theorem PhaseCreditSpec.rustAlloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M (· = rustAllocEvents req al)
      (2 * req + 9539) (req + 8195) (req + 8195) req := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · exact (PhaseCreditSpec.rustAlloc_small_any hM hal hle).mono
      (hM.smallAlloc_le hle) (Nat.zero_le _) (Nat.zero_le _) (Nat.le_refl req)
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
    have hm := hM.meta_le
    have hl := hM.largeCost_le hgt
    exact (PhaseCreditSpec.rustAlloc_large M hal hgt).mono
      (by omega) hl hl (Nat.le_refl req)

/-- Regime-uniform temporary `alloc ++ dealloc` cancellation (`al ≤ 16`, arbitrary `req : Nat`
including `req = 0`) under `ModelHyps M`: regardless of whether `req ≤ smallMaxReq M` or
`smallMaxReq M < req`, post-free `Δlive = 0`, `Δcum ≤ 2 * req + 9539`, and `Δpeak ≤ req + 8195`. -/
theorem PhaseCreditSpec.tempAllocFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16) :
    PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents req al) (· = rustDeallocEvents req al))
      (2 * req + 9539) 0 (req + 8195) req := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · have halloc :
        PhaseCreditSpec M (· = rustAllocEvents req al)
          (HasFineReallocCredit.smallAllocCost M req) (0 + 0) 0 req :=
      PhaseCreditSpec.rustAlloc_small_any hM hal hle
    have hcancel := halloc.concat_dealloc_cancel (DeallocCreditSpec.free_small M hal hle)
    exact hcancel.mono (hM.smallAlloc_le hle) (Nat.le_refl 0) (Nat.zero_le _) (Nat.le_refl req)
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
    have hm := hM.meta_le
    have hl := hM.largeCost_le hgt
    exact (PhaseCreditSpec.largeAllocFree_cancel M hal hgt).mono
      (by omega) (Nat.le_refl 0) hl (Nat.le_refl req)

/-- Regime-uniform bracketed `alloc ++ body ++ dealloc` cancellation (`al ≤ 16`, arbitrary
`req : Nat` including `req = 0`, left-associated) under `ModelHyps M`: works uniformly across
both `req ≤ smallMaxReq M` and `smallMaxReq M < req`, leaving `Δlive = l_b` and
`Δpeak = req + 8195 + p_b`. -/
theorem PhaseCreditSpec.tempAllocBodyFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hal : al ≤ 16)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv (· = rustAllocEvents req al) E_body) (· = rustDeallocEvents req al))
      (2 * req + 9539 + c_b) l_b (req + 8195 + p_b) (max req r_b) := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · have h12 := (PhaseCreditSpec.rustAlloc_small_any hM hal hle).concat hbody
    have hsa := hM.smallAlloc_le hle
    have h12' :
        PhaseCreditSpec M (ConcatEnv (· = rustAllocEvents req al) E_body)
          (2 * req + 9539 + c_b) (l_b + 0) (req + 8195 + p_b) (max req r_b) :=
      h12.mono (by omega) (by omega) (by omega) (Nat.le_refl _)
    exact h12'.concat_dealloc_cancel (DeallocCreditSpec.free_small M hal hle)
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
    have hm := hM.meta_le
    have hl := hM.largeCost_le hgt
    exact (PhaseCreditSpec.largeAllocBodyFree_cancel hal hgt hbody).mono
      (by omega) (Nat.le_refl l_b) (by omega) (Nat.le_refl _)

/-- Right-associated variant of `PhaseCreditSpec.tempAllocBodyFree_aff`. -/
theorem PhaseCreditSpec.tempAllocBodyFree_aff_right
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} {E_body : List AllocEvent → Prop} {c_b l_b p_b r_b : Nat}
    (hal : al ≤ 16)
    (hbody : PhaseCreditSpec M E_body c_b l_b p_b r_b) :
    PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents req al) (ConcatEnv E_body (· = rustDeallocEvents req al)))
      (2 * req + 9539 + c_b) l_b (req + 8195 + p_b) (max req r_b) :=
  (PhaseCreditSpec.tempAllocBodyFree_aff hM hal hbody).of_imp fun _ =>
    ConcatEnv.assoc_iff.mpr

/-! ## 5. Whole-Trace `evalLog` & `footprint_le` Corollaries (`st0 = M.init`) -/

/-- Specialize `PhaseCreditSpec.credit_le` at `st0 = M.init` (`M.evalLog evs`). -/
theorem PhaseCreditSpec.evalLog_bounds {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {Δcum Δlive Δpeak maxReq : Nat}
    (h : PhaseCreditSpec M Env Δcum Δlive Δpeak maxReq)
    {evs : List AllocEvent} (hEnv : Env evs) :
    HasFineReallocCredit.cumSmall (M.evalLog evs) ≤ Δcum ∧
    HasFineReallocCredit.liveLarge (M.evalLog evs) ≤ Δlive ∧
    HasFineReallocCredit.peakLarge (M.evalLog evs) ≤ Δpeak := by
  unfold AllocCostModel.evalLog
  obtain ⟨hc, hl, hp⟩ := h.credit_le M.init hEnv
  have hc0 := HasFineReallocCredit.cumSmall_init (M := M)
  have hl0 := HasFineReallocCredit.liveLarge_init (M := M)
  have hp0 := HasFineReallocCredit.peakLarge_init (M := M)
  omega

/-- Parametric mapped-footprint bound on `M.evalLog evs` via `HasFineReallocCredit.footprint_le`:
`M.footprint (M.evalLog evs) ≤ baseFine + Δcum + max Δlive Δpeak`. -/
theorem PhaseCreditSpec.evalLog_footprint_le {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {Δcum Δlive Δpeak maxReq : Nat}
    (h : PhaseCreditSpec M Env Δcum Δlive Δpeak maxReq)
    {evs : List AllocEvent} (hEnv : Env evs) :
    M.footprint (M.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := M) + Δcum + max Δlive Δpeak := by
  obtain ⟨hc, hl, hp⟩ := h.evalLog_bounds hEnv
  have hfp := HasFineReallocCredit.footprint_le (M := M) (M.evalLog evs)
  omega

/-- Specialization of `evalLog_footprint_le` when `Δlive ≤ Δpeak`:
`M.footprint (M.evalLog evs) ≤ baseFine + Δcum + Δpeak`. -/
theorem PhaseCreditSpec.evalLog_footprint_le_of_live_le_peak
    {M : AllocCostModel} [HasFineReallocCredit M]
    {Env : List AllocEvent → Prop} {Δcum Δlive Δpeak maxReq : Nat}
    (h : PhaseCreditSpec M Env Δcum Δlive Δpeak maxReq)
    (hlp : Δlive ≤ Δpeak) {evs : List AllocEvent} (hEnv : Env evs) :
    M.footprint (M.evalLog evs) ≤
      HasFineReallocCredit.baseFine (M := M) + Δcum + Δpeak := by
  have hfp := h.evalLog_footprint_le hEnv
  omega

end LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
