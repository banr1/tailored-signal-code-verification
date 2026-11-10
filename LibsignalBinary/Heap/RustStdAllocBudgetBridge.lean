/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ProgramReflection
public import ProofLib.StdStartup.MemOps
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.SepLogic.WPp
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocHelpers
public import VerifiedLibraries.RustStd.Spec.AllocStringClone
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Specifications.RustHeap.Vec
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Heap.GrowOneSpecs

/-!
# Budget-Threaded Bridges for Rust `alloc` Routines

Budget-threaded specifications (`CondSpec`, `NoOomSpec`, and `FitsEnv` envelope forms) and
`subroutine_ok` lift lemmas connecting `<String as Clone>::clone` and `<RawVec<T>>::grow_one`
(`RawVec<u8>` and `RawVec<Vec<u8>>`) to `RustCliAllocBudget M`, together with `VmPreserved`
auxiliary callee contracts and unconditional `B` branch-stub validators.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.RustStdAllocBudgetBridge

open Arm64 ProofLib SepProp
open ProofLib.SepLogic
open ProofLib.ProgramReflection
open ProofLib.StdStartup
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget RustAllocAddrs
   RustCliAllocBudgetEntries FitsEvents FitsEnv NullAllowed RustLayoutOk VmPreserved OomPreserved
   AllocCallPreserved rustAllocEvents rustDeallocEvents rustReallocEvents
   not_nullAllowed_of_fitsAllocEvents not_nullAllowed_of_fitsReallocEvents)
open CryptoVerification.RustHeap (vecHeader vecU8At vecU8 allocHookStack LayoutOk)
open CryptoVerification.LibsignalSessionRepr (VecGhost vecGhostAt)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall newCapU8 newCapVecU8)
open VerifiedLibraries.Mallocng.Proofs
  (memRegion_entails_exists_pointsToBytes memcpySymWords
   memcpy_allInstrs_noSvc_noMsr memcpy_pureWords_ok)
open VerifiedLibraries.RustStd (checkShimInstrsAt fetch_instr_at0)

/-! ## `<String as Clone>::clone` Events and Envelope -/

/-- Deterministic `AllocEvent` list emitted by `<String as Clone>::clone` on `g`:
    `[]` when `g.bytes.length = 0`, else `rustAllocEvents g.bytes.length 1`. -/
def stringCloneEvents (g : VecGhost) : List AllocEvent :=
  if g.bytes.length = 0 then [] else rustAllocEvents g.bytes.length 1

/-- Allocation envelope for `<String as Clone>::clone`. -/
def StringCloneEnv (g : VecGhost) (evs : List AllocEvent) : Prop :=
  (g.bytes.length = 0 ∧ evs = []) ∨
  (0 < g.bytes.length ∧ evs = rustAllocEvents g.bytes.length 1)

theorem stringCloneEnv_events (g : VecGhost) :
    StringCloneEnv g (stringCloneEvents g) := by
  unfold StringCloneEnv stringCloneEvents
  by_cases h : g.bytes.length = 0
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨Nat.pos_of_ne_zero h, by simp only [h, ↓reduceIte]⟩

theorem stringCloneEvents_eq_of_env {g : VecGhost} {evs : List AllocEvent}
    (h : StringCloneEnv g evs) :
    evs = stringCloneEvents g := by
  unfold stringCloneEvents
  rcases h with ⟨hz, rfl⟩ | ⟨hpos, rfl⟩
  · simp only [hz, ↓reduceIte]
  · simp only [Nat.ne_of_gt hpos, ↓reduceIte]

theorem fitsEvents_stringClone_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) (g : VecGhost) (h : FitsEnv M lim st (StringCloneEnv g)) :
    FitsEvents M lim st (stringCloneEvents g) :=
  h (stringCloneEvents g) (stringCloneEnv_events g)

private theorem vecGhostAt_bytes_lt_2pow63 {A : CryptoVerification.RustHeap.RustAlloc}
    {m : Memory} {g : VecGhost} {p : BitVec 64} {R : SepProp}
    (hm : m ⊨ vecGhostAt A g p ∗ R) :
    g.bytes.length < 2 ^ 63 := by
  unfold vecGhostAt vecU8At at hm
  have hm' : m ⊨ ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (vecHeader p g.cap g.ptr (BitVec.ofNat 64 g.bytes.length) ∗
        (if g.cap = 0 then emp
         else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
           memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length)) ∗ R) := by
    refine Satisfies.mono ?_ hm
    sep_entail
  rw [satisfies_pure_sepConj] at hm'
  omega

/-! ## Budget-Threaded `<String as Clone>::clone` Contracts -/

/-- Full conditional-OOM budget-threaded contract for `<String as Clone>::clone`:
    - `len = 0`: writes `{0, 1, 0}` with `0` allocator events (`stringCloneEvents g = []`),
      never panicking or OOMing;
    - `0 < len`: calls `__rust_alloc(len, 1)` (`stringCloneEvents g = rustAllocEvents len 1`);
      may OOM only when `¬ FitsEvents M lim st (stringCloneEvents g)` with `OomPreserved s0 sf`,
      and may panic (via `handle_error`) only on null return (`NullAllowed len 1`) with
      `sf.fs = s0.fs ∧ sf.trace = s0.trace` (no `allocFailedEvent`). -/
def stringCloneBudgetCondSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) where
  pre := fun (p, ret, g, st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents (stringCloneEvents g) st) sf ∗ stackAt s0.sp extHookStack
  onPanic := fun (_, _, g, _) s0 sf =>
    ⌜0 < g.bytes.length ∧ NullAllowed g.bytes.length 1 ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (_, _, g, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (stringCloneEvents g) ∧ OomPreserved s0 sf⌝

open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr)

/-- Deterministic-event `NoOom` specialization of `stringCloneBudgetCondSpec` under
    `FitsEvents M lim st (stringCloneEvents g)` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`,
    preserving `AllocCallPreserved s0 sf`). -/
def stringCloneNoOomSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) where
  pre := fun (p, ret, g, st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧
      FitsEvents M lim st (stringCloneEvents g) ∧ LsRetAddr (s.readReg64 .lr)⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents (stringCloneEvents g) st) sf ∗ stackAt s0.sp extHookStack

/-- Envelope contract for `<String as Clone>::clone` under `FitsEnv M lim st (StringCloneEnv g)`. -/
def stringCloneBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (BitVec 64 × BitVec 64 × VecGhost × M.σ) where
  pre := fun (p, ret, g, st) s =>
    ⌜s.readReg64 .x0 = p ∧ s.readReg64 .x8 = ret ∧ FitsEnv M lim st (StringCloneEnv g) ∧
      LsRetAddr (s.readReg64 .lr)⌝ ∗
      vecGhostAt A.repAlloc g p ∗ memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (p, ret, g, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ StringCloneEnv g evs⌝ ∗
      vecGhostAt A.repAlloc g p ∗ vecU8 A.repAlloc ret g.bytes ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

theorem subroutine_ok_stringCloneNoOom_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (stringCloneBudgetCondSpec M A lim)) :
    subroutine_ok P entry (stringCloneNoOomSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, ret, g, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [stringCloneNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hFit, _hlr⟩, hrest⟩
  have hlt63 : g.bytes.length < 2 ^ 63 := by
    refine vecGhostAt_bytes_lt_2pow63 (A := A.repAlloc) (m := s0.mem) (p := p)
      (R := memRegion ret 24 ∗ (A.pool lim st s0 ∗ (stackAt s0.sp extHookStack ∗ R))) ?_
    simpa only [sepConj_assoc] using hrest
  have hpreC : s0.mem ⊨ (stringCloneBudgetCondSpec M A lim).pre (p, ret, g, st) s0 ∗ R := by
    dsimp only [stringCloneBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (p, ret, g, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [stringCloneBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan with ⟨⟨hpos, hna, _, _⟩, _⟩
    have hev : stringCloneEvents g = rustAllocEvents g.bytes.length 1 := by
      unfold stringCloneEvents
      simp only [Nat.ne_of_gt hpos, ↓reduceIte]
    rw [hev] at hFit
    have hLay : RustLayoutOk g.bytes.length 1 :=
      ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    exact not_nullAllowed_of_fitsAllocEvents hLay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [stringCloneBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.1 hFit

theorem subroutine_ok_stringCloneBudget_of_noOom [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (stringCloneNoOomSpec M A lim)) :
    subroutine_ok P entry (stringCloneBudgetSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, ret, g, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [stringCloneBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx8, hEnv, hlr⟩, hrest⟩
  have hFit : FitsEvents M lim st (stringCloneEvents g) :=
    fitsEvents_stringClone_of_fitsEnv M lim st g hEnv
  have hpreN : s0.mem ⊨ (stringCloneNoOomSpec M A lim).pre (p, ret, g, st) s0 ∗ R := by
    dsimp only [stringCloneNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx8, hFit, hlr⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (p, ret, g, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [stringCloneNoOomSpec] at hpost
    dsimp only [stringCloneBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨stringCloneEvents g, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2.1, stringCloneEnv_events g⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_stringCloneBudget_of_cond [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (stringCloneBudgetCondSpec M A lim)) :
    subroutine_ok P entry (stringCloneBudgetSpec M A lim) :=
  subroutine_ok_stringCloneBudget_of_noOom (subroutine_ok_stringCloneNoOom_of_cond h)

/-! ## Parametric `<RawVec<T>>::grow_one` Contracts -/

/-- Amortized target capacity after `<RawVec<T>>::grow_one`: `max (2 * cap) minCap`. -/
def rawVecNewCap (minCap cap : Nat) : Nat :=
  max (2 * cap) minCap

/-- Deterministic `AllocEvent` list emitted by `<RawVec<T>>::grow_one` when `newCap * elemSz` is a
    valid `Layout` (`RustLayoutOk (newCap * elemSz) align`):
    `rustAllocEvents (minCap * elemSz) align` when `cap = 0`, else
    `rustReallocEvents (cap.toNat * elemSz) (rawVecNewCap minCap cap.toNat * elemSz) align`. -/
def rawVecGrowEvents (elemSz minCap align : Nat) (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then
    rustAllocEvents (minCap * elemSz) align
  else
    rustReallocEvents (cap.toNat * elemSz) (rawVecNewCap minCap cap.toNat * elemSz) align

/-- Concrete allocation envelope for `<RawVec<T>>::grow_one` parameterized by `(elemSz, minCap, align)`. -/
def RawVecGrowEnv (elemSz minCap align : Nat) (x : GrowOneCall) (evs : List AllocEvent) : Prop :=
  (x.cap = 0#64 ∧ evs = rustAllocEvents (minCap * elemSz) align) ∨
  (x.cap ≠ 0#64 ∧
    evs = rustReallocEvents (x.cap.toNat * elemSz) (rawVecNewCap minCap x.cap.toNat * elemSz) align)

theorem rawVecGrowEnv_events (elemSz minCap align : Nat) (x : GrowOneCall) :
    RawVecGrowEnv elemSz minCap align x (rawVecGrowEvents elemSz minCap align x.cap) := by
  unfold RawVecGrowEnv rawVecGrowEvents
  by_cases h : x.cap = 0#64
  · simp only [h, ↓reduceIte, true_and, true_or]
  · exact Or.inr ⟨h, by simp only [h, ↓reduceIte]⟩

theorem rawVecGrowEvents_eq_of_env {elemSz minCap align : Nat} {x : GrowOneCall}
    {evs : List AllocEvent} (h : RawVecGrowEnv elemSz minCap align x evs) :
    evs = rawVecGrowEvents elemSz minCap align x.cap := by
  unfold rawVecGrowEvents
  rcases h with ⟨hz, rfl⟩ | ⟨hnz, rfl⟩
  · simp only [hz, ↓reduceIte]
  · simp only [hnz, ↓reduceIte]

theorem fitsEvents_rawVecGrow_of_fitsEnv (elemSz minCap align : Nat)
    (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ) (x : GrowOneCall)
    (h : FitsEnv M lim st (RawVecGrowEnv elemSz minCap align x)) :
    FitsEvents M lim st (rawVecGrowEvents elemSz minCap align x.cap) :=
  h (rawVecGrowEvents elemSz minCap align x.cap) (rawVecGrowEnv_events elemSz minCap align x)

/-- Conditional-OOM budget contract for `<RawVec<T>>::grow_one` parameterized by `(elemSz, minCap, align)`:
* If `¬ RustLayoutOk (rawVecNewCap minCap x.cap.toNat * elemSz) align`, `finish_grow` fails with
  `CapacityOverflow` before calling the allocator (`onOom` requires `RustLayoutOk ...`) and panics
  via `handle_error` preserving `fs` and `trace`.
* When `RustLayoutOk` holds, calls `__rust_alloc` (`x.cap = 0`) or `__rust_realloc` (`x.cap ≠ 0`),
  permitting `.OutOfMemory` only when `¬ FitsEvents` and panicking only under `NullAllowed`. -/
def rawVecGrowBudgetCondSpec (elemSz minCap align : Nat)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * elemSz ∧ x.ptr ≠ 0 ∧
      x.cap.toNat * elemSz < 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length align ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    let newCap := rawVecNewCap minCap x.cap.toNat
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % align = 0⌝ ∗
        (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * elemSz) align ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap - x.cap.toNat) * elemSz)) ∗
      A.pool lim (M.stepEvents (rawVecGrowEvents elemSz minCap align x.cap) st) sf ∗
      stackAt s0.sp extHookStack
  onPanic := fun (x, _) s0 sf =>
    let newBytes := rawVecNewCap minCap x.cap.toNat * elemSz
    ⌜(¬ RustLayoutOk newBytes align ∨ NullAllowed newBytes align) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    let newBytes := rawVecNewCap minCap x.cap.toNat * elemSz
    ⌜RustLayoutOk newBytes align ∧
      ¬ FitsEvents M lim st (rawVecGrowEvents elemSz minCap align x.cap) ∧
      OomPreserved s0 sf⌝

/-- Deterministic-event `NoOom` specialization of `rawVecGrowBudgetCondSpec` under
    `RustLayoutOk` and `FitsEvents` (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def rawVecGrowNoOomSpec (elemSz minCap align : Nat)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * elemSz ∧ x.ptr ≠ 0 ∧
      rawVecNewCap minCap x.cap.toNat * elemSz + align ≤ 2 ^ 63 ∧
      FitsEvents M lim st (rawVecGrowEvents elemSz minCap align x.cap)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length align ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    let newCap := rawVecNewCap minCap x.cap.toNat
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0 ∧ p'.toNat % align = 0⌝ ∗
        (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (newCap * elemSz) align ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap - x.cap.toNat) * elemSz)) ∗
      A.pool lim (M.stepEvents (rawVecGrowEvents elemSz minCap align x.cap) st) sf ∗
      stackAt s0.sp extHookStack

/-- Envelope form of `<RawVec<T>>::grow_one` parameterized by `(elemSz, minCap, align)`. -/
def rawVecGrowBudgetSpec (elemSz minCap align : Nat)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat * elemSz ∧ x.ptr ≠ 0 ∧
      rawVecNewCap minCap x.cap.toNat * elemSz + align ≤ 2 ^ 63 ∧
      FitsEnv M lim st (RawVecGrowEnv elemSz minCap align x)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length align ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    let newCap := rawVecNewCap minCap x.cap.toNat
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ RawVecGrowEnv elemSz minCap align x evs⌝ ∗
        (∃∗ (p' : BitVec 64),
          ⌜p' ≠ 0 ∧ p'.toNat % align = 0⌝ ∗
          (x.v ↦₆₄ BitVec.ofNat 64 newCap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
          A.live p' (newCap * elemSz) align ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) ((newCap - x.cap.toNat) * elemSz)) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp extHookStack

theorem subroutine_ok_rawVecGrowNoOom_of_cond {elemSz minCap align : Nat}
    (helem : 0 < elemSz) (hmin : 0 < minCap)
    (hpow : ∃ k, align = 2 ^ k) (hal : align ≤ 2 ^ 31)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rawVecGrowBudgetCondSpec elemSz minCap align M A lim)) :
    subroutine_ok P entry (rawVecGrowNoOomSpec elemSz minCap align M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rawVecGrowNoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hbnd, hFit⟩, hrest⟩
  have hpos_al : 0 < align := by
    rcases hpow with ⟨k, rfl⟩
    exact Nat.two_pow_pos k
  have hnew_ge_min : minCap ≤ rawVecNewCap minCap x.cap.toNat := Nat.le_max_right _ _
  have hnew_ge_2c : 2 * x.cap.toNat ≤ rawVecNewCap minCap x.cap.toNat := Nat.le_max_left _ _
  have hcap_lt : x.cap.toNat * elemSz < 2 ^ 63 := by
    have hle : x.cap.toNat * elemSz ≤ rawVecNewCap minCap x.cap.toNat * elemSz :=
      Nat.mul_le_mul_right elemSz (by omega)
    omega
  have hnew_pos : 0 < rawVecNewCap minCap x.cap.toNat * elemSz :=
    Nat.mul_pos (Nat.lt_of_lt_of_le hmin hnew_ge_min) helem
  have hLay : RustLayoutOk (rawVecNewCap minCap x.cap.toNat * elemSz) align :=
    ⟨⟨hnew_pos, hpow, hbnd⟩, hal⟩
  have hpreC :
      s0.mem ⊨ (rawVecGrowBudgetCondSpec elemSz minCap align M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [rawVecGrowBudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hcap_lt⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [rawVecGrowBudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan with ⟨⟨hpan_or, _, _⟩, _⟩
    rcases hpan_or with hnotLay | hna
    · exact hnotLay hLay
    · unfold rawVecGrowEvents at hFit
      by_cases hcz : x.cap = 0#64
      · simp only [hcz, ↓reduceIte] at hFit
        have hcap0 : x.cap.toNat = 0 := by rw [hcz]; rfl
        have hEq : rawVecNewCap minCap x.cap.toNat = minCap := by
          unfold rawVecNewCap; rw [hcap0]; omega
        rw [hEq] at hLay hna
        exact not_nullAllowed_of_fitsAllocEvents hLay hFit hna
      · simp only [hcz, ↓reduceIte] at hFit
        exact not_nullAllowed_of_fitsReallocEvents hLay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [rawVecGrowBudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.2.1 hFit

theorem subroutine_ok_rawVecGrowBudget_of_noOom {elemSz minCap align : Nat}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rawVecGrowNoOomSpec elemSz minCap align M A lim)) :
    subroutine_ok P entry (rawVecGrowBudgetSpec elemSz minCap align M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rawVecGrowBudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hbnd, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (rawVecGrowEvents elemSz minCap align x.cap) :=
    fitsEvents_rawVecGrow_of_fitsEnv elemSz minCap align M lim st x hEnv
  have hpreN :
      s0.mem ⊨ (rawVecGrowNoOomSpec elemSz minCap align M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [rawVecGrowNoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hbnd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rawVecGrowNoOomSpec] at hpost
    dsimp only [rawVecGrowBudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨rawVecGrowEvents elemSz minCap align x.cap, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2.1, rawVecGrowEnv_events elemSz minCap align x⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_rawVecGrowBudget_of_cond {elemSz minCap align : Nat}
    (helem : 0 < elemSz) (hmin : 0 < minCap)
    (hpow : ∃ k, align = 2 ^ k) (hal : align ≤ 2 ^ 31)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rawVecGrowBudgetCondSpec elemSz minCap align M A lim)) :
    subroutine_ok P entry (rawVecGrowBudgetSpec elemSz minCap align M A lim) :=
  subroutine_ok_rawVecGrowBudget_of_noOom
    (subroutine_ok_rawVecGrowNoOom_of_cond helem hmin hpow hal h)

/-! ### `RawVec<u8>::grow_one` (`elemSz = 1, minCap = 8, align = 1`) -/

/-- Deterministic `AllocEvent` list for `<RawVec<u8>>::grow_one` (`elemSz = 1, minCap = 8, align = 1`). -/
def growOneU8Events (cap : BitVec 64) : List AllocEvent :=
  if cap = 0#64 then
    rustAllocEvents 8 1
  else
    rustReallocEvents cap.toNat (max (2 * cap.toNat) 8) 1

theorem growOneU8Events_eq_rawVecGrowEvents (cap : BitVec 64) :
    growOneU8Events cap = rawVecGrowEvents 1 8 1 cap := by
  unfold growOneU8Events rawVecGrowEvents rawVecNewCap
  simp only [Nat.mul_one]

def GrowOneU8Env (x : GrowOneCall) (evs : List AllocEvent) : Prop :=
  (x.cap = 0#64 ∧ evs = rustAllocEvents 8 1) ∨
  (x.cap ≠ 0#64 ∧ evs = rustReallocEvents x.cap.toNat (max (2 * x.cap.toNat) 8) 1)

theorem GrowOneU8Env_iff_rawVecGrowEnv (x : GrowOneCall) (evs : List AllocEvent) :
    GrowOneU8Env x evs ↔ RawVecGrowEnv 1 8 1 x evs := by
  unfold GrowOneU8Env RawVecGrowEnv rawVecNewCap
  simp only [Nat.mul_one]

theorem growOneU8Env_events (x : GrowOneCall) :
    GrowOneU8Env x (growOneU8Events x.cap) := by
  rw [growOneU8Events_eq_rawVecGrowEvents, GrowOneU8Env_iff_rawVecGrowEnv]
  exact rawVecGrowEnv_events 1 8 1 x

theorem growOneU8Events_eq_of_env {x : GrowOneCall} {evs : List AllocEvent}
    (h : GrowOneU8Env x evs) :
    evs = growOneU8Events x.cap := by
  rw [growOneU8Events_eq_rawVecGrowEvents]
  exact rawVecGrowEvents_eq_of_env ((GrowOneU8Env_iff_rawVecGrowEnv x evs).mp h)

theorem fitsEvents_growOneU8_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (st : M.σ) (x : GrowOneCall) (h : FitsEnv M lim st (GrowOneU8Env x)) :
    FitsEvents M lim st (growOneU8Events x.cap) :=
  h (growOneU8Events x.cap) (growOneU8Env_events x)

/-- Conditional-OOM budget contract for `<RawVec<u8>>::grow_one` (`rawVecGrowBudgetCondSpec 1 8 1`). -/
def growOneU8BudgetCondSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat ∧ x.ptr ≠ 0 ∧
      x.cap.toNat < 2 ^ 63⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 1 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0⌝ ∗
        (x.v ↦₆₄ newCapU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 8) 1 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) (max (2 * x.cap.toNat) 8 - x.cap.toNat)) ∗
      A.pool lim (M.stepEvents (growOneU8Events x.cap) st) sf ∗
      stackAt s0.sp extHookStack
  onPanic := fun (x, _) s0 sf =>
    let newCap := max (2 * x.cap.toNat) 8
    ⌜(2 ^ 63 ≤ newCap ∨ NullAllowed newCap 1) ∧
      sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap
  onOom := fun (x, st) s0 sf =>
    ⌜max (2 * x.cap.toNat) 8 < 2 ^ 63 ∧
      ¬ FitsEvents M lim st (growOneU8Events x.cap) ∧
      OomPreserved s0 sf⌝

def growOneU8NoOomSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 8 < 2 ^ 63 ∧
      FitsEvents M lim st (growOneU8Events x.cap)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 1 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      (∃∗ (p' : BitVec 64),
        ⌜p' ≠ 0⌝ ∗
        (x.v ↦₆₄ newCapU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * x.cap.toNat) 8) 1 ∗ (p' ↦ₛ x.bs) ∗
        memRegion (p' + BitVec.ofNat 64 x.bs.length) (max (2 * x.cap.toNat) 8 - x.cap.toNat)) ∗
      A.pool lim (M.stepEvents (growOneU8Events x.cap) st) sf ∗
      stackAt s0.sp extHookStack

/-- Envelope budget contract for `<RawVec<u8>>::grow_one`. -/
def growOneU8BudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) :
    Spec (GrowOneCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ x.bs.length = x.cap.toNat ∧ x.ptr ≠ 0 ∧
      max (2 * x.cap.toNat) 8 < 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneU8Env x)⌝ ∗
      (x.v ↦₆₄ x.cap) ∗ ((x.v + 8#64) ↦₆₄ x.ptr) ∗
      (if x.cap = 0 then emp else A.live x.ptr x.bs.length 1 ∗ (x.ptr ↦ₛ x.bs)) ∗
      A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneU8Env x evs⌝ ∗
        (∃∗ (p' : BitVec 64),
          ⌜p' ≠ 0⌝ ∗
          (x.v ↦₆₄ newCapU8 x.cap) ∗ ((x.v + 8#64) ↦₆₄ p') ∗
          A.live p' (max (2 * x.cap.toNat) 8) 1 ∗ (p' ↦ₛ x.bs) ∗
          memRegion (p' + BitVec.ofNat 64 x.bs.length) (max (2 * x.cap.toNat) 8 - x.cap.toNat)) ∗
        A.pool lim (M.stepEvents evs st) sf ∗
        stackAt s0.sp extHookStack

theorem subroutine_ok_growOneU8Cond_of_rawVecGrow {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rawVecGrowBudgetCondSpec 1 8 1 M A lim)) :
    subroutine_ok P entry (growOneU8BudgetCondSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  have hpreR : s0.mem ⊨ (rawVecGrowBudgetCondSpec 1 8 1 M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [rawVecGrowBudgetCondSpec]
    dsimp only [growOneU8BudgetCondSpec] at hpre
    simpa only [Nat.mul_one] using hpre
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreR hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rawVecGrowBudgetCondSpec, rawVecNewCap] at hpost
    dsimp only [growOneU8BudgetCondSpec, newCapU8]
    rw [growOneU8Events_eq_rawVecGrowEvents]
    simp only [sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right,
      satisfies_sepExists] at hpost ⊢
    rcases hpost with ⟨p', hpost⟩
    refine ⟨p', ?_⟩
    simpa only [Nat.mul_one, Nat.mod_one, and_true] using hpost
  · refine Or.inr (Or.inl ⟨hp, ?_⟩)
    dsimp only [rawVecGrowBudgetCondSpec, rawVecNewCap] at hpan
    dsimp only [growOneU8BudgetCondSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
    rcases hpan with ⟨⟨hor, hfs, htr⟩, htop⟩
    refine ⟨⟨?_, hfs, htr⟩, htop⟩
    rcases hor with hnotLay | hna
    · refine Or.inl (Classical.byContradiction fun hlt => hnotLay ?_)
      have hpos : 0 < max (2 * x.cap.toNat) 8 * 1 := by omega
      exact ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩
    · rw [Nat.mul_one] at hna
      exact Or.inr hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
    dsimp only [rawVecGrowBudgetCondSpec, rawVecNewCap] at hoom
    dsimp only [growOneU8BudgetCondSpec]
    rw [satisfies_pure_sepConj] at hoom ⊢
    rcases hoom with ⟨⟨hLay, hnf, hoomp⟩, hR⟩
    rw [growOneU8Events_eq_rawVecGrowEvents]
    have hbnd : max (2 * x.cap.toNat) 8 * 1 + 1 ≤ 2 ^ 63 := hLay.1.2.2
    exact ⟨⟨by omega, hnf, hoomp⟩, hR⟩

theorem subroutine_ok_growOneU8NoOom_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneU8BudgetCondSpec M A lim)) :
    subroutine_ok P entry (growOneU8NoOomSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [growOneU8NoOomSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hbnd, hFit⟩, hrest⟩
  have hcap_lt : x.cap.toNat < 2 ^ 63 := by
    have : 2 * x.cap.toNat ≤ max (2 * x.cap.toNat) 8 := Nat.le_max_left _ _
    omega
  have hLay : RustLayoutOk (max (2 * x.cap.toNat) 8) 1 :=
    ⟨⟨by omega, ⟨0, rfl⟩, by omega⟩, by decide⟩
  have hpreC : s0.mem ⊨ (growOneU8BudgetCondSpec M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [growOneU8BudgetCondSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hcap_lt⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreC hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · exfalso
    dsimp only [growOneU8BudgetCondSpec] at hpan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpan
    rcases hpan with ⟨⟨hge | hna, _, _⟩, _⟩
    · omega
    · unfold growOneU8Events at hFit
      by_cases hcz : x.cap = 0#64
      · simp only [hcz, ↓reduceIte] at hFit
        have hcap0 : x.cap.toNat = 0 := by rw [hcz]; rfl
        have hEq : max (2 * x.cap.toNat) 8 = 8 := by rw [hcap0]; decide
        rw [hEq] at hLay hna
        exact not_nullAllowed_of_fitsAllocEvents hLay hFit hna
      · simp only [hcz, ↓reduceIte] at hFit
        exact not_nullAllowed_of_fitsReallocEvents hLay hFit hna
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exfalso
    dsimp only [growOneU8BudgetCondSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact hoom.1.2.1 hFit

theorem subroutine_ok_growOneU8Budget_of_noOom {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneU8NoOomSpec M A lim)) :
    subroutine_ok P entry (growOneU8BudgetSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨x, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [growOneU8BudgetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hbs, hptr, hbnd, hEnv⟩, hrest⟩
  have hFit : FitsEvents M lim st (growOneU8Events x.cap) :=
    fitsEvents_growOneU8_of_fitsEnv M lim st x hEnv
  have hpreN : s0.mem ⊨ (growOneU8NoOomSpec M A lim).pre (x, st) s0 ∗ R := by
    dsimp only [growOneU8NoOomSpec]
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc,
        satisfies_pure_sepConj]
    exact ⟨⟨hx0, hbs, hptr, hbnd, hFit⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (x, st) R s0 hpc hrun hpreN hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [growOneU8NoOomSpec] at hpost
    dsimp only [growOneU8BudgetSpec]
    rw [sepExists_sepConj_left, satisfies_sepExists]
    refine ⟨growOneU8Events x.cap, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨⟨hpost.1.2.1, growOneU8Env_events x⟩, hpost.2⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem subroutine_ok_growOneU8Budget_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneU8BudgetCondSpec M A lim)) :
    subroutine_ok P entry (growOneU8BudgetSpec M A lim) :=
  subroutine_ok_growOneU8Budget_of_noOom (subroutine_ok_growOneU8NoOom_of_cond h)

/-! ### `RawVec<Vec<u8>>::grow_one` (`elemSz = 24, minCap = 4, align = 8`) -/

abbrev growOneVecU8Events (cap : BitVec 64) : List AllocEvent :=
  rawVecGrowEvents 24 4 8 cap

abbrev GrowOneVecU8Env (x : GrowOneCall) (evs : List AllocEvent) : Prop :=
  RawVecGrowEnv 24 4 8 x evs

abbrev growOneVecU8BudgetCondSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) :=
  rawVecGrowBudgetCondSpec 24 4 8 M A lim

abbrev growOneVecU8NoOomSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) :=
  rawVecGrowNoOomSpec 24 4 8 M A lim

/-- Envelope budget contract for `<RawVec<Vec<u8>>::grow_one`. -/
abbrev growOneVecU8BudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (GrowOneCall × M.σ) :=
  rawVecGrowBudgetSpec 24 4 8 M A lim

theorem subroutine_ok_growOneVecU8NoOom_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneVecU8BudgetCondSpec M A lim)) :
    subroutine_ok P entry (growOneVecU8NoOomSpec M A lim) :=
  subroutine_ok_rawVecGrowNoOom_of_cond (by decide) (by decide) ⟨3, rfl⟩ (by decide) h

theorem subroutine_ok_growOneVecU8Budget_of_cond {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (growOneVecU8BudgetCondSpec M A lim)) :
    subroutine_ok P entry (growOneVecU8BudgetSpec M A lim) :=
  subroutine_ok_rawVecGrowBudget_of_cond (by decide) (by decide) ⟨3, rfl⟩ (by decide) h

/-! ## Auxiliary Callee Contracts and Stack Splits -/

/-- `VmPreserved`-preserving no-op contract for `__rustc::__rust_no_alloc_shim_is_unstable_v2()`. -/
def rustAllocShimVmSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝

theorem rustAllocShimVm_ret_ok {P : Program} {shimAddr : BitVec 64}
    (h : hasInstrs P shimAddr [ .ret .x30 ]) :
    subroutine_ok P shimAddr rustAllocShimVmSpec := by
  apply subroutine_ok_outcome_intro
  intro _ R s0 hpc hrun hpre _hsp
  dsimp only [rustAllocShimVmSpec] at hpre
  rw [emp_sepConj] at hpre
  have hf : P.fetch s0.pc = some (.ret .x30) :=
    hpc ▸ fetch_instr_at0 h
  apply reaches_outcome_step hrun hf
  have hev : P.evalInst (.ret .x30) s0 = s0.setPC (s0.readReg64 .x30) := by
    simp only [Program.evalInst, execInstWithSvc]
  rw [hev]
  refine reaches_outcome_refl_return rfl hrun ⟨?_, rfl, ?_⟩
  · dsimp only [rustAllocShimVmSpec]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨⟨rfl, rfl, rfl⟩, by cases s0; rfl, fun _ => by cases s0; rfl,
        fun _ _ _ => by cases s0; rfl⟩⟩, hpre⟩
  · rw [CalleeSavedPreserved_setPC]
    unfold CalleeSavedPreserved
    simp [calleeSavedVRegs]

private theorem allocMemcpyVm_len_le_2pow63 {m : Memory} {dst src : BitVec 64}
    {bs : List (BitVec 8)} {R : SepProp} (hlen : bs.length ≤ 2 ^ 64)
    (h : m ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R) :
    bs.length ≤ 2 ^ 63 := by
  have hro : m ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    refine Satisfies.pointsToBytes_to_ro ?_
    rwa [sepConj_comm (memRegion dst bs.length), sepConj_assoc] at h
  have hsep : ∀ a, InRegion src bs.length a → ¬InRegion dst bs.length a := fun a hs hd =>
    not_satisfies_ownsRO_ownsRW (ownsRO_pointsToBytesRO_at hlen hs)
      (ownsRW_sepConj_left (ownsRW_memRegion dst bs.length a hd)) hro
  have hself : ∀ b : BitVec 64, bs.length > 2 ^ 63 → InRegion b bs.length b := fun b hgt => by
    simp only [InRegion, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine Classical.byContradiction fun hgt => ?_
  by_cases hsd : InRegion dst bs.length src
  · exact hsep src (hself src (by omega)) hsd
  · refine hsep dst ?_ (hself dst (by omega))
    simp only [InRegion] at hsd ⊢
    bv_omega

/-- Total-correctness contract for `void *memcpy(void *dst, const void *src, size_t n)` over a
    read-write source buffer `src ↦ₛ bs`, preserving both `AllocCallPreserved` and `VmPreserved`
    so `RustCliAllocBudget.pool` transports across `memcpy`. -/
def allocMemcpyVmSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
    (memRegion dst bs.length ∗ (src ↦ₛ bs))
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs))

/-- Discharge `subroutine_ok P memcpyAddr allocMemcpyVmSpec` for any hook-free program `P`
    containing `musl` v1.2.5's AArch64 `memcpySymWords` at `memcpyAddr`. -/
theorem allocMemcpyVm_ok_of_hasWords (P : Program) (memcpyAddr : BitVec 64)
    (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_words : P.hasWords memcpyAddr memcpySymWords) :
    subroutine_ok P memcpyAddr allocMemcpyVmSpec := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _hL
  simp only [allocMemcpyVmSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hm⟩ := hpre
  have hm_assoc : s0.mem ⊨ (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ R := by
    rwa [← sepConj_assoc] at hm
  have hn63 : bs.length ≤ 2 ^ 63 := allocMemcpyVm_len_le_2pow63 (Nat.le_of_lt hlt) hm_assoc
  have hn_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hm_ex : s0.mem ⊨
      (∃∗ dstBs : List (BitVec 8), ⌜dstBs.length = bs.length⌝ ∗ (dst ↦ₛ dstBs)) ∗
        ((src ↦ₛ bs) ∗ R) :=
    Satisfies.mono
      (sepConj_mono_left (memRegion_entails_exists_pointsToBytes bs.length dst (Nat.le_of_lt hlt))) hm
  rw [sepExists_sepConj_left] at hm_ex
  obtain ⟨dstBs, hm_dst⟩ := (satisfies_sepExists _ _).mp hm_ex
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_dst
  obtain ⟨hdstLen, hm_pts⟩ := hm_dst
  have hLift := subroutine_ok_lift_pureWords_process
    (P := P)
    (memcpy_pureWords_ok memcpyAddr dst src dstBs bs (BitVec.ofNat 64 bs.length)
      (hdstLen.trans hn_nat.symm) hn_nat.symm (by rw [hn_nat]; exact hn63))
    (memcpy_allInstrs_noSvc_noMsr memcpyAddr)
    h_words h_no_ext
    (h_pre_mem := fun _ _ _ => rfl)
    (h_post_mem := fun _ _ _ _ _ => rfl)
  refine hLift.mono_outcome () R s0 hpc hrun ?_ hsp fun sf hout => ?_
  · simp only [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, hm_pts⟩
  · rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, he_st, he⟩ | ⟨ho_st, ho⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      dsimp only [allocMemcpyVmSpec]
      refine Entails.pure_left fun hpf => Entails.pure_left fun ⟨horc, hsym, hx0f⟩ => ?_
      rcases hpf with ⟨hfs, htr, htp, hsig, hbrk, hbrks, hphys, hperm⟩
      exact Entails.pure_right
        ⟨hx0f, ⟨hfs, htr, hsig, htp, hbrks, horc, hsym⟩,
          ⟨⟨hbrks, hbrk, htp⟩, hphys, hperm, LibsignalBinary.Heap.FdsHiFrame.of_fs_eq hfs⟩⟩
        (Entails.refl _)
    · exact Or.inr (Or.inl ⟨hp_st, hp⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨code, he_st, he⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho_st, ho⟩))

/-- Panic contract for `alloc::raw_vec::handle_error(err)` covering BOTH
    `TryReserveErrorKind::CapacityOverflow` (`x0 = 0`) and `TryReserveErrorKind::AllocError`
    (`x0 = align, x1 = size`): panics with `sf.fs = s0.fs ∧ sf.trace = s0.trace` and never returns
    or OOMs. -/
def rustHandleErrorPanicSpec : Spec Unit where
  pre := fun _ s0 => stackFrameAt s0.sp 16
  post := fun _ _ _ => ⌜False⌝
  onPanic := fun _ s0 sf => ⌜sf.fs = s0.fs ∧ sf.trace = s0.trace⌝ ∗ anyHeap

/-- Discharge `rustHandleErrorPanicSpec` when `handle_error` is mapped to `Rust.panicked`
    (as `Rust.withPanics` and `withImagePanics` install it). -/
theorem rustHandleErrorPanic_of_extern {P : Program} {handleErrorAddr : BitVec 64}
    (hExt : P.externAt? handleErrorAddr = some Rust.panicked) :
    subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec := by
  apply subroutine_ok_outcome_intro
  intro _ R s0 hpc hrun hpre _hsp
  apply reaches_outcome_rust_panicked hrun (hpc ▸ hExt)
  dsimp only [rustHandleErrorPanicSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨rfl, rfl⟩, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hpre⟩

/-- Bundle of auxiliary callee contracts consumed by `<String as Clone>::clone` and
    `<RawVec<u8>>::grow_one`. -/
structure RustStdAllocAuxEntries (P : Program)
    (shimAddr memcpyAddr handleErrorAddr : BitVec 64) : Prop where
  shim_ok        : subroutine_ok P shimAddr rustAllocShimVmSpec
  memcpy_ok      : subroutine_ok P memcpyAddr allocMemcpyVmSpec
  handleError_ok : subroutine_ok P handleErrorAddr rustHandleErrorPanicSpec

/-- Split `stackAt sp extHookStack` (`16384` B) into `<String as Clone>::clone`'s `48`-byte frame,
    `allocHookStack` (`4096` B), and `12240` B slack. -/
theorem extHookStack_split_48 (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackFrameAt sp 48 ∗
        (stackAt (sp - 48#64) allocHookStack ∗
          stackFrameAt (sp - 48#64 - 4096#64) 12240) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 48#64) 4096 (by decide),
      show (16384 : Nat) = 48 + 16336 from rfl,
      stackFrameAt_split sp 48 16336 (by decide),
      show (16336 : Nat) = 4096 + 12240 from rfl,
      stackFrameAt_split (sp - 48#64) 4096 12240 (by decide)]

/-- Split `stackAt sp extHookStack` (`16384` B) into `<RawVec<u8>>::grow_one`'s `64`-byte frame,
    `RawVecInner::finish_grow`'s `32`-byte frame, `allocHookStack` (`4096` B), and `12192` B slack. -/
theorem extHookStack_split_64_32 (sp : BitVec 64) :
    stackAt sp extHookStack =
      stackFrameAt sp 64 ∗
        (stackFrameAt (sp - 64#64) 32 ∗
          (stackAt (sp - 64#64 - 32#64) allocHookStack ∗
            stackFrameAt (sp - 64#64 - 32#64 - 4096#64) 12192)) := by
  unfold stackAt extHookStack allocHookStack
  change memRegion (sp - 16384#64) 16384 = _
  rw [← stackFrameAt_eq_memRegion sp 16384 (by decide),
      ← stackFrameAt_eq_memRegion (sp - 64#64 - 32#64) 4096 (by decide),
      show (16384 : Nat) = 64 + 16320 from rfl,
      stackFrameAt_split sp 64 16320 (by decide),
      show (16320 : Nat) = 32 + 16288 from rfl,
      stackFrameAt_split (sp - 64#64) 32 16288 (by decide),
      show (16288 : Nat) = 4096 + 12192 from rfl,
      stackFrameAt_split (sp - 64#64 - 32#64) 4096 12192 (by decide)]

/-! ## Unconditional `B` Branch-Stub Lifts and `WordTree` Validators -/

/-- Lift `subroutine_ok P targetAddr spec` across a 1-instruction unconditional branch stub
    `hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ]` (parametric in `aliasAddr` and
    `targetAddr`, supporting normal return, `onPanic`, `onExit`, and `onOom` for any `spec`
    whose `pre`/`post`/`onPanic`/`onExit`/`onOom` are invariant under `s0.setPC targetAddr`). -/
theorem subroutine_ok_of_branchStub {α : Type} {P : Program}
    (aliasAddr targetAddr : BitVec 64) {spec : Spec α}
    (hStub : hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ])
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64),
      spec.pre x (s.setPC pc') = spec.pre x s := by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hpan_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onPanic x (s0.setPC pc') sf = spec.onPanic x s0 sf := by intros; rfl)
    (hno_exit : ∀ x (c : BitVec 64) (s0 sf : State),
      spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hTarget : subroutine_ok P targetAddr spec) :
    subroutine_ok P aliasAddr spec := by
  apply subroutine_ok_of_sepWPp_init
  intro x R s0 hpc hrun hpre hsp
  refine ⟨spec.pre x s0, hpre, ?_⟩
  have hf0 : P.fetch aliasAddr = some (.b (targetAddr - aliasAddr)) :=
    fetch_instr_at0 hStub
  have hev : P.evalInst (.b (targetAddr - aliasAddr)) (s0.setPC aliasAddr) = s0.setPC targetAddr := by
    cases s0
    dsimp only [Program.evalInst, execInstWithSvc, State.setPC]
    congr 1
    bv_omega
  have hmem : (s0.setPC targetAddr).mem = s0.mem := by cases s0; rfl
  refine SepWPp.step_pure hpc hrun hf0 hev hmem ?_
  refine SepWPp.tailcall (x := x) (F := emp) hTarget rfl hrun hsp rfl ?_ ?_ ?_ ?_ ?_
  · intro R' hm'
    rw [emp_sepConj, hpre_pc]
    exact hm'
  · intro sf code R' _ hex
    rw [hno_exit] at hex
    exact not_satisfies_false_sepConj hex
  · intro sf _ hm'
    rw [sepConj_emp, hpan_pc] at hm'
    exact hm'
  · intro sf _ _ hspf hcsf
    refine ⟨fun hm' => ?_, hspf, (CalleeSavedPreserved_setPC_left s0 sf targetAddr).mp hcsf⟩
    rw [sepConj_emp, hpost_pc] at hm'
    exact hm'
  · intro sf R' _ ho
    rw [emp_sepConj, hoom_pc] at ho
    exact ho

/-- Lift `subroutine_ok P targetAddr spec` across a 2-hop unconditional branch chain
    `snapstubAddr → aliasAddr → targetAddr` (e.g. `BL __snapstub_<k>` → `B <gnu_sym>` in `stubs.o`
    → `B <musl_sym>` in `rdl_shim.o`). Parametric in `snapstubAddr`, `aliasAddr`, and `targetAddr`. -/
theorem subroutine_ok_of_branchStub2 {α : Type} {P : Program}
    (snapstubAddr aliasAddr targetAddr : BitVec 64) {spec : Spec α}
    (hSnap : hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ])
    (hAlias : hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ])
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64),
      spec.pre x (s.setPC pc') = spec.pre x s := by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hpan_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onPanic x (s0.setPC pc') sf = spec.onPanic x s0 sf := by intros; rfl)
    (hno_exit : ∀ x (c : BitVec 64) (s0 sf : State),
      spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hTarget : subroutine_ok P targetAddr spec) :
    subroutine_ok P snapstubAddr spec :=
  subroutine_ok_of_branchStub snapstubAddr aliasAddr hSnap
    hpre_pc hpost_pc hpan_pc hno_exit hoom_pc
    (subroutine_ok_of_branchStub aliasAddr targetAddr hAlias
      hpre_pc hpost_pc hpan_pc hno_exit hoom_pc hTarget)

/-- Chain of 1-instruction unconditional `B` stubs through `hops` ending at `targetAddr`. -/
def hasBranchChain (P : Program) : List (BitVec 64) → BitVec 64 → Prop
  | [], _ => True
  | [a], targetAddr => hasInstrs P a [ .b (targetAddr - a) ]
  | a :: b :: rest, targetAddr =>
      hasInstrs P a [ .b (b - a) ] ∧ hasBranchChain P (b :: rest) targetAddr

/-- Lift `subroutine_ok P targetAddr spec` across any non-empty chain `entryAddr :: rest` of
    1-instruction unconditional `B` stubs ending at `targetAddr`. -/
theorem subroutine_ok_of_branchChain {α : Type} {P : Program}
    (entryAddr : BitVec 64) (rest : List (BitVec 64)) (targetAddr : BitVec 64) {spec : Spec α}
    (hChain : hasBranchChain P (entryAddr :: rest) targetAddr)
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64),
      spec.pre x (s.setPC pc') = spec.pre x s := by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hpan_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onPanic x (s0.setPC pc') sf = spec.onPanic x s0 sf := by intros; rfl)
    (hno_exit : ∀ x (c : BitVec 64) (s0 sf : State),
      spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hTarget : subroutine_ok P targetAddr spec) :
    subroutine_ok P entryAddr spec := by
  induction rest generalizing entryAddr with
  | nil =>
    exact subroutine_ok_of_branchStub entryAddr targetAddr hChain
      hpre_pc hpost_pc hpan_pc hno_exit hoom_pc hTarget
  | cons next tail ih =>
    exact subroutine_ok_of_branchStub entryAddr next hChain.1
      hpre_pc hpost_pc hpan_pc hno_exit hoom_pc (ih next hChain.2)

/-- Discharge `hasInstrs P fnAddr is` on any linked ELF `Program` via kernel evaluation over its
    `WordTree` (`checkShimInstrsAt P.base t fnAddr is = true`), requiring only that no hook sits
    in the instruction range `[fnAddr - P.base, fnAddr - P.base + 4 * is.length)` (which holds both
    when `P.externs` is empty and when `P` installs panic externs at stub addresses outside `.text`). -/
theorem hasShimInstrs_of_wordTree {P : Program} {t : WordTree}
    {fnAddr : BitVec 64} {is : List Instr} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < is.length → P.hookAtOff? ((fnAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t fnAddr is = true) :
    hasInstrs P fnAddr is := by
  simp only [checkShimInstrsAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  intro i hi
  have hmem : i ∈ List.range is.length := List.mem_range.mpr hi
  have hall := beq_iff_eq.mp (List.all_eq_true.mp hok.2 i hmem)
  rw [List.getElem?_eq_getElem hi] at hall
  have hf := fetch_of_wordTree n hcode hwf hall (by omega) (hhook i hi)
  have hbase : P.base + BitVec.ofNat 64 (fnAddr - P.base).toNat = fnAddr := hok.1.1
  have hadd :
      P.base + BitVec.ofNat 64 ((fnAddr - P.base).toNat + 4 * i) =
        fnAddr + BitVec.ofNat 64 (4 * i) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hbase]
  rwa [hadd] at hf

/-- Discharge `hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ]` on any linked ELF `Program`
    via kernel evaluation over its `WordTree` (`checkShimInstrsAt P.base t aliasAddr ... = true`). -/
theorem hasBranchStub_of_wordTree {P : Program} {t : WordTree}
    {aliasAddr targetAddr : BitVec 64} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t aliasAddr [ .b (targetAddr - aliasAddr) ] = true) :
    hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ] :=
  hasShimInstrs_of_wordTree n hcode hwf hhook hok

theorem subroutine_ok_of_branchStub_wordTree {α : Type} {P : Program} {t : WordTree}
    (n : Nat) (aliasAddr targetAddr : BitVec 64) {spec : Spec α}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhook : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkShimInstrsAt P.base t aliasAddr [ .b (targetAddr - aliasAddr) ] = true)
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64),
      spec.pre x (s.setPC pc') = spec.pre x s := by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hpan_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onPanic x (s0.setPC pc') sf = spec.onPanic x s0 sf := by intros; rfl)
    (hno_exit : ∀ x (c : BitVec 64) (s0 sf : State),
      spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hTarget : subroutine_ok P targetAddr spec) :
    subroutine_ok P aliasAddr spec :=
  subroutine_ok_of_branchStub aliasAddr targetAddr
    (hasBranchStub_of_wordTree n hcode hwf hhook hok)
    hpre_pc hpost_pc hpan_pc hno_exit hoom_pc hTarget

/-- Single `Bool` validator checking a 2-hop `B` stub chain `snapstubAddr → aliasAddr → targetAddr`
    in `WordTree` `t` at `fnBase` (typically `P.base`). -/
def checkBranchStub2 (fnBase : BitVec 64) (t : WordTree)
    (snapstubAddr aliasAddr targetAddr : BitVec 64) : Bool :=
  checkShimInstrsAt fnBase t snapstubAddr [ .b (aliasAddr - snapstubAddr) ] &&
  checkShimInstrsAt fnBase t aliasAddr [ .b (targetAddr - aliasAddr) ]

theorem hasBranchStub2_of_wordTree {P : Program} {t : WordTree}
    {snapstubAddr aliasAddr targetAddr : BitVec 64} (n : Nat)
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr targetAddr = true) :
    hasInstrs P snapstubAddr [ .b (aliasAddr - snapstubAddr) ] ∧
      hasInstrs P aliasAddr [ .b (targetAddr - aliasAddr) ] := by
  simp only [checkBranchStub2, Bool.and_eq_true] at hok
  exact ⟨hasBranchStub_of_wordTree n hcode hwf hhookSnap hok.1,
    hasBranchStub_of_wordTree n hcode hwf hhookAlias hok.2⟩

theorem subroutine_ok_of_branchStub2_wordTree {α : Type} {P : Program} {t : WordTree}
    (n : Nat) (snapstubAddr aliasAddr targetAddr : BitVec 64) {spec : Spec α}
    (hcode : P.code = t.toBytes) (hwf : t.checkSize? = some n)
    (hhookSnap : ∀ i, i < 1 → P.hookAtOff? ((snapstubAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hhookAlias : ∀ i, i < 1 → P.hookAtOff? ((aliasAddr - P.base).toNat + 4 * i) = none := by
      intro _ _; exact hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) _)
    (hok : checkBranchStub2 P.base t snapstubAddr aliasAddr targetAddr = true)
    (hpre_pc : ∀ x (s : State) (pc' : BitVec 64),
      spec.pre x (s.setPC pc') = spec.pre x s := by intros; rfl)
    (hpost_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.post x (s0.setPC pc') sf = spec.post x s0 sf := by intros; rfl)
    (hpan_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onPanic x (s0.setPC pc') sf = spec.onPanic x s0 sf := by intros; rfl)
    (hno_exit : ∀ x (c : BitVec 64) (s0 sf : State),
      spec.onExit x c s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom_pc : ∀ x (s0 sf : State) (pc' : BitVec 64),
      spec.onOom x (s0.setPC pc') sf = spec.onOom x s0 sf := by intros; rfl)
    (hTarget : subroutine_ok P targetAddr spec) :
    subroutine_ok P snapstubAddr spec := by
  obtain ⟨hSnap, hAlias⟩ :=
    hasBranchStub2_of_wordTree n hcode hwf hhookSnap hhookAlias hok
  exact subroutine_ok_of_branchStub2 snapstubAddr aliasAddr targetAddr
    hSnap hAlias hpre_pc hpost_pc hpan_pc hno_exit hoom_pc hTarget

end LibsignalBinary.Heap.RustStdAllocBudgetBridge
