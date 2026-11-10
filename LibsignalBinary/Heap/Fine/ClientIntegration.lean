/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# `fineCostModel` Client Integration Surface

Combines `RustEntriesFine`, `ClientBounds`, and `RustStdAllocBudgetBridge` into client-facing
startup and `FitsEvents` bridges over `fineCostModel`:
- Total-correctness (`onOom := ⌜False⌝`) startup + `RustCliAllocNoOomEntries` bundles for direct
  `__rdl_*` entrypoints and 1-instruction `__rust_*` `B`-thunks.
- Automatic `withinMaxAlloc` discharge from `FitsStep` virtual-address bounds (`2 ^ 48 < MallocngMaxAllocSize`)
  and `FitsEvents` bridges for `rustAllocEvents`, `rustDeallocEvents`, `rustReallocEvents`,
  `rawVecGrowEvents`, and `stringCloneEvents`.
- Small-bucket bounds for Kyber keys/ciphertexts (`req ≤ 1,612`) and cumulative doubling bounds for
  `Vec<Vec<u8>>` (`stride = 24`).
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine.ClientIntegration

open Arm64 Arm64.Obj
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open LibsignalBinary.Heap
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (
  stringCloneEvents rawVecNewCap rawVecGrowEvents growOneU8Events growOneVecU8Events
)
open LibsignalBinary.Heap.Fine
open LibsignalBinary.Heap.Fine.ClientBounds
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit

/-! ## Total-Correctness Startup and Entrypoint Bundles -/

/-- Placed startup initialization paired directly with total-correctness (`onOom := ⌜False⌝`)
    `RustCliAllocNoOomEntries fineCostModel` at `__rustc::__rdl_{alloc,dealloc,realloc}` (`addrs`). -/
theorem fineRustCliAllocNoOomEntries_of_placed_init
    {P : Program} {mpl : Obj.MultiPlacement}
    {addrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (tp brkStart auxvPtr : BitVec 64) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (hShims : RustStdRdlShimCode P addrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (htpLo : 0xa4 ≤ tp.toNat) (htpHi : tp.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf brkStart)
    (htp : s0.tpidrEl0 = tp) (hbrkStart : s0.brkStart = brkStart) (hbrk : s0.brk = brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl tp brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P addrs := by
  obtain ⟨γ, hPool, hEntries⟩ :=
    fineRustCliAllocBudgetEntries_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, hPool, hEntries.toNoOom lim⟩

/-- Placed startup initialization paired directly with total-correctness (`onOom := ⌜False⌝`)
    `RustCliAllocNoOomEntries fineCostModel` at 1-instruction `B`-thunk entry points
    `__rustc::__rust_{alloc,dealloc,realloc}` (`thunkAddrs`), matching the `hEntries` premise of
    `AllocContractsBudgetPlaced.of_block0_noOomEntries`. -/
theorem fineRustCliAllocNoOomEntries_thunks_of_placed_init
    {P : Program} {mpl : Obj.MultiPlacement}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (tp brkStart auxvPtr : BitVec 64) (lim : BudgetLimits)
    (staticIvs : List (BitVec 64 × Nat)) (R : SepProp) (s0 : State)
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (htpLo : 0xa4 ≤ tp.toNat) (htpHi : tp.toNat ≤ 2 ^ 48)
    (hbrkWf : MallocngBrkStartWf brkStart)
    (htp : s0.tpidrEl0 = tp) (hbrkStart : s0.brkStart = brkStart) (hbrk : s0.brk = brkStart)
    (hInv : mallocngBudgetPoolInv lim staticIvs [] s0)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) tp ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ mpl tp brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P thunkAddrs := by
  obtain ⟨γ, hPool, hEntries⟩ :=
    fineRustCliAllocBudgetEntries_thunks_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hThunks hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, hPool, hEntries.toNoOom lim⟩

/-- Convenience specialization discharging `hMemcpy` directly from `P.hasWords memcpyAddr memcpySymWords`
    on a pure-instruction program (`∀ pc, P.externAt? pc = none`). -/
theorem fineRustCliAllocNoOomEntries_thunks_of_hasWords
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hNoExt : ∀ pc, P.externAt? pc = none)
    (hWords : P.hasWords memcpyAddr memcpySymWords) :
    RustCliAllocNoOomEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      lim P thunkAddrs :=
  fineRustCliAllocNoOomEntries_thunks hP γ tp brkStart lim hThunks hShims
    (allocMemcpyVm_ok_of_hasWords P memcpyAddr hNoExt hWords)

/-! ## `withinMaxAlloc` Elimination and Call-Site `FitsEvents` Bridges -/

theorem req_add_align_le_fineStepReserveOfCum (maxReq maxAlign cumB : Nat) :
    maxReq + (max maxAlign 16 - 16) ≤ fineStepReserveOfCum maxReq maxAlign cumB := by
  unfold fineStepReserveOfCum FineStepBound
  have hle := pageAlignUp_le (maxReq + (max maxAlign 16 - 16) + 8192)
  omega

/-- Any `ev` bounded by `(maxReq, maxAlign)` automatically satisfies `ev.withinMaxAlloc` whenever
    `fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48` (which holds under every `FitsStep` `hva`
    inequality, since `2 ^ 48 < MallocngMaxAllocSize = 2 ^ 63 - 4098`). -/
theorem withinMaxAlloc_of_stepReserve_le_2pow48
    {ev : AllocEvent} {maxReq maxAlign cumB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (hstep : fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    ev.withinMaxAlloc := by
  have hbase := req_add_align_le_fineStepReserveOfCum maxReq maxAlign cumB
  cases ev with
  | alloc req =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega
  | aligned align req =>
    simp only [eventStepReq] at hreq
    simp only [eventStepAlign] at hal
    simp only [AllocEvent.withinMaxAlloc, mallocngAlignedEffSize, MallocngMaxAllocSize]
    split <;> omega
  | free _ _ =>
    exact True.intro
  | realloc _ _ newSz =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega

/-- Single-event `FitsEvent fineCostModel lim b ev` without an explicit `ev.withinMaxAlloc` premise
    (derived automatically from `hreq`, `hal`, and `hva`). -/
theorem fitsEvent_fineCostModel_of_bounds_autoWf
    {lim : BudgetLimits} {b : fineCostModel.σ} {ev : AllocEvent}
    {maxReq maxAlign cumB peakB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsEvent fineCostModel lim b ev :=
  fitsEvent_fineCostModel_of_bounds
    (withinMaxAlloc_of_stepReserve_le_2pow48 (cumB := cumB) hreq hal (by omega))
    hreq hal henf hcum hlive hpeak hram hva

/-- While subroutine-level `rustCliDeallocNoOomSpec` requires no `FitsEvents` premise
    (`onOom := ⌜False⌝`), event-list `FitsEvents` on `rustDeallocEvents size align = [.free align size]`
    reduces to `FitsStep` at `stepReserve = FineStepBound 0 16 (fineMaxMetaAreas b)`. -/
theorem fitsEvents_rustDealloc_iff
    {lim : BudgetLimits} {b : fineCostModel.σ} {size align : Nat} :
    FitsEvents fineCostModel lim b (rustDeallocEvents size align) ↔
      FitsStep lim (fineCostModel.stepReserve (.free align size) b)
        (fineCostModel.maxDynIvs b) (fineCostModel.footprint b) := by
  unfold rustDeallocEvents FitsEvents FitsEvent AllocEvent.withinMaxAlloc
  simp

/-- Event-list `FitsEvents fineCostModel lim b (rustDeallocEvents size align)` discharged from
    explicit `(henf, hcum, hlive, hpeak, hram, hva)` bounds at `(maxReq = 0, maxAlign = 16)`. -/
theorem fitsEvents_rustDealloc_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {size align cumB peakB : Nat}
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum 0 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum 0 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum 0 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum 0 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustDeallocEvents size align) := by
  unfold rustDeallocEvents
  exact ⟨fitsEvent_fineCostModel_of_bounds_autoWf (Nat.le_refl 0) (Nat.le_refl 16)
    henf hcum hlive hpeak hram hva, True.intro⟩

/-- Call-site `FitsEvents fineCostModel lim b (rustAllocEvents size align)` bridge covering both
    `[.alloc size]` (`align ≤ 16 ∧ align ≤ size`) and `[.aligned (max align 8) size]`. -/
theorem fitsEvents_rustAlloc_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {size align maxReq maxAlign cumB peakB : Nat}
    (hsize : size ≤ maxReq)
    (hal : max align 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustAllocEvents size align) := by
  unfold rustAllocEvents
  split
  · exact ⟨fitsEvent_fineCostModel_of_bounds_autoWf hsize (by simp only [eventStepAlign]; omega)
      henf hcum hlive hpeak hram hva, True.intro⟩
  · exact ⟨fitsEvent_fineCostModel_of_bounds_autoWf hsize (by simp only [eventStepAlign]; omega)
      henf hcum hlive hpeak hram hva, True.intro⟩

/-- Specialization of `fitsEvents_rustAlloc_fineCostModel_of_bounds` to standard `align ≤ 16` Rust layouts. -/
theorem fitsEvents_rustAlloc_align16_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {size align maxReq cumB peakB : Nat}
    (hsize : size ≤ maxReq)
    (hal : align ≤ 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustAllocEvents size align) :=
  fitsEvents_rustAlloc_fineCostModel_of_bounds hsize (by omega) henf hcum hlive hpeak hram hva

/-- Call-site `FitsEvents fineCostModel lim b (rustReallocEvents old new align)` bridge for standard
    `align ≤ 16 ∧ align ≤ new` Rust reallocations (`[.realloc align old new]`), checking bounds on
    pre-call state `b` only. -/
theorem fitsEvents_rustRealloc_align16_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {old new align maxReq cumB peakB : Nat}
    (hal : align ≤ 16)
    (hal_new : align ≤ new)
    (hnew : new ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustReallocEvents old new align) := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  exact ⟨fitsEvent_fineCostModel_of_bounds_autoWf hnew (by simp only [eventStepAlign]; omega)
    henf hcum hlive hpeak hram hva, True.intro⟩

/-- Shrink-safe `align ≤ 16` `FitsEvents fineCostModel lim b (rustReallocEvents old new align)`
    bridge without `align ≤ new`: when `new < align ≤ 16`, `__rdl_realloc` executes the 2-event
    fallback `[.aligned (max align 8) new, .free align old]`, and `new ≤ 15` adds at most `488` B
    to `cumSmall` before the `.free` step (`stepAligned_small_credit` + `smallAllocCost_le_488_of_le_28`). -/
theorem fitsEvents_rustRealloc_align16_any_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {old new align maxReq cumB peakB : Nat}
    (hal : align ≤ 16)
    (hnew : new ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b + 488 ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustReallocEvents old new align) := by
  by_cases hal_new : align ≤ new
  · exact fitsEvents_rustRealloc_align16_fineCostModel_of_bounds hal hal_new hnew
      henf (by omega) hlive hpeak hram hva
  · unfold rustReallocEvents
    have hcond : ¬ (align ≤ 16 ∧ align ≤ new) := fun h => hal_new h.2
    simp only [hcond, ↓reduceIte]
    have h1 : FitsEvent fineCostModel lim b (.aligned (max align 8) new) :=
      fitsEvent_fineCostModel_of_bounds_autoWf hnew (by simp only [eventStepAlign]; omega)
        henf (by omega) hlive hpeak hram hva
    have hstep := stepAligned_small_credit b (al := max align 8) (req := new)
      (by omega) (by unfold fineSmallMaxReq; omega)
    have h488 : fineSmallAllocCost new ≤ 488 :=
      smallAllocCost_le_488_of_le_28 (req := new) (by omega)
    have hcum0 : fineCumSmall b + 488 ≤ cumB := hcum
    have hlive0 : fineLiveLarge b ≤ peakB := hlive
    have hpeak0 : finePeakLarge b ≤ peakB := hpeak
    have hcum' : HasFineReallocCredit.cumSmall (M := fineCostModel)
        (fineCostModel.step (.aligned (max align 8) new) b) ≤ cumB := by
      change fineCumSmall (FineBudget.stepAligned (max align 8) new b) ≤ cumB
      omega
    have hlive' : HasFineReallocCredit.liveLarge (M := fineCostModel)
        (fineCostModel.step (.aligned (max align 8) new) b) ≤ peakB := by
      change fineLiveLarge (FineBudget.stepAligned (max align 8) new b) ≤ peakB
      omega
    have hpeak' : HasFineReallocCredit.peakLarge (M := fineCostModel)
        (fineCostModel.step (.aligned (max align 8) new) b) ≤ peakB := by
      change finePeakLarge (FineBudget.stepAligned (max align 8) new b) ≤ peakB
      omega
    have h2 : FitsEvent fineCostModel lim
        (fineCostModel.step (.aligned (max align 8) new) b) (.free align old) :=
      fitsEvent_fineCostModel_of_bounds_autoWf (Nat.zero_le maxReq)
        (by simp only [eventStepAlign]; omega) henf hcum' hlive' hpeak' hram hva
    exact ⟨h1, h2, True.intro⟩

/-- Fully general `FitsEvents fineCostModel lim b (rustReallocEvents old new align)` bridge for
    arbitrary `align`: when `¬ (align ≤ 16 ∧ align ≤ new)`, states the exact post-`aligned`
    credit premise `hpost` needed to discharge the trailing `.free align old` event. -/
theorem fitsEvents_rustRealloc_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {old new align maxReq maxAlign cumB peakB : Nat}
    (hnew : new ≤ maxReq)
    (hal : max align 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hpost : ¬ (align ≤ 16 ∧ align ≤ new) →
      let b' := fineCostModel.step (.aligned (max align 8) new) b
      HasFineReallocCredit.cumSmall (M := fineCostModel) b' ≤ cumB ∧
      HasFineReallocCredit.liveLarge (M := fineCostModel) b' ≤ peakB ∧
      HasFineReallocCredit.peakLarge (M := fineCostModel) b' ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rustReallocEvents old new align) := by
  unfold rustReallocEvents
  split
  · exact ⟨fitsEvent_fineCostModel_of_bounds_autoWf hnew (by simp only [eventStepAlign]; omega)
      henf hcum hlive hpeak hram hva, True.intro⟩
  · rename_i hnot
    obtain ⟨hcum', hlive', hpeak'⟩ := hpost hnot
    have h1 : FitsEvent fineCostModel lim b (.aligned (max align 8) new) :=
      fitsEvent_fineCostModel_of_bounds_autoWf hnew (by simp only [eventStepAlign]; omega)
        henf hcum hlive hpeak hram hva
    have h2 : FitsEvent fineCostModel lim
        (fineCostModel.step (.aligned (max align 8) new) b) (.free align old) :=
      fitsEvent_fineCostModel_of_bounds_autoWf (Nat.zero_le maxReq)
        (by simp only [eventStepAlign]; omega) henf hcum' hlive' hpeak' hram hva
    exact ⟨h1, h2, True.intro⟩

/-- Parametric `<RawVec<T>>::grow_one` (`rawVecGrowEvents elemSz minCap align cap`) `FitsEvents`
    bridge for `align ≤ 16` and `align ≤ minCap * elemSz`. -/
theorem fitsEvents_rawVecGrow_align16_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ}
    {elemSz minCap align : Nat} {cap : BitVec 64} {maxReq cumB peakB : Nat}
    (hal : align ≤ 16)
    (hal_min : align ≤ minCap * elemSz)
    (hnew : rawVecNewCap minCap cap.toNat * elemSz ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (rawVecGrowEvents elemSz minCap align cap) := by
  unfold rawVecGrowEvents
  split
  · rename_i hcap0
    have hmin_le : minCap * elemSz ≤ maxReq := by
      unfold rawVecNewCap at hnew
      have hm : minCap ≤ max (2 * cap.toNat) minCap := Nat.le_max_right _ _
      exact Nat.le_trans (Nat.mul_le_mul_right elemSz hm) hnew
    exact fitsEvents_rustAlloc_align16_fineCostModel_of_bounds hmin_le hal
      henf hcum hlive hpeak hram hva
  · have hal_new : align ≤ rawVecNewCap minCap cap.toNat * elemSz := by
      unfold rawVecNewCap
      have hm : minCap ≤ max (2 * cap.toNat) minCap := Nat.le_max_right _ _
      exact Nat.le_trans hal_min (Nat.mul_le_mul_right elemSz hm)
    exact fitsEvents_rustRealloc_align16_fineCostModel_of_bounds hal hal_new hnew
      henf hcum hlive hpeak hram hva

/-- `FitsEvents` bridge for `RawVec<u8>::grow_one` (`elemSz = 1, minCap = 8, align = 1`). -/
theorem fitsEvents_growOneU8_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {cap : BitVec 64} {maxReq cumB peakB : Nat}
    (hnew : max (2 * cap.toNat) 8 ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (growOneU8Events cap) := by
  rw [RustStdAllocBudgetBridge.growOneU8Events_eq_rawVecGrowEvents]
  exact fitsEvents_rawVecGrow_align16_fineCostModel_of_bounds
    (by decide) (by decide) (by unfold rawVecNewCap; omega)
    henf hcum hlive hpeak hram hva

/-- `FitsEvents` bridge for `RawVec<Vec<u8>>::grow_one` (`elemSz = 24, minCap = 4, align = 8`). -/
theorem fitsEvents_growOneVecU8_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {cap : BitVec 64} {maxReq cumB peakB : Nat}
    (hnew : max (2 * cap.toNat) 4 * 24 ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (growOneVecU8Events cap) :=
  fitsEvents_rawVecGrow_align16_fineCostModel_of_bounds
    (by decide) (by decide) (by unfold rawVecNewCap; exact hnew)
    henf hcum hlive hpeak hram hva

/-- `<String as Clone>::clone` (`stringCloneEvents g`) `FitsEvents` bridge: `True` when
    `g.bytes.length = 0`, and delegates to `fitsEvents_rustAlloc_align16_fineCostModel_of_bounds`
    otherwise. -/
theorem fitsEvents_stringClone_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {g : VecGhost} {maxReq cumB peakB : Nat}
    (hlen : g.bytes.length ≤ maxReq)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEvents fineCostModel lim b (stringCloneEvents g) := by
  unfold stringCloneEvents
  split
  · exact True.intro
  · exact fitsEvents_rustAlloc_align16_fineCostModel_of_bounds hlen (by decide)
      henf hcum hlive hpeak hram hva

/-- Whole-trace `FitsTrace fineCostModel` bridge without an explicit `ev.withinMaxAlloc` conjunct
    in `hevs` (derived automatically from `eventStepReq`, `eventStepAlign`, and `hva`). -/
theorem fitsTrace_fineCostModel_of_bounds_autoWf
    {lim : BudgetLimits} {fullLog : List AllocEvent}
    {maxReq maxAlign cumB peakB : Nat}
    (hevs : ∀ ev ∈ fullLog,
      eventStepReq ev ≤ maxReq ∧ max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum maxReq maxAlign cumB) fullLog :=
  fitsTrace_fineCostModel_of_bounds
    (fun ev hmem =>
      let ⟨hreq, hal⟩ := hevs ev hmem
      ⟨withinMaxAlloc_of_stepReserve_le_2pow48 (cumB := cumB) hreq hal (by omega), hreq, hal⟩)
    henf hcum hlive hpeak hram hva

/-! ## Kyber Small-Bucket Bounds and `Vec<24>` Doubling Chain -/

theorem le_smallMaxReq_98304 :
    98304 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  decide

private def checkKyberBucket : Bool :=
  (List.range 101).all fun u =>
    let sc0 := sizeToClassUnits u
    let aWt := coarseSlotWt sc0 + (122 * coarseGrpWtS sc0 + FineScale - 1) / FineScale
    decide (
      aWt ≤ 9789 ∧
      (62 ≤ u → aWt ≤ 3506) ∧
      (93 ≤ u → aWt ≤ 2792))

private theorem checkKyberBucket_true : checkKyberBucket = true := by
  decide +kernel

/-- Uniform small-bucket bound for all requests `req ≤ 1,612` (`(req + 3) / 16 ≤ 100`, covering
    32–96 B Curve25519/AES/HMAC keys as well as 1,568–1,569 B Kyber1024 public keys & ciphertexts):
    `smallAllocCost fineCostModel req ≤ 9,789`. -/
theorem smallAllocCost_le_9789_of_le_1612 {req : Nat} (hreq : req ≤ 1612) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  change fineSmallAllocCost req ≤ 9789
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 101 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkKyberBucket_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).1

/-- Tight Kyber768/Kyber1024 public-key & ciphertext range bound (`989 ≤ req ≤ 1,612`):
    `smallAllocCost fineCostModel req ≤ 3,506`. -/
theorem smallAllocCost_le_3506_of_kyber_range {req : Nat}
    (hlo : 989 ≤ req) (hhi : req ≤ 1612) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 3506 := by
  change fineSmallAllocCost req ≤ 3506
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 101 := by omega
  have hu62 : 62 ≤ (req + 3) / 16 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkKyberBucket_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.1 hu62

/-- Exact Kyber1024 public-key & ciphertext sub-bucket bound (`1,485 ≤ req ≤ 1,612`):
    `smallAllocCost fineCostModel req ≤ 2,792`. -/
theorem smallAllocCost_le_2792_of_kyber1024_range {req : Nat}
    (hlo : 1485 ≤ req) (hhi : req ≤ 1612) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 2792 := by
  change fineSmallAllocCost req ≤ 2792
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 101 := by omega
  have hu93 : 93 ≤ (req + 3) / 16 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkKyberBucket_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.2 hu93

private def intPointPairs : List (Bool × Nat × Nat) :=
  [ (true, 32, 738), (true, 33, 738), (true, 64, 1607),
    (true, 1088, 2109), (true, 1184, 2109),
    (true, 1568, 2792), (true, 1569, 2792),
    (true, 2400, 4218), (true, 3168, 4218),
    (true, 96, 1997),
    (false, 192, 8604), (false, 384, 8734), (false, 768, 9085), (false, 1536, 9853),
    (false, 3072, 11389), (false, 6144, 14461), (false, 12288, 20605),
    (false, 24576, 32893), (false, 49152, 57469), (false, 98304, 106621) ]

private def checkIntPoints : Bool :=
  intPointPairs.all fun (isAlloc, req, expected) =>
    if isAlloc then fineSmallAllocCost req == expected
    else fineSmallReallocCost req == expected

private theorem checkIntPoints_true : checkIntPoints = true := by
  decide +kernel

private theorem extractIntAllocPoint {req expected : Nat}
    (hmem : (true, req, expected) ∈ intPointPairs) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  have hcell := List.all_eq_true.mp checkIntPoints_true (true, req, expected) hmem
  exact of_decide_eq_true hcell

private theorem extractIntReallocPoint {req expected : Nat}
    (hmem : (false, req, expected) ∈ intPointPairs) :
    HasFineReallocCredit.smallReallocCost fineCostModel req = expected := by
  change fineSmallReallocCost req = expected
  have hcell := List.all_eq_true.mp checkIntPoints_true (false, req, expected) hmem
  exact of_decide_eq_true hcell

@[scoped simp] theorem smallAllocCost_32 :
    HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_33 :
    HasFineReallocCredit.smallAllocCost fineCostModel 33 = 738 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_64 :
    HasFineReallocCredit.smallAllocCost fineCostModel 64 = 1607 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_1088 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1088 = 2109 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_1184 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1184 = 2109 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_1568 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1568 = 2792 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_1569 :
    HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_2400 :
    HasFineReallocCredit.smallAllocCost fineCostModel 2400 = 4218 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_3168 :
    HasFineReallocCredit.smallAllocCost fineCostModel 3168 = 4218 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallAllocCost_96 :
    HasFineReallocCredit.smallAllocCost fineCostModel 96 = 1997 :=
  extractIntAllocPoint (by decide)

@[scoped simp] theorem smallReallocCost_192 :
    HasFineReallocCredit.smallReallocCost fineCostModel 192 = 8604 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_384 :
    HasFineReallocCredit.smallReallocCost fineCostModel 384 = 8734 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_768 :
    HasFineReallocCredit.smallReallocCost fineCostModel 768 = 9085 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_1536 :
    HasFineReallocCredit.smallReallocCost fineCostModel 1536 = 9853 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_3072 :
    HasFineReallocCredit.smallReallocCost fineCostModel 3072 = 11389 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_6144 :
    HasFineReallocCredit.smallReallocCost fineCostModel 6144 = 14461 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_12288 :
    HasFineReallocCredit.smallReallocCost fineCostModel 12288 = 20605 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_24576 :
    HasFineReallocCredit.smallReallocCost fineCostModel 24576 = 32893 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_49152 :
    HasFineReallocCredit.smallReallocCost fineCostModel 49152 = 57469 :=
  extractIntReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_98304 :
    HasFineReallocCredit.smallReallocCost fineCostModel 98304 = 106621 :=
  extractIntReallocPoint (by decide)

/-- Per-step `cumSmall` charge of one `RawVec<Vec<u8>>::grow_one` step (`0 → 4` or `cap → 2 * cap`,
    stride `24`, `minCap = 4`, `align = 8`). -/
def fineVec24StepCumCost (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap = 0 then
    if 4 * 24 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallAllocCost M (4 * 24)
    else
      HasFineReallocCredit.largeMetaCost M
  else
    if 2 * cap * 24 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallReallocCost M (2 * cap * 24)
    else
      HasFineReallocCredit.largeMetaCost M

/-- Cumulative `cumSmall` upper bound along the `Vec<24>` doubling chain `0 → 4 → 8 → … → cap`. -/
def fineVec24CumOfCap (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap < 4 then 0
  else if cap < 8 then fineVec24StepCumCost M 0
  else fineVec24CumOfCap M (cap / 2) + fineVec24StepCumCost M (cap / 2)
termination_by cap
decreasing_by omega

@[scoped simp] theorem fineVec24CumOfCap_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVec24CumOfCap M 0 = 0 := by
  unfold fineVec24CumOfCap
  rfl

theorem fineVec24CumOfCap_four (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVec24CumOfCap M 4 = fineVec24StepCumCost M 0 := by
  unfold fineVec24CumOfCap
  rfl

theorem fineVec24CumOfCap_two_mul (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : 4 ≤ cap) :
    fineVec24CumOfCap M (2 * cap) = fineVec24CumOfCap M cap + fineVec24StepCumCost M cap := by
  conv_lhs => unfold fineVec24CumOfCap
  have h1 : ¬ (2 * cap < 4) := by omega
  have h2 : ¬ (2 * cap < 8) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

theorem fineVec24CumOfCap_pow2_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {i j : Nat} (hij : i ≤ j) :
    fineVec24CumOfCap M (4 * 2 ^ i) ≤ fineVec24CumOfCap M (4 * 2 ^ j) := by
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i k _
    have hge : 4 ≤ 4 * 2 ^ k := by
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVec24CumOfCap_two_mul M hge]
    omega

private theorem fineVec24StepCumCost_small {cap : Nat} (hne : cap ≠ 0)
    (hle : 2 * cap * 24 ≤ 135167) :
    fineVec24StepCumCost fineCostModel cap =
      HasFineReallocCredit.smallReallocCost fineCostModel (2 * cap * 24) := by
  unfold fineVec24StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hle, ↓reduceIte]

theorem fineVec24StepCumCost_large_of_ge_4096 {cap : Nat} (hge : 4096 ≤ cap) :
    fineVec24StepCumCost fineCostModel cap = 122 := by
  have hne : cap ≠ 0 := by omega
  have hgt : ¬ (2 * cap * 24 ≤ 135167) := by omega
  unfold fineVec24StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hgt, fineCostModel_largeMetaCost_eq, ↓reduceIte]

@[scoped simp] theorem fineVec24CumOfCap_4 :
    fineVec24CumOfCap fineCostModel 4 = 1997 := by
  rw [fineVec24CumOfCap_four]
  unfold fineVec24StepCumCost
  have hle : 4 * 24 ≤ 135167 := by decide
  simp only [fineCostModel_smallMaxReq_eq, hle, ↓reduceIte]
  exact smallAllocCost_96

@[scoped simp] theorem fineVec24CumOfCap_4096 :
    fineVec24CumOfCap fineCostModel 4096 = 281711 := by
  have h8 : fineVec24CumOfCap fineCostModel 8 = 10601 := by
    rw [show (8 : Nat) = 2 * 4 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      fineVec24CumOfCap_4, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_192]
  have h16 : fineVec24CumOfCap fineCostModel 16 = 19335 := by
    rw [show (16 : Nat) = 2 * 8 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h8, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_384]
  have h32 : fineVec24CumOfCap fineCostModel 32 = 28420 := by
    rw [show (32 : Nat) = 2 * 16 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h16, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_768]
  have h64 : fineVec24CumOfCap fineCostModel 64 = 38273 := by
    rw [show (64 : Nat) = 2 * 32 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h32, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_1536]
  have h128 : fineVec24CumOfCap fineCostModel 128 = 49662 := by
    rw [show (128 : Nat) = 2 * 64 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h64, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_3072]
  have h256 : fineVec24CumOfCap fineCostModel 256 = 64123 := by
    rw [show (256 : Nat) = 2 * 128 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h128, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_6144]
  have h512 : fineVec24CumOfCap fineCostModel 512 = 84728 := by
    rw [show (512 : Nat) = 2 * 256 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h256, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_12288]
  have h1024 : fineVec24CumOfCap fineCostModel 1024 = 117621 := by
    rw [show (1024 : Nat) = 2 * 512 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h512, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_24576]
  have h2048 : fineVec24CumOfCap fineCostModel 2048 = 175090 := by
    rw [show (2048 : Nat) = 2 * 1024 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
      h1024, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_49152]
  rw [show (4096 : Nat) = 2 * 2048 from rfl, fineVec24CumOfCap_two_mul _ (by decide),
    h2048, fineVec24StepCumCost_small (by decide) (by decide), smallReallocCost_98304]

theorem fineVec24CumOfCap_pow2_ge_10 {j : Nat} (hj : 10 ≤ j) :
    fineVec24CumOfCap fineCostModel (4 * 2 ^ j) = 281711 + 122 * (j - 10) := by
  induction hj with
  | refl =>
    exact fineVec24CumOfCap_4096
  | @step k hle ih =>
    have hk : 10 ≤ k := hle
    have hk_pow : 2 ^ 10 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hge4096 : 4096 ≤ 4 * 2 ^ k := by omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVec24CumOfCap_two_mul _ (by omega), ih,
      fineVec24StepCumCost_large_of_ge_4096 hge4096]
    omega

@[scoped simp] theorem fineVec24CumOfCap_2pow20 :
    fineVec24CumOfCap fineCostModel (2 ^ 20) = 282687 := by
  have h := fineVec24CumOfCap_pow2_ge_10 (j := 18) (by decide)
  simpa using h

theorem fineVec24CumOfCap_le_281711 {cap : Nat}
    (hpow : cap = 0 ∨ ∃ j, cap = 4 * 2 ^ j) (hle : cap ≤ 4096) :
    fineVec24CumOfCap fineCostModel cap ≤ 281711 := by
  rcases hpow with rfl | ⟨j, rfl⟩
  · simp
  · have hj : j ≤ 10 := by
      by_contra hgt
      have h11 : 11 ≤ j := by omega
      have hp : 2 ^ 11 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h11
      omega
    exact Nat.le_trans (fineVec24CumOfCap_pow2_mono fineCostModel hj)
      (Nat.le_of_eq fineVec24CumOfCap_4096)

theorem fineVec24CumOfCap_le_282687 {cap : Nat}
    (hpow : cap = 0 ∨ ∃ j, cap = 4 * 2 ^ j) (hle : cap ≤ 2 ^ 20) :
    fineVec24CumOfCap fineCostModel cap ≤ 282687 := by
  rcases hpow with rfl | ⟨j, rfl⟩
  · simp
  · have hj : j ≤ 18 := by
      by_contra hgt
      have h19 : 19 ≤ j := by omega
      have hp : 2 ^ 19 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h19
      omega
    have hmono := fineVec24CumOfCap_pow2_mono fineCostModel hj
    have heq18 := fineVec24CumOfCap_pow2_ge_10 (j := 18) (by decide)
    omega

end LibsignalBinary.Heap.Fine.ClientIntegration
