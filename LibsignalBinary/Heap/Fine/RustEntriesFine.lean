/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.Accounting
public import LibsignalBinary.Heap.Fine.CostModel
public import LibsignalBinary.Heap.MallocngRustBudget
public import LibsignalBinary.Heap.NonVacBudget
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Fine-Grained Rust Global-Allocator Bundles and Coarse Projection

Instantiates `MallocngRustBudget` and `MallocngBridgeBudget` at `fineCostModel`:
- Projects `FineCoreImpl` and `FineHeapImpl` satisfaction to the underlying coarse `MallocngWF`
  invariant and dynamic-region bounds (`coarse_of_fineCore`, `coarse_of_fine`).
- Provides `RustCliAllocBudgetEntries`, `RustCliAllocNoOomEntries`, and unbudgeted
  `RustCliAllocEntries` bundles for both direct `__rdl_*` shims and 1-instruction `__rust_*`
  `B`-thunks, paired with startup pool initialization.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.RustStd (
  MallocngCEntryAddrs RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs
)
open LibsignalBinary.Heap

/-! ## Coarse `MallocngWF` Projection (`coarse_of_fine`) -/

private theorem holds_sepConj_right {P Q : SepProp} {h : Heap}
    (hh : (P ∗ Q).holds h) :
    ∃ h₂, Q.holds h₂ := by
  rw [sepConj_comm] at hh
  exact SepProp.holds_sepConj_left hh

/-- Extract both `MallocngFineInv` and `MallocngWFInflight` from `FineCoreStInflightA`. -/
theorem coarseWf_of_fineCoreSt {inflight : Nat} {γ : GhostName}
    {A : MallocngAddrs} {brkStart brk : BitVec 64}
    {b : FineBudget} {ivs : List (BitVec 64 × Nat)}
    {alignMap : BitVec 64 → Option Nat}
    {liveCost peakCost : Nat} {st : MallocngSt} {h : Heap}
    (hHolds : SepProp.Holds
      (FineCoreStInflightA inflight γ A brkStart brk b ivs alignMap liveCost peakCost st) h) :
    MallocngFineInv inflight b ivs alignMap st ∧
    MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st := by
  have hBody :
      (FineCoreStInflightA inflight γ A brkStart brk b ivs alignMap liveCost peakCost st).holds h :=
    hHolds
  unfold FineCoreStInflightA MallocngCoreStInflightA at hBody
  obtain ⟨hFine, hRest1⟩ := SepProp.holds_pure_sepConj hBody
  obtain ⟨_, hRest2⟩ := holds_sepConj_right hRest1
  obtain ⟨hwf, _⟩ := SepProp.holds_pure_sepConj hRest2
  exact ⟨hFine, hwf⟩

/-- Project quiescent `FineCoreImpl` satisfaction to `MallocngFineInv` footprint bounds and the
    underlying coarse `MallocngWF` invariant. -/
theorem coarse_of_fineCore
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (FineCoreImpl γ A brkStart brk b ivs) h) :
    ∃ (st : MallocngSt) (alignMap : BitVec 64 → Option Nat) (liveCost peakCost : Nat),
      MallocngFineInv 0 b ivs alignMap st ∧
      MallocngWF A.base brkStart brk liveCost peakCost st ∧
      ivs = dynamicRootRegions st ∧
      (ivs.length ≤ fineMaxDynIvs b ∧
        (ivs.map Prod.snd).sum ≤ fineFootprint b ∧
        ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48) ∧
      st.masterDom.length ≤ fineFootprint b ∧
      ((dynamicRootRegions st).length ≤ 48 + peakCost / 32768 ∧
        ((dynamicRootRegions st).map Prod.snd).sum ≤
          30 * 1024 * 1024 + MallocngLinearFactor * peakCost) ∧
      st.masterDom.length ≤ 30 * 1024 * 1024 + MallocngLinearFactor * peakCost := by
  have hCore : (FineCoreImpl γ A brkStart brk b ivs).holds h := hHolds
  rw [FineCoreImpl_eq] at hCore
  obtain ⟨_, hExH⟩ := holds_sepConj_right hCore
  obtain ⟨st, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨alignMap, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨liveCost, hExH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨peakCost, hBodyH⟩ := SepProp.holds_sepExists hExH
  obtain ⟨hFine, hwf⟩ := coarseWf_of_fineCoreSt hBodyH
  have hIvs : ivs = dynamicRootRegions st := hFine.ivs_eq rfl
  have hFineDyn := dynamicRootRegions_fine_bounds hwf hFine
  refine ⟨st, alignMap, liveCost, peakCost, hFine, hwf, hIvs, ?_,
    masterDom_fine_length_le hwf hFine,
    dynamicRootRegions_bounds hwf,
    masterDom_length_le hwf⟩
  rwa [hIvs]

/-- Project `FineHeapImpl` satisfaction to `MallocngFineInv`, coarse `MallocngWF`, and dynamic
    virtual-memory bounds. -/
theorem coarse_of_fine
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : FineBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap)
    (hHolds : SepProp.Holds (FineHeapImpl γ A tp brkStart brk b ivs) h) :
    ∃ (st : MallocngSt) (alignMap : BitVec 64 → Option Nat) (liveCost peakCost : Nat),
      MallocngFineInv 0 b ivs alignMap st ∧
      MallocngWF A.base brkStart brk liveCost peakCost st ∧
      ivs = dynamicRootRegions st ∧
      (ivs.length ≤ fineMaxDynIvs b ∧
        (ivs.map Prod.snd).sum ≤ fineFootprint b ∧
        ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48) ∧
      st.masterDom.length ≤ fineFootprint b ∧
      ((dynamicRootRegions st).length ≤ 48 + peakCost / 32768 ∧
        ((dynamicRootRegions st).map Prod.snd).sum ≤
          30 * 1024 * 1024 + MallocngLinearFactor * peakCost) ∧
      st.masterDom.length ≤ 30 * 1024 * 1024 + MallocngLinearFactor * peakCost := by
  have hHeap : (FineHeapImpl γ A tp brkStart brk b ivs).holds h := hHolds
  rw [FineHeapImpl_eq] at hHeap
  obtain ⟨hCoreH, hCore⟩ := SepProp.holds_sepConj_left hHeap
  exact coarse_of_fineCore γ A brkStart brk b ivs hCoreH hCore

/-! ## `RustCliAllocBudgetEntries` and `RustCliAllocNoOomEntries` Bundles -/

/-- Placed `__rustc::__rdl_{alloc,dealloc,realloc}` `RustCliAllocBudgetEntries fineCostModel`
    bundle over `fineRustCliAllocBudgetAt` from an arbitrary `MallocngProgBudgetCContracts`. -/
theorem fineRustCliAllocBudgetAtEntries
    (γ : GhostName) {P : Program} {mAddrs : MallocngAddrs} (tp brkStart : BitVec 64)
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd cAddrs memcpyAddr)
    (hC : MallocngProgBudgetCContracts fineCostModel fineCostModelIface γ mAddrs tp brkStart
      P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudgetAt γ mAddrs tp brkStart)
      P rdlAddrs :=
  mallocngRustCliAllocBudgetAtEntries fineCostModelSound γ tp brkStart hShims hC hMemcpy

/-- 1-instruction `B`-thunk (`__rustc::__rust_{alloc,dealloc,realloc}`) lift of
    `fineRustCliAllocBudgetAtEntries`. -/
theorem fineRustCliAllocBudgetAtEntries_thunks
    (γ : GhostName) {P : Program} {mAddrs : MallocngAddrs} (tp brkStart : BitVec 64)
    {cAddrs : MallocngCEntryAddrs} {callocAddr : BitVec 64}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd cAddrs memcpyAddr)
    (hC : MallocngProgBudgetCContracts fineCostModel fineCostModelIface γ mAddrs tp brkStart
      P cAddrs callocAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudgetAt γ mAddrs tp brkStart)
      P thunkAddrs :=
  mallocngRustCliAllocBudgetAtEntries_thunks fineCostModelSound γ tp brkStart
    hThunks hShims hC hMemcpy

/-- Placed `__rustc::__rdl_{alloc,dealloc,realloc}` `RustCliAllocBudgetEntries fineCostModel`
    bundle for any program `P` containing `VerifiedLibraries.mallocngLib` at `mpl`. -/
theorem fineRustCliAllocBudgetEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      P rdlAddrs :=
  mallocngRustCliAllocBudgetEntries fineCostModelSound hP γ tp brkStart hShims hMemcpy

/-- 1-instruction `B`-thunk (`__rustc::__rust_{alloc,dealloc,realloc}`) lift of
    `fineRustCliAllocBudgetEntries`. -/
theorem fineRustCliAllocBudgetEntries_thunks
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      P thunkAddrs :=
  mallocngRustCliAllocBudgetEntries_thunks fineCostModelSound hP γ tp brkStart
    hThunks hShims hMemcpy

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) `RustCliAllocNoOomEntries fineCostModel`
    bundle at direct `__rustc::__rdl_{alloc,dealloc,realloc}` shims `rdlAddrs`. -/
theorem fineRustCliAllocNoOomEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocNoOomEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      lim P rdlAddrs :=
  mallocngRustCliAllocNoOomEntries fineCostModelSound hP γ tp brkStart lim hShims hMemcpy

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) `RustCliAllocNoOomEntries fineCostModel`
    bundle at 1-instruction `B`-thunk entry points `__rustc::__rust_{alloc,dealloc,realloc}`. -/
theorem fineRustCliAllocNoOomEntries_thunks
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocNoOomEntriesBase fineCostModel
      (fineRustCliAllocBudget γ mpl tp brkStart)
      lim P thunkAddrs :=
  mallocngRustCliAllocNoOomEntries_thunks fineCostModelSound hP γ tp brkStart lim
    hThunks hShims hMemcpy

/-- Unbudgeted `RustCliAllocEntries` projection over
    `(fineRustCliAllocBudget γ mpl tp brkStart).toRustCliAlloc`. -/
theorem fineRustCliAllocEntries
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocEntries
      (fineRustCliAllocBudget γ mpl tp brkStart).toRustCliAlloc
      P rdlAddrs :=
  rustCliAllocEntries_of_budgetBase (fineRustCliAllocBudgetEntries hP γ tp brkStart hShims hMemcpy)

/-- 1-instruction `B`-thunk lift of unbudgeted `fineRustCliAllocEntries`. -/
theorem fineRustCliAllocEntries_thunks
    {P : Program} {mpl : Obj.MultiPlacement}
    (hP : VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl)
    (γ : GhostName) (tp brkStart : BitVec 64)
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec) :
    RustCliAllocEntries
      (fineRustCliAllocBudget γ mpl tp brkStart).toRustCliAlloc
      P thunkAddrs :=
  rustCliAllocEntries_of_budgetBase
    (fineRustCliAllocBudgetEntries_thunks hP γ tp brkStart hThunks hShims hMemcpy)

/-! ## Startup Initialization and Entrypoint Assembly -/

/-- Instantiate `RustCliAllocBudgetEntries fineCostModel` at `__rustc::__rdl_{alloc,dealloc,realloc}`
    together with initial pool satisfaction `(fineRustCliAllocBudget γ mpl tp brkStart).pool lim fineCostModel.init s0`. -/
theorem fineRustCliAllocBudgetEntries_of_placed_init
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
      RustCliAllocBudgetEntriesBase fineCostModel A P addrs := by
  have htpLo' : 0xa4 ≤ s0.tpidrEl0.toNat := by rwa [htp]
  have htpHi' : s0.tpidrEl0.toNat ≤ 2 ^ 48 := by rwa [htp]
  have hbrkWf' : MallocngBrkStartWf s0.brkStart := by rwa [hbrkStart]
  have hbrk' : s0.brk = s0.brkStart := hbrk.trans hbrkStart.symm
  have hmem' : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mpl) s0.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R := by
    rwa [htp]
  obtain ⟨γ, hPool⟩ :=
    mallocngBudgetPool_of_init fineCostModelSound htpLo' htpHi' hbrk' hbrkWf' hInv hmem'
  rw [htp, hbrkStart] at hPool
  exact ⟨γ, hPool, fineRustCliAllocBudgetEntries hP γ tp brkStart hShims hMemcpy⟩

/-- Instantiate `RustCliAllocBudgetEntries fineCostModel` at 1-instruction `B`-thunk entry points
    (`__rustc::__rust_{alloc,dealloc,realloc}`, `thunkAddrs` forwarding to `rdlAddrs`) and initial
    budgeted pool satisfaction `(fineRustCliAllocBudget γ mpl tp brkStart).pool lim
    fineCostModel.init s0`. -/
theorem fineRustCliAllocBudgetEntries_thunks_of_placed_init
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
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs := by
  obtain ⟨γ, hPool, hRdl⟩ :=
    fineRustCliAllocBudgetEntries_of_placed_init tp brkStart auxvPtr lim staticIvs R s0
      hP hShims hMemcpy htpLo htpHi hbrkWf htp hbrkStart hbrk hInv hmem
  exact ⟨γ, hPool, RustCliAllocBudgetEntriesBase.of_thunks hThunks hRdl⟩

end LibsignalBinary.Heap.Fine
