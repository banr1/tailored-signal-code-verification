/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.Bytes
public import VerifiedLibraries.Mallocng.Proofs.Common
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.Fine.AllocZeroedFine
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.CliPlacement
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie
public import LibsignalBinary.Heap.IfaceBudgetBase
public meta import ProofLib.ProgramReflection

/-!
# Concrete Startup, Initial-Pool, and Branch-Stub Witnesses on `f3TrialElf`

**Checked by Lean.** Instantiates on `f3TrialElf` (via `F3LayoutData`):
- `F3StartupCode` and whole-process `musl` startup/exit harnesses (`MuslHarnessNeedLocksN 80`,
  `MuslHarnessN 80`);
- separation-logic entailments from `StdExtraRo ∗ StdExtraRw` to `mallocngLib.dataInit f3MallocngMpl`;
- fine-budget and no-OOM Rust global allocator contracts (`__rdl_{alloc,dealloc,realloc,alloc_zeroed}`)
  on `f3TrialRxProg` (`seg[5]`);
- `ElfInitFine` pool and `cMainAddr` entry witnesses; and
- 1-hop `.img.text` (`seg[1]`) `--branch-stubs` `Instr.b` execution lifts into `seg[5]`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection ProofLib.StdStartup
open VerifiedLibraries.Mallocng (
  MallocngAuxvAt MallocngBrkStartWf MallocngRoTablesAt MallocngRuntime
  mallocngAddrsOfPlacement mallocngSizeClassBytes mallocngDebruijn32Table
  mallocngMedCntTabBytes mallocngSmallCntTabBytes
)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng mallocngLib_dataInit_eq)
open VerifiedLibraries.RustStd (StdErrnoCell mallocngPlacedCAddrs mallocngRustCliAlloc)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SignalSession (
  Inputs cliProcessInputs patchElfTokensPlaced
)
open CryptoVerification.SignalSession.Cli (
  cliInputs CliInputsOk InputsLoadable
)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk)
open CryptoVerification.SignalSession.InitStack (cliStackSize)
open LibsignalBinary.Heap (
  BudgetLimits RustAllocAddrs RustCliAllocBudget RustCliAllocBudgetEntriesBase RustCliAllocNoOomEntriesBase
  allocMemcpyVmSpec rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  rustCliAllocNoOomSpecBase
)
open LibsignalBinary.Heap.IfaceSimp (
  allocCallPreserved_setPC_left oomPreserved_setPC_left
)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpecBase)
open LibsignalBinary.Heap.Fine (
  CliElfMallocngLayout StartupVmPreserved allocMemsetVmSpec
  cliElf_fineBudgetPool_of_init cliElf_fineBudgetPool_and_entries_of_init
  f3SegCount f3SegByteSum f3RxWordCount f3StdLayout f3MallocngMpl
  f3StubAddrs f3RdlAddrs f3StubAzAddr f3RdlAzAddr
  fineCostModel fineRustCliAllocBudget
  fineRustCliAllocBudgetEntries fineRustCliAllocNoOomEntries
  fineRdlAllocZeroed_budget_placed_ok fineRdlAllocZeroed_noOom_placed_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.HarnessSpec (
  MuslHarnessNeedLocksN
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.TieSpec (
  steps_of_loaded_b_stub
)
open LibsignalBinary.Proofs.SignalSession.Cli.F3Relink.Startup (
  F3StartupCode checkF3StartupCode f3StartupCode_of_wordTree
  cStrAtRO argvAtRO MuslHarnessN
  f3StartupResidual f3StartupMainPre f3StartupMainPreNeedLocks
  f3InitFineBudgetPool f3InitMallocngHeap
  f3MuslHarnessNeedLocks80_of_layout f3MuslHarness80_of_layout
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Fixture (
  f3TrialElf f3TrialElf_cliElfMallocngLayout f3TrialElf_patched_cliElfMallocngLayout
)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (
  f3RxSegBase f3ImgTextBase f3TrialRxProg f3TrialRxWordTree
  f3TrialRxWordTree_eq f3TrialRxWordTree_size f3TrialRxProg_base
  f3TrialRxProg_svc f3TrialRxProg_no_ext f3TrialRxProg_externs_none
  f3TrialRxProg_overrides_none f3TrialRxProg_stubs f3TrialRxProg_symbols
  f3Trial_matchesImage f3Trial_progContainsMallocng f3Trial_seg5ShimBundle
  f3Trial_allocMemcpyVm_ok f3Trial_allocMemsetVm_ok
  f3StubAlloc_mem_targets f3StubDealloc_mem_targets f3StubRealloc_mem_targets
  f3StubAz_mem_targets f3StubAlloc_addr_eq f3StubDealloc_addr_eq
  f3StubRealloc_addr_eq f3StubAz_addr_eq f3Trial_keepsFrozen_stub_at
)

set_option maxRecDepth 400000

/-! ## Startup Code and `musl` Startup/Exit Harnesses -/

private theorem f3Trial_startupCode_chk :
    checkF3StartupCode f3StdLayout f3RxSegBase f3TrialRxWordTree = true := by
  rfl_kernel

/-- `F3StartupCode` witness for `f3TrialRxProg` (`seg[5]`). -/
theorem f3Trial_startupCode : F3StartupCode f3TrialRxProg f3StdLayout :=
  f3StartupCode_of_wordTree f3RxWordCount
    f3TrialRxWordTree_eq f3TrialRxWordTree_size
    f3TrialRxProg_svc f3TrialRxProg_stubs f3TrialRxProg_symbols
    f3TrialRxProg_externs_none f3TrialRxProg_overrides_none
    (by rw [f3TrialRxProg_base]; exact f3Trial_startupCode_chk)

/-- Whole-process `MuslHarnessNeedLocksN 80` on `f3TrialElf` (preserving writable
`(f3StdLayout.libcAddr + 3#64) ↦₈ 0#8` across `cMainAddr`) for any `Syscall.standard` program `P`
hook-free inside `seg[5]`. -/
theorem f3Trial_muslHarnessNeedLocks80 {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep f3TrialRxProg pc = true → (P.externAt? pc).isNone = true) :
    MuslHarnessNeedLocksN 80 f3StdLayout.libcAddr f3TrialElf P f3StdLayout.cMainAddr
      (StdMuslExitGlobalsNoNeedLocks f3StdLayout 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPreNeedLocks f3StdLayout f3TrialElf) :=
  f3MuslHarnessNeedLocks80_of_layout f3Trial_matchesImage f3Trial_startupCode hsvc hHookFree

/-- Whole-process `MuslHarnessN 80` on `f3TrialElf` for any `Syscall.standard` program `P`
hook-free inside `seg[5]`. -/
theorem f3Trial_muslHarness80 {P : Program}
    (hsvc : P.svc = Syscall.standard)
    (hHookFree : ∀ pc, progKeep f3TrialRxProg pc = true → (P.externAt? pc).isNone = true) :
    MuslHarnessN 80 f3TrialElf P f3StdLayout.cMainAddr
      (StdMuslExitGlobals f3StdLayout 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPre f3StdLayout f3TrialElf) :=
  f3MuslHarness80_of_layout f3Trial_matchesImage f3Trial_startupCode hsvc hHookFree

theorem f3TrialRx_muslHarnessNeedLocks80 :
    MuslHarnessNeedLocksN 80 f3StdLayout.libcAddr f3TrialElf f3TrialRxProg f3StdLayout.cMainAddr
      (StdMuslExitGlobalsNoNeedLocks f3StdLayout 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPreNeedLocks f3StdLayout f3TrialElf) :=
  f3Trial_muslHarnessNeedLocks80 f3TrialRxProg_svc
    (fun pc _ => by rw [f3TrialRxProg_no_ext pc]; rfl)

theorem f3TrialRx_muslHarness80 :
    MuslHarnessN 80 f3TrialElf f3TrialRxProg f3StdLayout.cMainAddr
      (StdMuslExitGlobals f3StdLayout 0#8)
      (fun i => CliInputsOk i ∧ InputsLoadable i)
      (f3StartupMainPre f3StdLayout f3TrialElf) :=
  f3Trial_muslHarness80 f3TrialRxProg_svc
    (fun pc _ => by rw [f3TrialRxProg_no_ext pc]; rfl)

/-! ## `StdExtraRo ∗ StdExtraRw` to `mallocngLib.dataInit` Bridge -/

/-- `MallocngAddrs` resolved from `f3MallocngMpl`. -/
noncomputable abbrev f3MAddrs : VerifiedLibraries.Mallocng.MallocngAddrs :=
  mallocngAddrsOfPlacement f3MallocngMpl

/-- Zero-initialized alignment padding (`4` + `5` bytes) inside the 200-byte `mallocng` `.rodata`
block. -/
noncomputable def f3MallocngRoPad : SepProp :=
  ((f3MAddrs.sizeClasses + 132#64) ↦ᵣ List.replicate 4 0#8) ∗
  ((f3MAddrs.sizeClasses + 163#64) ↦ᵣ List.replicate 5 0#8)

theorem f3MAddrs_libc : f3MAddrs.libc = f3StdLayout.libcAddr := by
  rfl_kernel

private theorem f3MAddrs_debruijnFree :
    f3MAddrs.debruijnFree = f3MAddrs.sizeClasses + 96#64 := by
  rfl_kernel

private theorem f3MAddrs_medCntTab :
    f3MAddrs.medCntTab = f3MAddrs.sizeClasses + 128#64 := by
  rfl_kernel

private theorem f3MAddrs_smallCntTab :
    f3MAddrs.smallCntTab = f3MAddrs.sizeClasses + 136#64 := by
  rfl_kernel

private theorem f3MAddrs_debruijnAlloc :
    f3MAddrs.debruijnAlloc = f3MAddrs.sizeClasses + 168#64 := by
  rfl_kernel

private theorem f3ExtraRo_eq :
    f3StdLayout.extraRoSlices = [(f3MAddrs.sizeClasses, ProofLib.mallocngRoTablesBytes)] := by
  rfl_kernel

private theorem f3ExtraRw_eq :
    f3StdLayout.extraRwAtoms =
      [ .u32 f3MAddrs.lock 0#32,
        .u32 f3MAddrs.aaReplaced 0#32,
        .u32 f3MAddrs.replaced 0#32,
        .bytes f3MAddrs.ctx (List.replicate 928 0#8) ] := by
  rfl_kernel

private theorem roTablesBytes_eq :
    ProofLib.mallocngRoTablesBytes = VerifiedLibraries.Mallocng.mallocngRoTablesBytes := by
  rfl_kernel

private theorem len_sizeClassBytes : mallocngSizeClassBytes.length = 96 := by rfl_kernel
private theorem len_debruijn32Table : mallocngDebruijn32Table.length = 32 := by rfl_kernel
private theorem len_medCntTabBytes : mallocngMedCntTabBytes.length = 4 := by rfl_kernel
private theorem len_smallCntTabBytes : mallocngSmallCntTabBytes.length = 27 := by rfl_kernel

private theorem roTablesBytes_pointsToRO_split (sc : BitVec 64) :
    (sc ↦ᵣ VerifiedLibraries.Mallocng.mallocngRoTablesBytes) =
      (sc ↦ᵣ mallocngSizeClassBytes) ∗
      ((sc + 96#64) ↦ᵣ mallocngDebruijn32Table) ∗
      ((sc + 128#64) ↦ᵣ mallocngMedCntTabBytes) ∗
      ((sc + 132#64) ↦ᵣ List.replicate 4 0#8) ∗
      ((sc + 136#64) ↦ᵣ mallocngSmallCntTabBytes) ∗
      ((sc + 163#64) ↦ᵣ List.replicate 5 0#8) ∗
      ((sc + 168#64) ↦ᵣ mallocngDebruijn32Table) := by
  unfold VerifiedLibraries.Mallocng.mallocngRoTablesBytes
  simp only [List.append_assoc]
  rw [pointsToBytesRO_append, len_sizeClassBytes]
  rw [show sc + BitVec.ofNat 64 96 = sc + 96#64 from rfl]
  rw [pointsToBytesRO_append, len_debruijn32Table]
  rw [show sc + 96#64 + BitVec.ofNat 64 32 = sc + 128#64 by bv_omega]
  rw [pointsToBytesRO_append, len_medCntTabBytes]
  rw [show sc + 128#64 + BitVec.ofNat 64 4 = sc + 132#64 by bv_omega]
  rw [pointsToBytesRO_append, List.length_replicate]
  rw [show sc + 132#64 + BitVec.ofNat 64 4 = sc + 136#64 by bv_omega]
  rw [pointsToBytesRO_append, len_smallCntTabBytes]
  rw [show sc + 136#64 + BitVec.ofNat 64 27 = sc + 163#64 by bv_omega]
  rw [pointsToBytesRO_append, List.length_replicate]
  rw [show sc + 163#64 + BitVec.ofNat 64 5 = sc + 168#64 by bv_omega]

/-- Unpacks `StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout` into `MallocngRoTablesAt f3MAddrs`,
the four `mallocng` `.bss` globals, and `f3MallocngRoPad`. -/
theorem f3StdExtra_entails_mallocngStartupData :
    StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout ⊢
      MallocngRoTablesAt f3MAddrs ∗
      (f3MAddrs.ctx ↦ₛ List.replicate 928 0#8) ∗
      (f3MAddrs.lock ↦₃₂ 0#32) ∗
      (f3MAddrs.replaced ↦₃₂ 0#32) ∗
      (f3MAddrs.aaReplaced ↦₃₂ 0#32) ∗
      f3MallocngRoPad := by
  unfold StdExtraRo StdExtraRw
  rw [f3ExtraRo_eq, f3ExtraRw_eq]
  dsimp only [roSliceListSep, rwAtomListSep, RwAtom.toSepProp]
  rw [roTablesBytes_eq, roTablesBytes_pointsToRO_split f3MAddrs.sizeClasses]
  unfold MallocngRoTablesAt f3MallocngRoPad
  rw [f3MAddrs_debruijnFree, f3MAddrs_medCntTab, f3MAddrs_smallCntTab, f3MAddrs_debruijnAlloc]
  sep_entail

/-- Entails `VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗ f3MallocngRoPad` from
`StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout`. -/
theorem f3StdExtra_entails_mallocngDataInit :
    StdExtraRo f3StdLayout ∗ StdExtraRw f3StdLayout ⊢
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗ f3MallocngRoPad := by
  refine Entails.trans f3StdExtra_entails_mallocngStartupData ?_
  have hEq : VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl =
      (MallocngRoTablesAt f3MAddrs ∗
        (f3MAddrs.ctx ↦ₛ List.replicate 928 0#8) ∗
        (f3MAddrs.lock ↦₃₂ 0#32) ∗
        (f3MAddrs.replaced ↦₃₂ 0#32) ∗
        (f3MAddrs.aaReplaced ↦₃₂ 0#32)) :=
    mallocngLib_dataInit_eq f3MallocngMpl
  rw [hEq]
  sep_entail

/-! ## Rust Global Allocator Contracts on `f3TrialRxProg` -/

/-- Fine-budget `RustCliAllocBudgetEntries` for `__rdl_{alloc,dealloc,realloc}` on `f3TrialRxProg`. -/
theorem f3Trial_fineRustCliAllocBudgetEntries (γ : GhostName) (tp brkStart : BitVec 64) :
    RustCliAllocBudgetEntriesBase fineCostModel
      (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart)
      f3TrialRxProg f3RdlAddrs :=
  fineRustCliAllocBudgetEntries f3Trial_progContainsMallocng γ tp brkStart
    f3Trial_seg5ShimBundle.rdlShims f3Trial_allocMemcpyVm_ok

/-- No-OOM (`onOom := ⌜False⌝`) `RustCliAllocNoOomEntries` for `__rdl_{alloc,dealloc,realloc}` on
`f3TrialRxProg`. -/
theorem f3Trial_fineRustCliAllocNoOomEntries (γ : GhostName) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    RustCliAllocNoOomEntriesBase fineCostModel
      (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart)
      lim f3TrialRxProg f3RdlAddrs :=
  fineRustCliAllocNoOomEntries f3Trial_progContainsMallocng γ tp brkStart lim
    f3Trial_seg5ShimBundle.rdlShims f3Trial_allocMemcpyVm_ok

/-- Fine-budget `rustAllocZeroedBudgetSpec` for `__rdl_alloc_zeroed` at `f3RdlAzAddr` on
`f3TrialRxProg`. -/
theorem f3Trial_fineRdlAllocZeroed_ok (γ : GhostName) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    subroutine_ok f3TrialRxProg f3RdlAzAddr
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim) :=
  fineRdlAllocZeroed_budget_placed_ok f3Trial_progContainsMallocng γ tp brkStart
    f3RdlAzAddr f3StdLayout.memsetAddr lim
    f3Trial_seg5ShimBundle.allocZeroedInstrs f3Trial_allocMemsetVm_ok

/-- No-OOM (`onOom := ⌜False⌝`) `rustCliAllocNoOomSpec` for `__rdl_alloc_zeroed` at `f3RdlAzAddr`
on `f3TrialRxProg`. -/
theorem f3Trial_fineRdlAllocZeroed_noOom_ok (γ : GhostName) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) :
    subroutine_ok f3TrialRxProg f3RdlAzAddr
      (rustCliAllocNoOomSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim true) :=
  fineRdlAllocZeroed_noOom_placed_ok f3Trial_progContainsMallocng γ tp brkStart
    f3RdlAzAddr f3StdLayout.memsetAddr lim
    f3Trial_seg5ShimBundle.allocZeroedInstrs f3Trial_allocMemsetVm_ok

/-! ## `ElfInitFine` Pool and `cMainAddr` Entry Witnesses -/

/-- Initial `A.pool lim fineCostModel.init s0` witness on `f3TrialElf` from `ElfInitFine`. -/
theorem f3TrialElf_fineBudgetPool_of_init {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hLoad : f3TrialElf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 164 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗
        MallocngRuntime f3MAddrs s0.tpidrEl0 ∗
        ((f3MAddrs.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R :=
  cliElf_fineBudgetPool_of_init
    (f3TrialElf_cliElfMallocngLayout hcnt hbytes hphys)
    hLoad hVm htpLo htpHi hmem

/-- Token-patched counterpart of `f3TrialElf_fineBudgetPool_of_init` on
`patchElfTokensPlaced f3TrialElf`. -/
theorem f3TrialElf_patched_fineBudgetPool_of_init [LibsignalPlacement] {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hLoad : (patchElfTokensPlaced f3TrialElf).loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 164 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗
        MallocngRuntime f3MAddrs s0.tpidrEl0 ∗
        ((f3MAddrs.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl s0.tpidrEl0 s0.brkStart
      s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R :=
  cliElf_fineBudgetPool_of_init
    (f3TrialElf_patched_cliElfMallocngLayout hcnt hbytes hphys)
    hLoad hVm htpLo htpHi hmem

/-- Combines `f3TrialElf_fineBudgetPool_of_init` with `RustCliAllocBudgetEntries` for any program
`P` containing `mallocngLib`, 1-instruction `B`-thunks, `rdl_shim`, and `memcpy`. -/
theorem f3TrialElf_fineBudgetPool_and_entries_of_init
    {P : Program} {lim : BudgetLimits}
    {thunkAddrs rdlAddrs : RustAllocAddrs} {memcpyAddr : BitVec 64}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hP : ProgContainsMallocng P f3MallocngMpl)
    (hThunks : VerifiedLibraries.RustStd.RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : VerifiedLibraries.RustStd.RustStdRdlShimCode P rdlAddrs.toRustStd
      (mallocngPlacedCAddrs f3MallocngMpl) memcpyAddr)
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hLoad : f3TrialElf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 164 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗
        MallocngRuntime f3MAddrs s0.tpidrEl0 ∗
        ((f3MAddrs.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl s0.tpidrEl0 s0.brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs :=
  cliElf_fineBudgetPool_and_entries_of_init hP hThunks hShims hMemcpy
    (f3TrialElf_cliElfMallocngLayout hcnt hbytes hphys)
    hLoad hVm htpLo htpHi hmem

/-- Closed `seg[5]` counterpart of `f3TrialElf_fineBudgetPool_and_entries_of_init` on
`f3TrialRxProg` at `f3RdlAddrs` and `f3RdlAzAddr`. -/
theorem f3TrialElf_rdl_fineBudgetPool_and_entries_of_init {lim : BudgetLimits}
    {i : Inputs} {sLoad s0 : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hLoad : f3TrialElf.loadState (cliProcessInputs i) = .ok sLoad)
    (hVm : StartupVmPreserved sLoad s0)
    (htpLo : 164 ≤ s0.tpidrEl0.toNat)
    (htpHi : s0.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : s0.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit f3MallocngMpl ∗
        MallocngRuntime f3MAddrs s0.tpidrEl0 ∗
        ((f3MAddrs.libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl s0.tpidrEl0 s0.brkStart
      (s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A f3TrialRxProg f3RdlAddrs ∧
      (∀ k : BudgetLimits,
        subroutine_ok f3TrialRxProg f3RdlAzAddr (rustAllocZeroedBudgetSpecBase fineCostModel A k)) := by
  obtain ⟨γ, hPool⟩ :=
    f3TrialElf_fineBudgetPool_of_init hcnt hbytes hphys hLoad hVm htpLo htpHi hmem
  exact ⟨γ, hPool,
    f3Trial_fineRustCliAllocBudgetEntries γ s0.tpidrEl0 s0.brkStart,
    fun k => f3Trial_fineRdlAllocZeroed_ok γ s0.tpidrEl0 s0.brkStart k⟩

/-- Produces `A.pool lim fineCostModel.init sm` and `cliMainStk` stack ownership at `cMainAddr`
entry from `f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R`. -/
theorem f3TrialElf_main_fineBudgetPool {lim : BudgetLimits} {i : Inputs} {sm : State} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart
      sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜f3TrialRxProg.CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of f3TrialElf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = f3StdLayout.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = f3StdLayout.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          f3MallocngRoPad ∗
          f3StartupResidual f3StdLayout f3TrialElf i) ∗ R := by
  have hrx : f3StdLayout.rxProgram f3TrialElf = f3TrialRxProg := rfl
  simpa only [hrx] using
    f3InitFineBudgetPool
      (f3TrialElf_cliElfMallocngLayout hcnt hbytes hphys)
      f3MAddrs_libc f3StdExtra_entails_mallocngDataInit hm

/-- Pairs `f3TrialElf_main_fineBudgetPool` with `RustCliAllocBudgetEntries` (`f3RdlAddrs`) and
`rustAllocZeroedBudgetSpec` (`f3RdlAzAddr`) on `f3TrialRxProg`. -/
theorem f3TrialElf_main_fineBudgetPool_and_entries {lim : BudgetLimits}
    {i : Inputs} {sm : State} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart
      (sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜f3TrialRxProg.CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of f3TrialElf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = f3StdLayout.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = f3StdLayout.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          f3MallocngRoPad ∗
          f3StartupResidual f3StdLayout f3TrialElf i) ∗ R) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A f3TrialRxProg f3RdlAddrs ∧
      (∀ k : BudgetLimits,
        subroutine_ok f3TrialRxProg f3RdlAzAddr (rustAllocZeroedBudgetSpecBase fineCostModel A k)) := by
  obtain ⟨γ, hPool⟩ := f3TrialElf_main_fineBudgetPool hcnt hbytes hphys hm
  exact ⟨γ, hPool,
    f3Trial_fineRustCliAllocBudgetEntries γ sm.tpidrEl0 sm.brkStart,
    fun k => f3Trial_fineRdlAllocZeroed_ok γ sm.tpidrEl0 sm.brkStart k⟩

/-- Unbudgeted `cMainAddr` heap initializer (`(mallocngRustCliAlloc γ f3MAddrs).pool 0 0 sm`) on
`f3TrialElf`. -/
theorem f3TrialElf_main_mallocngHeap {i : Inputs} {sm : State} {R : SepProp}
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      sm.mem ⊨
        ((mallocngRustCliAlloc γ f3MAddrs).pool 0 0 sm ∗
          StdErrnoCell sm.tpidrEl0 ∗
          ⌜f3TrialRxProg.CodeLoaded sm.mem ∧
            cliMainStk ≤ sm.sp.toNat ∧
            sm.sp = (StackLayout.of f3TrialElf (cliInputs i)).sp0 - 48#64 ∧
            sm.readReg64 .lr = f3StdLayout.libcStartMainStage2Addr + 56#64 ∧
            sm.tpidrEl0 = f3StdLayout.builtinTlsAddr + 200#64 ∧
            MallocngBrkStartWf sm.brkStart ∧
            sm.brk = sm.brkStart ∧
            sm.brkStart = f3StdLayout.brkStart⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp cliMainStk ∗
          f3MallocngRoPad ∗
          f3StartupResidual f3StdLayout f3TrialElf i) ∗ R := by
  have hrx : f3StdLayout.rxProgram f3TrialElf = f3TrialRxProg := rfl
  simpa only [hrx] using
    f3InitMallocngHeap f3MAddrs_libc f3StdExtra_entails_mallocngStartupData hm

/-! ## `.img.text` 1-Hop `--branch-stubs` Execution Lifts -/

/-- Steps `__rust_alloc` from `f3StubAddrs.alloc` (`.img.text` `Instr.b` into `seg[5]`
`__rdl_alloc`) under any hook-unfetched `Syscall.standard` program `P`. -/
theorem f3Trial_stub_alloc_steps {P : Program} {inputs : ProcessInputs} {sLoad s0 : State}
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : Nat × Nat × fineCostModel.σ) (R : SepProp)
    (hsLoad : f3TrialElf.loadState inputs = .ok sLoad)
    (hkf : sLoad.mem.KeepsFrozen s0.mem)
    (hrx_cl : f3TrialRxProg.CodeLoaded s0.mem)
    (hp_svc : P.svc = Syscall.standard)
    (hp_stub : P.externAt? f3StubAddrs.alloc = none)
    (hhooks : P.HooksUnfetched s0.mem)
    (hpc : s0.pc = f3StubAddrs.alloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (rustCliAllocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim false).pre x s0 ∗ R) :
    ∃ sf, Steps P s0 sf ∧
      SubroutineOutcome
        (rustCliAllocBudgetSpecBase fineCostModel
          (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim false)
        x R s0 sf := by
  obtain ⟨hal, hexec, hdec⟩ :=
    f3Trial_keepsFrozen_stub_at hsLoad hkf f3StubAlloc_mem_targets f3StubAlloc_addr_eq
  have hpre' : s0.mem ⊨
      (rustCliAllocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim false).pre x
        (s0.setPC f3RdlAddrs.alloc) ∗ R := by
    rcases x with ⟨sz, al, st⟩
    simpa only [rustCliAllocBudgetSpecBase, State.readReg64_setPC, State.sp_setPC,
      RustCliAllocBudget.pool_setPC] using hpre
  exact steps_of_loaded_b_stub
    ((f3Trial_fineRustCliAllocBudgetEntries γ tp brkStart).alloc lim)
    f3TrialRxProg_svc f3TrialRxProg_no_ext hp_svc hp_stub
    hpc hrun hsp hal hexec hdec hrx_cl hhooks hpre'
    (fun sf => by
      rcases x with ⟨sz, al, st⟩
      simp only [rustCliAllocBudgetSpecBase, allocCallPreserved_setPC_left, State.sp_setPC])
    (fun _ => rfl) (fun _ _ => rfl)
    (fun sf => by
      rcases x with ⟨sz, al, st⟩
      simp only [rustCliAllocBudgetSpecBase, oomPreserved_setPC_left])

/-- Steps `__rust_dealloc` from `f3StubAddrs.dealloc` (`.img.text` `Instr.b` into `seg[5]`
`__rdl_dealloc`) under any hook-unfetched `Syscall.standard` program `P`. -/
theorem f3Trial_stub_dealloc_steps {P : Program} {inputs : ProcessInputs} {sLoad s0 : State}
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × fineCostModel.σ) (R : SepProp)
    (hsLoad : f3TrialElf.loadState inputs = .ok sLoad)
    (hkf : sLoad.mem.KeepsFrozen s0.mem)
    (hrx_cl : f3TrialRxProg.CodeLoaded s0.mem)
    (hp_svc : P.svc = Syscall.standard)
    (hp_stub : P.externAt? f3StubAddrs.dealloc = none)
    (hhooks : P.HooksUnfetched s0.mem)
    (hpc : s0.pc = f3StubAddrs.dealloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (rustCliDeallocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x s0 ∗ R) :
    ∃ sf, Steps P s0 sf ∧
      SubroutineOutcome
        (rustCliDeallocBudgetSpecBase fineCostModel
          (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim)
        x R s0 sf := by
  obtain ⟨hal, hexec, hdec⟩ :=
    f3Trial_keepsFrozen_stub_at hsLoad hkf f3StubDealloc_mem_targets f3StubDealloc_addr_eq
  have hpre' : s0.mem ⊨
      (rustCliDeallocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x
        (s0.setPC f3RdlAddrs.dealloc) ∗ R := by
    rcases x with ⟨p, sz, al, st⟩
    simpa only [rustCliDeallocBudgetSpecBase, State.readReg64_setPC, State.sp_setPC,
      RustCliAllocBudget.pool_setPC] using hpre
  exact steps_of_loaded_b_stub
    ((f3Trial_fineRustCliAllocBudgetEntries γ tp brkStart).dealloc lim)
    f3TrialRxProg_svc f3TrialRxProg_no_ext hp_svc hp_stub
    hpc hrun hsp hal hexec hdec hrx_cl hhooks hpre'
    (fun sf => by
      rcases x with ⟨p, sz, al, st⟩
      simp only [rustCliDeallocBudgetSpecBase, allocCallPreserved_setPC_left, State.sp_setPC])
    (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

/-- Steps `__rust_realloc` from `f3StubAddrs.realloc` (`.img.text` `Instr.b` into `seg[5]`
`__rdl_realloc`) under any hook-unfetched `Syscall.standard` program `P`. -/
theorem f3Trial_stub_realloc_steps {P : Program} {inputs : ProcessInputs} {sLoad s0 : State}
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × fineCostModel.σ) (R : SepProp)
    (hsLoad : f3TrialElf.loadState inputs = .ok sLoad)
    (hkf : sLoad.mem.KeepsFrozen s0.mem)
    (hrx_cl : f3TrialRxProg.CodeLoaded s0.mem)
    (hp_svc : P.svc = Syscall.standard)
    (hp_stub : P.externAt? f3StubAddrs.realloc = none)
    (hhooks : P.HooksUnfetched s0.mem)
    (hpc : s0.pc = f3StubAddrs.realloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (rustCliReallocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x s0 ∗ R) :
    ∃ sf, Steps P s0 sf ∧
      SubroutineOutcome
        (rustCliReallocBudgetSpecBase fineCostModel
          (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim)
        x R s0 sf := by
  obtain ⟨hal, hexec, hdec⟩ :=
    f3Trial_keepsFrozen_stub_at hsLoad hkf f3StubRealloc_mem_targets f3StubRealloc_addr_eq
  have hpre' : s0.mem ⊨
      (rustCliReallocBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x
        (s0.setPC f3RdlAddrs.realloc) ∗ R := by
    rcases x with ⟨p, old, al, nw, bs, st⟩
    simpa only [rustCliReallocBudgetSpecBase, State.readReg64_setPC, State.sp_setPC,
      RustCliAllocBudget.pool_setPC] using hpre
  exact steps_of_loaded_b_stub
    ((f3Trial_fineRustCliAllocBudgetEntries γ tp brkStart).realloc lim)
    f3TrialRxProg_svc f3TrialRxProg_no_ext hp_svc hp_stub
    hpc hrun hsp hal hexec hdec hrx_cl hhooks hpre'
    (fun sf => by
      rcases x with ⟨p, old, al, nw, bs, st⟩
      simp only [rustCliReallocBudgetSpecBase, allocCallPreserved_setPC_left, State.sp_setPC])
    (fun _ => rfl) (fun _ _ => rfl)
    (fun sf => by
      rcases x with ⟨p, old, al, nw, bs, st⟩
      simp only [rustCliReallocBudgetSpecBase, oomPreserved_setPC_left])

/-- Steps `__rust_alloc_zeroed` from `f3StubAzAddr` (`.img.text` `Instr.b` into `seg[5]`
`__rdl_alloc_zeroed`) under any hook-unfetched `Syscall.standard` program `P`. -/
theorem f3Trial_stub_allocZeroed_steps {P : Program} {inputs : ProcessInputs} {sLoad s0 : State}
    (γ : GhostName) (tp brkStart : BitVec 64) (lim : BudgetLimits)
    (x : Nat × Nat × fineCostModel.σ) (R : SepProp)
    (hsLoad : f3TrialElf.loadState inputs = .ok sLoad)
    (hkf : sLoad.mem.KeepsFrozen s0.mem)
    (hrx_cl : f3TrialRxProg.CodeLoaded s0.mem)
    (hp_svc : P.svc = Syscall.standard)
    (hp_stub : P.externAt? f3StubAzAddr = none)
    (hhooks : P.HooksUnfetched s0.mem)
    (hpc : s0.pc = f3StubAzAddr)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hpre : s0.mem ⊨
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x s0 ∗ R) :
    ∃ sf, Steps P s0 sf ∧
      SubroutineOutcome
        (rustAllocZeroedBudgetSpecBase fineCostModel
          (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim)
        x R s0 sf := by
  obtain ⟨hal, hexec, hdec⟩ :=
    f3Trial_keepsFrozen_stub_at hsLoad hkf f3StubAz_mem_targets f3StubAz_addr_eq
  have hpre' : s0.mem ⊨
      (rustAllocZeroedBudgetSpecBase fineCostModel
        (fineRustCliAllocBudget γ f3MallocngMpl tp brkStart) lim).pre x
        (s0.setPC f3RdlAzAddr) ∗ R := by
    rcases x with ⟨sz, al, st⟩
    simpa only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, State.readReg64_setPC,
      State.sp_setPC, RustCliAllocBudget.pool_setPC] using hpre
  exact steps_of_loaded_b_stub
    (f3Trial_fineRdlAllocZeroed_ok γ tp brkStart lim)
    f3TrialRxProg_svc f3TrialRxProg_no_ext hp_svc hp_stub
    hpc hrun hsp hal hexec hdec hrx_cl hhooks hpre'
    (fun sf => by
      rcases x with ⟨sz, al, st⟩
      simp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase,
        allocCallPreserved_setPC_left, State.sp_setPC])
    (fun _ => rfl) (fun _ _ => rfl)
    (fun sf => by
      rcases x with ⟨sz, al, st⟩
      simp only [rustAllocZeroedBudgetSpecBase, rustCliAllocBudgetSpecBase, oomPreserved_setPC_left])

example {lim : BudgetLimits} {i : Inputs} {sm : State} {R : SepProp}
    (hcnt : lim.enforced = true → f3SegCount + 1 ≤ lim.staticCount)
    (hbytes : lim.enforced = true → cliStackSize + f3SegByteSum ≤ lim.staticBytes)
    (hphys : lim.enforced = true → lim.physCap ≤ 2 ^ 30)
    (hm : sm.mem ⊨ f3StartupMainPreNeedLocks f3StdLayout f3TrialElf i sm ∗ R) :
    ∃ γ : GhostName,
      let A := fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart
      sm.mem ⊨
        (A.pool lim fineCostModel.init sm ∗
          ⌜8371776 ≤ sm.sp.toNat⌝ ∗
          argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
          stackAt sm.sp 8371776 ∗
          anyHeap) ∗ R := by
  obtain ⟨γ, hPool⟩ := f3TrialElf_main_fineBudgetPool hcnt hbytes hphys hm
  dsimp only [cliMainStk] at hPool ⊢
  simp only [sepConj_assoc,
    sepConj_left_comm ((fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart).pool
      lim fineCostModel.init sm),
    satisfies_pure_sepConj] at hPool
  obtain ⟨⟨_, hsp_ge, _⟩, hPool⟩ := hPool
  refine ⟨γ, Satisfies.mono ?_ hPool⟩
  rw [pure_sepConj_of_true hsp_ge]
  refine Entails.trans
    (Q := ((fineRustCliAllocBudget γ f3MallocngMpl sm.tpidrEl0 sm.brkStart).pool
        lim fineCostModel.init sm ∗
      argvAtRO (sm.readReg64 .x1) (("libsignal-cli" :: i.argv).map bytesOfString) ∗
      stackAt sm.sp 8371776 ∗
      (f3MallocngRoPad ∗ f3StartupResidual f3StdLayout f3TrialElf i)) ∗ R)
    (by sep_entail)
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (entails_anyHeap _)))))

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Inst
