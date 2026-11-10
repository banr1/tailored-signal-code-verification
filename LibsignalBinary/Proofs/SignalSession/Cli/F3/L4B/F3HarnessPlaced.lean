/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ElfInitFine
public import LibsignalBinary.Heap.Fine.SpecBudgetFine
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatch
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Top
public import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
public import LibsignalBinary.Proofs.SignalSession.Coins.CoinsPlaced
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Heap.IfaceBudgetBase
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Two-Placement `mallocng` Harness, Token Patch, and `cliRunExtOnInputsSigAt` Bridges

Two-placement `(mpl, mmpl : Obj.MultiPlacement)` harness and execution-program definitions:
explicit-`mpl` CPU-probe token patching (`CliElfTokenCellsPlacedAt`, `patchElfTokensPlacedAt`),
`CliStackShape` `fineHookRustCliAllocBudget` pool initialization (`b2FineHookPool_of_needLocks`),
relocatable `CliRunsToExtOnInputsAt` / `cliRunExtOnInputsSigAt` bridges, and explicit-placement
writable statics (`cliStaticsPlacedAt mpl`, `mallocngRwBssAt mmpl`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (lsLogFilterSym)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.SignalSession
  (AddrInElf CliHooks CliRun Inputs Outcome OutcomeMatchesProcess ProcessResult
   abortOnPanic addrInElf_patchElfByte cliExternsPlaced cliProcessInputs
   elfStaticOk_patchElfByte filesOf libsignalSessionLib loadState_patchElfByte
   loadState_status_running observe outcomeOf outcomeOf_eq_some_iff patchElfByte patchRegionByte
   processExitsWith_of_exited processExitsWith_of_signaled processInputs segSlice_addrInElf
   sigAbrt toOutcome)
open CryptoVerification.SignalSession.Placed
  (CliRunsToPlaced cliProgPlacedSig cliRunPlacedSig cliTokenPatchPlaced)
open CryptoVerification.SignalSession.Cli
  (ElfStaticOk MainResult RunAnswer cliInputs)
open CryptoVerification.SignalSession.Coins (coinsLeftSym coinsNextSym)
open CryptoVerification.SignalSession.InitStack (cliStackSize)
open CryptoVerification.SignalSession.MuslElf (SegSlice)
open LibsignalBinary.Heap
  (BudgetLimits RustAllocAddrs RustCliAllocNoOomEntriesBase mallocngBudgetPoolInv
   rustCliAllocNoOomSpecBase subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout MallocngInitResources StartupVmPreserved allocMemsetVmSpec
   buildInitialStack_sub_stack cliElfStaticIvs elfLoadState_fields elfLoadState_poolInv
   elfStaticIvs fineBudgetPool_of_initResources fineCostModel fineHookBudgetPool_of_codeLoaded
   fineHookRustCliAllocBudget fineHookRustCliAllocBudgetEntries_thunks
   fineHookRustCliAllocZeroedBudget_thunk_ok mallocngBrkStartWf_of_elf
   mallocngBudgetPoolInv_of_startupVmPreserved rdlAllocZeroedInstrs)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries (mallocngLib)
open VerifiedLibraries.Mallocng
  (MallocngAuxvAt MallocngBrkStartWf MallocngRoTablesAt MallocngRuntime
   mallocngAddrsOfPlacement mallocngDebruijn32Table mallocngMedCntTabBytes mallocngSizeClassBytes
   mallocngSmallCntTabBytes)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng mallocngLib_dataInit_eq)
open VerifiedLibraries.RustStd
  (RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs)

/-! ## Explicit-`mpl` Token Patch and `CliStackShape` Pool Initialization -/

/-- Explicit-`mpl` `PT_LOAD` `.data` slice bundle witnessing SPQR's initial unprobed CPU-feature
cells (`STORAGE.0 = 0xff` at `mpl.ρ tokenStorageName`, `TOKEN`'s `Once` state `= 3` at
`mpl.ρ tokenName + 8#64`). -/
structure CliElfTokenCellsPlacedAt (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop where
  storage : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName)
    [0xff#8] Perm.rw
  once : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    [3#8, 0#8, 0#8, 0#8] Perm.rw

/-- Ghost `ElfImage` with spqr's 5 CPU-probe `.data` bytes pre-set to `0` (`DEV-CLI10`) at an
explicit placement `mpl`, so `(patchElfTokensPlacedAt mpl elf).loadState inputs =
(elf.loadState inputs).map (Placed.cliTokenPatchPlaced mpl)`. -/
def patchElfTokensPlacedAt (mpl : Obj.MultiPlacement) (elf : ElfImage) : ElfImage :=
  let sAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName
  let oAddr := mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64
  patchElfByte (oAddr + 3#64) 0#8 (patchElfByte (oAddr + 2#64) 0#8
    (patchElfByte (oAddr + 1#64) 0#8 (patchElfByte oAddr 0#8 (patchElfByte sAddr 0#8 elf))))

theorem elfStaticOk_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) : ElfStaticOk (patchElfTokensPlacedAt mpl elf) :=
  elfStaticOk_patchElfByte (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte
    (elfStaticOk_patchElfByte (elfStaticOk_patchElfByte hE))))

private theorem bv_add_1_1_at (x : BitVec 64) : x + 1#64 + 1#64 = x + 2#64 := by
  rw [BitVec.add_assoc]; rfl

private theorem bv_add_2_1_at (x : BitVec 64) : x + 2#64 + 1#64 = x + 3#64 := by
  rw [BitVec.add_assoc]; rfl

theorem loadState_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement} {elf : ElfImage}
    (hE : ElfStaticOk elf) (htok : CliElfTokenCellsPlacedAt mpl elf) (inputs : ProcessInputs) :
    (patchElfTokensPlacedAt mpl elf).loadState inputs =
      (elf.loadState inputs).map (cliTokenPatchPlaced mpl) := by
  have hs : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.storage hE (j := 0) (by decide)
  have ho0 : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      segSlice_addrInElf htok.once hE (j := 0) (by decide)
  have ho1 : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 1#64) :=
    segSlice_addrInElf htok.once hE (j := 1) (by decide)
  have ho2 : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 2#64) :=
    segSlice_addrInElf htok.once hE (j := 2) (by decide)
  have ho3 : AddrInElf elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64 + 3#64) :=
    segSlice_addrInElf htok.once hE (j := 3) (by decide)
  unfold patchElfTokensPlacedAt
  dsimp only
  rw [loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho3),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho2),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho1),
      loadState_patchElfByte _ (by simpa only [addrInElf_patchElfByte] using ho0),
      loadState_patchElfByte _ hs]
  cases elf.loadState inputs with
  | error _ => rfl
  | ok s0 =>
    simp only [Except.map, cliTokenPatchPlaced, State.setMem,
      Memory.writeBytes, bv_add_1_1_at, bv_add_2_1_at]

private theorem bytes_length_patchRegionByte (a : BitVec 64) (v : BitVec 8) (r : Snapshot.Region) :
    (patchRegionByte a v r).bytes.length = r.bytes.length := by
  unfold patchRegionByte; dsimp only; split <;> simp

private theorem map_bytes_length_patchElfByte (a : BitVec 64) (v : BitVec 8) (elf : ElfImage) :
    (patchElfByte a v elf).segments.map (fun r => r.bytes.length) =
      elf.segments.map (fun r => r.bytes.length) := by
  unfold patchElfByte
  simp [List.map_map, Function.comp_def, bytes_length_patchRegionByte]

theorem cliElfMallocngLayout_iff_patchElfByte {a : BitVec 64} {v : BitVec 8}
    {elf : ElfImage} {lim : BudgetLimits} :
    CliElfMallocngLayout (patchElfByte a v elf) lim ↔ CliElfMallocngLayout elf lim := by
  have hbrk : (patchElfByte a v elf).brkStart = elf.brkStart := rfl
  have hlen : (patchElfByte a v elf).segments.length = elf.segments.length := by
    simp [patchElfByte]
  have hmap := map_bytes_length_patchElfByte a v elf
  constructor <;> intro h <;>
    exact
      { brkStart_min := by simpa [hbrk] using h.brkStart_min
        staticCount_le := by simpa [hlen] using h.staticCount_le
        staticBytes_le := by simpa [hmap] using h.staticBytes_le
        physCap_le := h.physCap_le }

/-- `patchElfTokensPlacedAt mpl elf` preserves `CliElfMallocngLayout` (`brkStart`, segment count,
and segment byte-length sum are all unchanged). -/
theorem cliElfMallocngLayout_iff_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement}
    {elf : ElfImage} {lim : BudgetLimits} :
    CliElfMallocngLayout (patchElfTokensPlacedAt mpl elf) lim ↔ CliElfMallocngLayout elf lim := by
  unfold patchElfTokensPlacedAt
  dsimp only
  simp only [cliElfMallocngLayout_iff_patchElfByte]

/-- Common `InitConfig` stack/RAM parameters shared by `cliProcessInputs i`, `cliInputs i`, and
`hwcap = 0x3#64` inputs. -/
def CliStackShape (pi : ProcessInputs) : Prop :=
  pi.init.stackTop = defaultStackTop ∧
  pi.init.stackSize = cliStackSize ∧
  pi.init.physMemAvail = 2 ^ 30

theorem cliStackShape_cliProcessInputs (i : Inputs) : CliStackShape (cliProcessInputs i) :=
  ⟨rfl, rfl, rfl⟩

theorem cliStackShape_cliInputs (i : Inputs) : CliStackShape (cliInputs i) :=
  cliStackShape_cliProcessInputs i

theorem cliStackShape_withHwcap (argv : List String) (stdin : List (BitVec 8))
    (files : List (String × List (BitVec 8))) (dirs : List String) (hw : BitVec 64) :
    CliStackShape
      { processInputs argv stdin files dirs with
        init := { stackSize := 8388608, auxv := { hwcap := hw } } } :=
  ⟨rfl, rfl, rfl⟩

theorem elfStaticIvs_of_cliStackShape {elf : ElfImage} {inputs : ProcessInputs}
    (hsh : CliStackShape inputs) :
    elfStaticIvs elf inputs = cliElfStaticIvs elf := by
  unfold elfStaticIvs cliElfStaticIvs
  rw [hsh.1, hsh.2.1]
  rfl

theorem mallocngInitResources_of_inputs
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {inputs : ProcessInputs} {sLoad sm : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState inputs = .ok sLoad)
    (hVm : StartupVmPreserved sLoad sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : sm.mem ⊨
      mallocngLib.dataInit mmpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mmpl) sm.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mmpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    MallocngInitResources mmpl lim (cliElfStaticIvs elf) R sm ∧ sm.brkStart = elf.brkStart := by
  obtain ⟨hwf, hbsLoad, hbrkLoad, _, _, _, hb, _, _⟩ := elfLoadState_fields hLoad
  have htopLt : inputs.init.stackTop.toNat < 2 ^ 64 := by
    rw [hsh.1]; decide
  have htopLe : inputs.init.stackTop.toNat ≤ Arm64.USER_VA_LIMIT := by
    rw [hsh.1]; decide
  obtain ⟨hbrkLeSb, _⟩ := buildInitialStack_sub_stack hb htopLt
  have hsbLe48 : inputs.init.stackTop.toNat - inputs.init.stackSize ≤ 2 ^ 48 := by
    rw [hsh.1, hsh.2.1]; decide
  have hBrkWfElf : MallocngBrkStartWf elf.brkStart :=
    mallocngBrkStartWf_of_elf hwf hLayout.brkStart_min (Nat.le_trans hbrkLeSb hsbLe48)
  have hInvLoad : mallocngBudgetPoolInv lim (cliElfStaticIvs elf) [] sLoad := by
    rw [← elfStaticIvs_of_cliStackShape hsh]
    exact elfLoadState_poolInv hLoad htopLe hLayout.staticCount_le
      (fun henf => by rw [hsh.2.1]; exact hLayout.staticBytes_le henf)
      (fun henf => by rw [hsh.2.2]; exact hLayout.physCap_le henf)
  have hbs0 : sm.brkStart = elf.brkStart := hVm.1.trans hbsLoad
  have hbrk0 : sm.brk = sm.brkStart := (hVm.2.1.trans hbrkLoad).trans hbs0.symm
  exact
    ⟨{ tp_lo := htpLo
       tp_hi := htpHi
       brk_eq := hbrk0
       brkStart_wf := hbs0 ▸ hBrkWfElf
       poolInv := mallocngBudgetPoolInv_of_startupVmPreserved hVm hInvLoad
       startup := ⟨auxvPtr, hmem⟩ },
     hbs0⟩

/-- Produce `(fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart).pool lim fineCostModel.init sm`
from any `CliStackShape` ELF load and `StartupVmPreserved`, rewriting `sm.brkStart` to `elf.brkStart`
so the budget parameter `elf.brkStart` is state-independent across inputs. -/
theorem fineHookBudgetPool_of_inputs
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {inputs : ProcessInputs} {sLoad sm : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hCL : mallocngLib.CodeLoaded mmpl sm.mem)
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState inputs = .ok sLoad)
    (hVm : StartupVmPreserved sLoad sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : sm.mem ⊨
      mallocngLib.dataInit mmpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mmpl) sm.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mmpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      sm.mem ⊨
        (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart).pool
          lim fineCostModel.init sm ∗ R := by
  obtain ⟨hInit, hbs0⟩ :=
    mallocngInitResources_of_inputs hsh hLayout hLoad hVm htpLo htpHi hmem
  obtain ⟨γ, hPool⟩ := fineBudgetPool_of_initResources hInit
  have hHook := fineHookBudgetPool_of_codeLoaded hCL hPool
  rw [hbs0] at hHook
  exact ⟨γ, hHook⟩

theorem fineHookNoOomInit_of_inputs
    {P : Program} {elf : ElfImage} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {thunkAddrs rdlAddrs : RustAllocAddrs}
    {allocZeroedThunkAddr allocZeroedRdlAddr memcpyAddr memsetAddr : BitVec 64}
    {inputs : ProcessInputs} {sLoad sm : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hP : ProgContainsMallocng P mmpl)
    (hCL : mallocngLib.CodeLoaded mmpl sm.mem)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mmpl) memcpyAddr)
    (hZeroThunk : hasInstrs P allocZeroedThunkAddr [.b (allocZeroedRdlAddr - allocZeroedThunkAddr)])
    (hZeroCode : hasInstrs P allocZeroedRdlAddr
      (rdlAllocZeroedInstrs allocZeroedRdlAddr (mallocngLib.fnAddr mmpl "calloc")
        (mallocngPlacedCAddrs mmpl).posixMemalign memsetAddr))
    (hMemcpy : subroutine_ok P memcpyAddr allocMemcpyVmSpec)
    (hMemset : subroutine_ok P memsetAddr allocMemsetVmSpec)
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState inputs = .ok sLoad)
    (hVm : StartupVmPreserved sLoad sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : sm.mem ⊨
      mallocngLib.dataInit mmpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement mmpl) sm.tpidrEl0 ∗
        (((mallocngAddrsOfPlacement mmpl).libc + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
      (sm.mem ⊨ A.pool lim fineCostModel.init sm ∗ R) ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P thunkAddrs ∧
      subroutine_ok P allocZeroedThunkAddr (rustCliAllocNoOomSpecBase fineCostModel A lim true) := by
  obtain ⟨γ, hPool⟩ :=
    fineHookBudgetPool_of_inputs hCL hsh hLayout hLoad hVm htpLo htpHi hmem
  exact ⟨γ, hPool,
    (fineHookRustCliAllocBudgetEntries_thunks hP γ sm.tpidrEl0 elf.brkStart
      hThunks hShims hMemcpy).toNoOom lim,
    subroutine_ok_allocNoOom_of_budgetBase
      (fineHookRustCliAllocZeroedBudget_thunk_ok hP γ sm.tpidrEl0 elf.brkStart
        allocZeroedThunkAddr allocZeroedRdlAddr memsetAddr lim hZeroThunk hZeroCode hMemset)⟩

/-- Package `(libcAddr + 3) ↦₈ 0`, `(sm.tpidrEl0 - 0xa4) ↦₃₂ errnoVal`, `(libcAddr + 8) ↦₆₄ auxvPtr`,
`(libcAddr + 48) ↦₆₄ 4096`, `MallocngAuxvAt auxvPtr`, and `VerifiedLibraries.mallocngLib.dataInit mmpl`
into `∃ γ, sm.mem ⊨ (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart).pool lim fineCostModel.init sm ∗ R`. -/
theorem b2FineHookPool_of_needLocks
    {elf : ElfImage} {inputs : ProcessInputs} {s0 sm : State}
    {mmpl : Obj.MultiPlacement} {lim : BudgetLimits} {R : SepProp}
    {libcAddr auxvPtr : BitVec 64} {errnoVal : BitVec 32}
    (hCode : mallocngLib.CodeLoaded mmpl sm.mem)
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hload : elf.loadState inputs = .ok s0)
    (hVm : StartupVmPreserved s0 sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hmem : sm.mem ⊨
      mallocngLib.dataInit mmpl ∗
        ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((libcAddr + 3#64) ↦₈ 0#8) ∗
        ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      sm.mem ⊨
        (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart).pool
          lim fineCostModel.init sm ∗ R := by
  refine fineHookBudgetPool_of_inputs hCode hsh hLayout hload hVm htpLo htpHi (auxvPtr := auxvPtr) ?_
  unfold MallocngRuntime
  rw [hlibc]
  have hassoc :
      (mallocngLib.dataInit mmpl ∗
        ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((libcAddr + 3#64) ↦₈ 0#8) ∗
        ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) =
      (mallocngLib.dataInit mmpl ∗
        (((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
          ((libcAddr + 3#64) ↦₈ 0#8) ∗
          ((libcAddr + 48#64) ↦₆₄ 4096#64)) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) := by sep_ac_rfl
  rw [hassoc] at hmem
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_intro errnoVal))))
    hmem

/-! ## Generic `CliRunsToExtOnInputsAt` and Two-Placement Specializations -/

/-- Relocatable `libsignalSessionLib` program at block `idx` under extern family `ext`. -/
noncomputable def cliProgExtPlacedAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (ext W)

/-- `abortOnPanic`-wrapped relocatable `libsignalSessionLib` program at block `idx`. -/
noncomputable def cliProgExtPlacedSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (fun name => (ext W name).map abortOnPanic)

/-- Relocatable `CliRunsTo` parameterized by `ext`, `idx`, and `inputsOf : Inputs → ProcessInputs`. -/
def CliRunsToExtOnInputsAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (inputsOf i) = .ok s0 ∧
    ProcessRunsTo (cliProgExtPlacedSigAt mpl ext idx W)
      (cliTokenPatchPlaced mpl s0) (OutcomeMatchesProcess o)

abbrev CliRunsToExtPlacedAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  CliRunsToExtOnInputsAt mpl ext idx cliProcessInputs elf W i o

open Classical in
/-- Relocatable `CliRun` parameterized by `ext`, `idx`, and `inputsOf : Inputs → ProcessInputs`. -/
noncomputable def cliRunExtOnInputsSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs)
    (elf : ElfImage) (W : CliHooks) : CliRun := fun i =>
  if h : ∃ o, CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o then
    some (Classical.choose h)
  else none

noncomputable abbrev cliRunExtPlacedSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  cliRunExtOnInputsSigAt mpl ext idx cliProcessInputs elf W

theorem cliProgExtPlacedSigAt_cliExternsPlaced_eq
    (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 W =
      cliProgPlacedSig mpl mmpl W :=
  rfl

theorem cliRunsToExtPlacedAt_cliExternsPlaced_eq
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) :
    CliRunsToExtPlacedAt mpl (cliExternsPlaced mmpl) 617 elf W i o =
      CliRunsToPlaced mpl mmpl elf W i o :=
  rfl

theorem cliRunExtPlacedSigAt_cliExternsPlaced_eq
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    cliRunExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 elf W =
      cliRunPlacedSig mpl mmpl elf W :=
  rfl

private theorem processTerminatedOutcome_not_running_ext {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

private theorem processTerminatedOutcome_unique_ext {sf : State} {out₁ out₂ : ProcessOutcome}
    (h₁ : ProcessTerminatedOutcome sf out₁) (h₂ : ProcessTerminatedOutcome sf out₂) :
    out₁ = out₂ := by
  rcases h₁ with ⟨_, hst₁, rfl⟩ | ⟨_, hst₁, rfl⟩ <;>
    rcases h₂ with ⟨_, hst₂, rfl⟩ | ⟨_, hst₂, rfl⟩
  · rw [hst₁] at hst₂; cases hst₂; rfl
  · rw [hst₁] at hst₂; cases hst₂
  · rw [hst₁] at hst₂; cases hst₂
  · rw [hst₁] at hst₂; cases hst₂; rfl

private theorem outcomeObserved_unique_ext {o₁ o₂ : Outcome} {out : ProcessOutcome}
    (h₁ : OutcomeMatchesProcess o₁ out) (h₂ : OutcomeMatchesProcess o₂ out) :
    o₁ = o₂ := by
  cases o₁ with
  | exited c₁ s₁ f₁ =>
    cases o₂ with
    | exited c₂ s₂ f₂ =>
      obtain ⟨_, rfl, rfl, rfl⟩ := h₁
      obtain ⟨_, rfl, rfl, rfl⟩ := h₂
      rfl
    | aborted =>
      exact nomatch h₁.1.symm.trans h₂.1
  | aborted =>
    cases o₂ with
    | exited c₂ s₂ f₂ =>
      exact nomatch h₁.1.symm.trans h₂.1
    | aborted => rfl

theorem cliRunsToExtOnInputsAt_unique {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {o₁ o₂ : Outcome}
    (h₁ : CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o₁)
    (h₂ : CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o₂) :
    o₁ = o₂ := by
  rcases h₁ with ⟨s0, hLoad₁, ⟨out₁, ⟨sf, hSteps, hTerm₁⟩, hObs₁⟩ | ⟨_, _, _, hOom₁⟩, _⟩
  · rcases h₂ with ⟨s0', hLoad₂, _, hSafe₂⟩
    rw [hLoad₁] at hLoad₂
    cases hLoad₂
    rcases hSafe₂ sf hSteps with ⟨out₂, hTerm₂, hObs₂⟩ | ⟨_, hOom⟩ | ⟨hRun, _⟩
    · cases processTerminatedOutcome_unique_ext hTerm₁ hTerm₂
      exact outcomeObserved_unique_ext hObs₁ hObs₂
    · exact False.elim hOom
    · exact absurd hRun (processTerminatedOutcome_not_running_ext hTerm₁)
  · exact False.elim hOom₁

theorem cliRunExtOnInputsSigAt_eq_some {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o) :
    cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o := by
  unfold cliRunExtOnInputsSigAt
  split
  · next hex => exact congrArg some (cliRunsToExtOnInputsAt_unique (Classical.choose_spec hex) h)
  · next hne => exact absurd ⟨o, h⟩ hne

theorem cliRunsToExtOnInputsAt_of_eq_some {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf : ElfImage} {W : CliHooks} {i : Inputs} {o : Outcome}
    (h : cliRunExtOnInputsSigAt mpl ext idx inputsOf elf W i = some o) :
    CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i o := by
  unfold cliRunExtOnInputsSigAt at h
  split at h
  · next hex =>
    injection h with hEq
    rw [← hEq]
    exact Classical.choose_spec hex
  · cases h

private theorem findSome?_stubs_map_ext (stubs : List (String × Nat))
    (X : String → Option (State → State)) (f : (State → State) → (State → State)) (off : Nat) :
    (stubs.findSome? fun x => if x.2 == off then (X x.1).map f else none) =
      (stubs.findSome? fun x => if x.2 == off then X x.1 else none).map f := by
  induction stubs with
  | nil => rfl
  | cons p stubs ih =>
    simp only [List.findSome?_cons]
    cases p.2 == off
    · exact ih
    · cases X p.1
      · exact ih
      · rfl

private theorem findSome?_const_none_ext {α β : Type} (l : List α) :
    (l.findSome? fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem externAt?_cliProgExtPlacedSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks)
    (pc : BitVec 64) :
    (cliProgExtPlacedSigAt mpl ext idx W).externAt? pc =
      ((cliProgExtPlacedAt mpl ext idx W).externAt? pc).map abortOnPanic := by
  unfold cliProgExtPlacedSigAt cliProgExtPlacedAt MultiPlacedLib.blockProgram
    PlacedLib.program Program.externAt? Program.hookAtOff?
  dsimp only
  simp only [ite_self, findSome?_const_none_ext, Option.or_none]
  exact findSome?_stubs_map_ext _ _ _ _

theorem externAt?_cliProgExtPlacedSigAt_isSome (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks)
    (pc : BitVec 64) :
    ((cliProgExtPlacedSigAt mpl ext idx W).externAt? pc).isSome =
      ((cliProgExtPlacedAt mpl ext idx W).externAt? pc).isSome := by
  rw [externAt?_cliProgExtPlacedSigAt]
  cases (cliProgExtPlacedAt mpl ext idx W).externAt? pc <;> rfl

theorem externAt?_cliProgExtPlacedSigAt_eq_none {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {pc : BitVec 64} :
    (cliProgExtPlacedSigAt mpl ext idx W).externAt? pc = none ↔
      (cliProgExtPlacedAt mpl ext idx W).externAt? pc = none := by
  rw [externAt?_cliProgExtPlacedSigAt]
  cases (cliProgExtPlacedAt mpl ext idx W).externAt? pc <;> simp

theorem fetchMem_cliProgExtPlacedSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks)
    (m : Memory) (pc : BitVec 64) :
    (cliProgExtPlacedSigAt mpl ext idx W).fetchMem m pc =
      (cliProgExtPlacedAt mpl ext idx W).fetchMem m pc := by
  unfold Program.fetchMem
  rw [externAt?_cliProgExtPlacedSigAt_isSome]

def toSigState_ext (s : State) : State :=
  match s.status with
  | .Panicked => s.setStatus (.Signaled sigAbrt)
  | _ => s

private theorem abortOnPanic_eq_toSigState_ext (h : State → State) (s : State) :
    abortOnPanic h s = toSigState_ext (h s) := rfl

private theorem toSigState_of_ne_panicked_ext {s : State} (h : s.status ≠ .Panicked) :
    toSigState_ext s = s := by
  unfold toSigState_ext
  split
  · rename_i hp; exact absurd hp h
  · rfl

private theorem toSigState_mem_ext (s : State) : (toSigState_ext s).mem = s.mem := by
  unfold toSigState_ext; split <;> rfl

private theorem toSigState_symtab_ext (s : State) : (toSigState_ext s).symtab = s.symtab := by
  unfold toSigState_ext; split <;> rfl

private theorem elfImageRunsTo_of_load_map_ext {elf elf' : ElfImage} {inputs : ProcessInputs}
    {post : ProcessOutcome → Prop} {prog : Program} {patch : State → State}
    (hpatch : elf'.loadState inputs = (elf.loadState inputs).map patch)
    (hraw : ElfImageRunsTo elf' inputs post (oom := fun _ => False) (prog := prog)) :
    ∃ s0, elf.loadState inputs = .ok s0 ∧ ProcessRunsTo prog (patch s0) post := by
  rcases hraw with ⟨s0', hload', hRuns⟩
  rw [hpatch] at hload'
  cases hload : elf.loadState inputs with
  | error _ =>
    rw [hload] at hload'
    cases hload'
  | ok s0 =>
    rw [hload] at hload'
    simp only [Except.map, Except.ok.injEq] at hload'
    subst hload'
    exact ⟨s0, rfl, hRuns⟩

theorem step_cliProgExtPlacedAt_to_sig {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {s s' : State}
    (h : Step (cliProgExtPlacedAt mpl ext idx W) s s') :
    Step (cliProgExtPlacedSigAt mpl ext idx W) s (toSigState_ext s') := by
  cases h with
  | @exec inst h_run h_fetch =>
    have hs_ne : s.status ≠ .Panicked := by rw [h_run]; intro hc; cases hc
    have h_ne : ((cliProgExtPlacedAt mpl ext idx W).evalInst inst s).status ≠ .Panicked :=
      evalInst_standard_status_ne_panicked rfl inst hs_ne
    rw [toSigState_of_ne_panicked_ext h_ne]
    exact Step.exec h_run ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
  | halt_unmapped h_run h_fetch h_ext =>
    have h_ne : ({ s with status := .Halted } : State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked_ext h_ne]
    exact Step.halt_unmapped h_run
      ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
      (externAt?_cliProgExtPlacedSigAt_eq_none.mpr h_ext)
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    rw [← abortOnPanic_eq_toSigState_ext]
    refine Step.extern h_run h_ext_sig ?_ ?_
    · rw [abortOnPanic_eq_toSigState_ext, toSigState_mem_ext]; exact h_keep
    · rw [abortOnPanic_eq_toSigState_ext, toSigState_symtab_ext]; exact h_sym
  | @extern_fault f h_run h_ext h_nkeep =>
    have h_ne :
        ({ s with status := .Exception "extern hook modified read-only memory or symbol table" } :
          State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked_ext h_ne]
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    refine Step.extern_fault h_run h_ext_sig ?_
    rw [abortOnPanic_eq_toSigState_ext, toSigState_mem_ext, toSigState_symtab_ext]
    exact h_nkeep

theorem steps_cliProgExtPlacedAt_to_sig {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {s0 sf : State}
    (hrun0 : s0.status = .Running)
    (hsteps : Steps (cliProgExtPlacedAt mpl ext idx W) s0 sf) :
    Steps (cliProgExtPlacedSigAt mpl ext idx W) s0 (toSigState_ext sf) := by
  induction hsteps with
  | refl s =>
    have h_ne : s.status ≠ .Panicked := by rw [hrun0]; intro hc; cases hc
    rw [toSigState_of_ne_panicked_ext h_ne]
    exact Steps.refl s
  | @step s1 s2 s3 h1 h2 ih =>
    cases h2 with
    | refl _ =>
      exact Steps.step (step_cliProgExtPlacedAt_to_sig h1) (Steps.refl _)
    | step h2a _ =>
      have hrun2 : s2.status = .Running := h2a.status_running
      have h_ne2 : s2.status ≠ .Panicked := by rw [hrun2]; intro hc; cases hc
      have h1' : Step (cliProgExtPlacedSigAt mpl ext idx W) s1 s2 := by
        have := step_cliProgExtPlacedAt_to_sig h1
        rwa [toSigState_of_ne_panicked_ext h_ne2] at this
      exact Steps.step h1' (ih hrun2)

/-- Lift `outcomeOf elf' (cliProgExtPlacedAt mpl ext idx W) (inputsOf i) = some res` under token
patch `elf'.loadState (inputsOf i) = (elf.loadState (inputsOf i)).map (cliTokenPatchPlaced mpl)`
directly to `CliRunsToExtOnInputsAt`. -/
theorem cliRunsToExtOnInputsAt_of_outcomeOf {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf elf' : ElfImage} {W : CliHooks} {i : Inputs} {res : ProcessResult}
    (hpatch : elf'.loadState (inputsOf i) =
      (elf.loadState (inputsOf i)).map (cliTokenPatchPlaced mpl))
    (hout : outcomeOf elf' (cliProgExtPlacedAt mpl ext idx W) (inputsOf i) = some res) :
    CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i (toOutcome res) := by
  obtain ⟨s0', hload', _, sf, hsteps, hres⟩ := outcomeOf_eq_some_iff.mp hout
  have hsteps_sig := steps_cliProgExtPlacedAt_to_sig (loadState_status_running hload') hsteps
  have hraw : ElfImageRunsTo elf' (inputsOf i) (OutcomeMatchesProcess (toOutcome res))
      (oom := fun _ => False) (prog := cliProgExtPlacedSigAt mpl ext idx W) := by
    cases hst : sf.status <;> simp only [ProcessResult.ofState?, hst] at hres <;> cases hres
    · have heq : toSigState_ext sf = sf :=
        toSigState_of_ne_panicked_ext (by rw [hst]; intro hc; cases hc)
      rw [heq] at hsteps_sig
      exact ElfImageRunsTo.of_exitsWith hload'
        (processExitsWith_of_exited hsteps_sig hst) ⟨rfl, rfl, rfl, rfl⟩
    · have hsig : (toSigState_ext sf).status = .Signaled sigAbrt := by
        simp [toSigState_ext, hst, State.status_setStatus]
      exact ElfImageRunsTo.of_exitsWith hload'
        (processExitsWith_of_signaled hsteps_sig hsig) ⟨rfl, rfl⟩
  exact elfImageRunsTo_of_load_map_ext hpatch hraw

theorem cliRunsToExtOnInputsAt_of_outcomeOf_observed {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf elf' : ElfImage} {W : CliHooks} {i : Inputs} {a : RunAnswer} {res : ProcessResult}
    (hpatch : elf'.loadState (inputsOf i) =
      (elf.loadState (inputsOf i)).map (cliTokenPatchPlaced mpl))
    (hout : outcomeOf elf' (cliProgExtPlacedAt mpl ext idx W) (inputsOf i) = some res)
    (hobs : MainResult.Observed i.files (MainResult.ofAnswer a) res) :
    CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i (observe i.files a) := by
  rw [← MainResult.observed_ofAnswer i.files a res hobs]
  exact cliRunsToExtOnInputsAt_of_outcomeOf hpatch hout

theorem cliRunsToExtOnInputsAt_of_outcomeOf_usage {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {inputsOf : Inputs → ProcessInputs}
    {elf elf' : ElfImage} {W : CliHooks} {i : Inputs} {res : ProcessResult}
    (hpatch : elf'.loadState (inputsOf i) =
      (elf.loadState (inputsOf i)).map (cliTokenPatchPlaced mpl))
    (hout : outcomeOf elf' (cliProgExtPlacedAt mpl ext idx W) (inputsOf i) = some res)
    (hobs : MainResult.Observed i.files (.ret 2 [] []) res) :
    CliRunsToExtOnInputsAt mpl ext idx inputsOf elf W i (.exited 2 [] (filesOf i.files)) := by
  rw [← MainResult.observed_usage i.files res hobs]
  exact cliRunsToExtOnInputsAt_of_outcomeOf hpatch hout

theorem codeLoaded_cliProgExtPlacedAt_of_inElf
    {mpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    {idx : Nat} {elf : ElfImage} {inputs : ProcessInputs} {s0 : State} {m : Memory}
    (hpl : libsignalSessionLib.Placeable mpl)
    (hin : libsignalSessionLib.InElf elf mpl)
    (hload : elf.loadState inputs = .ok s0)
    (hkf : s0.mem.KeepsFrozen m)
    (hidx : idx < libsignalSessionLib.blocks.length)
    (W : CliHooks) :
    (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m :=
  (libsignalSessionLib.blockProgram_codeLoaded_of_inElf hpl hin hload hidx).of_keepsFrozen hkf

theorem codeLoaded_cliProgExtPlaced_of_codeRoLoaded
    {mpl : Obj.MultiPlacement} {ext : CliHooks → String → Option (State → State)}
    (W : CliHooks) {m : Memory} (h : LibsignalCodeRoLoaded mpl m) :
    (cliProgExtPlacedAt mpl ext 617 W).CodeLoaded m :=
  h.1 617 (by decide) (by decide) (ext W) (fun _ => none) Syscall.standard

/-! ## Explicit-`mpl` `cliStaticsPlacedAt` and `mallocng` `.bss` / `.rodata` Helpers -/

/-- Explicit-`mpl` coin-tape globals (`COINS_NEXT`, `COINS_LEFT`). -/
def coinsStaticsPlacedAt (mpl : Obj.MultiPlacement) : SepProp :=
  (∃∗ v : BitVec 64, mpl.ρ coinsNextSym ↦₆₄ v) ∗
  (∃∗ v : BitVec 64, mpl.ρ coinsLeftSym ↦₆₄ v)

/-- Explicit-`mpl` SPQR CPU-probe token cells (`STORAGE.0 = 0`, `TOKEN.state = 0`). -/
def tokenInitPlacedAtMpl (mpl : Obj.MultiPlacement) : SepProp :=
  (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName ↦₈ 0#8) ∗
  ((mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64) ↦₃₂ 0#32)

/-- Explicit-`mpl` `libsignal` log-filter cell (`MAX_LOG_LEVEL_FILTER = 0`). -/
def lsLogOffAt (mpl : Obj.MultiPlacement) : SepProp :=
  mpl.ρ lsLogFilterSym ↦₆₄ 0#64

/-- Explicit-`mpl` writable statics bundle for `main`. -/
def cliStaticsPlacedAt (mpl : Obj.MultiPlacement) : SepProp :=
  coinsStaticsPlacedAt mpl ∗ tokenInitPlacedAtMpl mpl ∗ lsLogOffAt mpl

/-- Writable `.bss` portion of `VerifiedLibraries.mallocngLib.dataInit mmpl` (the 4 mutable globals
`__malloc_context` `928` B, `__malloc_lock` `4` B, `__malloc_replaced` `4` B, and
`__aligned_alloc_replaced` `4` B), separated from the read-only `.rodata` tables `MallocngRoTablesAt`. -/
def mallocngRwBssAt (mmpl : Obj.MultiPlacement) : SepProp :=
  let A := mallocngAddrsOfPlacement mmpl
  (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32)

theorem mallocngLib_dataInit_eq_ro_rw (mmpl : Obj.MultiPlacement) :
    mallocngLib.dataInit mmpl =
      MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ mallocngRwBssAt mmpl := by
  simpa only [mallocngRwBssAt] using mallocngLib_dataInit_eq mmpl

/-- Read-only slice witness `(m.RO base bs.length ∧ m.readBytes base bs.length = bs)` in `m`. -/
def MallocngRoSlice (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  m.RO base bs.length ∧ m.readBytes base bs.length = bs

/-- All 5 read-only `.rodata` lookup tables of `VerifiedLibraries.mallocngLib` at `mmpl` hold in
`m` with `Perm.ro`. -/
def MallocngRoTablesInMem (mmpl : Obj.MultiPlacement) (m : Memory) : Prop :=
  let A := mallocngAddrsOfPlacement mmpl
  MallocngRoSlice m A.sizeClasses mallocngSizeClassBytes ∧
    MallocngRoSlice m A.debruijnFree mallocngDebruijn32Table ∧
    MallocngRoSlice m A.medCntTab mallocngMedCntTabBytes ∧
    MallocngRoSlice m A.smallCntTab mallocngSmallCntTabBytes ∧
    MallocngRoSlice m A.debruijnAlloc mallocngDebruijn32Table

private theorem readBytes_eq_of_keepsFrozen_ro {m m' : Memory} (hkf : m.KeepsFrozen m') :
    ∀ (n : Nat) (base : BitVec 64), n ≤ 2 ^ 64 → m.RO base n →
      m'.readBytes base n = m.readBytes base n
  | 0, _, _, _ => rfl
  | n + 1, base, hn, hro => by
    have ha0 : InRegion base (n + 1) base := by
      unfold InRegion
      simp only [BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_lt_succ]
    have hfr0 : m.Frozen base := by
      unfold Memory.Frozen
      rw [(hro base ha0).1]
      rfl
    have hroTail : m.RO (base + 1#64) n := fun a ha => by
      apply hro a
      unfold InRegion at ha ⊢
      have hsub : a - base = (a - (base + 1#64)) + 1#64 := by bv_arith
      rw [hsub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [Memory.readBytes, (hkf base hfr0).1,
      readBytes_eq_of_keepsFrozen_ro hkf n (base + 1#64) (by omega) hroTail]

theorem mallocngRoSlice_of_keepsFrozen {m m' : Memory} {base : BitVec 64} {bs : List (BitVec 8)}
    (hs : MallocngRoSlice m base bs) (hlen : bs.length ≤ 2 ^ 64) (hkf : m.KeepsFrozen m') :
    MallocngRoSlice m' base bs := by
  refine ⟨fun a ha => ?_, (readBytes_eq_of_keepsFrozen_ro hkf bs.length base hlen hs.1).trans hs.2⟩
  have hfr : m.Frozen a := by
    unfold Memory.Frozen
    rw [(hs.1 a ha).1]
    rfl
  obtain ⟨_, hp, hlf, _⟩ := hkf a hfr
  exact ⟨hp.trans (hs.1 a ha).1, hlf.trans (hs.1 a ha).2⟩

theorem satisfies_mallocngRoTablesAt_of_keepsFrozen
    {mmpl : Obj.MultiPlacement} {m m' : Memory} {Q : SepProp}
    (hro : MallocngRoTablesInMem mmpl m) (hkf : m.KeepsFrozen m') (hQ : m' ⊨ Q) :
    m' ⊨ MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ Q := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4⟩ := hro
  have h0 := mallocngRoSlice_of_keepsFrozen hs0 (by decide) hkf
  have h1 := mallocngRoSlice_of_keepsFrozen hs1 (by decide) hkf
  have h2 := mallocngRoSlice_of_keepsFrozen hs2 (by decide) hkf
  have h3 := mallocngRoSlice_of_keepsFrozen hs3 (by decide) hkf
  have h4 := mallocngRoSlice_of_keepsFrozen hs4 (by decide) hkf
  have hSat :=
    Satisfies.rodata_intro h0.1 h0.2 (by decide)
      (Satisfies.rodata_intro h1.1 h1.2 (by decide)
        (Satisfies.rodata_intro h2.1 h2.2 (by decide)
          (Satisfies.rodata_intro h3.1 h3.2 (by decide)
            (Satisfies.rodata_intro h4.1 h4.2 (by decide) hQ))))
  have hassoc :
      ((mallocngAddrsOfPlacement mmpl).sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (((mallocngAddrsOfPlacement mmpl).debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
          (((mallocngAddrsOfPlacement mmpl).medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
            (((mallocngAddrsOfPlacement mmpl).smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
              (((mallocngAddrsOfPlacement mmpl).debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ Q)))) =
      MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ Q := by
    unfold MallocngRoTablesAt
    sep_ac_rfl
  rwa [hassoc] at hSat

theorem satisfies_mallocngDataInit_of_dataDisjoint
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {inputs : ProcessInputs} {s0 : State}
    (hpl : mallocngLib.Placeable mmpl)
    (hin : mallocngLib.InElf elf mmpl)
    (hdisj : mallocngLib.DataDisjoint mmpl)
    (hload : elf.loadState inputs = .ok s0) :
    s0.mem ⊨ mallocngLib.dataInit mmpl :=
  mallocngLib.satisfies_dataInit_of_inElf hpl hin hload (by decide) hdisj

theorem satisfies_mallocngRoAndRwBss_of_dataDisjoint
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {inputs : ProcessInputs} {s0 : State}
    (hpl : mallocngLib.Placeable mmpl)
    (hin : mallocngLib.InElf elf mmpl)
    (hdisj : mallocngLib.DataDisjoint mmpl)
    (hload : elf.loadState inputs = .ok s0) :
    s0.mem ⊨ MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ mallocngRwBssAt mmpl := by
  have h := satisfies_mallocngDataInit_of_dataDisjoint hpl hin hdisj hload
  rwa [mallocngLib_dataInit_eq_ro_rw mmpl] at h

end LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced
