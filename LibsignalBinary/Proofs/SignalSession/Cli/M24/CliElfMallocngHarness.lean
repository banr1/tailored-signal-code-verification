/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.CliBinaryTokenPatchPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.AllocNeverFailsOfPeak
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.MuslStartFineResources
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Heap.IfaceBudgetBase
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.Main.GamePaths
import LibsignalBinary.Proofs.SignalSession.Cli.Main.MuslHarnessOk
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridgeExec
import LibsignalBinary.Proofs.SignalSession.Cli.RunBridge
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process

/-!
# Placed ELF `mallocng` Harness and Strict Whole-Process Bridges

Whole-process `mallocng` harness and strict (`0`-excused-abort) execution bridges over an
`ElfImage` and split placements `(mpl, mmpl)`: explicit-`mpl` CPU-feature token patching,
`fineHookBudgetPool` and `NoOom` thunk initialization, the 41-row `WithClone` shared-allocator
hook table, parametric `CliRunsToExtOnInputsAt` / `cliRunExtPlacedSigAt` definitions, and the
per-input `MuslHarnessFinePerInput` composer.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.RustHeap (allocFailedEvent allocFailedIn)
open CryptoVerification.SignalSession
  (AddrInElf CliHooks CliRun Inputs Outcome OutcomeMatchesProcess PanickedAllocFails ProcessResult
   abortOnPanic abortOnPanic_eq_toSigState addrInElf_patchElfByte cliExternsPlaced
   cliExternsPlacedSig cliInputs_eq_cliProcessInputs cliMainStk_le_stackBudget cliProcessInputs
   elfStaticOk_patchElfByte filesOf isCliPanicSymbolPlaced
   libsignalSessionLib loadState_patchElfByte loadState_status_running observe
   outcomeObserved_unique outcomeOf outcomeOf_eq_aborted outcomeOf_eq_exited outcomeOf_eq_some_iff
   patchElfByte patchRegionByte processExitsWith_of_exited processExitsWith_of_signaled
   processInputs processTerminatedOutcome_unique segSlice_addrInElf sigAbrt toOutcome toSigState
   toSigState_mem toSigState_of_ne_panicked toSigState_symtab toSigState_trace)
open CryptoVerification.SignalSession.Cli
  (CliInputsOk CoinsReadable CommitOk ElfStaticOk InputsLoadable IsSendOverCap IsStdinOverCap
   MainCaseB2 MainEntryFacts MainGhost MainPost MainResult RunAnswer argvAt_eq
   cliInputs cliStaticsPlaced exit_frame fsView_congr
   fsView_writeAll_initFsState loadState_fs_trace signExtend_ofNat_small)
open CryptoVerification.SignalSession.Cli.MainHops (cliMainStk cli_stk_outcome)
open CryptoVerification.SignalSession.InitStack (cliStackSize stackBase stackBase_eq)
open CryptoVerification.SignalSession.MuslElf (CliElfMusl SegSlice cliStackBudget codeLoaded_of_text entry_bound)
open CryptoVerification.SignalSession.MuslExit
  (MuslExitFetch muslExitFetch_muslProg muslFiniFr muslProg muslProg_externAt? musl_exit_steps)
open CryptoVerification.SignalSession.Placed
  (CliRunsToPlaced cliProgPlacedSig cliRunPlacedSig cliTokenPatchPlaced)
open LibsignalBinary.Heap
  (AllocCostModel BudgetLimits RustAllocAddrs RustCliAllocBudget
   RustCliAllocNoOomEntriesBase mallocngBudgetPoolInv mallocngBudgetPool_of_init
   rustCliAllocNoOomSpecBase subroutine_ok_allocNoOom_of_budgetBase)
open LibsignalBinary.Heap.Fine
  (CliElfMallocngLayout FineBudget MallocngInitResources StartupVmPreserved allocMemsetVmSpec
   buildInitialStack_sub_stack cliElfStaticIvs elfLoadState_fields elfLoadState_poolInv
   elfStaticIvs fineBudgetPool_of_initResources fineCostModel fineHookBudgetPool_of_codeLoaded
   fineHookRustCliAllocBudget fineHookRustCliAllocBudgetEntries_thunks
   fineHookRustCliAllocZeroedBudget_thunk_ok fineRustCliAllocBudget
   mallocngBrkStartWf_of_elf mallocngBudgetPoolInv_of_startupVmPreserved rdlAllocZeroedInstrs
   stringCloneHookMallocng)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (allocMemcpyVmSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.AllocNeverFailsOfPeak
  (preservesNoAllocFailed_stringCloneHookMallocng)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.M2ExternNoAllocFail
  (ExternPreservesNoAllocFailed PreservesNoAllocFailed cliM2ExternsPlaced cliM2HookTablePlaced
   cliM2ProgPlacedSig cliM2ProgPlacedSigAt externPreservesNoAllocFailed_cliM2ExternsPlaced
   externPreservesNoAllocFailed_none externPreserves_map_abortOnPanic
   not_panickedAllocFails_of_externPreserves steps_preserves_no_allocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MuslStartFineResources
  (MuslStartFetchAt MuslStartupVmPreserved mainPcOf muslTpOf musl_startup_fineInit_ofProg)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
  (mainEntryPrePlaced mainSpecTightPlaced mainSpecTightPlacedAt)
open ProofLib.StdStartup (hasInstrs)
open VerifiedLibraries.Mallocng
  (MallocngAddrs MallocngAuxvAt MallocngBrkStartWf MallocngRoTablesAt MallocngRuntime
   mallocngAddrsOfPlacement mallocngDebruijn32Table mallocngMedCntTabBytes mallocngSizeClassBytes
   mallocngSmallCntTabBytes)
open VerifiedLibraries.Mallocng.Proofs (ProgContainsMallocng mallocngLib_dataInit_eq)
open VerifiedLibraries.RustStd
  (RustStdRdlShimCode RustStdThunkCode mallocngPlacedCAddrs)

/-! ## Explicit-`mpl` token patch and `fineHookBudgetPool` initialization -/

private theorem blockProgram_stubs_lt (lib : MultiPlacedLib) (mpl : MultiPlacement) (idx : Nat)
    (X O : String → Option (State → State)) (svc : State → State) :
    ∀ x ∈ (lib.blockProgram mpl idx X O svc).stubs, x.2 < 2 ^ 64 := by
  dsimp only [MultiPlacedLib.blockProgram, PlacedLib.program]
  intro x hx
  rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
  exact BitVec.isLt _

private theorem musl_exit_ofProg {P : Program} {B : BitVec 64} {code : List (BitVec 8)}
    (hst : ∀ x ∈ P.stubs, x.2 < 2 ^ 64)
    (hov : ∀ n, P.overrides n = none)
    (hsvcP : P.svc = Syscall.standard)
    (hB : B &&& 0xfff#64 = 0#64)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb74 → P.externAt? (B + k) = none)
    (hf : MuslExitFetch ({ code } : Program) 0#64)
    {sm sr : State} (hL : ({ base := B, code } : Program).CodeLoaded sm.mem)
    (hlr : sm.readReg64 .lr = B + 0x854#64) (hal : sm.spAligned = true)
    (hsteps : Steps P sm sr) (hret : Returned sm sr)
    (hm : sr.mem ⊨ stackAt sm.sp 48 ∗ muslFiniFr B ∗ anyHeap) :
    ∃ sx, Steps P sr sx ∧
      sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
      sx.fs = sr.fs ∧ sx.trace = sr.trace := by
  obtain ⟨hpc, hsp, hrun⟩ := hret
  have hPQ : ∀ pc, (muslProg P B code).externAt? pc = P.externAt? pc :=
    muslProg_externAt? P B code hst hov
  have hfQ : MuslExitFetch (muslProg P B code) B :=
    muslExitFetch_muslProg P B code (fun k hk => (hPQ (B + k)).trans (hnoHook k hk)) hf
  have hLQ : (muslProg P B code).CodeLoaded sr.mem :=
    Steps.codeLoaded hsteps (hL.of_base_code rfl rfl)
  have hal' : sr.spAligned = true := by
    simp only [State.spAligned, hsp] at hal ⊢; exact hal
  rw [← hsp] at hm
  rcases P with ⟨base, code', symbols, stubs, externs, overrides, svc⟩
  dsimp only at hsvcP
  subst hsvcP
  exact musl_exit_steps hPQ hfQ hB hLQ (hpc.trans hlr) hrun hal' hm

/-- Explicit-`mpl` `PT_LOAD` `.data` slice witness for `spqr`'s initial CPU-feature cells
(`STORAGE.0 = 0xff`, `TOKEN.state = 3`). -/
structure CliElfTokenCellsPlacedAt (mpl : Obj.MultiPlacement) (elf : ElfImage) : Prop where
  storage : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenStorageName)
    [0xff#8] Perm.rw
  once : SegSlice elf (mpl.ρ CryptoVerification.LibsignalSpqrV1.tokenName + 8#64)
    [3#8, 0#8, 0#8, 0#8] Perm.rw

/-- Ghost `ElfImage` with `spqr`'s 5 CPU-probe `.data` bytes pre-set to `0` (`DEV-CLI10`) at
placement `mpl`, satisfying `(patchElfTokensPlacedAt mpl elf).loadState inputs =
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

/-- `patchElfTokensPlacedAt` preserves `CliElfMallocngLayout`. -/
theorem cliElfMallocngLayout_iff_patchElfTokensPlacedAt {mpl : Obj.MultiPlacement}
    {elf : ElfImage} {lim : BudgetLimits} :
    CliElfMallocngLayout (patchElfTokensPlacedAt mpl elf) lim ↔ CliElfMallocngLayout elf lim := by
  unfold patchElfTokensPlacedAt
  dsimp only
  simp only [cliElfMallocngLayout_iff_patchElfByte]

/-- Stack and physical-RAM `InitConfig` parameters shared by `cliProcessInputs` and `hwcap = 0x3`
inputs. -/
def CliStackShape (inputs : ProcessInputs) : Prop :=
  inputs.init.stackTop = defaultStackTop ∧
  inputs.init.stackSize = cliStackSize ∧
  inputs.init.physMemAvail = 2 ^ 30

theorem cliStackShape_cliProcessInputs (i : Inputs) : CliStackShape (cliProcessInputs i) :=
  ⟨rfl, rfl, rfl⟩

theorem cliStackShape_cliInputs (i : Inputs) : CliStackShape (cliInputs i) := by
  rw [cliInputs_eq_cliProcessInputs]
  exact cliStackShape_cliProcessInputs i

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
      VerifiedLibraries.mallocngLib.dataInit mmpl ∗
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

theorem fineHookBudgetPool_of_inputs
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {inputs : ProcessInputs} {sLoad sm : State} {auxvPtr : BitVec 64} {R : SepProp}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState inputs = .ok sLoad)
    (hVm : StartupVmPreserved sLoad sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hmem : sm.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mmpl ∗
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
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hThunks : RustStdThunkCode P thunkAddrs.toRustStd rdlAddrs.toRustStd)
    (hShims : RustStdRdlShimCode P rdlAddrs.toRustStd (mallocngPlacedCAddrs mmpl) memcpyAddr)
    (hZeroThunk : hasInstrs P allocZeroedThunkAddr [.b (allocZeroedRdlAddr - allocZeroedThunkAddr)])
    (hZeroCode : hasInstrs P allocZeroedRdlAddr
      (rdlAllocZeroedInstrs allocZeroedRdlAddr (VerifiedLibraries.mallocngLib.fnAddr mmpl "calloc")
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
      VerifiedLibraries.mallocngLib.dataInit mmpl ∗
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

/-- Package `__libc.need_locks = 0`, TLS `errno`, `auxv`, page size `4096`, and
`mallocngLib.dataInit` into `fineHookRustCliAllocBudget.pool` at `fineCostModel.init`. -/
theorem b2FineHookPool_of_needLocks
    {elf : ElfImage} {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {inputs : ProcessInputs} {sLoad sm : State}
    {libcAddr auxvPtr : BitVec 64} {errnoVal : BitVec 32} {R : SepProp}
    (hCL : VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hsh : CliStackShape inputs)
    (hLayout : CliElfMallocngLayout elf lim)
    (hLoad : elf.loadState inputs = .ok sLoad)
    (hVm : StartupVmPreserved sLoad sm)
    (htpLo : 0xa4 ≤ sm.tpidrEl0.toNat)
    (htpHi : sm.tpidrEl0.toNat ≤ 2 ^ 48)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = libcAddr)
    (hmem : sm.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit mmpl ∗
        ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((libcAddr + 3#64) ↦₈ 0#8) ∗
        ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) :
    ∃ γ : GhostName,
      sm.mem ⊨
        (fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart).pool
          lim fineCostModel.init sm ∗ R := by
  refine fineHookBudgetPool_of_inputs hCL hsh hLayout hLoad hVm htpLo htpHi (auxvPtr := auxvPtr) ?_
  unfold MallocngRuntime
  rw [hlibc]
  have hassoc :
      (VerifiedLibraries.mallocngLib.dataInit mmpl ∗
        ((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
        ((libcAddr + 3#64) ↦₈ 0#8) ∗
        ((libcAddr + 48#64) ↦₆₄ 4096#64) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) =
      (VerifiedLibraries.mallocngLib.dataInit mmpl ∗
        (((sm.tpidrEl0 - 0xa4#64) ↦₃₂ errnoVal) ∗
          ((libcAddr + 3#64) ↦₈ 0#8) ∗
          ((libcAddr + 48#64) ↦₆₄ 4096#64)) ∗
        ((libcAddr + 8#64) ↦₆₄ auxvPtr) ∗
        MallocngAuxvAt auxvPtr ∗ R) := by sep_ac_rfl
  rw [hassoc] at hmem
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono_left (sepConj_mono_left (Entails.sepExists_intro errnoVal))))
    hmem

/-! ## 41-row `WithClone` shared-allocator hook table -/

/-- Mangled ELF symbol for `<alloc::string::String as core::clone::Clone>::clone`. -/
abbrev lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

/-- 41-row shared-allocator CLI hook table extending `cliM2HookTablePlaced` with
`stringCloneHookMallocng`. -/
noncomputable def cliM2HookTableWithClonePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    List (String × (State → State)) :=
  (lsStringCloneSym, stringCloneHookMallocng mmpl) :: cliM2HookTablePlaced mmpl W

noncomputable def cliM2ExternsWithClonePlaced (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name =>
    if isCliPanicSymbolPlaced name then some Rust.panicked
    else (cliM2HookTableWithClonePlaced mmpl W).lookup name

noncomputable def cliM2ExternsWithClonePlacedSig (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    String → Option (State → State) :=
  fun name => (cliM2ExternsWithClonePlaced mmpl W name).map abortOnPanic

noncomputable def cliM2ProgWithClonePlacedAt (mpl mmpl : Obj.MultiPlacement) (idx : Nat)
    (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (cliM2ExternsWithClonePlaced mmpl W)

noncomputable def cliM2ProgWithClonePlaced (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Program :=
  cliM2ProgWithClonePlacedAt mpl mmpl 617 W

noncomputable def cliM2ProgWithClonePlacedSigAt (mpl mmpl : Obj.MultiPlacement) (idx : Nat)
    (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (cliM2ExternsWithClonePlacedSig mmpl W)

noncomputable def cliM2ProgWithClonePlacedSig (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    Program :=
  cliM2ProgWithClonePlacedSigAt mpl mmpl 617 W

theorem cliM2ExternsWithClonePlaced_stringClone (mmpl : Obj.MultiPlacement) (W : CliHooks)
    (hnpan : isCliPanicSymbolPlaced lsStringCloneSym = false) :
    cliM2ExternsWithClonePlaced mmpl W lsStringCloneSym = some (stringCloneHookMallocng mmpl) := by
  unfold cliM2ExternsWithClonePlaced cliM2HookTableWithClonePlaced
  simp [hnpan, List.lookup]

private theorem preservesNoAllocFailed_rustPanicked : PreservesNoAllocFailed Rust.panicked := by
  intro s h
  simpa [Rust.panicked] using h

theorem externPreservesNoAllocFailed_cliM2ExternsWithClonePlaced
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ExternPreservesNoAllocFailed (cliM2ExternsWithClonePlaced mmpl W) := by
  intro name f h
  unfold cliM2ExternsWithClonePlaced cliM2HookTableWithClonePlaced at h
  split at h
  · injection h with hrf
    subst hrf
    exact preservesNoAllocFailed_rustPanicked
  · rename_i hnpan
    simp only [List.lookup] at h
    cases hbeq : (name == lsStringCloneSym) with
    | true =>
      rw [hbeq] at h
      injection h with hcf
      subst hcf
      exact preservesNoAllocFailed_stringCloneHookMallocng mmpl
    | false =>
      rw [hbeq] at h
      have h40 : cliM2ExternsPlaced mmpl W name = some f := by
        unfold cliM2ExternsPlaced
        simp only [hnpan, Bool.false_eq_true, ↓reduceIte]
        exact h
      exact externPreservesNoAllocFailed_cliM2ExternsPlaced mmpl W name f h40

theorem externPreservesNoAllocFailed_cliM2ExternsWithClonePlacedSig
    (mmpl : Obj.MultiPlacement) (W : CliHooks) :
    ExternPreservesNoAllocFailed (cliM2ExternsWithClonePlacedSig mmpl W) :=
  externPreserves_map_abortOnPanic
    (externPreservesNoAllocFailed_cliM2ExternsWithClonePlaced mmpl W)

theorem not_panickedAllocFails_cliM2ProgWithClonePlacedAt
    (mpl mmpl : Obj.MultiPlacement) (idx : Nat) (elf : ElfImage) (W : CliHooks) (i : Inputs) :
    ¬ PanickedAllocFails elf (cliM2ProgWithClonePlacedAt mpl mmpl idx W) i :=
  not_panickedAllocFails_of_externPreserves rfl externPreservesNoAllocFailed_none
    (externPreservesNoAllocFailed_cliM2ExternsWithClonePlaced mmpl W)

theorem not_panickedAllocFails_cliM2ProgWithClonePlaced
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) (i : Inputs) :
    ¬ PanickedAllocFails elf (cliM2ProgWithClonePlaced mpl mmpl W) i :=
  not_panickedAllocFails_cliM2ProgWithClonePlacedAt mpl mmpl 617 elf W i

theorem cliM2WithClone_allocNeverFailsPlacedAt
    (mpl mmpl : Obj.MultiPlacement) (idx : Nat) (elf : ElfImage) (W : CliHooks) :
    ∀ i : Inputs, ∀ s0 s : State,
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliM2ProgWithClonePlacedSigAt mpl mmpl idx W) (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace := by
  intro i s0 s hload hsteps
  have hloadCli : elf.loadState (cliInputs i) = .ok s0 := by
    rwa [cliInputs_eq_cliProcessInputs]
  have hs0 : allocFailedEvent ∉ (cliTokenPatchPlaced mpl s0).trace := by
    unfold cliTokenPatchPlaced State.setMem
    rw [(loadState_fs_trace hloadCli).2]
    simp
  exact steps_preserves_no_allocFailed rfl
    (externPreservesNoAllocFailed_cliM2ExternsWithClonePlacedSig mmpl W)
    externPreservesNoAllocFailed_none hsteps hs0

theorem cliM2WithClone_allocNeverFailsPlaced
    (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage) (W : CliHooks) :
    ∀ i : Inputs, ∀ s0 s : State,
      elf.loadState (cliProcessInputs i) = .ok s0 →
      Steps (cliM2ProgWithClonePlacedSig mpl mmpl W) (cliTokenPatchPlaced mpl s0) s →
      allocFailedEvent ∉ s.trace :=
  cliM2WithClone_allocNeverFailsPlacedAt mpl mmpl 617 elf W

/-! ## Parametric `CliRunsTo` / `CliRun` and `abortOnPanic` transport -/

noncomputable def cliProgExtPlacedAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (ext W)

noncomputable def cliProgExtPlacedSigAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat) (W : CliHooks) : Program :=
  libsignalSessionLib.blockProgram mpl idx (fun name => (ext W name).map abortOnPanic)

/-- Relocatable `CliRunsTo` parameterized by extern family `ext`, entry block `idx`, and
`inputsOf`. -/
def CliRunsToExtOnInputsAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (inputsOf : Inputs → ProcessInputs)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  ∃ s0, elf.loadState (inputsOf i) = .ok s0 ∧
    _root_.Arm64.Process.ProcessRunsTo (cliProgExtPlacedSigAt mpl ext idx W)
      (cliTokenPatchPlaced mpl s0) (OutcomeMatchesProcess o)

abbrev CliRunsToExtPlacedAt (mpl : Obj.MultiPlacement)
    (ext : CliHooks → String → Option (State → State)) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) (i : Inputs) (o : Outcome) : Prop :=
  CliRunsToExtOnInputsAt mpl ext idx cliProcessInputs elf W i o

open Classical in
/-- Relocatable `CliRun` parameterized by extern family `ext`, entry block `idx`, and `inputsOf`. -/
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

noncomputable abbrev cliM2RunPlacedSigAt (mpl mmpl : Obj.MultiPlacement) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  cliRunExtPlacedSigAt mpl (cliM2ExternsPlaced mmpl) idx elf W

noncomputable abbrev cliM2RunPlacedSig (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  cliM2RunPlacedSigAt mpl mmpl 617 elf W

noncomputable abbrev cliM2WithCloneRunPlacedSigAt (mpl mmpl : Obj.MultiPlacement) (idx : Nat)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  cliRunExtPlacedSigAt mpl (cliM2ExternsWithClonePlaced mmpl) idx elf W

noncomputable abbrev cliM2WithCloneRunPlacedSig (mpl mmpl : Obj.MultiPlacement)
    (elf : ElfImage) (W : CliHooks) : CliRun :=
  cliM2WithCloneRunPlacedSigAt mpl mmpl 617 elf W

theorem cliProgExtPlacedSigAt_cliExterns_eq (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    cliProgExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 W = cliProgPlacedSig mpl mmpl W := rfl

theorem cliProgExtPlacedSigAt_m2_eq (mpl mmpl : Obj.MultiPlacement) (idx : Nat) (W : CliHooks) :
    cliProgExtPlacedSigAt mpl (cliM2ExternsPlaced mmpl) idx W =
      cliM2ProgPlacedSigAt mpl mmpl idx W := rfl

theorem cliProgExtPlacedSigAt_m2WithClone_eq (mpl mmpl : Obj.MultiPlacement) (idx : Nat)
    (W : CliHooks) :
    cliProgExtPlacedSigAt mpl (cliM2ExternsWithClonePlaced mmpl) idx W =
      cliM2ProgWithClonePlacedSigAt mpl mmpl idx W := rfl

theorem cliRunsToExtPlacedAt_cliExterns_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) (i : Inputs) (o : Outcome) :
    CliRunsToExtPlacedAt mpl (cliExternsPlaced mmpl) 617 elf W i o =
      CliRunsToPlaced mpl mmpl elf W i o := rfl

theorem cliRunExtPlacedSigAt_cliExterns_eq (mpl mmpl : Obj.MultiPlacement) (elf : ElfImage)
    (W : CliHooks) :
    cliRunExtPlacedSigAt mpl (cliExternsPlaced mmpl) 617 elf W = cliRunPlacedSig mpl mmpl elf W := rfl

private theorem processTerminatedOutcome_not_running_ext {sf : State} {out : ProcessOutcome}
    (h : ProcessTerminatedOutcome sf out) : sf.status ≠ .Running := by
  rcases h with ⟨_, hst, _⟩ | ⟨_, hst, _⟩ <;> rw [hst] <;> intro hr <;> cases hr

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
    · cases processTerminatedOutcome_unique hTerm₁ hTerm₂
      exact outcomeObserved_unique hObs₁ hObs₂
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

theorem step_cliProgExtPlacedAt_to_sig {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {s s' : State}
    (h : Step (cliProgExtPlacedAt mpl ext idx W) s s') :
    Step (cliProgExtPlacedSigAt mpl ext idx W) s (toSigState s') := by
  cases h with
  | @exec inst h_run h_fetch =>
    have hs_ne : s.status ≠ .Panicked := by rw [h_run]; intro hc; cases hc
    have h_ne : ((cliProgExtPlacedAt mpl ext idx W).evalInst inst s).status ≠ .Panicked :=
      evalInst_standard_status_ne_panicked rfl inst hs_ne
    rw [toSigState_of_ne_panicked h_ne]
    exact Step.exec h_run ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
  | halt_unmapped h_run h_fetch h_ext =>
    have h_ne : ({ s with status := .Halted } : State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    exact Step.halt_unmapped h_run
      ((fetchMem_cliProgExtPlacedSigAt mpl ext idx W s.mem s.pc).trans h_fetch)
      (externAt?_cliProgExtPlacedSigAt_eq_none.mpr h_ext)
  | @extern f h_run h_ext h_keep h_sym =>
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    rw [← abortOnPanic_eq_toSigState]
    refine Step.extern h_run h_ext_sig ?_ ?_
    · rw [abortOnPanic_eq_toSigState, toSigState_mem]; exact h_keep
    · rw [abortOnPanic_eq_toSigState, toSigState_symtab]; exact h_sym
  | @extern_fault f h_run h_ext h_nkeep =>
    have h_ne :
        ({ s with status := .Exception "extern hook modified read-only memory or symbol table" } :
          State).status ≠ .Panicked := by
      intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
    have h_ext_sig : (cliProgExtPlacedSigAt mpl ext idx W).externAt? s.pc = some (abortOnPanic f) := by
      rw [externAt?_cliProgExtPlacedSigAt, h_ext]; rfl
    refine Step.extern_fault h_run h_ext_sig ?_
    rw [abortOnPanic_eq_toSigState, toSigState_mem, toSigState_symtab]
    exact h_nkeep

theorem steps_cliProgExtPlacedAt_to_sig {mpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks} {s0 sf : State}
    (hrun0 : s0.status = .Running)
    (hsteps : Steps (cliProgExtPlacedAt mpl ext idx W) s0 sf) :
    Steps (cliProgExtPlacedSigAt mpl ext idx W) s0 (toSigState sf) := by
  induction hsteps with
  | refl s =>
    have h_ne : s.status ≠ .Panicked := by rw [hrun0]; intro hc; cases hc
    rw [toSigState_of_ne_panicked h_ne]
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
        rwa [toSigState_of_ne_panicked h_ne2] at this
      exact Steps.step h1' (ih hrun2)

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
    · have heq : toSigState sf = sf :=
        toSigState_of_ne_panicked (by rw [hst]; intro hc; cases hc)
      rw [heq] at hsteps_sig
      exact ElfImageRunsTo.of_exitsWith hload'
        (processExitsWith_of_exited hsteps_sig hst) ⟨rfl, rfl, rfl, rfl⟩
    · have hsig : (toSigState sf).status = .Signaled sigAbrt := by
        simp [toSigState, hst, State.status_setStatus]
      exact ElfImageRunsTo.of_exitsWith hload'
        (processExitsWith_of_signaled hsteps_sig hsig) ⟨rfl, rfl⟩
  exact CryptoVerification.SignalSession.elfImageRunsTo_of_load_map hpatch hraw

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

/-! ## Per-input `MuslHarnessFinePerInput` and strict `main` outcome composers -/

/-- Per-input `∃ (Fr : SepProp) (γ : GhostName)` whole-process harness for
`fineHookRustCliAllocBudget` at cost-model state `st`. -/
def MuslHarnessFinePerInput
    (elf : ElfImage) (P : Program) (mainPc : BitVec 64)
    (mmpl : Obj.MultiPlacement) (lim : BudgetLimits) (st : FineBudget)
    (stk : Nat) (CodeOk : Memory → Prop) (Statics : SepProp) : Prop :=
  ElfStaticOk elf →
  ∀ i : Inputs, CliInputsOk i ∧ InputsLoadable i →
    ∃ (s0 sm : State) (Fr : SepProp) (γ : GhostName),
      let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
      elf.loadState (cliInputs i) = .ok s0 ∧
      Steps P s0 sm ∧
      sm.pc = mainPc ∧
      sm.status = .Running ∧
      sm.spAligned = true ∧
      sm.fs = s0.fs ∧
      sm.trace = s0.trace ∧
      (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (i.argv.length + 1) ∧
      (sm.mem ⊨ mainEntryPrePlaced CodeOk A lim st stk Statics i sm ∗ Fr) ∧
      ∀ sr : State, Steps P sm sr → Returned sm sr →
        (sr.mem ⊨ stackAt sm.sp 48 ∗ Fr ∗ anyHeap) →
        ∃ sx : State, Steps P sr sx ∧
          sx.status = .Exited (((sr.readReg64 .x0).setWidth 32).signExtend 64) ∧
          sx.fs = sr.fs ∧ sx.trace = sr.trace

/-- Strict (`0`-excused-abort) whole-process `main` outcome theorem from `MuslHarnessFinePerInput`
and `mainSpecTightPlacedAt`. -/
theorem outcome_of_main_strict_m2_perInput_at
    {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFinePerInput elf P mainPc mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        (mainSpecTightPlacedAt CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim st stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (cliInputs i) = some res ∧ MainResult.Observed i.files r res := by
  obtain ⟨s0, sm, Fr, γ, hload, hsteps0, hpc, hrun, hal, hfs, htr, hx0, hmem, hexit⟩ :=
    hH hE i ⟨hi, hl⟩
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  obtain ⟨hfs0, htr0⟩ := loadState_fs_trace hload
  simp only [mainEntryPrePlaced, sepConj_assoc, satisfies_pure_sepConj] at hmem
  obtain ⟨⟨hCO, hsp⟩, hmem⟩ := hmem
  have hpre : sm.mem ⊨ (mainSpecTightPlacedAt CodeOk A lim st stk Statics Run).pre ⟨i, r⟩ sm ∗ Fr := by
    simp only [mainSpecTightPlacedAt, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hCO, hc, hi, ⟨hx0, hfs.trans hfs0, htr.trans htr0⟩, hsp⟩, hmem⟩
  obtain ⟨sf, hsteps1, hout, _⟩ :=
    (hmain γ sm.tpidrEl0).no_fault_before_outcome ⟨i, r⟩ Fr sm hpc hrun hpre hal (hCode sm.mem hCO)
  have hsteps01 := hsteps0.trans hsteps1
  rcases hout with ⟨hret, _, hpost⟩ | ⟨hpan, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
  · simp only [mainSpecTightPlacedAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨code, w, out, rfl, hw0, hfiles, hout⟩, hpost⟩ := hpost
    rw [← sepConj_assoc] at hpost
    obtain ⟨sx, hsteps2, hst, hfsx, htrx⟩ :=
      hexit sf hsteps1 hret (exit_frame hstk hstk' hpost)
    have hle := hc.code_le rfl
    refine ⟨_, outcomeOf_eq_exited hload (hsteps01.trans hsteps2) hst, ?_⟩
    dsimp only [MainResult.Observed]
    refine ⟨?_, ?_, ?_⟩
    · rw [hw0, signExtend_ofNat_small hle]
    · rw [htrx, hout]
    · rw [hfsx, fsView_congr hfiles, hfs, hfs0]
      exact fsView_writeAll_initFsState i w hc.commitOk
  · simp only [mainSpecTightPlacedAt, sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost.1 with rfl | hA
    · exact ⟨_, outcomeOf_eq_aborted hload hsteps01 hpan, trivial⟩
    · exact (not_panickedAllocFails_of_externPreserves hsvc hovr hext
        ⟨s0, sf, hload, hsteps01, hpan, List.mem_of_mem_drop hA⟩).elim
  · exact (not_satisfies_false_sepConj hpost).elim
  · exact (not_satisfies_false_sepConj hpost).elim

theorem outcome_of_main_strict_m2_perInput
    {elf : ElfImage} {P : Program} {mainPc : BitVec 64}
    {mmpl : Obj.MultiPlacement} {CodeOk : Memory → Prop}
    {lim : BudgetLimits} {st : FineBudget} {stk : Nat} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hsvc : P.svc = Syscall.standard)
    (hovr : ExternPreservesNoAllocFailed P.overrides)
    (hext : ExternPreservesNoAllocFailed P.externs)
    (hE : ElfStaticOk elf)
    (hCode : ∀ m, CodeOk m → P.CodeLoaded m)
    (hH : MuslHarnessFinePerInput elf P mainPc mmpl lim st stk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok P mainPc
        (mainSpecTightPlaced CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim stk Statics Run))
    (hstk : 48 ≤ stk) (hstk' : stk ≤ 2 ^ 64)
    {i : Inputs} {r : MainResult} (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hc : MainCaseB2 Run IsSendOverCap IsStdinOverCap i r) :
    ∃ res, outcomeOf elf P (cliInputs i) = some res ∧ MainResult.Observed i.files r res :=
  outcome_of_main_strict_m2_perInput_at hsvc hovr hext hE hCode hH
    (fun γ tp => subroutine_ok.of_codeLoaded fun g R s0 hpc hrun hpre hal _ =>
      (hmain γ tp).mono_outcome (g, st) R s0 hpc hrun hpre hal fun _ hout => hout)
    hstk hstk' hi hl hc

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

theorem cliRunExtPlacedSigAt_of_strict_main_stdinOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) mmpl lim st cliMainStk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (mainSpecTightPlacedAt CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim st cliMainStk Statics Run))
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hstin : IsStdinOverCap i) :
    cliRunExtPlacedSigAt mpl ext idx elf W i = some (.exited 2 [] (filesOf i.files)) := by
  obtain ⟨hstk, hstk'⟩ := cli_stk_outcome
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_m2_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.stdinOverCap hstin)
  rw [cliInputs_eq_cliProcessInputs] at hout
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_usage
    (loadState_patchElfTokensPlacedAt hE htok (cliProcessInputs i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtPlacedSigAt_of_strict_main_sendOverCap
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) mmpl lim st cliMainStk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (mainSpecTightPlacedAt CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim st cliMainStk Statics Run))
    {i : Inputs}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hover : IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hcoins : CoinsReadable i) :
    cliRunExtPlacedSigAt mpl ext idx elf W i = some (.exited 1 [] (filesOf i.files)) := by
  obtain ⟨hstk, hstk'⟩ := cli_stk_outcome
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_m2_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.sendOverCap hover hnstin hcoins)
  rw [cliInputs_eq_cliProcessInputs] at hout
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed (a := some none)
    (loadState_patchElfTokensPlacedAt hE htok (cliProcessInputs i)) hout hresObs
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtPlacedSigAt_of_strict_main_call_obs
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) mmpl lim st cliMainStk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (mainSpecTightPlacedAt CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim st cliMainStk Statics Run))
    {i : Inputs} {a : RunAnswer} {o : Outcome}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hobs : observe i.files a = o)
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    cliRunExtPlacedSigAt mpl ext idx elf W i = some o := by
  obtain ⟨hstk, hstk'⟩ := cli_stk_outcome
  have hbrk : (patchElfTokensPlacedAt mpl elf).brkStart = elf.brkStart := rfl
  obtain ⟨res, hout, hresObs⟩ :=
    outcome_of_main_strict_m2_perInput_at rfl externPreservesNoAllocFailed_none hext
      (elfStaticOk_patchElfTokensPlacedAt hE) hCode hH
      (fun γ tp => by simpa only [hbrk] using hmain γ tp)
      hstk hstk' hi hl (MainCaseB2.call hrun hnover hnstin hcoins hcommit)
  rw [cliInputs_eq_cliProcessInputs] at hout
  have hruns := cliRunsToExtOnInputsAt_of_outcomeOf_observed
    (loadState_patchElfTokensPlacedAt hE htok (cliProcessInputs i)) hout hresObs
  rw [hobs] at hruns
  exact cliRunExtOnInputsSigAt_eq_some hruns

theorem cliRunExtPlacedSigAt_of_strict_main_call_pred
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat}
    {elf : ElfImage} {W : CliHooks}
    {CodeOk : Memory → Prop} {lim : BudgetLimits} {st : FineBudget} {Statics : SepProp}
    {Run : Inputs → RunAnswer → Prop} {P : Outcome → Prop}
    (hext : ExternPreservesNoAllocFailed (ext W))
    (hE : ElfStaticOk elf)
    (htok : CliElfTokenCellsPlacedAt mpl elf)
    (hCode : ∀ m, CodeOk m → (cliProgExtPlacedAt mpl ext idx W).CodeLoaded m)
    (hH : MuslHarnessFinePerInput (patchElfTokensPlacedAt mpl elf)
      (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx) mmpl lim st cliMainStk CodeOk Statics)
    (hmain : ∀ (γ : GhostName) (tp : BitVec 64),
      subroutine_ok (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
        (mainSpecTightPlacedAt CodeOk
          (fineHookRustCliAllocBudget γ mmpl tp elf.brkStart) lim st cliMainStk Statics Run))
    {i : Inputs} {a : RunAnswer}
    (hi : CliInputsOk i) (hl : InputsLoadable i)
    (hrun : Run i a) (hnover : ¬ IsSendOverCap i) (hnstin : ¬ IsStdinOverCap i)
    (hp : P (observe i.files a))
    (hcoins : CoinsReadable i) (hcommit : CommitOk i (MainResult.ofAnswer a)) :
    ∃ o, cliRunExtPlacedSigAt mpl ext idx elf W i = some o ∧ P o :=
  ⟨observe i.files a,
    cliRunExtPlacedSigAt_of_strict_main_call_obs hext hE htok hCode hH hmain
      hi hl hrun hnover hnstin rfl hcoins hcommit,
    hp⟩

/-! ### `MuslStartFineResources` builder for `MuslHarnessFinePerInput` -/

/-- Writable `.bss` globals of `mallocngLib.dataInit mmpl` (`__malloc_context`, `__malloc_lock`,
`__malloc_replaced`, `__aligned_alloc_replaced`). -/
def mallocngRwBssAt (mmpl : Obj.MultiPlacement) : SepProp :=
  let A := mallocngAddrsOfPlacement mmpl
  (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32)

theorem mallocngLib_dataInit_eq_ro_rw (mmpl : Obj.MultiPlacement) :
    VerifiedLibraries.mallocngLib.dataInit mmpl =
      MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ mallocngRwBssAt mmpl := by
  simpa only [mallocngRwBssAt] using mallocngLib_dataInit_eq mmpl

def MallocngRoSlice (m : Memory) (base : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  m.RO base bs.length ∧ m.readBytes base bs.length = bs

/-- Read-only `.rodata` lookup tables of `mallocngLib` at `mmpl` held with `Perm.ro` in `m`. -/
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

/-- Build `MuslHarnessFinePerInput` from `musl_startup_fineInit_ofProg` and `musl_exit_ofProg`. -/
theorem muslHarnessFinePerInput_of_muslStartFine
    {elf : ElfImage} {P : Program} {code : List (BitVec 8)}
    {mmpl : Obj.MultiPlacement} {lim : BudgetLimits}
    {dynPageImm pageImm : BitVec 64} {addImm : BitVec 12}
    {CodeOk : Memory → Prop} {Statics : SepProp} {S : Nat → Prop}
    (hstP : ∀ x ∈ P.stubs, x.2 < 2 ^ 64)
    (hovrP : ∀ n, P.overrides n = none)
    (hsvcP : P.svc = Syscall.standard)
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 → P.externAt? (elf.entry + k) = none)
    (hMusl : CliElfMusl elf code)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = elf.entry + 0x21e8#64)
    (hfS : MuslStartFetchAt ({ code } : Program) 0#64 dynPageImm pageImm addImm)
    (hfE : MuslExitFetch ({ code } : Program) 0#64)
    (hLayout : CliElfMallocngLayout elf lim)
    (hCodeOk : ∀ (i : Inputs) (s0 sm : State),
      elf.loadState (cliInputs i) = .ok s0 →
      s0.mem.KeepsFrozen sm.mem →
      CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hRo : ∀ (i : Inputs) (s0 : State),
      elf.loadState (cliInputs i) = .ok s0 →
      MallocngRoTablesInMem mmpl s0.mem)
    (hSupp : ∀ (i : Inputs) (s0 : State),
      elf.loadState (cliInputs i) = .ok s0 →
      SupportedOn 0#64 S s0.mem (mallocngRwBssAt mmpl ∗ Statics))
    (hS : ∀ k, S k → k < stackBase ∧
      ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600)) :
    MuslHarnessFinePerInput elf P (mainPcOf elf.entry pageImm addImm)
      mmpl lim fineCostModel.init cliMainStk CodeOk Statics := by
  intro hE i ⟨⟨hargs, hfits⟩, ⟨hdirs, hfiles⟩⟩
  have hargs' : ∀ a ∈ i.argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128 :=
    fun a ha => (hargs a ha).2
  obtain ⟨s0, sm, auxvPtr, hload, hsteps, hpc, hrun, hal, hsp, hx0, hx1, hlr, hfs, htr,
    _, htpLo, htpHi, hvm, hmem, hstkSp⟩ :=
    musl_startup_fineInit_ofProg hsvcP hnoHook hMusl hE.1 hE.2 hlibc hfS
      i.argv i.stdin i.files i.dirs hargs' hfits hdirs hfiles
      cliMainStk cliMainStk_le_stackBudget
      (fun s0 hl => hSupp i s0 hl) hS
  obtain ⟨hCO, hCL⟩ := hCodeOk i s0 sm hload hsteps.keepsFrozen
  rw [argvAt_eq] at hmem
  let Rt := MallocngRuntime (mallocngAddrsOfPlacement mmpl) sm.tpidrEl0
  let Libc8 := (((mallocngAddrsOfPlacement mmpl).libc + 8#64) ↦₆₄ auxvPtr)
  let Auxv := MallocngAuxvAt auxvPtr
  let Argv := CryptoVerification.SignalSession.Cli.argvAt (sm.readReg64 .x1)
    (("libsignal-cli" :: i.argv).map bytesOfString)
  let Stk := stackAt sm.sp cliMainStk
  let RwBss := mallocngRwBssAt mmpl
  let Fini := muslFiniFr elf.entry
  have hmemRw : sm.mem ⊨ RwBss ∗ Rt ∗ Libc8 ∗ Auxv ∗ (Argv ∗ Stk ∗ Statics ∗ Fini) := by
    have heq :
        ((Argv ∗ Stk ∗ (Rt ∗ Libc8 ∗ Auxv) ∗ (RwBss ∗ Statics)) ∗ Fini) =
        (RwBss ∗ Rt ∗ Libc8 ∗ Auxv ∗ (Argv ∗ Stk ∗ Statics ∗ Fini)) := by sep_ac_rfl
    dsimp only [CryptoVerification.SignalSession.InitStack.cliStrs, List.map_cons] at hmem
    exact heq ▸ hmem
  have hmemRo :=
    satisfies_mallocngRoTablesAt_of_keepsFrozen (hRo i s0 hload) hsteps.keepsFrozen hmemRw
  have hmem' :
      sm.mem ⊨
        VerifiedLibraries.mallocngLib.dataInit mmpl ∗
          Rt ∗ Libc8 ∗ Auxv ∗ (Argv ∗ Stk ∗ Statics ∗ Fini) := by
    rw [mallocngLib_dataInit_eq_ro_rw mmpl]
    have hassoc :
        (MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗
          (RwBss ∗ Rt ∗ Libc8 ∗ Auxv ∗ (Argv ∗ Stk ∗ Statics ∗ Fini))) =
        ((MallocngRoTablesAt (mallocngAddrsOfPlacement mmpl) ∗ RwBss) ∗
          Rt ∗ Libc8 ∗ Auxv ∗ (Argv ∗ Stk ∗ Statics ∗ Fini)) := by sep_ac_rfl
    exact hassoc ▸ hmemRo
  obtain ⟨γ, hPool⟩ := fineHookBudgetPool_of_inputs hCL (cliStackShape_cliInputs i)
    hLayout hload hvm htpLo htpHi hmem'
  let A := fineHookRustCliAllocBudget γ mmpl sm.tpidrEl0 elf.brkStart
  have hEntry : sm.mem ⊨
      mainEntryPrePlaced CodeOk A lim fineCostModel.init cliMainStk Statics i sm ∗ Fini := by
    simp only [mainEntryPrePlaced, LibsignalBinary.Proofs.SignalSession.Cli.Main.TopBudget.mainFrame,
      sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hCO, hstkSp⟩, ?_⟩
    have heq2 :
        (A.pool lim fineCostModel.init sm ∗ (Argv ∗ Stk ∗ Statics ∗ Fini)) =
        (Argv ∗ Stk ∗ A.pool lim fineCostModel.init sm ∗ Statics ∗ Fini) := by sep_ac_rfl
    exact heq2 ▸ hPool
  refine ⟨s0, sm, Fini, γ, hload, hsteps, hpc, hrun, hal, hfs, htr, hx0, hEntry, ?_⟩
  intro sr hstepsR hret hmemR
  have hL : ({ base := elf.entry, code } : Program).CodeLoaded sm.mem :=
    hsteps.codeLoaded (codeLoaded_of_text hMusl hE.1 hE.2 hload)
  exact musl_exit_ofProg hstP hovrP hsvcP hMusl.entry_page
    (fun k hk => hnoHook k (by omega)) hfE hL hlr hal hstepsR hret hmemR

theorem muslHarnessFinePerInput_of_muslStartFine_blockProgram
    {mpl mmpl : Obj.MultiPlacement}
    {ext : CliHooks → String → Option (State → State)} {idx : Nat} {W : CliHooks}
    {elf : ElfImage} {code : List (BitVec 8)} {lim : BudgetLimits}
    {dynPageImm pageImm : BitVec 64} {addImm : BitVec 12}
    {CodeOk : Memory → Prop} {Statics : SepProp} {S : Nat → Prop}
    (hnoHook : ∀ k : BitVec 64, k.toNat < 0xb90 →
      (cliProgExtPlacedAt mpl ext idx W).externAt? (elf.entry + k) = none)
    (hMusl : CliElfMusl elf code)
    (hlibc : (mallocngAddrsOfPlacement mmpl).libc = elf.entry + 0x21e8#64)
    (hfS : MuslStartFetchAt ({ code } : Program) 0#64 dynPageImm pageImm addImm)
    (hfE : MuslExitFetch ({ code } : Program) 0#64)
    (hLayout : CliElfMallocngLayout elf lim)
    (hmainPc : mpl.base idx = mainPcOf elf.entry pageImm addImm)
    (hCodeOk : ∀ (i : Inputs) (s0 sm : State),
      elf.loadState (cliInputs i) = .ok s0 →
      s0.mem.KeepsFrozen sm.mem →
      CodeOk sm.mem ∧ VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem)
    (hRo : ∀ (i : Inputs) (s0 : State),
      elf.loadState (cliInputs i) = .ok s0 →
      MallocngRoTablesInMem mmpl s0.mem)
    (hSupp : ∀ (i : Inputs) (s0 : State),
      elf.loadState (cliInputs i) = .ok s0 →
      SupportedOn 0#64 S s0.mem (mallocngRwBssAt mmpl ∗ Statics))
    (hS : ∀ k, S k → k < stackBase ∧
      ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600)) :
    MuslHarnessFinePerInput elf (cliProgExtPlacedAt mpl ext idx W) (mpl.base idx)
      mmpl lim fineCostModel.init cliMainStk CodeOk Statics := by
  rw [hmainPc]
  exact muslHarnessFinePerInput_of_muslStartFine
    (blockProgram_stubs_lt libsignalSessionLib mpl idx (ext W) (fun _ => none) Syscall.standard)
    (fun _ => rfl) rfl hnoHook hMusl hlibc hfS hfE hLayout hCodeOk hRo hSupp hS

end LibsignalBinary.Proofs.SignalSession.Cli.M24.CliElfMallocngHarness
